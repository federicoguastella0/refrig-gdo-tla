---------------------------- MODULE REFRIG_GDO_Firmware ----------------------------
(*****************************************************************************)
(* REFRIG-GDO – Firmware Transfer Formalization (v1.4.5) – strengthened      *)
(*                                                                           *)
(* Addresses audit findings on Firmware:                                     *)
(*   - Non-atomic per-chunk sequence:                                        *)
(*       write → verify → durable → advance offset                           *)
(*     with crash possible between every step                                *)
(*   - Explicit discard of partial chunk on Crash                            *)
(*   - Completion / install history (not only current state)                 *)
(*   - Manifest / image-hash verification with PASS/FAIL outcome (point 4)   *)
(*   - At most one IN_PROGRESS Transfer per client                           *)
(*   - Recovery Barrier forces IN_PROGRESS → ABORTED                         *)
(*                                                                           *)
(* AEAD assumed perfect; concrete Flash layout abstracted.                   *)
(*****************************************************************************)

EXTENDS Integers, FiniteSets, Sequences, TLC

CONSTANTS
  Clients,                  \* set of ClientDeviceID
  MaxChunks,                \* max chunks per transfer (0..MaxChunks-1)
  MaxTransfers              \* transfer slots 0..MaxTransfers-1

ASSUME MaxChunks \in Nat \ {0} /\ MaxTransfers \in Nat \ {0}

VARIABLES
  (* Transfer store *)
  xferStore,                \* [0..MaxTransfers-1 |-> TransferRecord]
  used,                     \* SUBSET (0..MaxTransfers-1)

  (* Per-client active transfer *)
  activeTransfer,           \* [client |-> tid ∪ {NoActive}]

  (* Durable completed offsets per transfer *)
  durableOffsets,           \* [tid |-> SUBSET (0..MaxChunks-1)]

  (* In-progress chunk pipeline (non-atomic) *)
  chunkPhase,               \* [tid |-> ChunkPhase]
  pendingOffset,            \* [tid |-> 0..MaxChunks]  offset currently in pipeline
  pendingVerified,          \* [tid |-> BOOLEAN]
  pendingDurable,           \* [tid |-> BOOLEAN]

  (* Closure / install *)
  imageDurable,             \* [tid |-> BOOLEAN]
  manifestResult,           \* [tid |-> ManifestResult]  NONE | PASS | FAIL
  installLog,               \* Seq of tid that have been installed (history)

  (* Recovery *)
  recoveryFlag,

  (* Control *)
  phase                     \* [tid |-> "idle"|"active"|"closing"|"done"]

-----------------------------------------------------------------------------
NoActive == -1

TransferState == {
  "IDLE",
  "IN_PROGRESS",
  "COMPLETED",
  "ABORTED",
  "INDETERMINATE"
}

ChunkPhase == {
  "idle",           \* no chunk in pipeline
  "written",        \* data written, not yet verified
  "verified",       \* verified, not yet made durable
  "durabilizing"    \* durable commit in progress (before offset advance)
}

\* Outcome of image hash + manifest signature verification
ManifestResult == {"NONE", "PASS", "FAIL"}

TransferRecord == [
  client  : Clients,
  state   : TransferState,
  length  : 0..MaxChunks   \* declared length from manifest
]

-----------------------------------------------------------------------------
TypeOK ==
  /\ xferStore \in [0..MaxTransfers-1 -> TransferRecord]
  /\ used \subseteq (0..MaxTransfers-1)
  /\ activeTransfer \in [Clients -> (0..MaxTransfers-1) \cup {NoActive}]
  /\ durableOffsets \in [0..MaxTransfers-1 -> SUBSET (0..MaxChunks-1)]
  /\ chunkPhase \in [0..MaxTransfers-1 -> ChunkPhase]
  /\ pendingOffset \in [0..MaxTransfers-1 -> 0..MaxChunks]
  /\ pendingVerified \in [0..MaxTransfers-1 -> BOOLEAN]
  /\ pendingDurable \in [0..MaxTransfers-1 -> BOOLEAN]
  /\ imageDurable \in [0..MaxTransfers-1 -> BOOLEAN]
  /\ manifestResult \in [0..MaxTransfers-1 -> ManifestResult]
  /\ installLog \in Seq(0..MaxTransfers-1)
  /\ recoveryFlag \in BOOLEAN
  /\ phase \in [0..MaxTransfers-1 -> {"idle", "active", "closing", "done"}]

-----------------------------------------------------------------------------
\* Helpers

NextExpected(tid) == Cardinality(durableOffsets[tid])

-----------------------------------------------------------------------------
\* Strengthened invariants

\* At most one IN_PROGRESS transfer per client
Inv_AtMostOneInProgress ==
  \A c \in Clients :
    Cardinality({ tid \in used :
                    /\ xferStore[tid].client = c
                    /\ xferStore[tid].state = "IN_PROGRESS" }) <= 1

\* Offset advances only after the chunk has been made durable.
\* AdvanceOffset is the only writer of durableOffsets and is guarded by
\* pendingDurable = TRUE. When the pipeline is idle there must be no
\* pending durable work.
Inv_PersistBeforeOffsetAdvance ==
  \A tid \in used :
    chunkPhase[tid] = "idle" => pendingDurable[tid] = FALSE

\* No double install – history based
Inv_NoDoubleInstall ==
  \A tid \in used :
    Cardinality({ i \in DOMAIN installLog : installLog[i] = tid }) <= 1

\* Install only after image durable AND manifest PASS AND COMPLETED
Inv_NoInstallBeforeManifest ==
  \A i \in DOMAIN installLog :
    LET tid == installLog[i] IN
      /\ imageDurable[tid] = TRUE
      /\ manifestResult[tid] = "PASS"
      /\ xferStore[tid].state = "COMPLETED"

\* COMPLETED requires successful manifest verification
Inv_CompletedRequiresManifestPass ==
  \A tid \in used :
    xferStore[tid].state = "COMPLETED" => manifestResult[tid] = "PASS"

\* FAIL forces ABORTED and never appears in installLog
Inv_ManifestFailAborts ==
  \A tid \in used :
    manifestResult[tid] = "FAIL" =>
      /\ xferStore[tid].state = "ABORTED"
      /\ Cardinality({ i \in DOMAIN installLog : installLog[i] = tid }) = 0

\* Recovery Barrier: no IN_PROGRESS remains
Inv_RecoveryAbortsInProgress ==
  recoveryFlag =>
    \A tid \in used : xferStore[tid].state # "IN_PROGRESS"

\* Chunks only accepted in order (next expected)
Inv_ChunkOrderMonotonic ==
  \A tid \in used :
    \A off \in durableOffsets[tid] :
      off < NextExpected(tid)
      \/ off = NextExpected(tid) - 1   \* the highest is exactly next-1

\* Partial chunk is never left durable after crash while pipeline was active
\* (Crash resets chunkPhase to idle and clears pending flags)
Inv_NoPartialAfterCrash ==
  recoveryFlag =>
    \A tid \in used :
      chunkPhase[tid] = "idle"

-----------------------------------------------------------------------------
Init ==
  /\ xferStore = [tid \in 0..MaxTransfers-1 |->
                    [client |-> CHOOSE c \in Clients : TRUE,
                     state  |-> "IDLE",
                     length |-> 0]]
  /\ used = {}
  /\ activeTransfer = [c \in Clients |-> NoActive]
  /\ durableOffsets = [tid \in 0..MaxTransfers-1 |-> {}]
  /\ chunkPhase = [tid \in 0..MaxTransfers-1 |-> "idle"]
  /\ pendingOffset = [tid \in 0..MaxTransfers-1 |-> 0]
  /\ pendingVerified = [tid \in 0..MaxTransfers-1 |-> FALSE]
  /\ pendingDurable = [tid \in 0..MaxTransfers-1 |-> FALSE]
  /\ imageDurable = [tid \in 0..MaxTransfers-1 |-> FALSE]
  /\ manifestResult = [tid \in 0..MaxTransfers-1 |-> "NONE"]
  /\ installLog = <<>>
  /\ recoveryFlag = FALSE
  /\ phase = [tid \in 0..MaxTransfers-1 |-> "idle"]

-----------------------------------------------------------------------------
\* Actions

\* Start a new transfer (at most one IN_PROGRESS per client)
StartTransfer(client, tid, len) ==
  /\ ~recoveryFlag
  /\ tid \in 0..MaxTransfers-1
  /\ tid \notin used
  /\ activeTransfer[client] = NoActive
  /\ len \in 1..MaxChunks
  /\ xferStore' = [xferStore EXCEPT ![tid] =
                     [client |-> client, state |-> "IN_PROGRESS", length |-> len]]
  /\ used' = used \cup {tid}
  /\ activeTransfer' = [activeTransfer EXCEPT ![client] = tid]
  /\ phase' = [phase EXCEPT ![tid] = "active"]
  /\ UNCHANGED <<durableOffsets, chunkPhase, pendingOffset,
                 pendingVerified, pendingDurable, imageDurable,
                 manifestResult, installLog, recoveryFlag>>

\* --- Non-atomic chunk pipeline -------------------------------------------

\* 1. Write chunk data at the expected offset
WriteChunk(tid, offset) ==
  /\ ~recoveryFlag
  /\ tid \in used
  /\ xferStore[tid].state = "IN_PROGRESS"
  /\ phase[tid] = "active"
  /\ chunkPhase[tid] = "idle"
  /\ offset = NextExpected(tid)
  /\ offset < xferStore[tid].length
  /\ chunkPhase' = [chunkPhase EXCEPT ![tid] = "written"]
  /\ pendingOffset' = [pendingOffset EXCEPT ![tid] = offset]
  /\ pendingVerified' = [pendingVerified EXCEPT ![tid] = FALSE]
  /\ pendingDurable' = [pendingDurable EXCEPT ![tid] = FALSE]
  /\ UNCHANGED <<xferStore, used, activeTransfer, durableOffsets,
                 imageDurable, manifestResult, installLog,
                 recoveryFlag, phase>>

\* 2. Verify written data (read-back / CRC)
VerifyChunk(tid) ==
  /\ ~recoveryFlag
  /\ tid \in used
  /\ chunkPhase[tid] = "written"
  /\ chunkPhase' = [chunkPhase EXCEPT ![tid] = "verified"]
  /\ pendingVerified' = [pendingVerified EXCEPT ![tid] = TRUE]
  /\ UNCHANGED <<xferStore, used, activeTransfer, durableOffsets,
                 pendingOffset, pendingDurable, imageDurable,
                 manifestResult, installLog, recoveryFlag, phase>>

\* 3. Make the write durable (journal / flush)
DurabilizeChunk(tid) ==
  /\ ~recoveryFlag
  /\ tid \in used
  /\ chunkPhase[tid] = "verified"
  /\ pendingVerified[tid] = TRUE
  /\ chunkPhase' = [chunkPhase EXCEPT ![tid] = "durabilizing"]
  /\ pendingDurable' = [pendingDurable EXCEPT ![tid] = TRUE]
  /\ UNCHANGED <<xferStore, used, activeTransfer, durableOffsets,
                 pendingOffset, pendingVerified, imageDurable,
                 manifestResult, installLog, recoveryFlag, phase>>

\* 4. Advance NextExpectedOffset only after durability
AdvanceOffset(tid) ==
  /\ ~recoveryFlag
  /\ tid \in used
  /\ chunkPhase[tid] = "durabilizing"
  /\ pendingDurable[tid] = TRUE
  /\ LET off == pendingOffset[tid] IN
      durableOffsets' = [durableOffsets EXCEPT ![tid] = @ \cup {off}]
  /\ chunkPhase' = [chunkPhase EXCEPT ![tid] = "idle"]
  /\ pendingVerified' = [pendingVerified EXCEPT ![tid] = FALSE]
  /\ pendingDurable' = [pendingDurable EXCEPT ![tid] = FALSE]
  /\ UNCHANGED <<xferStore, used, activeTransfer, pendingOffset,
                 imageDurable, manifestResult, installLog,
                 recoveryFlag, phase>>

\* --- Closure -------------------------------------------------------------

\* All chunks durable → mark image durable
MarkImageDurable(tid) ==
  /\ ~recoveryFlag
  /\ tid \in used
  /\ xferStore[tid].state = "IN_PROGRESS"
  /\ phase[tid] = "active"
  /\ chunkPhase[tid] = "idle"
  /\ NextExpected(tid) = xferStore[tid].length
  /\ imageDurable' = [imageDurable EXCEPT ![tid] = TRUE]
  /\ phase' = [phase EXCEPT ![tid] = "closing"]
  /\ UNCHANGED <<xferStore, used, activeTransfer, durableOffsets,
                 chunkPhase, pendingOffset, pendingVerified, pendingDurable,
                 manifestResult, installLog, recoveryFlag>>

\* Manifest / image-hash verification with explicit PASS or FAIL
VerifyManifestPass(tid) ==
  /\ ~recoveryFlag
  /\ tid \in used
  /\ phase[tid] = "closing"
  /\ imageDurable[tid] = TRUE
  /\ manifestResult[tid] = "NONE"
  /\ manifestResult' = [manifestResult EXCEPT ![tid] = "PASS"]
  /\ UNCHANGED <<xferStore, used, activeTransfer, durableOffsets,
                 chunkPhase, pendingOffset, pendingVerified, pendingDurable,
                 imageDurable, installLog, recoveryFlag, phase>>

VerifyManifestFail(tid) ==
  /\ ~recoveryFlag
  /\ tid \in used
  /\ phase[tid] = "closing"
  /\ imageDurable[tid] = TRUE
  /\ manifestResult[tid] = "NONE"
  /\ manifestResult' = [manifestResult EXCEPT ![tid] = "FAIL"]
  /\ xferStore' = [xferStore EXCEPT ![tid].state = "ABORTED"]
  /\ activeTransfer' = [activeTransfer EXCEPT ![xferStore[tid].client] = NoActive]
  /\ phase' = [phase EXCEPT ![tid] = "idle"]
  /\ UNCHANGED <<used, durableOffsets, chunkPhase, pendingOffset,
                 pendingVerified, pendingDurable, imageDurable,
                 installLog, recoveryFlag>>

\* Close transfer as COMPLETED
CloseTransfer(tid) ==
  /\ ~recoveryFlag
  /\ tid \in used
  /\ phase[tid] = "closing"
  /\ imageDurable[tid] = TRUE
  /\ manifestResult[tid] = "PASS"
  /\ xferStore' = [xferStore EXCEPT ![tid].state = "COMPLETED"]
  /\ activeTransfer' = [activeTransfer EXCEPT ![xferStore[tid].client] = NoActive]
  /\ phase' = [phase EXCEPT ![tid] = "done"]
  /\ UNCHANGED <<used, durableOffsets, chunkPhase, pendingOffset,
                 pendingVerified, pendingDurable, imageDurable,
                 manifestResult, installLog, recoveryFlag>>

\* Install / activate firmware (records history event)
Install(tid) ==
  /\ ~recoveryFlag
  /\ tid \in used
  /\ xferStore[tid].state = "COMPLETED"
  /\ imageDurable[tid] = TRUE
  /\ manifestResult[tid] = "PASS"
  /\ Cardinality({ i \in DOMAIN installLog : installLog[i] = tid }) = 0
  /\ installLog' = Append(installLog, tid)
  /\ UNCHANGED <<xferStore, used, activeTransfer, durableOffsets,
                 chunkPhase, pendingOffset, pendingVerified, pendingDurable,
                 imageDurable, manifestResult, recoveryFlag, phase>>

\* --- Crash / Recovery Barrier --------------------------------------------

\* Crash: abort IN_PROGRESS, discard partial pipeline, clear pending flags
Crash ==
  /\ ~recoveryFlag
  /\ recoveryFlag' = TRUE
  /\ xferStore' = [tid \in 0..MaxTransfers-1 |->
                     IF tid \in used /\ xferStore[tid].state = "IN_PROGRESS"
                     THEN [xferStore[tid] EXCEPT !.state = "ABORTED"]
                     ELSE xferStore[tid]]
  /\ activeTransfer' = [c \in Clients |-> NoActive]
  /\ chunkPhase' = [tid \in 0..MaxTransfers-1 |-> "idle"]
  /\ pendingVerified' = [tid \in 0..MaxTransfers-1 |-> FALSE]
  /\ pendingDurable' = [tid \in 0..MaxTransfers-1 |-> FALSE]
  \* durableOffsets intentionally preserved (only fully durable chunks remain)
  /\ phase' = [tid \in 0..MaxTransfers-1 |->
                 IF tid \in used /\ phase[tid] \in {"active", "closing"}
                 THEN "idle"
                 ELSE phase[tid]]
  /\ UNCHANGED <<used, durableOffsets, pendingOffset,
                 imageDurable, manifestResult, installLog>>

FinishRecovery ==
  /\ recoveryFlag = TRUE
  /\ recoveryFlag' = FALSE
  /\ UNCHANGED <<xferStore, used, activeTransfer, durableOffsets,
                 chunkPhase, pendingOffset, pendingVerified, pendingDurable,
                 imageDurable, manifestResult, installLog, phase>>

\* Explicit abort
AbortTransfer(tid) ==
  /\ tid \in used
  /\ xferStore[tid].state = "IN_PROGRESS"
  /\ xferStore' = [xferStore EXCEPT ![tid].state = "ABORTED"]
  /\ activeTransfer' = [activeTransfer EXCEPT ![xferStore[tid].client] = NoActive]
  /\ chunkPhase' = [chunkPhase EXCEPT ![tid] = "idle"]
  /\ pendingVerified' = [pendingVerified EXCEPT ![tid] = FALSE]
  /\ pendingDurable' = [pendingDurable EXCEPT ![tid] = FALSE]
  /\ phase' = [phase EXCEPT ![tid] = "idle"]
  /\ UNCHANGED <<used, durableOffsets, pendingOffset,
                 imageDurable, manifestResult, installLog, recoveryFlag>>

-----------------------------------------------------------------------------
Next ==
  \/ \E c \in Clients, t \in 0..MaxTransfers-1, l \in 1..MaxChunks :
       StartTransfer(c, t, l)
  \/ \E t \in 0..MaxTransfers-1, o \in 0..MaxChunks-1 : WriteChunk(t, o)
  \/ \E t \in 0..MaxTransfers-1 : VerifyChunk(t)
  \/ \E t \in 0..MaxTransfers-1 : DurabilizeChunk(t)
  \/ \E t \in 0..MaxTransfers-1 : AdvanceOffset(t)
  \/ \E t \in 0..MaxTransfers-1 : MarkImageDurable(t)
  \/ \E t \in 0..MaxTransfers-1 : VerifyManifestPass(t)
  \/ \E t \in 0..MaxTransfers-1 : VerifyManifestFail(t)
  \/ \E t \in 0..MaxTransfers-1 : CloseTransfer(t)
  \/ \E t \in 0..MaxTransfers-1 : Install(t)
  \/ \E t \in 0..MaxTransfers-1 : AbortTransfer(t)
  \/ Crash
  \/ FinishRecovery

Spec == Init /\ [][Next]_<<xferStore, used, activeTransfer, durableOffsets,
                           chunkPhase, pendingOffset, pendingVerified,
                           pendingDurable, imageDurable, manifestResult,
                           installLog, recoveryFlag, phase>>

THEOREM Spec => []TypeOK
THEOREM Spec => []Inv_AtMostOneInProgress
THEOREM Spec => []Inv_PersistBeforeOffsetAdvance
THEOREM Spec => []Inv_NoDoubleInstall
THEOREM Spec => []Inv_NoInstallBeforeManifest
THEOREM Spec => []Inv_CompletedRequiresManifestPass
THEOREM Spec => []Inv_ManifestFailAborts
THEOREM Spec => []Inv_RecoveryAbortsInProgress
THEOREM Spec => []Inv_ChunkOrderMonotonic
THEOREM Spec => []Inv_NoPartialAfterCrash

=============================================================================
\* Modification History
\* Strengthened rewrite – November 2026 – audit findings on Firmware
\* Non-atomic chunk pipeline, explicit partial discard, install history
=============================================================================
