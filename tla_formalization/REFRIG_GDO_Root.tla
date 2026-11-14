---------------------------- MODULE REFRIG_GDO_Root ----------------------------
(*****************************************************************************)
(* REFRIG-GDO – Root composition (v1.4.5)                                    *)
(*                                                                           *)
(* Composes the three strengthened machines under a single specification:    *)
(*   - Epoch / anti-replay / 0x40-0x41                                       *)
(*   - Transactions + Recovery Barrier + physical uncertainty window         *)
(*   - Firmware Transfer (non-atomic chunk pipeline)                         *)
(*                                                                           *)
(* Goal: expose interactions that separate models cannot see, in particular  *)
(* Recovery Barrier affecting both ordinary transactions and transfers, and  *)
(* the constraint that ordinary traffic respects the current Epoch state.    *)
(*                                                                           *)
(* This is still a high-level composition: AEAD is assumed perfect; concrete *)
(* framing and NVM layout remain abstracted.                                 *)
(*****************************************************************************)

EXTENDS Integers, FiniteSets, Sequences, TLC

CONSTANTS
  Clients,
  MaxEpoch,
  MaxSeq,
  SoftRotationThreshold,
  MaxTx,
  MaxHash,
  MaxChunks,
  MaxTransfers

ASSUME
  /\ MaxEpoch \in Nat \ {0}
  /\ MaxSeq \in Nat \ {0}
  /\ SoftRotationThreshold \in Nat /\ SoftRotationThreshold > 0
  /\ SoftRotationThreshold <= MaxSeq
  /\ MaxTx \in Nat \ {0}
  /\ MaxHash \in Nat \ {0}
  /\ MaxChunks \in Nat \ {0}
  /\ MaxTransfers \in Nat \ {0}

-----------------------------------------------------------------------------
\* Shared / cross-cutting state

VARIABLES
  (* ---- Epoch machine ---- *)
  senderEpoch,
  seqNum,
  senderRebooted,
  lastAcceptedEpoch,
  acceptedPairs,
  syncState,
  proposedEpoch,
  syncAttempts,
  hasInflight,
  inflightEpoch,
  inflightSeq,
  epochPc,

  (* ---- Core / transactions ---- *)
  txStore,
  txUsed,
  actuationLog,
  physicalEffectLog,
  identityLocks,
  recoveryLock,
  resolutionEvidence,
  txPhase,

  (* ---- Firmware ---- *)
  xferStore,
  xferUsed,
  activeTransfer,
  durableOffsets,
  chunkPhase,
  pendingOffset,
  pendingVerified,
  pendingDurable,
  imageDurable,
  manifestChecked,
  installLog,
  fwPhase,

  (* ---- Shared Recovery Barrier ---- *)
  recoveryFlag

-----------------------------------------------------------------------------
NoActive == -1

TxState == {
  "IDLE", "NEW", "PERSISTED", "DISPATCHED", "EFFECT_DONE",
  "COMPLETED", "INDETERMINATE", "RESOLVED", "REJECTED"
}
TxPhase == {"idle", "persisting", "dispatching", "awaiting_effect", "recording", "done"}
TxRecord == [
  client : Clients, appTxId : 0..MaxTx-1,
  state : TxState, payloadHash : 0..MaxHash, durable : BOOLEAN
]

TransferState == {"IDLE", "IN_PROGRESS", "COMPLETED", "ABORTED", "INDETERMINATE"}
ChunkPhase == {"idle", "written", "verified", "durabilizing"}
FwPhase == {"idle", "active", "closing", "done"}
TransferRecord == [client : Clients, state : TransferState, length : 0..MaxChunks]

-----------------------------------------------------------------------------
TypeOK ==
  (* Epoch *)
  /\ senderEpoch \in 0..MaxEpoch
  /\ seqNum \in 0..MaxSeq
  /\ senderRebooted \in BOOLEAN
  /\ lastAcceptedEpoch \in 0..MaxEpoch
  /\ acceptedPairs \in Seq((0..MaxEpoch) \X (0..MaxSeq))
  /\ syncState \in {"idle", "req_sent", "resp_pending", "done"}
  /\ proposedEpoch \in 0..MaxEpoch
  /\ syncAttempts \in 0..3
  /\ hasInflight \in BOOLEAN
  /\ inflightEpoch \in 0..MaxEpoch
  /\ inflightSeq \in 0..MaxSeq
  /\ epochPc \in {"idle", "sending", "syncing"}
  (* Core *)
  /\ txStore \in [0..MaxTx-1 -> TxRecord]
  /\ txUsed \subseteq (0..MaxTx-1)
  /\ actuationLog \in Seq(0..MaxTx-1)
  /\ physicalEffectLog \in Seq(0..MaxTx-1)
  /\ identityLocks \subseteq (0..MaxTx-1)
  /\ recoveryLock \in BOOLEAN
  /\ resolutionEvidence \in [0..MaxTx-1 -> BOOLEAN]
  /\ txPhase \in [0..MaxTx-1 -> TxPhase]
  (* Firmware *)
  /\ xferStore \in [0..MaxTransfers-1 -> TransferRecord]
  /\ xferUsed \subseteq (0..MaxTransfers-1)
  /\ activeTransfer \in [Clients -> (0..MaxTransfers-1) \cup {NoActive}]
  /\ durableOffsets \in [0..MaxTransfers-1 -> SUBSET (0..MaxChunks-1)]
  /\ chunkPhase \in [0..MaxTransfers-1 -> ChunkPhase]
  /\ pendingOffset \in [0..MaxTransfers-1 -> 0..MaxChunks]
  /\ pendingVerified \in [0..MaxTransfers-1 -> BOOLEAN]
  /\ pendingDurable \in [0..MaxTransfers-1 -> BOOLEAN]
  /\ imageDurable \in [0..MaxTransfers-1 -> BOOLEAN]
  /\ manifestChecked \in [0..MaxTransfers-1 -> BOOLEAN]
  /\ installLog \in Seq(0..MaxTransfers-1)
  /\ fwPhase \in [0..MaxTransfers-1 -> FwPhase]
  (* Shared *)
  /\ recoveryFlag \in BOOLEAN

-----------------------------------------------------------------------------
\* Cross-cutting invariants

Inv_NonceUniqueness ==
  \A i, j \in DOMAIN acceptedPairs :
    i # j => acceptedPairs[i] # acceptedPairs[j]

Inv_NoDoubleActuation ==
  \A tid \in txUsed :
    Cardinality({ i \in DOMAIN actuationLog : actuationLog[i] = tid }) <= 1

Inv_PersistBeforeDispatch ==
  \A tid \in txUsed :
    Cardinality({ i \in DOMAIN actuationLog : actuationLog[i] = tid }) > 0
      => txStore[tid].durable = TRUE

Inv_NoActuationDuringRecovery ==
  recoveryFlag =>
    /\ \A tid \in txUsed : txPhase[tid] \notin {"dispatching", "awaiting_effect", "recording"}
    /\ \A tid \in xferUsed : xferStore[tid].state # "IN_PROGRESS"

Inv_NoDeadlockUnderRecovery ==
  recoveryFlag =>
    /\ recoveryLock = TRUE
    /\ identityLocks = {}

Inv_AuthorizedResolution ==
  \A tid \in txUsed :
    txStore[tid].state = "RESOLVED" => resolutionEvidence[tid] = TRUE

Inv_NoDoubleInstall ==
  \A tid \in xferUsed :
    Cardinality({ i \in DOMAIN installLog : installLog[i] = tid }) <= 1

Inv_NoInstallBeforeManifest ==
  \A i \in DOMAIN installLog :
    LET tid == installLog[i] IN
      /\ imageDurable[tid] = TRUE
      /\ manifestChecked[tid] = TRUE
      /\ xferStore[tid].state = "COMPLETED"

Inv_AtMostOneTransferPerClient ==
  \A c \in Clients :
    Cardinality({ tid \in xferUsed :
                    /\ xferStore[tid].client = c
                    /\ xferStore[tid].state = "IN_PROGRESS" }) <= 1

\* Recovery is global: both machines see the same barrier
Inv_SharedRecovery ==
  recoveryFlag => recoveryLock = TRUE

-----------------------------------------------------------------------------
Init ==
  (* Epoch *)
  /\ senderEpoch = 0 /\ seqNum = 0 /\ senderRebooted = FALSE
  /\ lastAcceptedEpoch = 0 /\ acceptedPairs = <<>>
  /\ syncState = "idle" /\ proposedEpoch = 0 /\ syncAttempts = 0
  /\ hasInflight = FALSE /\ inflightEpoch = 0 /\ inflightSeq = 0
  /\ epochPc = "idle"
  (* Core *)
  /\ txStore = [tid \in 0..MaxTx-1 |->
                  [client |-> CHOOSE c \in Clients : TRUE,
                   appTxId |-> 0, state |-> "IDLE",
                   payloadHash |-> 0, durable |-> FALSE]]
  /\ txUsed = {}
  /\ actuationLog = <<>> /\ physicalEffectLog = <<>>
  /\ identityLocks = {} /\ recoveryLock = FALSE
  /\ resolutionEvidence = [tid \in 0..MaxTx-1 |-> FALSE]
  /\ txPhase = [tid \in 0..MaxTx-1 |-> "idle"]
  (* Firmware *)
  /\ xferStore = [tid \in 0..MaxTransfers-1 |->
                    [client |-> CHOOSE c \in Clients : TRUE,
                     state |-> "IDLE", length |-> 0]]
  /\ xferUsed = {}
  /\ activeTransfer = [c \in Clients |-> NoActive]
  /\ durableOffsets = [tid \in 0..MaxTransfers-1 |-> {}]
  /\ chunkPhase = [tid \in 0..MaxTransfers-1 |-> "idle"]
  /\ pendingOffset = [tid \in 0..MaxTransfers-1 |-> 0]
  /\ pendingVerified = [tid \in 0..MaxTransfers-1 |-> FALSE]
  /\ pendingDurable = [tid \in 0..MaxTransfers-1 |-> FALSE]
  /\ imageDurable = [tid \in 0..MaxTransfers-1 |-> FALSE]
  /\ manifestChecked = [tid \in 0..MaxTransfers-1 |-> FALSE]
  /\ installLog = <<>>
  /\ fwPhase = [tid \in 0..MaxTransfers-1 |-> "idle"]
  (* Shared *)
  /\ recoveryFlag = FALSE

-----------------------------------------------------------------------------
\* --- Epoch actions (subset, composed) ------------------------------------

AlreadyAccepted(e, s) ==
  \E i \in DOMAIN acceptedPairs : acceptedPairs[i] = <<e, s>>

E_SendOrdinary ==
  /\ ~recoveryFlag
  /\ epochPc = "idle" /\ syncState = "idle"
  /\ seqNum < SoftRotationThreshold /\ seqNum < MaxSeq
  /\ seqNum' = seqNum + 1
  /\ hasInflight' = TRUE
  /\ inflightEpoch' = senderEpoch
  /\ inflightSeq' = seqNum + 1
  /\ epochPc' = "sending"
  /\ senderRebooted' = FALSE
  /\ UNCHANGED <<senderEpoch, lastAcceptedEpoch, acceptedPairs, syncState,
                 proposedEpoch, syncAttempts,
                 txStore, txUsed, actuationLog, physicalEffectLog,
                 identityLocks, recoveryLock, resolutionEvidence, txPhase,
                 xferStore, xferUsed, activeTransfer, durableOffsets,
                 chunkPhase, pendingOffset, pendingVerified, pendingDurable,
                 imageDurable, manifestChecked, installLog, fwPhase,
                 recoveryFlag>>

E_AcceptOrdinary ==
  /\ epochPc = "sending" /\ hasInflight
  /\ LET e == inflightEpoch s == inflightSeq IN
       /\ \/ e = lastAcceptedEpoch \/ e = lastAcceptedEpoch + 1
       /\ ~AlreadyAccepted(e, s)
       /\ acceptedPairs' = Append(acceptedPairs, <<e, s>>)
       /\ IF e = lastAcceptedEpoch + 1
          THEN lastAcceptedEpoch' = e
          ELSE UNCHANGED lastAcceptedEpoch
  /\ hasInflight' = FALSE /\ inflightEpoch' = 0 /\ inflightSeq' = 0
  /\ epochPc' = "idle"
  /\ UNCHANGED <<senderEpoch, seqNum, senderRebooted, syncState,
                 proposedEpoch, syncAttempts,
                 txStore, txUsed, actuationLog, physicalEffectLog,
                 identityLocks, recoveryLock, resolutionEvidence, txPhase,
                 xferStore, xferUsed, activeTransfer, durableOffsets,
                 chunkPhase, pendingOffset, pendingVerified, pendingDurable,
                 imageDurable, manifestChecked, installLog, fwPhase,
                 recoveryFlag>>

E_SoftRotate ==
  /\ epochPc \in {"idle", "sending"}
  /\ seqNum >= SoftRotationThreshold /\ senderEpoch < MaxEpoch
  /\ senderEpoch' = senderEpoch + 1 /\ seqNum' = 0
  /\ proposedEpoch' = senderEpoch + 1
  /\ syncState' = "req_sent" /\ syncAttempts' = 0
  /\ hasInflight' = FALSE /\ inflightEpoch' = 0 /\ inflightSeq' = 0
  /\ epochPc' = "syncing" /\ senderRebooted' = FALSE
  /\ UNCHANGED <<lastAcceptedEpoch, acceptedPairs,
                 txStore, txUsed, actuationLog, physicalEffectLog,
                 identityLocks, recoveryLock, resolutionEvidence, txPhase,
                 xferStore, xferUsed, activeTransfer, durableOffsets,
                 chunkPhase, pendingOffset, pendingVerified, pendingDurable,
                 imageDurable, manifestChecked, installLog, fwPhase,
                 recoveryFlag>>

E_DeliverSync ==
  /\ epochPc = "syncing" /\ syncState = "req_sent"
  /\ proposedEpoch >= lastAcceptedEpoch
  /\ lastAcceptedEpoch' = proposedEpoch
  /\ acceptedPairs' = <<>>
  /\ syncState' = "done" /\ epochPc' = "idle"
  /\ UNCHANGED <<senderEpoch, seqNum, senderRebooted, proposedEpoch, syncAttempts,
                 hasInflight, inflightEpoch, inflightSeq,
                 txStore, txUsed, actuationLog, physicalEffectLog,
                 identityLocks, recoveryLock, resolutionEvidence, txPhase,
                 xferStore, xferUsed, activeTransfer, durableOffsets,
                 chunkPhase, pendingOffset, pendingVerified, pendingDurable,
                 imageDurable, manifestChecked, installLog, fwPhase,
                 recoveryFlag>>

E_FinishSync ==
  /\ epochPc = "idle" /\ syncState = "done"
  /\ syncState' = "idle"
  /\ UNCHANGED <<senderEpoch, seqNum, senderRebooted, lastAcceptedEpoch,
                 acceptedPairs, proposedEpoch, syncAttempts,
                 hasInflight, inflightEpoch, inflightSeq, epochPc,
                 txStore, txUsed, actuationLog, physicalEffectLog,
                 identityLocks, recoveryLock, resolutionEvidence, txPhase,
                 xferStore, xferUsed, activeTransfer, durableOffsets,
                 chunkPhase, pendingOffset, pendingVerified, pendingDurable,
                 imageDurable, manifestChecked, installLog, fwPhase,
                 recoveryFlag>>

-----------------------------------------------------------------------------
\* --- Core actions (subset) -----------------------------------------------

CanAcquireIdentity(tid) ==
  /\ ~recoveryLock /\ ~recoveryFlag /\ tid \notin identityLocks

C_Start(client, tid, appId, hash) ==
  /\ ~recoveryFlag
  /\ tid \notin txUsed
  /\ \A t \in txUsed :
       ~(txStore[t].client = client /\ txStore[t].appTxId = appId
         /\ txStore[t].state \notin {"COMPLETED","RESOLVED","REJECTED","IDLE"})
  /\ txStore' = [txStore EXCEPT ![tid] =
                   [client |-> client, appTxId |-> appId, state |-> "NEW",
                    payloadHash |-> hash, durable |-> FALSE]]
  /\ txUsed' = txUsed \cup {tid}
  /\ txPhase' = [txPhase EXCEPT ![tid] = "idle"]
  /\ UNCHANGED <<senderEpoch, seqNum, senderRebooted, lastAcceptedEpoch,
                 acceptedPairs, syncState, proposedEpoch, syncAttempts,
                 hasInflight, inflightEpoch, inflightSeq, epochPc,
                 actuationLog, physicalEffectLog, identityLocks, recoveryLock,
                 resolutionEvidence,
                 xferStore, xferUsed, activeTransfer, durableOffsets,
                 chunkPhase, pendingOffset, pendingVerified, pendingDurable,
                 imageDurable, manifestChecked, installLog, fwPhase,
                 recoveryFlag>>

C_Persist(tid) ==
  /\ ~recoveryFlag /\ tid \in txUsed
  /\ txStore[tid].state = "NEW" /\ txPhase[tid] = "idle"
  /\ CanAcquireIdentity(tid)
  /\ identityLocks' = identityLocks \cup {tid}
  /\ txStore' = [txStore EXCEPT ![tid].state = "PERSISTED", ![tid].durable = TRUE]
  /\ txPhase' = [txPhase EXCEPT ![tid] = "persisting"]
  /\ UNCHANGED <<senderEpoch, seqNum, senderRebooted, lastAcceptedEpoch,
                 acceptedPairs, syncState, proposedEpoch, syncAttempts,
                 hasInflight, inflightEpoch, inflightSeq, epochPc,
                 txUsed, actuationLog, physicalEffectLog, recoveryLock,
                 resolutionEvidence,
                 xferStore, xferUsed, activeTransfer, durableOffsets,
                 chunkPhase, pendingOffset, pendingVerified, pendingDurable,
                 imageDurable, manifestChecked, installLog, fwPhase,
                 recoveryFlag>>

C_Dispatch(tid) ==
  /\ ~recoveryFlag /\ tid \in txUsed
  /\ txStore[tid].state = "PERSISTED" /\ txPhase[tid] = "persisting"
  /\ tid \in identityLocks /\ txStore[tid].durable
  /\ actuationLog' = Append(actuationLog, tid)
  /\ txStore' = [txStore EXCEPT ![tid].state = "DISPATCHED"]
  /\ txPhase' = [txPhase EXCEPT ![tid] = "dispatching"]
  /\ UNCHANGED <<senderEpoch, seqNum, senderRebooted, lastAcceptedEpoch,
                 acceptedPairs, syncState, proposedEpoch, syncAttempts,
                 hasInflight, inflightEpoch, inflightSeq, epochPc,
                 txUsed, physicalEffectLog, identityLocks, recoveryLock,
                 resolutionEvidence,
                 xferStore, xferUsed, activeTransfer, durableOffsets,
                 chunkPhase, pendingOffset, pendingVerified, pendingDurable,
                 imageDurable, manifestChecked, installLog, fwPhase,
                 recoveryFlag>>

C_Effect(tid) ==
  /\ ~recoveryFlag /\ tid \in txUsed
  /\ txStore[tid].state = "DISPATCHED" /\ txPhase[tid] = "dispatching"
  /\ physicalEffectLog' = Append(physicalEffectLog, tid)
  /\ txStore' = [txStore EXCEPT ![tid].state = "EFFECT_DONE"]
  /\ txPhase' = [txPhase EXCEPT ![tid] = "awaiting_effect"]
  /\ UNCHANGED <<senderEpoch, seqNum, senderRebooted, lastAcceptedEpoch,
                 acceptedPairs, syncState, proposedEpoch, syncAttempts,
                 hasInflight, inflightEpoch, inflightSeq, epochPc,
                 txUsed, actuationLog, identityLocks, recoveryLock,
                 resolutionEvidence,
                 xferStore, xferUsed, activeTransfer, durableOffsets,
                 chunkPhase, pendingOffset, pendingVerified, pendingDurable,
                 imageDurable, manifestChecked, installLog, fwPhase,
                 recoveryFlag>>

C_Record(tid) ==
  /\ ~recoveryFlag /\ tid \in txUsed
  /\ txStore[tid].state = "EFFECT_DONE" /\ txPhase[tid] = "awaiting_effect"
  /\ txStore' = [txStore EXCEPT ![tid].state = "COMPLETED"]
  /\ identityLocks' = identityLocks \ {tid}
  /\ txPhase' = [txPhase EXCEPT ![tid] = "done"]
  /\ UNCHANGED <<senderEpoch, seqNum, senderRebooted, lastAcceptedEpoch,
                 acceptedPairs, syncState, proposedEpoch, syncAttempts,
                 hasInflight, inflightEpoch, inflightSeq, epochPc,
                 txUsed, actuationLog, physicalEffectLog, recoveryLock,
                 resolutionEvidence,
                 xferStore, xferUsed, activeTransfer, durableOffsets,
                 chunkPhase, pendingOffset, pendingVerified, pendingDurable,
                 imageDurable, manifestChecked, installLog, fwPhase,
                 recoveryFlag>>

C_CollectEvidence(tid) ==
  /\ tid \in txUsed /\ txStore[tid].state = "INDETERMINATE"
  /\ resolutionEvidence' = [resolutionEvidence EXCEPT ![tid] = TRUE]
  /\ UNCHANGED <<senderEpoch, seqNum, senderRebooted, lastAcceptedEpoch,
                 acceptedPairs, syncState, proposedEpoch, syncAttempts,
                 hasInflight, inflightEpoch, inflightSeq, epochPc,
                 txStore, txUsed, actuationLog, physicalEffectLog,
                 identityLocks, recoveryLock, txPhase,
                 xferStore, xferUsed, activeTransfer, durableOffsets,
                 chunkPhase, pendingOffset, pendingVerified, pendingDurable,
                 imageDurable, manifestChecked, installLog, fwPhase,
                 recoveryFlag>>

C_Resolve(tid) ==
  /\ tid \in txUsed /\ txStore[tid].state = "INDETERMINATE"
  /\ resolutionEvidence[tid]
  /\ txStore' = [txStore EXCEPT ![tid].state = "RESOLVED"]
  /\ txPhase' = [txPhase EXCEPT ![tid] = "done"]
  /\ UNCHANGED <<senderEpoch, seqNum, senderRebooted, lastAcceptedEpoch,
                 acceptedPairs, syncState, proposedEpoch, syncAttempts,
                 hasInflight, inflightEpoch, inflightSeq, epochPc,
                 txUsed, actuationLog, physicalEffectLog,
                 identityLocks, recoveryLock, resolutionEvidence,
                 xferStore, xferUsed, activeTransfer, durableOffsets,
                 chunkPhase, pendingOffset, pendingVerified, pendingDurable,
                 imageDurable, manifestChecked, installLog, fwPhase,
                 recoveryFlag>>

-----------------------------------------------------------------------------
\* --- Firmware actions (subset) -------------------------------------------

FwNextExpected(tid) == Cardinality(durableOffsets[tid])

F_Start(client, tid, len) ==
  /\ ~recoveryFlag
  /\ tid \notin xferUsed /\ activeTransfer[client] = NoActive
  /\ len \in 1..MaxChunks
  /\ xferStore' = [xferStore EXCEPT ![tid] =
                     [client |-> client, state |-> "IN_PROGRESS", length |-> len]]
  /\ xferUsed' = xferUsed \cup {tid}
  /\ activeTransfer' = [activeTransfer EXCEPT ![client] = tid]
  /\ fwPhase' = [fwPhase EXCEPT ![tid] = "active"]
  /\ UNCHANGED <<senderEpoch, seqNum, senderRebooted, lastAcceptedEpoch,
                 acceptedPairs, syncState, proposedEpoch, syncAttempts,
                 hasInflight, inflightEpoch, inflightSeq, epochPc,
                 txStore, txUsed, actuationLog, physicalEffectLog,
                 identityLocks, recoveryLock, resolutionEvidence, txPhase,
                 durableOffsets, chunkPhase, pendingOffset, pendingVerified,
                 pendingDurable, imageDurable, manifestChecked, installLog,
                 recoveryFlag>>

F_Write(tid, offset) ==
  /\ ~recoveryFlag /\ tid \in xferUsed
  /\ xferStore[tid].state = "IN_PROGRESS" /\ fwPhase[tid] = "active"
  /\ chunkPhase[tid] = "idle" /\ offset = FwNextExpected(tid)
  /\ offset < xferStore[tid].length
  /\ chunkPhase' = [chunkPhase EXCEPT ![tid] = "written"]
  /\ pendingOffset' = [pendingOffset EXCEPT ![tid] = offset]
  /\ pendingVerified' = [pendingVerified EXCEPT ![tid] = FALSE]
  /\ pendingDurable' = [pendingDurable EXCEPT ![tid] = FALSE]
  /\ UNCHANGED <<senderEpoch, seqNum, senderRebooted, lastAcceptedEpoch,
                 acceptedPairs, syncState, proposedEpoch, syncAttempts,
                 hasInflight, inflightEpoch, inflightSeq, epochPc,
                 txStore, txUsed, actuationLog, physicalEffectLog,
                 identityLocks, recoveryLock, resolutionEvidence, txPhase,
                 xferStore, xferUsed, activeTransfer, durableOffsets,
                 imageDurable, manifestChecked, installLog, fwPhase,
                 recoveryFlag>>

F_Verify(tid) ==
  /\ ~recoveryFlag /\ tid \in xferUsed /\ chunkPhase[tid] = "written"
  /\ chunkPhase' = [chunkPhase EXCEPT ![tid] = "verified"]
  /\ pendingVerified' = [pendingVerified EXCEPT ![tid] = TRUE]
  /\ UNCHANGED <<senderEpoch, seqNum, senderRebooted, lastAcceptedEpoch,
                 acceptedPairs, syncState, proposedEpoch, syncAttempts,
                 hasInflight, inflightEpoch, inflightSeq, epochPc,
                 txStore, txUsed, actuationLog, physicalEffectLog,
                 identityLocks, recoveryLock, resolutionEvidence, txPhase,
                 xferStore, xferUsed, activeTransfer, durableOffsets,
                 pendingOffset, pendingDurable, imageDurable, manifestChecked,
                 installLog, fwPhase, recoveryFlag>>

F_Durabilize(tid) ==
  /\ ~recoveryFlag /\ tid \in xferUsed
  /\ chunkPhase[tid] = "verified" /\ pendingVerified[tid]
  /\ chunkPhase' = [chunkPhase EXCEPT ![tid] = "durabilizing"]
  /\ pendingDurable' = [pendingDurable EXCEPT ![tid] = TRUE]
  /\ UNCHANGED <<senderEpoch, seqNum, senderRebooted, lastAcceptedEpoch,
                 acceptedPairs, syncState, proposedEpoch, syncAttempts,
                 hasInflight, inflightEpoch, inflightSeq, epochPc,
                 txStore, txUsed, actuationLog, physicalEffectLog,
                 identityLocks, recoveryLock, resolutionEvidence, txPhase,
                 xferStore, xferUsed, activeTransfer, durableOffsets,
                 pendingOffset, pendingVerified, imageDurable, manifestChecked,
                 installLog, fwPhase, recoveryFlag>>

F_Advance(tid) ==
  /\ ~recoveryFlag /\ tid \in xferUsed
  /\ chunkPhase[tid] = "durabilizing" /\ pendingDurable[tid]
  /\ durableOffsets' = [durableOffsets EXCEPT ![tid] = @ \cup {pendingOffset[tid]}]
  /\ chunkPhase' = [chunkPhase EXCEPT ![tid] = "idle"]
  /\ pendingVerified' = [pendingVerified EXCEPT ![tid] = FALSE]
  /\ pendingDurable' = [pendingDurable EXCEPT ![tid] = FALSE]
  /\ UNCHANGED <<senderEpoch, seqNum, senderRebooted, lastAcceptedEpoch,
                 acceptedPairs, syncState, proposedEpoch, syncAttempts,
                 hasInflight, inflightEpoch, inflightSeq, epochPc,
                 txStore, txUsed, actuationLog, physicalEffectLog,
                 identityLocks, recoveryLock, resolutionEvidence, txPhase,
                 xferStore, xferUsed, activeTransfer, pendingOffset,
                 imageDurable, manifestChecked, installLog, fwPhase,
                 recoveryFlag>>

F_MarkDurable(tid) ==
  /\ ~recoveryFlag /\ tid \in xferUsed
  /\ xferStore[tid].state = "IN_PROGRESS" /\ fwPhase[tid] = "active"
  /\ chunkPhase[tid] = "idle" /\ FwNextExpected(tid) = xferStore[tid].length
  /\ imageDurable' = [imageDurable EXCEPT ![tid] = TRUE]
  /\ fwPhase' = [fwPhase EXCEPT ![tid] = "closing"]
  /\ UNCHANGED <<senderEpoch, seqNum, senderRebooted, lastAcceptedEpoch,
                 acceptedPairs, syncState, proposedEpoch, syncAttempts,
                 hasInflight, inflightEpoch, inflightSeq, epochPc,
                 txStore, txUsed, actuationLog, physicalEffectLog,
                 identityLocks, recoveryLock, resolutionEvidence, txPhase,
                 xferStore, xferUsed, activeTransfer, durableOffsets,
                 chunkPhase, pendingOffset, pendingVerified, pendingDurable,
                 manifestChecked, installLog, recoveryFlag>>

F_CheckManifest(tid) ==
  /\ ~recoveryFlag /\ tid \in xferUsed /\ fwPhase[tid] = "closing"
  /\ imageDurable[tid] /\ ~manifestChecked[tid]
  /\ manifestChecked' = [manifestChecked EXCEPT ![tid] = TRUE]
  /\ UNCHANGED <<senderEpoch, seqNum, senderRebooted, lastAcceptedEpoch,
                 acceptedPairs, syncState, proposedEpoch, syncAttempts,
                 hasInflight, inflightEpoch, inflightSeq, epochPc,
                 txStore, txUsed, actuationLog, physicalEffectLog,
                 identityLocks, recoveryLock, resolutionEvidence, txPhase,
                 xferStore, xferUsed, activeTransfer, durableOffsets,
                 chunkPhase, pendingOffset, pendingVerified, pendingDurable,
                 imageDurable, installLog, fwPhase, recoveryFlag>>

F_Close(tid) ==
  /\ ~recoveryFlag /\ tid \in xferUsed /\ fwPhase[tid] = "closing"
  /\ imageDurable[tid] /\ manifestChecked[tid]
  /\ xferStore' = [xferStore EXCEPT ![tid].state = "COMPLETED"]
  /\ activeTransfer' = [activeTransfer EXCEPT ![xferStore[tid].client] = NoActive]
  /\ fwPhase' = [fwPhase EXCEPT ![tid] = "done"]
  /\ UNCHANGED <<senderEpoch, seqNum, senderRebooted, lastAcceptedEpoch,
                 acceptedPairs, syncState, proposedEpoch, syncAttempts,
                 hasInflight, inflightEpoch, inflightSeq, epochPc,
                 txStore, txUsed, actuationLog, physicalEffectLog,
                 identityLocks, recoveryLock, resolutionEvidence, txPhase,
                 xferUsed, durableOffsets, chunkPhase, pendingOffset,
                 pendingVerified, pendingDurable, imageDurable, manifestChecked,
                 installLog, recoveryFlag>>

F_Install(tid) ==
  /\ ~recoveryFlag /\ tid \in xferUsed
  /\ xferStore[tid].state = "COMPLETED"
  /\ imageDurable[tid] /\ manifestChecked[tid]
  /\ Cardinality({ i \in DOMAIN installLog : installLog[i] = tid }) = 0
  /\ installLog' = Append(installLog, tid)
  /\ UNCHANGED <<senderEpoch, seqNum, senderRebooted, lastAcceptedEpoch,
                 acceptedPairs, syncState, proposedEpoch, syncAttempts,
                 hasInflight, inflightEpoch, inflightSeq, epochPc,
                 txStore, txUsed, actuationLog, physicalEffectLog,
                 identityLocks, recoveryLock, resolutionEvidence, txPhase,
                 xferStore, xferUsed, activeTransfer, durableOffsets,
                 chunkPhase, pendingOffset, pendingVerified, pendingDurable,
                 imageDurable, manifestChecked, fwPhase, recoveryFlag>>

-----------------------------------------------------------------------------
\* --- Shared Crash / Recovery ---------------------------------------------

\* Global crash: affects Epoch in-flight, Core transactions, Firmware transfers
Crash ==
  /\ ~recoveryFlag
  /\ recoveryFlag' = TRUE
  /\ recoveryLock' = TRUE
  /\ identityLocks' = {}
  /\ hasInflight' = FALSE /\ inflightEpoch' = 0 /\ inflightSeq' = 0
  /\ epochPc' = IF epochPc = "sending" THEN "idle" ELSE epochPc
  /\ txStore' = [tid \in 0..MaxTx-1 |->
                   IF tid \in txUsed
                      /\ txStore[tid].state \in {"PERSISTED","DISPATCHED","EFFECT_DONE"}
                   THEN [txStore[tid] EXCEPT !.state = "INDETERMINATE"]
                   ELSE txStore[tid]]
  /\ txPhase' = [tid \in 0..MaxTx-1 |->
                   IF tid \in txUsed
                      /\ txPhase[tid] \in {"persisting","dispatching","awaiting_effect","recording"}
                   THEN "idle" ELSE txPhase[tid]]
  /\ xferStore' = [tid \in 0..MaxTransfers-1 |->
                     IF tid \in xferUsed /\ xferStore[tid].state = "IN_PROGRESS"
                     THEN [xferStore[tid] EXCEPT !.state = "ABORTED"]
                     ELSE xferStore[tid]]
  /\ activeTransfer' = [c \in Clients |-> NoActive]
  /\ chunkPhase' = [tid \in 0..MaxTransfers-1 |-> "idle"]
  /\ pendingVerified' = [tid \in 0..MaxTransfers-1 |-> FALSE]
  /\ pendingDurable' = [tid \in 0..MaxTransfers-1 |-> FALSE]
  /\ fwPhase' = [tid \in 0..MaxTransfers-1 |->
                   IF tid \in xferUsed /\ fwPhase[tid] \in {"active","closing"}
                   THEN "idle" ELSE fwPhase[tid]]
  /\ UNCHANGED <<senderEpoch, seqNum, senderRebooted, lastAcceptedEpoch,
                 acceptedPairs, syncState, proposedEpoch, syncAttempts,
                 txUsed, actuationLog, physicalEffectLog, resolutionEvidence,
                 xferUsed, durableOffsets, pendingOffset,
                 imageDurable, manifestChecked, installLog>>

FinishRecovery ==
  /\ recoveryFlag /\ recoveryLock
  /\ recoveryFlag' = FALSE /\ recoveryLock' = FALSE
  /\ UNCHANGED <<senderEpoch, seqNum, senderRebooted, lastAcceptedEpoch,
                 acceptedPairs, syncState, proposedEpoch, syncAttempts,
                 hasInflight, inflightEpoch, inflightSeq, epochPc,
                 txStore, txUsed, actuationLog, physicalEffectLog,
                 identityLocks, resolutionEvidence, txPhase,
                 xferStore, xferUsed, activeTransfer, durableOffsets,
                 chunkPhase, pendingOffset, pendingVerified, pendingDurable,
                 imageDurable, manifestChecked, installLog, fwPhase>>

-----------------------------------------------------------------------------
Next ==
  \/ E_SendOrdinary \/ E_AcceptOrdinary \/ E_SoftRotate
  \/ E_DeliverSync \/ E_FinishSync
  \/ \E c \in Clients, t \in 0..MaxTx-1, a \in 0..MaxTx-1, h \in 0..MaxHash :
       C_Start(c, t, a, h)
  \/ \E t \in 0..MaxTx-1 : C_Persist(t)
  \/ \E t \in 0..MaxTx-1 : C_Dispatch(t)
  \/ \E t \in 0..MaxTx-1 : C_Effect(t)
  \/ \E t \in 0..MaxTx-1 : C_Record(t)
  \/ \E t \in 0..MaxTx-1 : C_CollectEvidence(t)
  \/ \E t \in 0..MaxTx-1 : C_Resolve(t)
  \/ \E c \in Clients, t \in 0..MaxTransfers-1, l \in 1..MaxChunks :
       F_Start(c, t, l)
  \/ \E t \in 0..MaxTransfers-1, o \in 0..MaxChunks-1 : F_Write(t, o)
  \/ \E t \in 0..MaxTransfers-1 : F_Verify(t)
  \/ \E t \in 0..MaxTransfers-1 : F_Durabilize(t)
  \/ \E t \in 0..MaxTransfers-1 : F_Advance(t)
  \/ \E t \in 0..MaxTransfers-1 : F_MarkDurable(t)
  \/ \E t \in 0..MaxTransfers-1 : F_CheckManifest(t)
  \/ \E t \in 0..MaxTransfers-1 : F_Close(t)
  \/ \E t \in 0..MaxTransfers-1 : F_Install(t)
  \/ Crash
  \/ FinishRecovery

vars == <<
  senderEpoch, seqNum, senderRebooted, lastAcceptedEpoch, acceptedPairs,
  syncState, proposedEpoch, syncAttempts, hasInflight, inflightEpoch,
  inflightSeq, epochPc,
  txStore, txUsed, actuationLog, physicalEffectLog, identityLocks,
  recoveryLock, resolutionEvidence, txPhase,
  xferStore, xferUsed, activeTransfer, durableOffsets, chunkPhase,
  pendingOffset, pendingVerified, pendingDurable, imageDurable,
  manifestChecked, installLog, fwPhase,
  recoveryFlag
>>

Spec == Init /\ [][Next]_vars

THEOREM Spec => []TypeOK
THEOREM Spec => []Inv_NonceUniqueness
THEOREM Spec => []Inv_NoDoubleActuation
THEOREM Spec => []Inv_PersistBeforeDispatch
THEOREM Spec => []Inv_NoActuationDuringRecovery
THEOREM Spec => []Inv_NoDeadlockUnderRecovery
THEOREM Spec => []Inv_AuthorizedResolution
THEOREM Spec => []Inv_NoDoubleInstall
THEOREM Spec => []Inv_NoInstallBeforeManifest
THEOREM Spec => []Inv_AtMostOneTransferPerClient
THEOREM Spec => []Inv_SharedRecovery

=============================================================================
\* Root composition – November 2026
\* Integrates Epoch + Core + Firmware under a shared Recovery Barrier
=============================================================================
