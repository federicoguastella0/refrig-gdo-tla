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
(* IMPORTANT ABSTRACTION BOUNDARY: this Root model uses a single in-flight     *)
(* ordinary packet (hasInflight/inflightEpoch/inflightSeq). It does NOT        *)
(* compose the standalone Epoch model's pendingPackets set, out-of-order      *)
(* delivery, or sliding replay-window eviction. The complete sliding-window  *)
(* behavior is modeled and checked only in REFRIG_GDO_Epoch.tla. Root results  *)
(* must not be interpreted as verification of that complete behavior.         *)
(*****************************************************************************)

EXTENDS Integers, FiniteSets, Sequences, TLC

CONSTANTS
  Clients,
  Resources,
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
  /\ Resources # {}

-----------------------------------------------------------------------------
\* Shared / cross-cutting state

VARIABLES
  (* ---- Epoch machine ---- *)
  senderEpoch,
  epochHighWater,
  seqNum,
  senderRebooted,
  lastAcceptedEpoch,
  lastAcceptedHighWater,
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
  txPhase,
  consumedIdentities,
  blockedResources,
  evidenceKind,
  resolveOutcome,

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
  manifestResult,
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
EvidenceKind == {
  "NONE", "HW_READBACK_ON", "HW_READBACK_OFF", "AUTHORIZED_OPERATOR"
}
ResolveOutcome == {
  "NONE", "CONFIRMED_EFFECT", "CONFIRMED_ABSENT", "OPERATOR_CLOSED"
}

TxRecord == [
  client : Clients, appTxId : 0..MaxTx-1, resource : Resources,
  state : TxState, payloadHash : 0..MaxHash, durable : BOOLEAN
]

TransferState == {"IDLE", "IN_PROGRESS", "COMPLETED", "ABORTED", "INDETERMINATE"}
ChunkPhase == {"idle", "written", "verified", "durabilizing"}
FwPhase == {"idle", "active", "closing", "done"}
ManifestResult == {"NONE", "PASS", "FAIL"}
TransferRecord == [client : Clients, state : TransferState, length : 0..MaxChunks]

-----------------------------------------------------------------------------
TypeOK ==
  (* Epoch *)
  /\ senderEpoch \in 0..MaxEpoch
  /\ epochHighWater \in 0..MaxEpoch
  /\ seqNum \in 0..MaxSeq
  /\ senderRebooted \in BOOLEAN
  /\ lastAcceptedEpoch \in 0..MaxEpoch
  /\ lastAcceptedHighWater \in 0..MaxEpoch
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
  /\ txPhase \in [0..MaxTx-1 -> TxPhase]
  /\ consumedIdentities \subseteq (Clients \X (0..MaxTx-1))
  /\ blockedResources \subseteq Resources
  /\ evidenceKind \in [0..MaxTx-1 -> EvidenceKind]
  /\ resolveOutcome \in [0..MaxTx-1 -> ResolveOutcome]
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
  /\ manifestResult \in [0..MaxTransfers-1 -> ManifestResult]
  /\ installLog \in Seq(0..MaxTransfers-1)
  /\ fwPhase \in [0..MaxTransfers-1 -> FwPhase]
  (* Shared *)
  /\ recoveryFlag \in BOOLEAN

-----------------------------------------------------------------------------
\* Cross-cutting invariants

Inv_NonceUniqueness ==
  \A i, j \in DOMAIN acceptedPairs :
    i # j => acceptedPairs[i] # acceptedPairs[j]

Inv_EpochMonotonic ==
  /\ senderEpoch = epochHighWater
  /\ epochHighWater \in 0..MaxEpoch

Inv_LastAcceptedMonotonic ==
  /\ lastAcceptedEpoch = lastAcceptedHighWater
  /\ lastAcceptedHighWater \in 0..MaxEpoch

Inv_AcceptedCoveredByLast ==
  \A i \in DOMAIN acceptedPairs :
    acceptedPairs[i][1] <= lastAcceptedEpoch

Inv_NoDoubleActuation ==
  \A tid \in txUsed :
    Cardinality({ i \in DOMAIN actuationLog : actuationLog[i] = tid }) <= 1

\* The transition guard on C_Dispatch enforces this cross-machine rule.
Inv_NoNewDispatchDuringEpochSync ==
  \A tid \in txUsed :
    txStore[tid].state = "PERSISTED" /\ syncState # "idle"
      => txPhase[tid] # "dispatching"

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
    txStore[tid].state = "RESOLVED" =>
      /\ evidenceKind[tid] = "AUTHORIZED_OPERATOR"
      /\ resolveOutcome[tid] \in {"CONFIRMED_EFFECT", "CONFIRMED_ABSENT", "OPERATOR_CLOSED"}

Inv_NoIdentityReuse ==
  /\ \A t1, t2 \in txUsed :
       /\ t1 # t2
       /\ txStore[t1].client = txStore[t2].client
       /\ txStore[t1].appTxId = txStore[t2].appTxId
       => FALSE
  /\ \A tid \in txUsed :
       txStore[tid].state \notin {"IDLE", "NEW"} =>
         <<txStore[tid].client, txStore[tid].appTxId>> \in consumedIdentities

Inv_IndeterminateBlocksResource ==
  \A tid \in txUsed :
    txStore[tid].state = "INDETERMINATE" =>
      txStore[tid].resource \in blockedResources

Inv_NoActiveOnBlockedResource ==
  \A tid \in txUsed :
    txStore[tid].state \in {"NEW", "PERSISTED", "DISPATCHED", "EFFECT_DONE"} =>
      txStore[tid].resource \notin blockedResources

Inv_NoDoubleInstall ==
  \A tid \in xferUsed :
    Cardinality({ i \in DOMAIN installLog : installLog[i] = tid }) <= 1

Inv_NoInstallBeforeManifest ==
  \A i \in DOMAIN installLog :
    LET tid == installLog[i] IN
      /\ imageDurable[tid] = TRUE
      /\ manifestResult[tid] = "PASS"
      /\ xferStore[tid].state = "COMPLETED"

Inv_CompletedRequiresManifestPass ==
  \A tid \in xferUsed :
    xferStore[tid].state = "COMPLETED" => manifestResult[tid] = "PASS"

Inv_ManifestFailAborts ==
  \A tid \in xferUsed :
    manifestResult[tid] = "FAIL" =>
      /\ xferStore[tid].state = "ABORTED"
      /\ Cardinality({ i \in DOMAIN installLog : installLog[i] = tid }) = 0

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
  /\ senderEpoch = 0 /\ epochHighWater = 0 /\ seqNum = 0 /\ senderRebooted = FALSE
  /\ lastAcceptedEpoch = 0 /\ lastAcceptedHighWater = 0 /\ acceptedPairs = <<>>
  /\ syncState = "idle" /\ proposedEpoch = 0 /\ syncAttempts = 0
  /\ hasInflight = FALSE /\ inflightEpoch = 0 /\ inflightSeq = 0
  /\ epochPc = "idle"
  (* Core *)
  /\ txStore = [tid \in 0..MaxTx-1 |->
                  [client |-> CHOOSE c \in Clients : TRUE,
                   appTxId |-> 0,
                   resource |-> CHOOSE r \in Resources : TRUE,
                   state |-> "IDLE",
                   payloadHash |-> 0, durable |-> FALSE]]
  /\ txUsed = {}
  /\ actuationLog = <<>> /\ physicalEffectLog = <<>>
  /\ identityLocks = {} /\ recoveryLock = FALSE
  /\ txPhase = [tid \in 0..MaxTx-1 |-> "idle"]
  /\ consumedIdentities = {}
  /\ blockedResources = {}
  /\ evidenceKind = [tid \in 0..MaxTx-1 |-> "NONE"]
  /\ resolveOutcome = [tid \in 0..MaxTx-1 |-> "NONE"]
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
  /\ manifestResult = [tid \in 0..MaxTransfers-1 |-> "NONE"]
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
  /\ UNCHANGED <<senderEpoch, epochHighWater, lastAcceptedEpoch, lastAcceptedHighWater, acceptedPairs, syncState,
                 proposedEpoch, syncAttempts,
                 txStore, txUsed, actuationLog, physicalEffectLog,
                 identityLocks, recoveryLock, consumedIdentities, blockedResources, evidenceKind, resolveOutcome, txPhase,
                 xferStore, xferUsed, activeTransfer, durableOffsets,
                 chunkPhase, pendingOffset, pendingVerified, pendingDurable,
                 imageDurable, manifestResult, installLog, fwPhase,
                 recoveryFlag>>


E_AcceptOrdinary ==
  /\ epochPc = "sending" /\ hasInflight
  /\ LET e == inflightEpoch s == inflightSeq IN
       /\ \/ e = lastAcceptedEpoch \/ e = lastAcceptedEpoch + 1
       /\ ~AlreadyAccepted(e, s)
       /\ acceptedPairs' = Append(acceptedPairs, <<e, s>>)
       /\ IF e = lastAcceptedEpoch + 1
          THEN /\ lastAcceptedEpoch' = e
               /\ lastAcceptedHighWater' = e
          ELSE UNCHANGED <<lastAcceptedEpoch, lastAcceptedHighWater>>
  /\ hasInflight' = FALSE /\ inflightEpoch' = 0 /\ inflightSeq' = 0
  /\ epochPc' = "idle"
  /\ UNCHANGED <<senderEpoch, epochHighWater, seqNum, senderRebooted, syncState,
                 proposedEpoch, syncAttempts,
                 txStore, txUsed, actuationLog, physicalEffectLog,
                 identityLocks, recoveryLock, consumedIdentities, blockedResources, evidenceKind, resolveOutcome, txPhase,
                 xferStore, xferUsed, activeTransfer, durableOffsets,
                 chunkPhase, pendingOffset, pendingVerified, pendingDurable,
                 imageDurable, manifestResult, installLog, fwPhase,
                 recoveryFlag>>


E_SoftRotate ==
  /\ epochPc \in {"idle", "sending"}
  /\ seqNum >= SoftRotationThreshold /\ senderEpoch < MaxEpoch
  /\ senderEpoch' = senderEpoch + 1
  /\ epochHighWater' = senderEpoch + 1
  /\ seqNum' = 0
  /\ proposedEpoch' = senderEpoch + 1
  /\ syncState' = "req_sent" /\ syncAttempts' = 0
  /\ hasInflight' = FALSE /\ inflightEpoch' = 0 /\ inflightSeq' = 0
  /\ epochPc' = "syncing" /\ senderRebooted' = FALSE
  /\ UNCHANGED <<lastAcceptedEpoch, lastAcceptedHighWater, acceptedPairs,
                 txStore, txUsed, actuationLog, physicalEffectLog,
                 identityLocks, recoveryLock, consumedIdentities, blockedResources, evidenceKind, resolveOutcome, txPhase,
                 xferStore, xferUsed, activeTransfer, durableOffsets,
                 chunkPhase, pendingOffset, pendingVerified, pendingDurable,
                 imageDurable, manifestResult, installLog, fwPhase,
                 recoveryFlag>>


E_DeliverSync ==
  /\ epochPc = "syncing" /\ syncState = "req_sent"
  /\ proposedEpoch >= lastAcceptedEpoch
  /\ lastAcceptedEpoch' = proposedEpoch
  /\ lastAcceptedHighWater' = proposedEpoch
  /\ syncState' = "done" /\ epochPc' = "idle"
  /\ UNCHANGED <<senderEpoch, epochHighWater, seqNum, senderRebooted, proposedEpoch, syncAttempts,
                 hasInflight, inflightEpoch, inflightSeq, acceptedPairs,
                 txStore, txUsed, actuationLog, physicalEffectLog,
                 identityLocks, recoveryLock, consumedIdentities, blockedResources, evidenceKind, resolveOutcome, txPhase,
                 xferStore, xferUsed, activeTransfer, durableOffsets,
                 chunkPhase, pendingOffset, pendingVerified, pendingDurable,
                 imageDurable, manifestResult, installLog, fwPhase,
                 recoveryFlag>>


E_FinishSync ==
  /\ epochPc = "idle" /\ syncState = "done"
  /\ syncState' = "idle"
  /\ UNCHANGED <<senderEpoch, epochHighWater, seqNum, senderRebooted, lastAcceptedEpoch, lastAcceptedHighWater,
                 acceptedPairs, proposedEpoch, syncAttempts,
                 hasInflight, inflightEpoch, inflightSeq, epochPc,
                 txStore, txUsed, actuationLog, physicalEffectLog,
                 identityLocks, recoveryLock, consumedIdentities, blockedResources, evidenceKind, resolveOutcome, txPhase,
                 xferStore, xferUsed, activeTransfer, durableOffsets,
                 chunkPhase, pendingOffset, pendingVerified, pendingDurable,
                 imageDurable, manifestResult, installLog, fwPhase,
                 recoveryFlag>>


-----------------------------------------------------------------------------
\* --- Core actions (subset) -----------------------------------------------

CanAcquireIdentity(tid) ==
  /\ ~recoveryLock /\ ~recoveryFlag /\ tid \notin identityLocks


C_Start(client, tid, appId, res, hash) ==
  /\ ~recoveryFlag
  /\ tid \notin txUsed
  /\ <<client, appId>> \notin consumedIdentities
  /\ \A t \in txUsed :
        ~(txStore[t].client = client /\ txStore[t].appTxId = appId
          /\ txStore[t].state \notin {"COMPLETED", "RESOLVED", "REJECTED", "IDLE"})
  /\ res \in Resources
  /\ res \notin blockedResources
  /\ \A t \in txUsed :
        \/ txStore[t].resource # res
        \/ txStore[t].state \notin {"NEW", "PERSISTED", "DISPATCHED", "EFFECT_DONE", "INDETERMINATE"}
  /\ txStore' = [txStore EXCEPT ![tid] =
                   [client |-> client, appTxId |-> appId, resource |-> res,
                    state |-> "NEW", payloadHash |-> hash, durable |-> FALSE]]
  /\ txUsed' = txUsed \cup {tid}
  /\ txPhase' = [txPhase EXCEPT ![tid] = "idle"]
  /\ UNCHANGED <<senderEpoch, epochHighWater, seqNum, senderRebooted, lastAcceptedEpoch, lastAcceptedHighWater,
                 acceptedPairs, syncState, proposedEpoch, syncAttempts,
                 hasInflight, inflightEpoch, inflightSeq, epochPc,
                 actuationLog, physicalEffectLog, identityLocks, recoveryLock,
                 blockedResources, evidenceKind, resolveOutcome, consumedIdentities,
                 xferStore, xferUsed, activeTransfer, durableOffsets,
                 chunkPhase, pendingOffset, pendingVerified, pendingDurable,
                 imageDurable, manifestResult, installLog, fwPhase,
                 recoveryFlag>>


C_Persist(tid) ==
  /\ ~recoveryFlag /\ tid \in txUsed
  /\ txStore[tid].state = "NEW" /\ txPhase[tid] = "idle"
  /\ CanAcquireIdentity(tid)
  /\ txStore[tid].resource \notin blockedResources
  /\ <<txStore[tid].client, txStore[tid].appTxId>> \notin consumedIdentities
  /\ identityLocks' = identityLocks \cup {tid}
  /\ txStore' = [txStore EXCEPT ![tid].state = "PERSISTED", ![tid].durable = TRUE]
  /\ consumedIdentities' =
       consumedIdentities \cup {<<txStore[tid].client, txStore[tid].appTxId>>}
  /\ txPhase' = [txPhase EXCEPT ![tid] = "persisting"]
  /\ UNCHANGED <<senderEpoch, epochHighWater, seqNum, senderRebooted, lastAcceptedEpoch, lastAcceptedHighWater,
                 acceptedPairs, syncState, proposedEpoch, syncAttempts,
                 hasInflight, inflightEpoch, inflightSeq, epochPc,
                 txUsed, actuationLog, physicalEffectLog, recoveryLock,
                 blockedResources, evidenceKind, resolveOutcome,
                 xferStore, xferUsed, activeTransfer, durableOffsets,
                 chunkPhase, pendingOffset, pendingVerified, pendingDurable,
                 imageDurable, manifestResult, installLog, fwPhase,
                 recoveryFlag>>


\* v1.4.5 §5.2.2: no new hardware dispatch while Epoch Sync is active.
\* An already-dispatched operation is not cancelled here; its physical outcome
\* must still be reconciled through the transaction state machine.
C_Dispatch(tid) ==
  /\ ~recoveryFlag /\ syncState = "idle" /\ tid \in txUsed
  /\ txStore[tid].state = "PERSISTED" /\ txPhase[tid] = "persisting"
  /\ tid \in identityLocks /\ txStore[tid].durable
  /\ actuationLog' = Append(actuationLog, tid)
  /\ txStore' = [txStore EXCEPT ![tid].state = "DISPATCHED"]
  /\ txPhase' = [txPhase EXCEPT ![tid] = "dispatching"]
  /\ UNCHANGED <<senderEpoch, epochHighWater, seqNum, senderRebooted, lastAcceptedEpoch, lastAcceptedHighWater,
                 acceptedPairs, syncState, proposedEpoch, syncAttempts,
                 hasInflight, inflightEpoch, inflightSeq, epochPc,
                 txUsed, physicalEffectLog, identityLocks, recoveryLock,
                 consumedIdentities, blockedResources, evidenceKind, resolveOutcome,
                 xferStore, xferUsed, activeTransfer, durableOffsets,
                 chunkPhase, pendingOffset, pendingVerified, pendingDurable,
                 imageDurable, manifestResult, installLog, fwPhase,
                 recoveryFlag>>

C_Effect(tid) ==
  /\ ~recoveryFlag /\ tid \in txUsed
  /\ txStore[tid].state = "DISPATCHED" /\ txPhase[tid] = "dispatching"
  /\ physicalEffectLog' = Append(physicalEffectLog, tid)
  /\ txStore' = [txStore EXCEPT ![tid].state = "EFFECT_DONE"]
  /\ txPhase' = [txPhase EXCEPT ![tid] = "awaiting_effect"]
  /\ UNCHANGED <<senderEpoch, epochHighWater, seqNum, senderRebooted, lastAcceptedEpoch, lastAcceptedHighWater,
                 acceptedPairs, syncState, proposedEpoch, syncAttempts,
                 hasInflight, inflightEpoch, inflightSeq, epochPc,
                 txUsed, actuationLog, identityLocks, recoveryLock,
                 consumedIdentities, blockedResources, evidenceKind, resolveOutcome,
                 xferStore, xferUsed, activeTransfer, durableOffsets,
                 chunkPhase, pendingOffset, pendingVerified, pendingDurable,
                 imageDurable, manifestResult, installLog, fwPhase,
                 recoveryFlag>>

C_Record(tid) ==
  /\ ~recoveryFlag /\ tid \in txUsed
  /\ txStore[tid].state = "EFFECT_DONE" /\ txPhase[tid] = "awaiting_effect"
  /\ txStore' = [txStore EXCEPT ![tid].state = "COMPLETED"]
  /\ identityLocks' = identityLocks \ {tid}
  /\ txPhase' = [txPhase EXCEPT ![tid] = "done"]
  /\ UNCHANGED <<senderEpoch, epochHighWater, seqNum, senderRebooted, lastAcceptedEpoch, lastAcceptedHighWater,
                 acceptedPairs, syncState, proposedEpoch, syncAttempts,
                 hasInflight, inflightEpoch, inflightSeq, epochPc,
                 txUsed, actuationLog, physicalEffectLog, recoveryLock,
                 consumedIdentities, blockedResources, evidenceKind, resolveOutcome,
                 xferStore, xferUsed, activeTransfer, durableOffsets,
                 chunkPhase, pendingOffset, pendingVerified, pendingDurable,
                 imageDurable, manifestResult, installLog, fwPhase,
                 recoveryFlag>>

C_CollectEvidence(tid, kind) ==
  /\ tid \in txUsed /\ txStore[tid].state = "INDETERMINATE"
  /\ kind \in EvidenceKind \ {"NONE"}
  /\ evidenceKind' = [evidenceKind EXCEPT ![tid] = kind]
  /\ UNCHANGED <<senderEpoch, epochHighWater, seqNum, senderRebooted, lastAcceptedEpoch, lastAcceptedHighWater,
                 acceptedPairs, syncState, proposedEpoch, syncAttempts,
                 hasInflight, inflightEpoch, inflightSeq, epochPc,
                 txStore, txUsed, actuationLog, physicalEffectLog,
                 identityLocks, recoveryLock, txPhase, consumedIdentities,
                 blockedResources, resolveOutcome,
                 xferStore, xferUsed, activeTransfer, durableOffsets,
                 chunkPhase, pendingOffset, pendingVerified, pendingDurable,
                 imageDurable, manifestResult, installLog, fwPhase,
                 recoveryFlag>>

C_Resolve(tid, outcome) ==
  /\ tid \in txUsed /\ txStore[tid].state = "INDETERMINATE"
  /\ evidenceKind[tid] = "AUTHORIZED_OPERATOR"
  /\ outcome \in {"CONFIRMED_EFFECT", "CONFIRMED_ABSENT", "OPERATOR_CLOSED"}
  /\ txStore' = [txStore EXCEPT ![tid].state = "RESOLVED"]
  /\ resolveOutcome' = [resolveOutcome EXCEPT ![tid] = outcome]
  /\ blockedResources' =
       IF \E t2 \in txUsed :
            /\ t2 # tid
            /\ txStore[t2].state = "INDETERMINATE"
            /\ txStore[t2].resource = txStore[tid].resource
       THEN blockedResources
       ELSE blockedResources \ {txStore[tid].resource}
  /\ txPhase' = [txPhase EXCEPT ![tid] = "done"]
  /\ UNCHANGED <<senderEpoch, epochHighWater, seqNum, senderRebooted, lastAcceptedEpoch, lastAcceptedHighWater,
                 acceptedPairs, syncState, proposedEpoch, syncAttempts,
                 hasInflight, inflightEpoch, inflightSeq, epochPc,
                 txUsed, actuationLog, physicalEffectLog,
                 identityLocks, recoveryLock, consumedIdentities, evidenceKind,
                 xferStore, xferUsed, activeTransfer, durableOffsets,
                 chunkPhase, pendingOffset, pendingVerified, pendingDurable,
                 imageDurable, manifestResult, installLog, fwPhase,
                 recoveryFlag>>


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
  /\ UNCHANGED <<senderEpoch, epochHighWater, seqNum, senderRebooted, lastAcceptedEpoch, lastAcceptedHighWater,
                 acceptedPairs, syncState, proposedEpoch, syncAttempts,
                 hasInflight, inflightEpoch, inflightSeq, epochPc,
                 txStore, txUsed, actuationLog, physicalEffectLog,
                 identityLocks, recoveryLock, consumedIdentities, blockedResources, evidenceKind, resolveOutcome, txPhase,
                 durableOffsets, chunkPhase, pendingOffset, pendingVerified,
                 pendingDurable, imageDurable, manifestResult, installLog,
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
  /\ UNCHANGED <<senderEpoch, epochHighWater, seqNum, senderRebooted, lastAcceptedEpoch, lastAcceptedHighWater,
                 acceptedPairs, syncState, proposedEpoch, syncAttempts,
                 hasInflight, inflightEpoch, inflightSeq, epochPc,
                 txStore, txUsed, actuationLog, physicalEffectLog,
                 identityLocks, recoveryLock, consumedIdentities, blockedResources, evidenceKind, resolveOutcome, txPhase,
                 xferStore, xferUsed, activeTransfer, durableOffsets,
                 imageDurable, manifestResult, installLog, fwPhase,
                 recoveryFlag>>

F_Verify(tid) ==
  /\ ~recoveryFlag /\ tid \in xferUsed /\ chunkPhase[tid] = "written"
  /\ chunkPhase' = [chunkPhase EXCEPT ![tid] = "verified"]
  /\ pendingVerified' = [pendingVerified EXCEPT ![tid] = TRUE]
  /\ UNCHANGED <<senderEpoch, epochHighWater, seqNum, senderRebooted, lastAcceptedEpoch, lastAcceptedHighWater,
                 acceptedPairs, syncState, proposedEpoch, syncAttempts,
                 hasInflight, inflightEpoch, inflightSeq, epochPc,
                 txStore, txUsed, actuationLog, physicalEffectLog,
                 identityLocks, recoveryLock, consumedIdentities, blockedResources, evidenceKind, resolveOutcome, txPhase,
                 xferStore, xferUsed, activeTransfer, durableOffsets,
                 pendingOffset, pendingDurable, imageDurable, manifestResult,
                 installLog, fwPhase, recoveryFlag>>

F_Durabilize(tid) ==
  /\ ~recoveryFlag /\ tid \in xferUsed
  /\ chunkPhase[tid] = "verified" /\ pendingVerified[tid]
  /\ chunkPhase' = [chunkPhase EXCEPT ![tid] = "durabilizing"]
  /\ pendingDurable' = [pendingDurable EXCEPT ![tid] = TRUE]
  /\ UNCHANGED <<senderEpoch, epochHighWater, seqNum, senderRebooted, lastAcceptedEpoch, lastAcceptedHighWater,
                 acceptedPairs, syncState, proposedEpoch, syncAttempts,
                 hasInflight, inflightEpoch, inflightSeq, epochPc,
                 txStore, txUsed, actuationLog, physicalEffectLog,
                 identityLocks, recoveryLock, consumedIdentities, blockedResources, evidenceKind, resolveOutcome, txPhase,
                 xferStore, xferUsed, activeTransfer, durableOffsets,
                 pendingOffset, pendingVerified, imageDurable, manifestResult,
                 installLog, fwPhase, recoveryFlag>>

F_Advance(tid) ==
  /\ ~recoveryFlag /\ tid \in xferUsed
  /\ chunkPhase[tid] = "durabilizing" /\ pendingDurable[tid]
  /\ durableOffsets' = [durableOffsets EXCEPT ![tid] = @ \cup {pendingOffset[tid]}]
  /\ chunkPhase' = [chunkPhase EXCEPT ![tid] = "idle"]
  /\ pendingVerified' = [pendingVerified EXCEPT ![tid] = FALSE]
  /\ pendingDurable' = [pendingDurable EXCEPT ![tid] = FALSE]
  /\ UNCHANGED <<senderEpoch, epochHighWater, seqNum, senderRebooted, lastAcceptedEpoch, lastAcceptedHighWater,
                 acceptedPairs, syncState, proposedEpoch, syncAttempts,
                 hasInflight, inflightEpoch, inflightSeq, epochPc,
                 txStore, txUsed, actuationLog, physicalEffectLog,
                 identityLocks, recoveryLock, consumedIdentities, blockedResources, evidenceKind, resolveOutcome, txPhase,
                 xferStore, xferUsed, activeTransfer, pendingOffset,
                 imageDurable, manifestResult, installLog, fwPhase,
                 recoveryFlag>>

F_MarkDurable(tid) ==
  /\ ~recoveryFlag /\ tid \in xferUsed
  /\ xferStore[tid].state = "IN_PROGRESS" /\ fwPhase[tid] = "active"
  /\ chunkPhase[tid] = "idle" /\ FwNextExpected(tid) = xferStore[tid].length
  /\ imageDurable' = [imageDurable EXCEPT ![tid] = TRUE]
  /\ fwPhase' = [fwPhase EXCEPT ![tid] = "closing"]
  /\ UNCHANGED <<senderEpoch, epochHighWater, seqNum, senderRebooted, lastAcceptedEpoch, lastAcceptedHighWater,
                 acceptedPairs, syncState, proposedEpoch, syncAttempts,
                 hasInflight, inflightEpoch, inflightSeq, epochPc,
                 txStore, txUsed, actuationLog, physicalEffectLog,
                 identityLocks, recoveryLock, consumedIdentities, blockedResources, evidenceKind, resolveOutcome, txPhase,
                 xferStore, xferUsed, activeTransfer, durableOffsets,
                 chunkPhase, pendingOffset, pendingVerified, pendingDurable,
                 manifestResult, installLog, recoveryFlag>>

F_VerifyManifestPass(tid) ==
  /\ ~recoveryFlag /\ tid \in xferUsed
  /\ fwPhase[tid] = "closing" /\ imageDurable[tid]
  /\ manifestResult[tid] = "NONE"
  /\ manifestResult' = [manifestResult EXCEPT ![tid] = "PASS"]
  /\ UNCHANGED <<senderEpoch, epochHighWater, seqNum, senderRebooted, lastAcceptedEpoch, lastAcceptedHighWater,
                 acceptedPairs, syncState, proposedEpoch, syncAttempts,
                 hasInflight, inflightEpoch, inflightSeq, epochPc,
                 txStore, txUsed, actuationLog, physicalEffectLog,
                 identityLocks, recoveryLock, consumedIdentities, blockedResources, evidenceKind, resolveOutcome, txPhase,
                 xferStore, xferUsed, activeTransfer, durableOffsets,
                 chunkPhase, pendingOffset, pendingVerified, pendingDurable,
                 imageDurable, installLog, fwPhase, recoveryFlag>>

F_VerifyManifestFail(tid) ==
  /\ ~recoveryFlag /\ tid \in xferUsed
  /\ fwPhase[tid] = "closing" /\ imageDurable[tid]
  /\ manifestResult[tid] = "NONE"
  /\ manifestResult' = [manifestResult EXCEPT ![tid] = "FAIL"]
  /\ xferStore' = [xferStore EXCEPT ![tid].state = "ABORTED"]
  /\ activeTransfer' = [activeTransfer EXCEPT ![xferStore[tid].client] = NoActive]
  /\ fwPhase' = [fwPhase EXCEPT ![tid] = "idle"]
  /\ UNCHANGED <<senderEpoch, epochHighWater, seqNum, senderRebooted, lastAcceptedEpoch, lastAcceptedHighWater,
                 acceptedPairs, syncState, proposedEpoch, syncAttempts,
                 hasInflight, inflightEpoch, inflightSeq, epochPc,
                 txStore, txUsed, actuationLog, physicalEffectLog,
                 identityLocks, recoveryLock, consumedIdentities, blockedResources, evidenceKind, resolveOutcome, txPhase,
                 xferUsed, durableOffsets, chunkPhase, pendingOffset, pendingVerified, pendingDurable,
                 imageDurable, installLog, recoveryFlag>>


F_Close(tid) ==
  /\ ~recoveryFlag /\ tid \in xferUsed /\ fwPhase[tid] = "closing"
  /\ imageDurable[tid] /\ manifestResult[tid] = "PASS"
  /\ xferStore' = [xferStore EXCEPT ![tid].state = "COMPLETED"]
  /\ activeTransfer' = [activeTransfer EXCEPT ![xferStore[tid].client] = NoActive]
  /\ fwPhase' = [fwPhase EXCEPT ![tid] = "done"]
  /\ UNCHANGED <<senderEpoch, epochHighWater, seqNum, senderRebooted, lastAcceptedEpoch, lastAcceptedHighWater,
                 acceptedPairs, syncState, proposedEpoch, syncAttempts,
                 hasInflight, inflightEpoch, inflightSeq, epochPc,
                 txStore, txUsed, actuationLog, physicalEffectLog,
                 identityLocks, recoveryLock, consumedIdentities, blockedResources, evidenceKind, resolveOutcome, txPhase,
                 xferUsed, durableOffsets, chunkPhase, pendingOffset,
                 pendingVerified, pendingDurable, imageDurable, manifestResult,
                 installLog, recoveryFlag>>

F_Install(tid) ==
  /\ ~recoveryFlag /\ tid \in xferUsed
  /\ xferStore[tid].state = "COMPLETED"
  /\ imageDurable[tid] /\ manifestResult[tid] = "PASS"
  /\ Cardinality({ i \in DOMAIN installLog : installLog[i] = tid }) = 0
  /\ installLog' = Append(installLog, tid)
  /\ UNCHANGED <<senderEpoch, epochHighWater, seqNum, senderRebooted, lastAcceptedEpoch, lastAcceptedHighWater,
                 acceptedPairs, syncState, proposedEpoch, syncAttempts,
                 hasInflight, inflightEpoch, inflightSeq, epochPc,
                 txStore, txUsed, actuationLog, physicalEffectLog,
                 identityLocks, recoveryLock, consumedIdentities, blockedResources, evidenceKind, resolveOutcome, txPhase,
                 xferStore, xferUsed, activeTransfer, durableOffsets,
                 chunkPhase, pendingOffset, pendingVerified, pendingDurable,
                 imageDurable, manifestResult, fwPhase, recoveryFlag>>

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
                      /\ txStore[tid].state \in {"PERSISTED", "DISPATCHED", "EFFECT_DONE"}
                   THEN [txStore[tid] EXCEPT !.state = "INDETERMINATE"]
                   ELSE IF tid \in txUsed /\ txStore[tid].state = "NEW"
                   THEN [txStore[tid] EXCEPT !.state = "IDLE"]
                   ELSE txStore[tid]]
  /\ txUsed' = txUsed \ { tid \in txUsed : txStore[tid].state = "NEW" }
  /\ blockedResources' =
       blockedResources \cup
       { txStore[tid].resource :
           tid \in { t \in txUsed :
                        txStore[t].state \in {"PERSISTED", "DISPATCHED", "EFFECT_DONE"} } }
  /\ txPhase' = [tid \in 0..MaxTx-1 |->
                   IF tid \in txUsed
                      /\ txPhase[tid] \in {"persisting", "dispatching", "awaiting_effect", "recording"}
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
                   IF tid \in xferUsed /\ fwPhase[tid] \in {"active", "closing"}
                   THEN "idle" ELSE fwPhase[tid]]
  /\ UNCHANGED <<senderEpoch, epochHighWater, seqNum, senderRebooted, lastAcceptedEpoch, lastAcceptedHighWater,
                 acceptedPairs, syncState, proposedEpoch, syncAttempts,
                 actuationLog, physicalEffectLog, consumedIdentities,
                 evidenceKind, resolveOutcome,
                 xferUsed, durableOffsets, pendingOffset,
                 imageDurable, manifestResult, installLog>>

FinishRecovery ==
  /\ recoveryFlag /\ recoveryLock
  /\ recoveryFlag' = FALSE /\ recoveryLock' = FALSE
  /\ UNCHANGED <<senderEpoch, epochHighWater, seqNum, senderRebooted, lastAcceptedEpoch, lastAcceptedHighWater,
                 acceptedPairs, syncState, proposedEpoch, syncAttempts,
                 hasInflight, inflightEpoch, inflightSeq, epochPc,
                 txStore, txUsed, actuationLog, physicalEffectLog,
                 identityLocks, consumedIdentities, blockedResources, evidenceKind, resolveOutcome, txPhase,
                 xferStore, xferUsed, activeTransfer, durableOffsets,
                 chunkPhase, pendingOffset, pendingVerified, pendingDurable,
                 imageDurable, manifestResult, installLog, fwPhase>>

-----------------------------------------------------------------------------
Next ==
  \/ E_SendOrdinary \/ E_AcceptOrdinary \/ E_SoftRotate
  \/ E_DeliverSync \/ E_FinishSync
  \/ \E c \in Clients, t \in 0..MaxTx-1, a \in 0..MaxTx-1, r \in Resources, h \in 0..MaxHash :
       C_Start(c, t, a, r, h)
  \/ \E t \in 0..MaxTx-1 : C_Persist(t)
  \/ \E t \in 0..MaxTx-1 : C_Dispatch(t)
  \/ \E t \in 0..MaxTx-1 : C_Effect(t)
  \/ \E t \in 0..MaxTx-1 : C_Record(t)
  \/ \E t \in 0..MaxTx-1, k \in EvidenceKind \ {"NONE"} : C_CollectEvidence(t, k)
  \/ \E t \in 0..MaxTx-1, o \in {"CONFIRMED_EFFECT", "CONFIRMED_ABSENT", "OPERATOR_CLOSED"} :
       C_Resolve(t, o)
  \/ \E c \in Clients, t \in 0..MaxTransfers-1, l \in 1..MaxChunks :
       F_Start(c, t, l)
  \/ \E t \in 0..MaxTransfers-1, o \in 0..MaxChunks-1 : F_Write(t, o)
  \/ \E t \in 0..MaxTransfers-1 : F_Verify(t)
  \/ \E t \in 0..MaxTransfers-1 : F_Durabilize(t)
  \/ \E t \in 0..MaxTransfers-1 : F_Advance(t)
  \/ \E t \in 0..MaxTransfers-1 : F_MarkDurable(t)
  \/ \E t \in 0..MaxTransfers-1 : F_VerifyManifestPass(t)
  \/ \E t \in 0..MaxTransfers-1 : F_VerifyManifestFail(t)
  \/ \E t \in 0..MaxTransfers-1 : F_Close(t)
  \/ \E t \in 0..MaxTransfers-1 : F_Install(t)
  \/ Crash
  \/ FinishRecovery

vars == <<
  senderEpoch, epochHighWater, seqNum, senderRebooted, lastAcceptedEpoch, lastAcceptedHighWater, acceptedPairs,
  syncState, proposedEpoch, syncAttempts, hasInflight, inflightEpoch,
  inflightSeq, epochPc,
  txStore, txUsed, actuationLog, physicalEffectLog, identityLocks,
  recoveryLock, txPhase, consumedIdentities, blockedResources,
  evidenceKind, resolveOutcome,
  xferStore, xferUsed, activeTransfer, durableOffsets, chunkPhase,
  pendingOffset, pendingVerified, pendingDurable, imageDurable,
  manifestResult, installLog, fwPhase,
  recoveryFlag
>>

Spec == Init /\ [][Next]_vars

THEOREM Spec => []TypeOK
THEOREM Spec => []Inv_NonceUniqueness
THEOREM Spec => []Inv_EpochMonotonic
THEOREM Spec => []Inv_LastAcceptedMonotonic
THEOREM Spec => []Inv_AcceptedCoveredByLast
THEOREM Spec => []Inv_NoDoubleActuation
THEOREM Spec => []Inv_NoNewDispatchDuringEpochSync
THEOREM Spec => []Inv_PersistBeforeDispatch
THEOREM Spec => []Inv_NoActuationDuringRecovery
THEOREM Spec => []Inv_NoDeadlockUnderRecovery
THEOREM Spec => []Inv_AuthorizedResolution
THEOREM Spec => []Inv_NoIdentityReuse
THEOREM Spec => []Inv_IndeterminateBlocksResource
THEOREM Spec => []Inv_NoActiveOnBlockedResource
THEOREM Spec => []Inv_NoDoubleInstall
THEOREM Spec => []Inv_NoInstallBeforeManifest
THEOREM Spec => []Inv_CompletedRequiresManifestPass
THEOREM Spec => []Inv_ManifestFailAborts
THEOREM Spec => []Inv_AtMostOneTransferPerClient
THEOREM Spec => []Inv_SharedRecovery

=============================================================================
\* Root composition – November 2026
\* Integrates Epoch + Core + Firmware under a shared Recovery Barrier
=============================================================================
