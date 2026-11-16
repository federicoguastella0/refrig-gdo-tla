---------------------------- MODULE REFRIG_GDO_Core ----------------------------
(*****************************************************************************)
(* REFRIG-GDO Protocol – Core TLA+ Formalization (v1.4.5)                     *)
(*                                                                           *)
(* Point 2 (audit): INDETERMINATE reconciliation + physical resource block   *)
(*                                                                           *)
(*   - Each transaction targets a physical resource                          *)
(*   - Crash → INDETERMINATE blocks that resource until authorised resolve   *)
(*   - No new transaction may start on a blocked resource                    *)
(*   - Evidence has a kind; only AUTHORIZED_OPERATOR may resolve             *)
(*   - Resolve records outcome and unblocks the resource                     *)
(*                                                                           *)
(* Also retains: actuation history, persist→dispatch→effect→record window,  *)
(* lock classes, permanent identity (client, appTxId).                       *)
(*****************************************************************************)

EXTENDS Integers, FiniteSets, Sequences, TLC

CONSTANTS
  Clients,
  Resources,                \* set of physical resource ids
  MaxTx,
  MaxHash

ASSUME
  /\ MaxTx \in Nat \ {0}
  /\ MaxHash \in Nat \ {0}
  /\ Resources # {}

VARIABLES
  txStore,
  used,
  actuationLog,
  physicalEffectLog,
  identityLocks,
  recoveryLock,
  recoveryFlag,
  consumedIdentities,
  (* Physical resource blocking under INDETERMINATE *)
  blockedResources,         \* SUBSET Resources
  (* Evidence: kind per tid – not a bare boolean *)
  evidenceKind,             \* [tid |-> EvidenceKind]
  (* Who resolved / outcome *)
  resolveOutcome,           \* [tid |-> ResolveOutcome]
  phase

-----------------------------------------------------------------------------
TxState == {
  "IDLE", "NEW", "PERSISTED", "DISPATCHED", "EFFECT_DONE",
  "COMPLETED", "INDETERMINATE", "RESOLVED", "REJECTED"
}

Phase == {
  "idle", "persisting", "dispatching", "awaiting_effect", "recording", "done"
}

\* Evidence collected during reconciliation (abstract but differentiated)
EvidenceKind == {
  "NONE",
  "HW_READBACK_ON",       \* hardware indicates effect present
  "HW_READBACK_OFF",      \* hardware indicates effect absent
  "AUTHORIZED_OPERATOR"   \* explicit authorised human/system resolution
}

ResolveOutcome == {
  "NONE",
  "CONFIRMED_EFFECT",     \* treated as completed successfully
  "CONFIRMED_ABSENT",     \* treated as no effect / safe reject path
  "OPERATOR_CLOSED"       \* closed under operator authority
}

TxRecord == [
  client      : Clients,
  appTxId     : 0..MaxTx-1,
  resource    : Resources,
  state       : TxState,
  payloadHash : 0..MaxHash,
  durable     : BOOLEAN
]

-----------------------------------------------------------------------------
TypeOK ==
  /\ txStore \in [0..MaxTx-1 -> TxRecord]
  /\ used \subseteq (0..MaxTx-1)
  /\ actuationLog \in Seq(0..MaxTx-1)
  /\ physicalEffectLog \in Seq(0..MaxTx-1)
  /\ identityLocks \subseteq (0..MaxTx-1)
  /\ recoveryLock \in BOOLEAN
  /\ recoveryFlag \in BOOLEAN
  /\ consumedIdentities \subseteq (Clients \X (0..MaxTx-1))
  /\ blockedResources \subseteq Resources
  /\ evidenceKind \in [0..MaxTx-1 -> EvidenceKind]
  /\ resolveOutcome \in [0..MaxTx-1 -> ResolveOutcome]
  /\ phase \in [0..MaxTx-1 -> Phase]

-----------------------------------------------------------------------------
CanAcquireIdentity(tid) ==
  /\ ~recoveryLock
  /\ ~recoveryFlag
  /\ tid \notin identityLocks

ResourceFree(r) == r \notin blockedResources

ActiveStates == {"NEW", "PERSISTED", "DISPATCHED", "EFFECT_DONE", "INDETERMINATE"}

NoOtherActiveOnResource(tid, res) ==
  \A t \in used :
    \/ t = tid
    \/ txStore[t].resource # res
    \/ txStore[t].state \notin ActiveStates \ {"INDETERMINATE"}
    \* allow multiple INDETERMINATE on same resource; block new actives only

-----------------------------------------------------------------------------
\* Safety invariants

Inv_NoDoubleActuation ==
  \A tid \in used :
    Cardinality({ i \in DOMAIN actuationLog : actuationLog[i] = tid }) <= 1

Inv_PersistBeforeDispatch ==
  \A tid \in used :
    Cardinality({ i \in DOMAIN actuationLog : actuationLog[i] = tid }) > 0
      => txStore[tid].durable = TRUE

Inv_EffectAfterDispatch ==
  \A tid \in used :
    Cardinality({ i \in DOMAIN physicalEffectLog : physicalEffectLog[i] = tid }) > 0
      => Cardinality({ i \in DOMAIN actuationLog : actuationLog[i] = tid }) > 0

Inv_NoActuationDuringRecovery ==
  recoveryFlag =>
    \A tid \in used :
      phase[tid] \notin {"dispatching", "awaiting_effect", "recording"}

Inv_NoDeadlockUnderRecovery ==
  recoveryFlag =>
    /\ recoveryLock = TRUE
    /\ identityLocks = {}

Inv_NoIdentityReuse ==
  /\ \A t1, t2 \in used :
       /\ t1 # t2
       /\ txStore[t1].client = txStore[t2].client
       /\ txStore[t1].appTxId = txStore[t2].appTxId
       => FALSE
  /\ \A tid \in used :
       <<txStore[tid].client, txStore[tid].appTxId>> \in consumedIdentities

\* Every INDETERMINATE transaction blocks its resource
Inv_IndeterminateBlocksResource ==
  \A tid \in used :
    txStore[tid].state = "INDETERMINATE" =>
      txStore[tid].resource \in blockedResources

\* No non-terminal transaction may hold a resource that is blocked
\* (except the INDETERMINATE owner itself)
Inv_NoActiveOnBlockedResource ==
  \A tid \in used :
    /\ txStore[tid].state \in {"NEW", "PERSISTED", "DISPATCHED", "EFFECT_DONE"}
    => txStore[tid].resource \notin blockedResources

\* RESOLVED only with AUTHORIZED_OPERATOR evidence and a defined outcome
Inv_AuthorizedResolution ==
  \A tid \in used :
    txStore[tid].state = "RESOLVED" =>
      /\ evidenceKind[tid] = "AUTHORIZED_OPERATOR"
      /\ resolveOutcome[tid] \in {"CONFIRMED_EFFECT", "CONFIRMED_ABSENT", "OPERATOR_CLOSED"}

\* After RESOLVED, that resource is no longer blocked by this tid
\* (resource may still be blocked by another INDETERMINATE tid)
\* If a RESOLVED tx's resource is still blocked, another INDETERMINATE holds it.
Inv_ResolvedDoesNotNeedBlock ==
  \A tid \in used :
    txStore[tid].state = "RESOLVED" =>
      (txStore[tid].resource \in blockedResources =>
        \E t2 \in used :
          /\ t2 # tid
          /\ txStore[t2].state = "INDETERMINATE"
          /\ txStore[t2].resource = txStore[tid].resource)

Inv_CompletedImpliesEffectOrResolved ==
  \A tid \in used :
    txStore[tid].state = "COMPLETED" =>
      Cardinality({ i \in DOMAIN physicalEffectLog : physicalEffectLog[i] = tid }) > 0

-----------------------------------------------------------------------------
Init ==
  /\ txStore = [tid \in 0..MaxTx-1 |->
                  [client      |-> CHOOSE c \in Clients : TRUE,
                   appTxId     |-> 0,
                   resource    |-> CHOOSE r \in Resources : TRUE,
                   state       |-> "IDLE",
                   payloadHash |-> 0,
                   durable     |-> FALSE]]
  /\ used = {}
  /\ actuationLog = <<>>
  /\ physicalEffectLog = <<>>
  /\ identityLocks = {}
  /\ recoveryLock = FALSE
  /\ recoveryFlag = FALSE
  /\ consumedIdentities = {}
  /\ blockedResources = {}
  /\ evidenceKind = [tid \in 0..MaxTx-1 |-> "NONE"]
  /\ resolveOutcome = [tid \in 0..MaxTx-1 |-> "NONE"]
  /\ phase = [tid \in 0..MaxTx-1 |-> "idle"]

-----------------------------------------------------------------------------
\* Start: permanent identity + resource must not be blocked
StartTransaction(client, tid, appId, res, hash) ==
  /\ ~recoveryFlag
  /\ tid \in 0..MaxTx-1
  /\ tid \notin used
  /\ appId \in 0..MaxTx-1
  /\ res \in Resources
  /\ hash \in 0..MaxHash
  /\ <<client, appId>> \notin consumedIdentities
  /\ ResourceFree(res)
  /\ \A t \in used :
        \/ txStore[t].resource # res
        \/ txStore[t].state \notin {"NEW", "PERSISTED", "DISPATCHED", "EFFECT_DONE", "INDETERMINATE"}
  /\ txStore' = [txStore EXCEPT ![tid] =
                   [client      |-> client,
                    appTxId     |-> appId,
                    resource    |-> res,
                    state       |-> "NEW",
                    payloadHash |-> hash,
                    durable     |-> FALSE]]
  /\ used' = used \cup {tid}
  /\ consumedIdentities' = consumedIdentities \cup {<<client, appId>>}
  /\ phase' = [phase EXCEPT ![tid] = "idle"]
  /\ UNCHANGED <<actuationLog, physicalEffectLog, identityLocks,
                 recoveryLock, recoveryFlag, blockedResources,
                 evidenceKind, resolveOutcome>>

Persist(tid) ==
  /\ ~recoveryFlag
  /\ tid \in used
  /\ txStore[tid].state = "NEW"
  /\ phase[tid] = "idle"
  /\ CanAcquireIdentity(tid)
  /\ ResourceFree(txStore[tid].resource)
  /\ identityLocks' = identityLocks \cup {tid}
  /\ txStore' = [txStore EXCEPT ![tid].state = "PERSISTED",
                               ![tid].durable = TRUE]
  /\ phase' = [phase EXCEPT ![tid] = "persisting"]
  /\ UNCHANGED <<used, actuationLog, physicalEffectLog,
                 recoveryLock, recoveryFlag, consumedIdentities,
                 blockedResources, evidenceKind, resolveOutcome>>

Dispatch(tid) ==
  /\ ~recoveryFlag
  /\ tid \in used
  /\ txStore[tid].state = "PERSISTED"
  /\ phase[tid] = "persisting"
  /\ tid \in identityLocks
  /\ txStore[tid].durable = TRUE
  /\ actuationLog' = Append(actuationLog, tid)
  /\ txStore' = [txStore EXCEPT ![tid].state = "DISPATCHED"]
  /\ phase' = [phase EXCEPT ![tid] = "dispatching"]
  /\ UNCHANGED <<used, physicalEffectLog, identityLocks,
                 recoveryLock, recoveryFlag, consumedIdentities,
                 blockedResources, evidenceKind, resolveOutcome>>

PhysicalEffect(tid) ==
  /\ ~recoveryFlag
  /\ tid \in used
  /\ txStore[tid].state = "DISPATCHED"
  /\ phase[tid] = "dispatching"
  /\ physicalEffectLog' = Append(physicalEffectLog, tid)
  /\ txStore' = [txStore EXCEPT ![tid].state = "EFFECT_DONE"]
  /\ phase' = [phase EXCEPT ![tid] = "awaiting_effect"]
  /\ UNCHANGED <<used, actuationLog, identityLocks,
                 recoveryLock, recoveryFlag, consumedIdentities,
                 blockedResources, evidenceKind, resolveOutcome>>

RecordCompletion(tid) ==
  /\ ~recoveryFlag
  /\ tid \in used
  /\ txStore[tid].state = "EFFECT_DONE"
  /\ phase[tid] = "awaiting_effect"
  /\ txStore' = [txStore EXCEPT ![tid].state = "COMPLETED"]
  /\ identityLocks' = identityLocks \ {tid}
  /\ phase' = [phase EXCEPT ![tid] = "done"]
  /\ UNCHANGED <<used, actuationLog, physicalEffectLog,
                 recoveryLock, recoveryFlag, consumedIdentities,
                 blockedResources, evidenceKind, resolveOutcome>>

\* Crash: non-terminal in-window txs become INDETERMINATE and block resources
Crash ==
  /\ ~recoveryFlag
  /\ recoveryFlag' = TRUE
  /\ recoveryLock' = TRUE
  /\ identityLocks' = {}
  /\ txStore' = [tid \in 0..MaxTx-1 |->
                   IF tid \in used
                      /\ txStore[tid].state \in {"NEW", "PERSISTED", "DISPATCHED", "EFFECT_DONE"}
                   THEN [txStore[tid] EXCEPT !.state = "INDETERMINATE"]
                   ELSE txStore[tid]]
  /\ blockedResources' =
       blockedResources \cup
       { txStore[tid].resource :
           tid \in { t \in used :
                        txStore[t].state \in {"NEW", "PERSISTED", "DISPATCHED", "EFFECT_DONE"} } }
  /\ phase' = [tid \in 0..MaxTx-1 |->
                 IF tid \in used
                    /\ phase[tid] \in {"persisting", "dispatching",
                                       "awaiting_effect", "recording"}
                 THEN "idle"
                 ELSE phase[tid]]
  /\ UNCHANGED <<used, actuationLog, physicalEffectLog, consumedIdentities,
                 evidenceKind, resolveOutcome>>

FinishRecovery ==
  /\ recoveryFlag = TRUE
  /\ recoveryLock = TRUE
  /\ recoveryFlag' = FALSE
  /\ recoveryLock' = FALSE
  \* blockedResources intentionally retained until ResolveIndeterminate
  /\ UNCHANGED <<txStore, used, actuationLog, physicalEffectLog,
                 identityLocks, consumedIdentities, blockedResources,
                 evidenceKind, resolveOutcome, phase>>

\* Collect hardware or operator evidence (not a bare boolean)
CollectEvidence(tid, kind) ==
  /\ tid \in used
  /\ txStore[tid].state = "INDETERMINATE"
  /\ kind \in EvidenceKind \ {"NONE"}
  /\ evidenceKind' = [evidenceKind EXCEPT ![tid] = kind]
  /\ UNCHANGED <<txStore, used, actuationLog, physicalEffectLog,
                 identityLocks, recoveryLock, recoveryFlag,
                 consumedIdentities, blockedResources, resolveOutcome, phase>>

\* Only AUTHORIZED_OPERATOR evidence permits resolution; outcome is recorded;
\* resource is unblocked unless another INDETERMINATE still holds it.
ResolveIndeterminate(tid, outcome) ==
  /\ tid \in used
  /\ txStore[tid].state = "INDETERMINATE"
  /\ evidenceKind[tid] = "AUTHORIZED_OPERATOR"
  /\ outcome \in {"CONFIRMED_EFFECT", "CONFIRMED_ABSENT", "OPERATOR_CLOSED"}
  /\ txStore' = [txStore EXCEPT ![tid].state = "RESOLVED"]
  /\ resolveOutcome' = [resolveOutcome EXCEPT ![tid] = outcome]
  /\ blockedResources' =
       IF \E t2 \in used :
            /\ t2 # tid
            /\ txStore[t2].state = "INDETERMINATE"
            /\ txStore[t2].resource = txStore[tid].resource
       THEN blockedResources
       ELSE blockedResources \ {txStore[tid].resource}
  /\ phase' = [phase EXCEPT ![tid] = "done"]
  /\ UNCHANGED <<used, actuationLog, physicalEffectLog,
                 identityLocks, recoveryLock, recoveryFlag,
                 consumedIdentities, evidenceKind>>

-----------------------------------------------------------------------------
Next ==
  \/ \E c \in Clients, t \in 0..MaxTx-1, a \in 0..MaxTx-1,
        r \in Resources, h \in 0..MaxHash :
       StartTransaction(c, t, a, r, h)
  \/ \E t \in 0..MaxTx-1 : Persist(t)
  \/ \E t \in 0..MaxTx-1 : Dispatch(t)
  \/ \E t \in 0..MaxTx-1 : PhysicalEffect(t)
  \/ \E t \in 0..MaxTx-1 : RecordCompletion(t)
  \/ Crash
  \/ FinishRecovery
  \/ \E t \in 0..MaxTx-1, k \in EvidenceKind \ {"NONE"} : CollectEvidence(t, k)
  \/ \E t \in 0..MaxTx-1,
        o \in {"CONFIRMED_EFFECT", "CONFIRMED_ABSENT", "OPERATOR_CLOSED"} :
       ResolveIndeterminate(t, o)

Spec == Init /\ [][Next]_<<txStore, used, actuationLog, physicalEffectLog,
                           identityLocks, recoveryLock, recoveryFlag,
                           consumedIdentities, blockedResources,
                           evidenceKind, resolveOutcome, phase>>

THEOREM Spec => []TypeOK
THEOREM Spec => []Inv_NoDoubleActuation
THEOREM Spec => []Inv_PersistBeforeDispatch
THEOREM Spec => []Inv_EffectAfterDispatch
THEOREM Spec => []Inv_NoActuationDuringRecovery
THEOREM Spec => []Inv_NoDeadlockUnderRecovery
THEOREM Spec => []Inv_NoIdentityReuse
THEOREM Spec => []Inv_IndeterminateBlocksResource
THEOREM Spec => []Inv_NoActiveOnBlockedResource
THEOREM Spec => []Inv_AuthorizedResolution
THEOREM Spec => []Inv_ResolvedDoesNotNeedBlock
THEOREM Spec => []Inv_CompletedImpliesEffectOrResolved

=============================================================================
\* Point 2 – INDETERMINATE + resource block – November 2026
=============================================================================
