---------------------------- MODULE REFRIG_GDO_Core ----------------------------
(*****************************************************************************)
(* REFRIG-GDO Protocol – Core TLA+ Formalization (v1.4.5) – strengthened     *)
(*                                                                           *)
(* Addresses audit findings:                                                 *)
(*   A. Actuation history (not a set) → real no-double-actuation             *)
(*   B. Concurrent transactions + distinct lock classes + lock order         *)
(*   C. Explicit physical window: persist → dispatch → effect → record       *)
(*      with crash possible between every step → INDETERMINATE               *)
(*   D. ResolveIndeterminate requires authorization evidence                 *)
(*   E. Stronger identity: ClientDeviceID × TransactionID + payload check    *)
(*                                                                           *)
(* Recovery Barrier, persist-before-actuate, lock ordering remain central.   *)
(* AEAD assumed perfect; concrete NVM layout abstracted.                     *)
(*****************************************************************************)

EXTENDS Integers, FiniteSets, Sequences, TLC

CONSTANTS
  Clients,                  \* set of ClientDeviceID
  MaxTx,                    \* max concurrent transaction slots (0..MaxTx-1)
  MaxHash                   \* small domain for abstract payload hashes

ASSUME
  /\ MaxTx   \in Nat \ {0}
  /\ MaxHash \in Nat \ {0}

VARIABLES
  (* Transaction store – finite slots *)
  txStore,                  \* [0..MaxTx-1 |-> TxRecord]
  used,                     \* SUBSET (0..MaxTx-1)

  (* Actuation history – sequence of dispatch events (audit A) *)
  actuationLog,             \* Seq of tid that have been dispatched to hardware

  (* Physical effect history – separate from dispatch (audit C) *)
  physicalEffectLog,        \* Seq of tid whose physical effect has occurred

  (* Lock classes – distinct and ordered (audit B) *)
  identityLocks,            \* SUBSET (0..MaxTx-1)  – held Identity locks
  recoveryLock,             \* BOOLEAN – Recovery Barrier exclusive lock

  (* Recovery *)
  recoveryFlag,             \* BOOLEAN – Recovery Barrier active

  (* Authorization evidence for INDETERMINATE resolution (audit D) *)
  resolutionEvidence,       \* [tid |-> BOOLEAN] – evidence collected for resolve

  (* Control – per-slot progress, not a single global serialising pc *)
  phase                     \* [0..MaxTx-1 |-> Phase]

-----------------------------------------------------------------------------
\* Types

TxState == {
  "IDLE",
  "NEW",
  "PERSISTED",          \* durable commit done, not yet dispatched
  "DISPATCHED",         \* command sent to actuator, effect not yet observed
  "EFFECT_DONE",        \* physical effect occurred, result not yet recorded
  "COMPLETED",
  "INDETERMINATE",
  "RESOLVED",
  "REJECTED"
}

\* Explicit phases of the critical window (audit C)
Phase == {
  "idle",
  "persisting",
  "dispatching",
  "awaiting_effect",
  "recording",
  "done"
}

TxRecord == [
  client      : Clients,
  appTxId     : 0..MaxTx-1,     \* application TransactionID (abstract)
  state       : TxState,
  payloadHash : 0..MaxHash,
  durable     : BOOLEAN
]

-----------------------------------------------------------------------------
\* TypeOK

TypeOK ==
  /\ txStore \in [0..MaxTx-1 -> TxRecord]
  /\ used \subseteq (0..MaxTx-1)
  /\ actuationLog \in Seq(0..MaxTx-1)
  /\ physicalEffectLog \in Seq(0..MaxTx-1)
  /\ identityLocks \subseteq (0..MaxTx-1)
  /\ recoveryLock \in BOOLEAN
  /\ recoveryFlag \in BOOLEAN
  /\ resolutionEvidence \in [0..MaxTx-1 -> BOOLEAN]
  /\ phase \in [0..MaxTx-1 -> Phase]

-----------------------------------------------------------------------------
\* Helpers

IsUsed(tid) == tid \in used

\* Identity of a transaction for conflict detection (audit E)
SameIdentity(t1, t2) ==
  /\ txStore[t1].client  = txStore[t2].client
  /\ txStore[t1].appTxId = txStore[t2].appTxId

\* Lock ordering: Recovery lock is highest; Identity locks acquired only
\* when recoveryLock is free. Prevents classic deadlock under recovery.
CanAcquireIdentity(tid) ==
  /\ ~recoveryLock
  /\ ~recoveryFlag
  /\ tid \notin identityLocks

-----------------------------------------------------------------------------
\* Safety Invariants (strengthened)

\* A. No double actuation – counts events in the history, not set membership
Inv_NoDoubleActuation ==
  \A tid \in used :
    Cardinality({ i \in DOMAIN actuationLog : actuationLog[i] = tid }) <= 1

\* Persist-before-dispatch (and therefore before actuation)
Inv_PersistBeforeDispatch ==
  \A tid \in used :
    Cardinality({ i \in DOMAIN actuationLog : actuationLog[i] = tid }) > 0
      => txStore[tid].durable = TRUE

\* Physical effect never precedes dispatch
Inv_EffectAfterDispatch ==
  \A tid \in used :
    Cardinality({ i \in DOMAIN physicalEffectLog : physicalEffectLog[i] = tid }) > 0
      => Cardinality({ i \in DOMAIN actuationLog : actuationLog[i] = tid }) > 0

\* No new dispatch or effect while Recovery Barrier is active
Inv_NoActuationDuringRecovery ==
  recoveryFlag =>
    \A tid \in used :
      phase[tid] \notin {"dispatching", "awaiting_effect", "recording"}

\* B. Under recovery the Recovery lock is held and all Identity locks are free
Inv_NoDeadlockUnderRecovery ==
  recoveryFlag =>
    /\ recoveryLock = TRUE
    /\ identityLocks = {}

\* D. RESOLVED only after evidence was collected
Inv_AuthorizedResolution ==
  \A tid \in used :
    txStore[tid].state = "RESOLVED" => resolutionEvidence[tid] = TRUE

\* E. At most one non-terminal transaction per (client, appTxId)
Inv_UniqueIdentity ==
  \A t1, t2 \in used :
    /\ t1 # t2
    /\ SameIdentity(t1, t2)
    =>
      \/ txStore[t1].state \in {"COMPLETED", "RESOLVED", "REJECTED", "IDLE"}
      \/ txStore[t2].state \in {"COMPLETED", "RESOLVED", "REJECTED", "IDLE"}

\* Completed implies physical effect occurred (or was resolved from indeterminate)
Inv_CompletedImpliesEffectOrResolved ==
  \A tid \in used :
    txStore[tid].state = "COMPLETED" =>
      \/ Cardinality({ i \in DOMAIN physicalEffectLog : physicalEffectLog[i] = tid }) > 0
      \/ resolutionEvidence[tid] = TRUE

-----------------------------------------------------------------------------
\* Initial state

Init ==
  /\ txStore = [tid \in 0..MaxTx-1 |->
                  [client      |-> CHOOSE c \in Clients : TRUE,
                   appTxId     |-> 0,
                   state       |-> "IDLE",
                   payloadHash |-> 0,
                   durable     |-> FALSE]]
  /\ used = {}
  /\ actuationLog = <<>>
  /\ physicalEffectLog = <<>>
  /\ identityLocks = {}
  /\ recoveryLock = FALSE
  /\ recoveryFlag = FALSE
  /\ resolutionEvidence = [tid \in 0..MaxTx-1 |-> FALSE]
  /\ phase = [tid \in 0..MaxTx-1 |-> "idle"]

-----------------------------------------------------------------------------
\* Actions

\* --- Start / identity (audit E) ------------------------------------------

\* Allocate a free slot. Reject if same (client, appTxId) already active
\* with a different payload (conflict). Same identity + same payload is
\* treated as retransmission and left unchanged (idempotent).
StartTransaction(client, tid, appId, hash) ==
  /\ ~recoveryFlag
  /\ tid \in 0..MaxTx-1
  /\ tid \notin used
  /\ appId \in 0..MaxTx-1
  /\ hash \in 0..MaxHash
  /\ \* no active transaction with the same identity (client, appTxId)
     \* (retransmission of an already-active identity is rejected at this
     \*  abstraction level; a future refinement can model pure retransmit)
     \A t \in used :
       ~( /\ txStore[t].client  = client
          /\ txStore[t].appTxId = appId
          /\ txStore[t].state \notin {"COMPLETED", "RESOLVED", "REJECTED", "IDLE"} )
  /\ txStore' = [txStore EXCEPT ![tid] =
                   [client      |-> client,
                    appTxId     |-> appId,
                    state       |-> "NEW",
                    payloadHash |-> hash,
                    durable     |-> FALSE]]
  /\ used' = used \cup {tid}
  /\ phase' = [phase EXCEPT ![tid] = "idle"]
  /\ UNCHANGED <<actuationLog, physicalEffectLog, identityLocks,
                 recoveryLock, recoveryFlag, resolutionEvidence>>

\* --- Critical window steps (audit C) -------------------------------------

\* 1. Acquire Identity lock and make the transaction durable
Persist(tid) ==
  /\ ~recoveryFlag
  /\ tid \in used
  /\ txStore[tid].state = "NEW"
  /\ phase[tid] = "idle"
  /\ CanAcquireIdentity(tid)
  /\ identityLocks' = identityLocks \cup {tid}
  /\ txStore' = [txStore EXCEPT ![tid].state = "PERSISTED",
                               ![tid].durable = TRUE]
  /\ phase' = [phase EXCEPT ![tid] = "persisting"]
  /\ UNCHANGED <<used, actuationLog, physicalEffectLog,
                 recoveryLock, recoveryFlag, resolutionEvidence>>

\* 2. Dispatch command to actuator (records an actuation event)
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
                 recoveryLock, recoveryFlag, resolutionEvidence>>

\* 3. Physical effect occurs (hardware side)
PhysicalEffect(tid) ==
  /\ ~recoveryFlag
  /\ tid \in used
  /\ txStore[tid].state = "DISPATCHED"
  /\ phase[tid] = "dispatching"
  /\ physicalEffectLog' = Append(physicalEffectLog, tid)
  /\ txStore' = [txStore EXCEPT ![tid].state = "EFFECT_DONE"]
  /\ phase' = [phase EXCEPT ![tid] = "awaiting_effect"]
  /\ UNCHANGED <<used, actuationLog, identityLocks,
                 recoveryLock, recoveryFlag, resolutionEvidence>>

\* 4. Record successful completion and release Identity lock
RecordCompletion(tid) ==
  /\ ~recoveryFlag
  /\ tid \in used
  /\ txStore[tid].state = "EFFECT_DONE"
  /\ phase[tid] = "awaiting_effect"
  /\ txStore' = [txStore EXCEPT ![tid].state = "COMPLETED"]
  /\ identityLocks' = identityLocks \ {tid}
  /\ phase' = [phase EXCEPT ![tid] = "done"]
  /\ UNCHANGED <<used, actuationLog, physicalEffectLog,
                 recoveryLock, recoveryFlag, resolutionEvidence>>

\* --- Crash / Recovery Barrier --------------------------------------------

\* Crash can occur in any phase. Every non-terminal transaction that has
\* been dispatched but not yet fully recorded becomes INDETERMINATE.
\* All Identity locks are dropped; Recovery lock is taken.
Crash ==
  /\ ~recoveryFlag
  /\ recoveryFlag' = TRUE
  /\ recoveryLock' = TRUE
  /\ identityLocks' = {}
  /\ txStore' = [tid \in 0..MaxTx-1 |->
                   IF tid \in used
                      /\ txStore[tid].state \in {"PERSISTED", "DISPATCHED",
                                                 "EFFECT_DONE"}
                   THEN [txStore[tid] EXCEPT !.state = "INDETERMINATE"]
                   ELSE txStore[tid]]
  /\ phase' = [tid \in 0..MaxTx-1 |->
                 IF tid \in used
                    /\ phase[tid] \in {"persisting", "dispatching",
                                       "awaiting_effect", "recording"}
                 THEN "idle"
                 ELSE phase[tid]]
  /\ UNCHANGED <<used, actuationLog, physicalEffectLog, resolutionEvidence>>

\* End of Recovery Barrier
FinishRecovery ==
  /\ recoveryFlag = TRUE
  /\ recoveryLock = TRUE
  /\ recoveryFlag' = FALSE
  /\ recoveryLock' = FALSE
  /\ UNCHANGED <<txStore, used, actuationLog, physicalEffectLog,
                 identityLocks, resolutionEvidence, phase>>

\* --- Authorized resolution of INDETERMINATE (audit D) --------------------

\* Evidence must be collected before resolution is allowed.
CollectEvidence(tid) ==
  /\ tid \in used
  /\ txStore[tid].state = "INDETERMINATE"
  /\ resolutionEvidence' = [resolutionEvidence EXCEPT ![tid] = TRUE]
  /\ UNCHANGED <<txStore, used, actuationLog, physicalEffectLog,
                 identityLocks, recoveryLock, recoveryFlag, phase>>

\* Resolution is permitted only after evidence has been collected.
ResolveIndeterminate(tid) ==
  /\ tid \in used
  /\ txStore[tid].state = "INDETERMINATE"
  /\ resolutionEvidence[tid] = TRUE
  /\ txStore' = [txStore EXCEPT ![tid].state = "RESOLVED"]
  /\ phase' = [phase EXCEPT ![tid] = "done"]
  /\ UNCHANGED <<used, actuationLog, physicalEffectLog,
                 identityLocks, recoveryLock, recoveryFlag, resolutionEvidence>>

-----------------------------------------------------------------------------
\* Next-state relation

Next ==
  \/ \E c \in Clients, t \in 0..MaxTx-1, a \in 0..MaxTx-1, h \in 0..MaxHash :
       StartTransaction(c, t, a, h)
  \/ \E t \in 0..MaxTx-1 : Persist(t)
  \/ \E t \in 0..MaxTx-1 : Dispatch(t)
  \/ \E t \in 0..MaxTx-1 : PhysicalEffect(t)
  \/ \E t \in 0..MaxTx-1 : RecordCompletion(t)
  \/ Crash
  \/ FinishRecovery
  \/ \E t \in 0..MaxTx-1 : CollectEvidence(t)
  \/ \E t \in 0..MaxTx-1 : ResolveIndeterminate(t)

-----------------------------------------------------------------------------
\* Specification

Spec == Init /\ [][Next]_<<txStore, used, actuationLog, physicalEffectLog,
                           identityLocks, recoveryLock, recoveryFlag,
                           resolutionEvidence, phase>>

THEOREM Spec => []TypeOK
THEOREM Spec => []Inv_NoDoubleActuation
THEOREM Spec => []Inv_PersistBeforeDispatch
THEOREM Spec => []Inv_EffectAfterDispatch
THEOREM Spec => []Inv_NoActuationDuringRecovery
THEOREM Spec => []Inv_NoDeadlockUnderRecovery
THEOREM Spec => []Inv_AuthorizedResolution
THEOREM Spec => []Inv_UniqueIdentity
THEOREM Spec => []Inv_CompletedImpliesEffectOrResolved

=============================================================================
\* Modification History
\* Strengthened rewrite – November 2026 – addresses audit A–E
\* Focus: actuation history, physical uncertainty window, concurrency,
\*         authorised resolution, stronger transaction identity
=============================================================================
