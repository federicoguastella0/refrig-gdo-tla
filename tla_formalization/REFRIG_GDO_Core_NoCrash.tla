------------------------ MODULE REFRIG_GDO_Core_NoCrash ------------------------
(*****************************************************************************)
(* Analysis aid: Core without Crash/FinishRecovery so TLC can surface        *)
(* functional terminals. Not part of the normative safety claim set.         *)
(*****************************************************************************)
EXTENDS REFRIG_GDO_Core

NextNoCrash ==
  \/ \E c \in Clients, t \in 0..MaxTx-1, a \in 0..MaxTx-1,
        r \in Resources, h \in 0..MaxHash :
       StartTransaction(c, t, a, r, h)
  \/ \E t \in 0..MaxTx-1 : Persist(t)
  \/ \E t \in 0..MaxTx-1 : Dispatch(t)
  \/ \E t \in 0..MaxTx-1 : PhysicalEffect(t)
  \/ \E t \in 0..MaxTx-1 : RecordCompletion(t)
  \/ \E t \in 0..MaxTx-1, k \in EvidenceKind \ {"NONE"} : CollectEvidence(t, k)
  \/ \E t \in 0..MaxTx-1,
        o \in {"CONFIRMED_EFFECT", "CONFIRMED_ABSENT", "OPERATOR_CLOSED"} :
       ResolveIndeterminate(t, o)

SpecNoCrash ==
  Init /\ [][NextNoCrash]_<<txStore, used, actuationLog, physicalEffectLog,
              identityLocks, recoveryLock, recoveryFlag, consumedIdentities,
              blockedResources, evidenceKind, resolveOutcome, phase>>

THEOREM SpecNoCrash => []TypeOK
THEOREM SpecNoCrash => []Inv_NoIdentityReuse
THEOREM SpecNoCrash => []Inv_IndeterminateBlocksResource

=============================================================================
