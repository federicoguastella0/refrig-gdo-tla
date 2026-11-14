------------------------ MODULE REFRIG_GDO_Core_NoCrash ------------------------
(*****************************************************************************)
(* Core with Crash disabled – used only to classify *functional* terminal    *)
(* states (work completed / slots exhausted) without the always-enabled      *)
(* Crash action masking them from TLC deadlock detection.                    *)
(*                                                                           *)
(* This is an analysis aid, not a claim that the system cannot crash.        *)
(*****************************************************************************)

EXTENDS REFRIG_GDO_Core

\* Restrict Next by removing Crash (and FinishRecovery, which is only
\* meaningful after Crash).
NextNoCrash ==
  \/ \E c \in Clients, t \in 0..MaxTx-1, a \in 0..MaxTx-1, h \in 0..MaxHash :
       StartTransaction(c, t, a, h)
  \/ \E t \in 0..MaxTx-1 : Persist(t)
  \/ \E t \in 0..MaxTx-1 : Dispatch(t)
  \/ \E t \in 0..MaxTx-1 : PhysicalEffect(t)
  \/ \E t \in 0..MaxTx-1 : RecordCompletion(t)
  \/ \E t \in 0..MaxTx-1 : CollectEvidence(t)
  \/ \E t \in 0..MaxTx-1 : ResolveIndeterminate(t)

SpecNoCrash == Init /\ [][NextNoCrash]_<<txStore, used, actuationLog, physicalEffectLog,
              identityLocks, recoveryLock, recoveryFlag, resolutionEvidence, phase>>

THEOREM SpecNoCrash => []TypeOK
THEOREM SpecNoCrash => []Inv_NoDoubleActuation
THEOREM SpecNoCrash => []Inv_PersistBeforeDispatch
THEOREM SpecNoCrash => []Inv_EffectAfterDispatch
THEOREM SpecNoCrash => []Inv_UniqueIdentity

=============================================================================
