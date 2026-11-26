------------------------- MODULE REFRIG_GDO_Epoch_Coverage -------------------------
(***************************************************************************)
(* Directed coverage scenario for REFRIG_GDO_Epoch.                       *)
(* Exercises: out-of-order acceptance, stale-window rejection, duplicate   *)
(* datagram rejection, soft rotation with an in-flight packet, and         *)
(* 0x40/0x41 loss + retransmission.                                        *)
(* This is a bounded scenario test, not a replacement for the base model.  *)
(***************************************************************************)

EXTENDS REFRIG_GDO_Epoch

VARIABLE stage

CovVars == <<senderEpoch, epochHighWater, seqNum, senderRebooted,
             lastAcceptedEpoch, lastAcceptedHighWater, seqHighWater,
             acceptedPairs, syncState, proposedEpoch, syncAttempts,
             pendingPackets, pc, stage>>

Stages == {"send1", "send2", "accept2", "send3", "accept3",
           "rejectOld", "duplicate", "rejectDuplicate", "send4",
           "rotateWithPending", "receiveSync1", "loseSyncResponse",
           "retransmitSync", "receiveSync2", "deliverSync", "finishSync",
           "done"}

InitCov ==
  /\ Init
  /\ stage = "send1"

CovSend1 ==
  /\ stage = "send1"
  /\ SendOrdinary
  /\ stage' = "send2"

CovSend2 ==
  /\ stage = "send2"
  /\ SendOrdinary
  /\ stage' = "accept2"

\* Force acceptance of sequence 2 while sequence 1 remains queued.
CovAcceptOutOfOrder ==
  /\ stage = "accept2"
  /\ AcceptOrdinary
  /\ acceptedPairs' = acceptedPairs \cup {<<senderEpoch, 2>>}
  /\ stage' = "send3"

CovSend3 ==
  /\ stage = "send3"
  /\ SendOrdinary
  /\ stage' = "accept3"

CovAccept3 ==
  /\ stage = "accept3"
  /\ AcceptOrdinary
  /\ acceptedPairs' = acceptedPairs \cup {<<senderEpoch, 3>>}
  /\ stage' = "rejectOld"

\* At this point seqHighWater=3, WindowSize=2, WindowLow=2;
\* sequence 1 is still queued and must be rejected as too old.
CovRejectTooOld ==
  /\ stage = "rejectOld"
  /\ RejectTooOld
  /\ stage' = "duplicate"

CovDuplicate ==
  /\ stage = "duplicate"
  /\ DuplicateAcceptedPacket
  /\ stage' = "rejectDuplicate"

CovRejectDuplicate ==
  /\ stage = "rejectDuplicate"
  /\ RejectDuplicate
  /\ stage' = "send4"

CovSend4 ==
  /\ stage = "send4"
  /\ SendOrdinary
  /\ stage' = "rotateWithPending"

\* Sequence 4 is still in the receive queue when soft rotation occurs.
CovRotateWithPending ==
  /\ stage = "rotateWithPending"
  /\ pendingPackets # <<>>
  /\ TriggerSoftRotation
  /\ stage' = "receiveSync1"

CovReceiveSync1 ==
  /\ stage = "receiveSync1"
  /\ ReceiveSyncRequest
  /\ stage' = "loseSyncResponse"

CovLoseSyncResponse ==
  /\ stage = "loseSyncResponse"
  /\ LoseSyncResponse
  /\ stage' = "retransmitSync"

CovRetransmitSync ==
  /\ stage = "retransmitSync"
  /\ RetransmitSyncReq
  /\ stage' = "receiveSync2"

CovReceiveSync2 ==
  /\ stage = "receiveSync2"
  /\ ReceiveSyncRequest
  /\ stage' = "deliverSync"

CovDeliverSync ==
  /\ stage = "deliverSync"
  /\ DeliverSyncResponse
  /\ stage' = "finishSync"

CovFinishSync ==
  /\ stage = "finishSync"
  /\ FinishSync
  /\ stage' = "done"

CovNext ==
  \/ CovSend1
  \/ CovSend2
  \/ CovAcceptOutOfOrder
  \/ CovSend3
  \/ CovAccept3
  \/ CovRejectTooOld
  \/ CovDuplicate
  \/ CovRejectDuplicate
  \/ CovSend4
  \/ CovRotateWithPending
  \/ CovReceiveSync1
  \/ CovLoseSyncResponse
  \/ CovRetransmitSync
  \/ CovReceiveSync2
  \/ CovDeliverSync
  \/ CovFinishSync

CoverageSpec ==
  InitCov
  /\ [][CovNext]_CovVars
  /\ WF_CovVars(CovNext)

EventuallyDone == <> (stage = "done")

THEOREM CoverageSpec => []TypeOK
THEOREM CoverageSpec => []Inv_SoftRotation
THEOREM CoverageSpec => []Inv_AcceptedCoveredByLast
THEOREM CoverageSpec => []Inv_NoOrphanEpochInHistory
THEOREM CoverageSpec => []Inv_SyncAdvancesEpoch
THEOREM CoverageSpec => []Inv_EpochMonotonic
THEOREM CoverageSpec => []Inv_LastAcceptedMonotonic
THEOREM CoverageSpec => []Inv_SeqHighWaterConsistent

=============================================================================
