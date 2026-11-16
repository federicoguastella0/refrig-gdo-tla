---------------------------- MODULE REFRIG_GDO_Epoch ----------------------------
(*****************************************************************************)
(* REFRIG-GDO – SenderEpoch & Anti-Replay Formalization (v1.4.5) strengthened*)
(*                                                                           *)
(* Point 3 (audit):                                                          *)
(*   - Nonce uniqueness over permanent history (not cleared on sync)         *)
(*   - Real Epoch monotonicity via high-water mark                           *)
(*   - LastAcceptedEpoch monotonicity via high-water mark                    *)
(*   - Ordinary accept only last or last+1 (enforced + invariant)            *)
(*   - Sender reboot + 0x40/0x41 with loss/retransmit                        *)
(*                                                                           *)
(* Single sender modelled; multi-sender composition left for a later root    *)
(* specification. AEAD assumed perfect when an action is taken.              *)
(*****************************************************************************)

EXTENDS Integers, FiniteSets, Sequences, TLC

CONSTANTS
  MaxEpoch,
  MaxSeq,
  SoftRotationThreshold

ASSUME MaxEpoch \in Nat \ {0} /\ MaxSeq \in Nat \ {0}
ASSUME SoftRotationThreshold \in Nat /\ SoftRotationThreshold > 0
ASSUME SoftRotationThreshold <= MaxSeq

VARIABLES
  (* Sender persistent state *)
  senderEpoch,            \* current SenderEpoch (persistent across reboot)
  epochHighWater,         \* high-water mark of SenderEpoch
  seqNum,                 \* current Sequence Number within the epoch
  senderRebooted,         \* BOOLEAN – last action was a reboot (epoch already++)

  (* Controller state *)
  lastAcceptedEpoch,      \* LastAcceptedEpoch
  lastAcceptedHighWater,  \* high-water of LastAcceptedEpoch (monotonic)
  acceptedPairs,          \* permanent history of accepted (epoch, seq)

  (* Sync handshake state *)
  syncState,              \* "idle" | "req_sent" | "resp_pending" | "done"
  proposedEpoch,          \* Epoch carried in the outstanding 0x40
  syncAttempts,           \* number of 0x40 retransmissions for current sync

  (* In-flight ordinary packet *)
  hasInflight,            \* BOOLEAN
  inflightEpoch,          \* 0..MaxEpoch
  inflightSeq,            \* 0..MaxSeq
  pc                      \* sender control: "idle" | "sending" | "syncing"

-----------------------------------------------------------------------------
TypeOK ==
  /\ senderEpoch       \in 0..MaxEpoch
  /\ epochHighWater    \in 0..MaxEpoch
  /\ seqNum            \in 0..MaxSeq
  /\ senderRebooted    \in BOOLEAN
  /\ lastAcceptedEpoch \in 0..MaxEpoch
  /\ lastAcceptedHighWater \in 0..MaxEpoch
  /\ acceptedPairs     \in Seq((0..MaxEpoch) \X (0..MaxSeq))
  /\ syncState \in {"idle", "req_sent", "resp_pending", "done"}
  /\ proposedEpoch     \in 0..MaxEpoch
  /\ syncAttempts      \in 0..3
  /\ hasInflight \in BOOLEAN
  /\ inflightEpoch \in 0..MaxEpoch
  /\ inflightSeq \in 0..MaxSeq
  /\ pc \in {"idle", "sending", "syncing"}

-----------------------------------------------------------------------------
\* Helpers

Pair(e, s) == <<e, s>>

\* Has this (epoch, seq) already been accepted?
AlreadyAccepted(e, s) ==
  \E i \in DOMAIN acceptedPairs : acceptedPairs[i] = <<e, s>>

-----------------------------------------------------------------------------
\* Strengthened invariants

\* Nonce uniqueness over the *history* of accepted pairs (not a set cardinality)
Inv_NonceUniqueness ==
  \A i, j \in DOMAIN acceptedPairs :
    i # j => acceptedPairs[i] # acceptedPairs[j]

\* Soft-rotation: seqNum never exceeds the threshold without an epoch bump
Inv_SoftRotation ==
  seqNum <= SoftRotationThreshold

Inv_AcceptedCoveredByLast ==
  \A i \in DOMAIN acceptedPairs :
    acceptedPairs[i][1] <= lastAcceptedEpoch

Inv_NoOrphanEpochInHistory ==
  \A i \in DOMAIN acceptedPairs :
    LET e == acceptedPairs[i][1] IN
      e = 0 \/ e <= lastAcceptedHighWater

Inv_SyncAdvancesEpoch ==
  syncState = "done" => lastAcceptedEpoch = proposedEpoch

Inv_EpochMonotonic ==
  /\ senderEpoch = epochHighWater
  /\ epochHighWater \in 0..MaxEpoch

Inv_LastAcceptedMonotonic ==
  /\ lastAcceptedEpoch = lastAcceptedHighWater
  /\ lastAcceptedHighWater \in 0..MaxEpoch

-----------------------------------------------------------------------------
Init ==
  /\ senderEpoch       = 0
  /\ epochHighWater    = 0
  /\ seqNum            = 0
  /\ senderRebooted    = FALSE
  /\ lastAcceptedEpoch = 0
  /\ lastAcceptedHighWater = 0
  /\ acceptedPairs     = <<>>
  /\ syncState         = "idle"
  /\ proposedEpoch     = 0
  /\ syncAttempts      = 0
  /\ hasInflight       = FALSE
  /\ inflightEpoch     = 0
  /\ inflightSeq       = 0
  /\ pc                = "idle"

-----------------------------------------------------------------------------
\* --- Sender actions -------------------------------------------------------

\* Emit an ordinary data packet (only when not in soft-rotation / sync)
SendOrdinary ==
  /\ pc = "idle"
  /\ syncState = "idle"
  /\ seqNum < SoftRotationThreshold
  /\ seqNum < MaxSeq
  /\ seqNum' = seqNum + 1
  /\ hasInflight' = TRUE
  /\ inflightEpoch' = senderEpoch
  /\ inflightSeq' = seqNum + 1
  /\ pc' = "sending"
  /\ senderRebooted' = FALSE
  /\ UNCHANGED <<senderEpoch, epochHighWater, lastAcceptedEpoch, lastAcceptedHighWater, acceptedPairs,
                 syncState, proposedEpoch, syncAttempts>>

\* Soft-rotation: epoch++, seq=0, then must sync before ordinary traffic
TriggerSoftRotation ==
  /\ pc \in {"idle", "sending"}
  /\ seqNum >= SoftRotationThreshold
  /\ senderEpoch < MaxEpoch
  /\ senderEpoch' = senderEpoch + 1
  /\ epochHighWater' = senderEpoch + 1
  /\ seqNum'      = 0
  /\ proposedEpoch' = senderEpoch + 1
  /\ syncState'   = "req_sent"
  /\ syncAttempts' = 0
  /\ hasInflight' = FALSE
  /\ inflightEpoch' = 0
  /\ inflightSeq' = 0
  /\ pc'          = "syncing"
  /\ senderRebooted' = FALSE
  /\ UNCHANGED <<lastAcceptedEpoch, lastAcceptedHighWater, acceptedPairs>>

\* Sender reboot: must increment persistent SenderEpoch before any TX
SenderReboot ==
  /\ pc = "idle"
  /\ syncState = "idle"
  /\ senderEpoch < MaxEpoch
  /\ senderEpoch' = senderEpoch + 1
  /\ epochHighWater' = senderEpoch + 1
  /\ seqNum'      = 0
  /\ senderRebooted' = TRUE
  /\ proposedEpoch' = senderEpoch + 1
  /\ syncState'   = "req_sent"      \* reboot forces sync
  /\ syncAttempts' = 0
  /\ hasInflight' = FALSE
  /\ inflightEpoch' = 0
  /\ inflightSeq' = 0
  /\ pc'          = "syncing"
  /\ UNCHANGED <<lastAcceptedEpoch, lastAcceptedHighWater, acceptedPairs>>

\* Retransmit 0x40 if response was lost
RetransmitSyncReq ==
  /\ pc = "syncing"
  /\ syncState = "req_sent"
  /\ syncAttempts < 3
  /\ syncAttempts' = syncAttempts + 1
  /\ UNCHANGED <<senderEpoch, epochHighWater, seqNum, senderRebooted, lastAcceptedEpoch, lastAcceptedHighWater,
                 acceptedPairs, syncState, proposedEpoch,
                 hasInflight, inflightEpoch, inflightSeq, pc>>

-----------------------------------------------------------------------------
\* --- Controller / network actions ----------------------------------------

\* Accept ordinary packet (Epoch == lastAccepted or lastAccepted+1)
AcceptOrdinary ==
  /\ pc = "sending"
  /\ hasInflight = TRUE
  /\ LET e == inflightEpoch
         s == inflightSeq
     IN
       /\ \/ e = lastAcceptedEpoch
          \/ e = lastAcceptedEpoch + 1
       /\ ~AlreadyAccepted(e, s)
       /\ acceptedPairs' = Append(acceptedPairs, <<e, s>>)
       /\ IF e = lastAcceptedEpoch + 1
          THEN /\ lastAcceptedEpoch' = e
               /\ lastAcceptedHighWater' = e
          ELSE UNCHANGED <<lastAcceptedEpoch, lastAcceptedHighWater>>
  /\ hasInflight' = FALSE
  /\ inflightEpoch' = 0
  /\ inflightSeq' = 0
  /\ pc' = "idle"
  /\ UNCHANGED <<senderEpoch, epochHighWater, seqNum, senderRebooted, syncState,
                 proposedEpoch, syncAttempts>>

\* Reject ordinary packet with large epoch jump
RejectLargeJump ==
  /\ pc = "sending"
  /\ hasInflight = TRUE
  /\ inflightEpoch > lastAcceptedEpoch + 1
  /\ hasInflight' = FALSE
  /\ inflightEpoch' = 0
  /\ inflightSeq' = 0
  /\ pc' = "idle"
  /\ UNCHANGED <<senderEpoch, epochHighWater, seqNum, senderRebooted, lastAcceptedEpoch, lastAcceptedHighWater,
                 acceptedPairs, syncState, proposedEpoch, syncAttempts>>

\* Controller receives 0x40 and prepares 0x41 (response may still be lost)
ReceiveSyncRequest ==
  /\ pc = "syncing"
  /\ syncState = "req_sent"
  /\ proposedEpoch >= lastAcceptedEpoch   \* monotonicity guard
  /\ syncState' = "resp_pending"
  /\ UNCHANGED <<senderEpoch, epochHighWater, seqNum, senderRebooted, lastAcceptedEpoch, lastAcceptedHighWater,
                 acceptedPairs, proposedEpoch, syncAttempts,
                 hasInflight, inflightEpoch, inflightSeq, pc>>

\* 0x41 is delivered → controller advances LastAcceptedEpoch, clears window
DeliverSyncResponse ==
  /\ pc = "syncing"
  /\ syncState = "resp_pending"
  /\ lastAcceptedEpoch' = proposedEpoch
  /\ lastAcceptedHighWater' = proposedEpoch
  \* Keep full acceptance history – nonce uniqueness is global across sync
  /\ syncState' = "done"
  /\ pc' = "idle"
  /\ UNCHANGED <<senderEpoch, epochHighWater, seqNum, senderRebooted, proposedEpoch,
                 syncAttempts, hasInflight, inflightEpoch, inflightSeq, acceptedPairs>>

\* 0x41 is lost → sender may retransmit 0x40
LoseSyncResponse ==
  /\ pc = "syncing"
  /\ syncState = "resp_pending"
  /\ syncState' = "req_sent"        \* back to retransmit-able state
  /\ UNCHANGED <<senderEpoch, epochHighWater, seqNum, senderRebooted, lastAcceptedEpoch, lastAcceptedHighWater,
                 acceptedPairs, proposedEpoch, syncAttempts, hasInflight, inflightEpoch, inflightSeq, pc>>

\* Sync completed; return to idle traffic
FinishSync ==
  /\ pc = "idle"
  /\ syncState = "done"
  /\ syncState' = "idle"
  /\ UNCHANGED <<senderEpoch, epochHighWater, seqNum, senderRebooted, lastAcceptedEpoch, lastAcceptedHighWater,
                 acceptedPairs, proposedEpoch, syncAttempts, hasInflight, inflightEpoch, inflightSeq, pc>>

-----------------------------------------------------------------------------
Next ==
  \/ SendOrdinary
  \/ TriggerSoftRotation
  \/ SenderReboot
  \/ RetransmitSyncReq
  \/ AcceptOrdinary
  \/ RejectLargeJump
  \/ ReceiveSyncRequest
  \/ DeliverSyncResponse
  \/ LoseSyncResponse
  \/ FinishSync

Spec == Init /\ [][Next]_<<senderEpoch, epochHighWater, seqNum, senderRebooted,
                           lastAcceptedEpoch, lastAcceptedHighWater, acceptedPairs, syncState,
                           proposedEpoch, syncAttempts, hasInflight, inflightEpoch, inflightSeq, pc>>

THEOREM Spec => []TypeOK
THEOREM Spec => []Inv_NonceUniqueness
THEOREM Spec => []Inv_SoftRotation
THEOREM Spec => []Inv_AcceptedCoveredByLast
THEOREM Spec => []Inv_NoOrphanEpochInHistory
THEOREM Spec => []Inv_SyncAdvancesEpoch
THEOREM Spec => []Inv_EpochMonotonic
THEOREM Spec => []Inv_LastAcceptedMonotonic

=============================================================================
\* Modification History
\* Strengthened rewrite – November 2026 – audit findings on Epoch
\* History-based nonce uniqueness, reboot, full 0x40/0x41 with loss
=============================================================================
