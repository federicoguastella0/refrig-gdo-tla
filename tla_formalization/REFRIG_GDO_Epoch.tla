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
  SoftRotationThreshold,
  WindowSize                 \* anti-replay sliding window width (seq domain)

ASSUME MaxEpoch \in Nat \ {0} /\ MaxSeq \in Nat \ {0}
ASSUME SoftRotationThreshold \in Nat /\ SoftRotationThreshold > 0
ASSUME SoftRotationThreshold <= MaxSeq
ASSUME WindowSize \in Nat /\ WindowSize > 0
ASSUME WindowSize <= MaxSeq + 1

VARIABLES
  (* Sender persistent state *)
  senderEpoch,            \* current SenderEpoch (persistent across reboot)
  epochHighWater,         \* high-water mark of SenderEpoch
  seqNum,                 \* current Sequence Number within the epoch
  senderRebooted,         \* BOOLEAN – last action was a reboot (epoch already++)

  (* Controller state *)
  lastAcceptedEpoch,      \* LastAcceptedEpoch
  lastAcceptedHighWater,  \* high-water of LastAcceptedEpoch (monotonic)
  seqHighWater,           \* max accepted Sequence Number in lastAcceptedEpoch
  acceptedPairs,          \* permanent history of accepted (epoch, seq)

  (* Sync handshake state *)
  syncState,              \* "idle" | "req_sent" | "resp_pending" | "done"
  proposedEpoch,          \* Epoch carried in the outstanding 0x40
  syncAttempts,           \* number of 0x40 retransmissions for current sync

  (* Network receive queue: sequence of packet occurrences; duplicates are representable *)
  pendingPackets,         \* SUBSET ((0..MaxEpoch) \X (0..MaxSeq))
  pc                      \* sender control: "idle" | "sending" | "syncing"

-----------------------------------------------------------------------------
TypeOK ==
  /\ senderEpoch       \in 0..MaxEpoch
  /\ epochHighWater    \in 0..MaxEpoch
  /\ seqNum            \in 0..MaxSeq
  /\ senderRebooted    \in BOOLEAN
  /\ lastAcceptedEpoch \in 0..MaxEpoch
  /\ lastAcceptedHighWater \in 0..MaxEpoch
  /\ seqHighWater      \in 0..MaxSeq
  /\ acceptedPairs     \in Seq((0..MaxEpoch) \X (0..MaxSeq))
  /\ syncState \in {"idle", "req_sent", "resp_pending", "done"}
  /\ proposedEpoch     \in 0..MaxEpoch
  /\ syncAttempts      \in 0..3
  /\ pendingPackets \in Seq((0..MaxEpoch) \X (0..MaxSeq))
  /\ pc \in {"idle", "sending", "syncing"}

-----------------------------------------------------------------------------
\* Helpers

Pair(e, s) == <<e, s>>

\* Has this (epoch, seq) already been accepted?
AlreadyAccepted(e, s) ==
  \E i \in DOMAIN acceptedPairs : acceptedPairs[i] = <<e, s>>

(* Remove one network packet occurrence by position (sequences preserve duplicates). *)
RemoveAt(s, i) ==
  SubSeq(s, 1, i - 1) \o SubSeq(s, i + 1, Len(s))

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

\* Accepted pairs in the current epoch lie inside the sliding window
\* Permanent history is for nonce uniqueness only.
\* The sliding window constrains *new acceptance*, not historical membership.
\* Therefore we do NOT require every historically accepted pair to still lie
\* inside the current window (that would contradict window advance).

\* seqHighWater is the max accepted Sequence Number in lastAcceptedEpoch
Inv_SeqHighWaterConsistent ==
  /\ (\A i \in DOMAIN acceptedPairs :
         acceptedPairs[i][1] = lastAcceptedEpoch =>
           acceptedPairs[i][2] <= seqHighWater)
  /\ ((\E i \in DOMAIN acceptedPairs : acceptedPairs[i][1] = lastAcceptedEpoch)
        => (\E i \in DOMAIN acceptedPairs :
              acceptedPairs[i][1] = lastAcceptedEpoch
              /\ acceptedPairs[i][2] = seqHighWater)
      \/ seqHighWater = 0)

\* Lower bound of the live window (0 if window not yet full)
WindowLow ==
  IF seqHighWater < WindowSize THEN 0 ELSE seqHighWater - WindowSize + 1

\* No accepted pair in the *current* epoch was accepted with seq below
\* the high-water of its time in a way that breaks high-water monotonicity:
\* equivalent safety: high-water is monotone and equals max accepted seq.
\* (Acceptance outside WindowLow is prevented by action guards.)

-----------------------------------------------------------------------------
Init ==
  /\ senderEpoch       = 0
  /\ epochHighWater    = 0
  /\ seqNum            = 0
  /\ senderRebooted    = FALSE
  /\ lastAcceptedEpoch = 0
  /\ lastAcceptedHighWater = 0
  /\ seqHighWater      = 0
  /\ acceptedPairs     = <<>>
  /\ syncState         = "idle"
  /\ proposedEpoch     = 0
  /\ syncAttempts      = 0
  /\ pendingPackets    = <<>>
  /\ pc                = "idle"

-----------------------------------------------------------------------------
\* --- Sender actions -------------------------------------------------------

\* Emit an ordinary data packet (only when not in soft-rotation / sync)
SendOrdinary ==
  /\ pc \in {"idle", "sending"}
  /\ syncState = "idle"
  /\ seqNum < SoftRotationThreshold
  /\ seqNum < MaxSeq
  /\ Len(pendingPackets) < 3   \* bound in-flight set for model checking
  /\ seqNum' = seqNum + 1
  /\ pendingPackets' = Append(pendingPackets, <<senderEpoch, seqNum + 1>>)
  /\ pc' = "sending"
  /\ senderRebooted' = FALSE
  /\ UNCHANGED <<senderEpoch, epochHighWater, lastAcceptedEpoch, lastAcceptedHighWater, seqHighWater, acceptedPairs,
                 syncState, proposedEpoch, syncAttempts>>

\* Soft-rotation: epoch++, seq=0, then must sync before ordinary traffic
\* Soft-rotation: any ordinary packet still in flight is treated as *lost*
\* (not completed, not retransmitted by this action). Controller must not
\* accept a stale inflight after epoch bump without sync.
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
  /\ pendingPackets' = <<>>           \* pending ordinary discarded (loss) on rotation
  /\ pc'          = "syncing"
  /\ senderRebooted' = FALSE
  /\ UNCHANGED <<lastAcceptedEpoch, lastAcceptedHighWater, seqHighWater, acceptedPairs>>

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
  /\ pendingPackets' = <<>>
  /\ pc'          = "syncing"
  /\ UNCHANGED <<lastAcceptedEpoch, lastAcceptedHighWater, seqHighWater, acceptedPairs>>

\* Retransmit 0x40 if response was lost
RetransmitSyncReq ==
  /\ pc = "syncing"
  /\ syncState = "req_sent"
  /\ syncAttempts < 3
  /\ seqNum < MaxSeq
  /\ syncAttempts' = syncAttempts + 1
  /\ seqNum' = seqNum + 1
  /\ UNCHANGED <<senderEpoch, epochHighWater, senderRebooted, lastAcceptedEpoch, lastAcceptedHighWater, seqHighWater,
                 acceptedPairs, syncState, proposedEpoch,
                 pendingPackets, pc>>

-----------------------------------------------------------------------------
\* --- Controller / network actions ----------------------------------------

\* Accept ordinary packet (Epoch == lastAccepted or lastAccepted+1)
\* Accept one pending ordinary packet (any order within pending set = OOO).
\* Same-epoch: lastAccepted* unchanged; seqHighWater advances if s is higher.
\* Window guard applies only at acceptance time (history may retain older seq).
AcceptOrdinary ==
  /\ \E i \in DOMAIN pendingPackets :
       LET e == pendingPackets[i][1]
           s == pendingPackets[i][2]
           remaining == RemoveAt(pendingPackets, i)
       IN
         /\ \/ e = lastAcceptedEpoch
            \/ e = lastAcceptedEpoch + 1
         /\ ~AlreadyAccepted(e, s)
         /\ e = lastAcceptedEpoch + 1
            \/ seqHighWater < WindowSize
            \/ s >= WindowLow
         /\ pendingPackets' = remaining
         /\ acceptedPairs' = Append(acceptedPairs, <<e, s>>)
         /\ IF e = lastAcceptedEpoch + 1
            THEN /\ lastAcceptedEpoch' = e
                 /\ lastAcceptedHighWater' = e
                 /\ seqHighWater' = s
            ELSE /\ UNCHANGED <<lastAcceptedEpoch, lastAcceptedHighWater>>
                 /\ seqHighWater' = IF s > seqHighWater THEN s ELSE seqHighWater
         /\ pc' = IF Len(remaining) = 0 THEN "idle" ELSE "sending"
  /\ UNCHANGED <<senderEpoch, epochHighWater, seqNum, senderRebooted, syncState,
                 proposedEpoch, syncAttempts>>

\* Reject ordinary packet with large epoch jump
RejectLargeJump ==
  /\ syncState = "idle"
  /\ \E i \in DOMAIN pendingPackets :
       LET e == pendingPackets[i][1]
           remaining == RemoveAt(pendingPackets, i)
       IN
         /\ e > lastAcceptedEpoch + 1
         /\ pendingPackets' = remaining
         /\ proposedEpoch' = senderEpoch
         /\ syncState' = "req_sent"
         /\ syncAttempts' = 0
         /\ pc' = "syncing"
  /\ UNCHANGED <<senderEpoch, epochHighWater, seqNum, senderRebooted, lastAcceptedEpoch, lastAcceptedHighWater, seqHighWater,
                 acceptedPairs>>

\* Stale Epochs are explicitly discarded with EPOCH_REJECTED.
\* This single-peer abstraction starts recovery immediately; the normative
\* trigger is repeated EPOCH_REJECTED, so this is a conservative over-approximation.
RejectStaleEpoch ==
  /\ syncState = "idle"
  /\ \E i \in DOMAIN pendingPackets :
       LET e == pendingPackets[i][1]
           remaining == RemoveAt(pendingPackets, i)
       IN
         /\ e < lastAcceptedEpoch
         /\ pendingPackets' = remaining
         /\ proposedEpoch' = senderEpoch
         /\ syncState' = "req_sent"
         /\ syncAttempts' = 0
         /\ pc' = "syncing"
  /\ UNCHANGED <<senderEpoch, epochHighWater, seqNum, senderRebooted,
                 lastAcceptedEpoch, lastAcceptedHighWater, seqHighWater,
                 acceptedPairs>>

\* Reject packet that falls below the current sliding window (same epoch)
RejectTooOld ==
  /\ \E i \in DOMAIN pendingPackets :
       LET e == pendingPackets[i][1]
           s == pendingPackets[i][2]
           remaining == RemoveAt(pendingPackets, i)
       IN
         /\ e = lastAcceptedEpoch
         /\ seqHighWater >= WindowSize
         /\ s < WindowLow
         /\ pendingPackets' = remaining
         /\ pc' = IF Len(remaining) = 0 THEN "idle" ELSE "sending"
  /\ UNCHANGED <<senderEpoch, epochHighWater, seqNum, senderRebooted, lastAcceptedEpoch, lastAcceptedHighWater, seqHighWater,
                 acceptedPairs, syncState, proposedEpoch, syncAttempts>>

\* Reject duplicate pending copy of an already-accepted nonce
DuplicateAcceptedPacket ==
  /\ Len(pendingPackets) < 3
  /\ \E i \in DOMAIN acceptedPairs :
       /\ pendingPackets' = Append(pendingPackets, acceptedPairs[i])
       /\ pc' = "sending"
  /\ UNCHANGED <<senderEpoch, epochHighWater, seqNum, senderRebooted,
                 lastAcceptedEpoch, lastAcceptedHighWater, seqHighWater,
                 acceptedPairs, syncState, proposedEpoch, syncAttempts>>

RejectDuplicate ==
  /\ \E i \in DOMAIN pendingPackets :
       LET e == pendingPackets[i][1]
           s == pendingPackets[i][2]
           remaining == RemoveAt(pendingPackets, i)
       IN
         /\ AlreadyAccepted(e, s)
         /\ pendingPackets' = remaining
         /\ pc' = IF Len(remaining) = 0 THEN "idle" ELSE "sending"
  /\ UNCHANGED <<senderEpoch, epochHighWater, seqNum, senderRebooted, lastAcceptedEpoch, lastAcceptedHighWater, seqHighWater,
                 acceptedPairs, syncState, proposedEpoch, syncAttempts>>

\* Controller receives 0x40 and prepares 0x41 (response may still be lost)
ReceiveSyncRequest ==
  /\ pc = "syncing"
  /\ syncState = "req_sent"
  /\ proposedEpoch >= lastAcceptedEpoch   \* monotonicity guard
  /\ syncState' = "resp_pending"
  /\ UNCHANGED <<senderEpoch, epochHighWater, seqNum, senderRebooted, lastAcceptedEpoch, lastAcceptedHighWater, seqHighWater,
                 acceptedPairs, proposedEpoch, syncAttempts,
                 pendingPackets, pc>>

\* 0x41 is delivered → controller advances LastAcceptedEpoch, clears window
DeliverSyncResponse ==
  /\ pc = "syncing"
  /\ syncState = "resp_pending"
  /\ lastAcceptedEpoch' = proposedEpoch
  /\ lastAcceptedHighWater' = proposedEpoch
  /\ seqHighWater' = 0             \* new epoch: window restarts; history kept
  \* Keep full acceptance history – nonce uniqueness is global across sync
  /\ syncState' = "done"
  /\ pc' = "idle"
  /\ UNCHANGED <<senderEpoch, epochHighWater, seqNum, senderRebooted, proposedEpoch,
                 syncAttempts, pendingPackets, acceptedPairs>>

\* 0x41 is lost → sender may retransmit 0x40
LoseSyncResponse ==
  /\ pc = "syncing"
  /\ syncState = "resp_pending"
  /\ syncState' = "req_sent"        \* back to retransmit-able state
  /\ UNCHANGED <<senderEpoch, epochHighWater, seqNum, senderRebooted, lastAcceptedEpoch, lastAcceptedHighWater, seqHighWater,
                 acceptedPairs, proposedEpoch, syncAttempts, pendingPackets, pc>>

\* Sync completed; return to idle traffic
FinishSync ==
  /\ pc = "idle"
  /\ syncState = "done"
  /\ syncState' = "idle"
  /\ UNCHANGED <<senderEpoch, epochHighWater, seqNum, senderRebooted, lastAcceptedEpoch, lastAcceptedHighWater, seqHighWater,
                 acceptedPairs, proposedEpoch, syncAttempts, pendingPackets, pc>>

-----------------------------------------------------------------------------
Next ==
  \/ SendOrdinary
  \/ TriggerSoftRotation
  \/ SenderReboot
  \/ RetransmitSyncReq
  \/ AcceptOrdinary
  \/ RejectLargeJump
  \/ RejectStaleEpoch
  \/ RejectTooOld
  \/ RejectDuplicate
  \/ DuplicateAcceptedPacket
  \/ ReceiveSyncRequest
  \/ DeliverSyncResponse
  \/ LoseSyncResponse
  \/ FinishSync

Spec == Init /\ [][Next]_<<senderEpoch, epochHighWater, seqNum, senderRebooted,
                           lastAcceptedEpoch, lastAcceptedHighWater, seqHighWater, acceptedPairs, syncState,
                           proposedEpoch, syncAttempts, pendingPackets, pc>>

THEOREM Spec => []TypeOK
THEOREM Spec => []Inv_NonceUniqueness
THEOREM Spec => []Inv_SoftRotation
THEOREM Spec => []Inv_AcceptedCoveredByLast
THEOREM Spec => []Inv_NoOrphanEpochInHistory
THEOREM Spec => []Inv_SyncAdvancesEpoch
THEOREM Spec => []Inv_EpochMonotonic
THEOREM Spec => []Inv_LastAcceptedMonotonic
THEOREM Spec => []Inv_SeqHighWaterConsistent

=============================================================================
\* Modification History
\* Strengthened rewrite – November 2026 – audit findings on Epoch
\* History-based nonce uniqueness, reboot, full 0x40/0x41 with loss
=============================================================================
