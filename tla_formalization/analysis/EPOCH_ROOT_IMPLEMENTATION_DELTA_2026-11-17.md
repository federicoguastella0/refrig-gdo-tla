# Epoch / Root corrective implementation delta

Date: 2026-11-17  
Normative basis: REFRIG-GDO v1.4.5 §§5.2.1–5.2.2  
Branch: `audit/epoch-window-config-alignment`

## Changes applied

### 1. Standalone Epoch model

File: `tla_formalization/REFRIG_GDO_Epoch.tla`

- Added `RejectStaleEpoch`: a queued ordinary packet with `Epoch < lastAcceptedEpoch` is removed instead of remaining indefinitely in the network queue. This models the discard outcome required by §5.2.1(1).
- The action initiates the synchronization state machine immediately after a stale packet is detected. This is a **conservative abstraction**, not a literal model of the word “repeated” in §5.2.2: the current model does not count repeated `EPOCH_REJECTED` events or parameterize their threshold. It therefore over-approximates the trigger and must not be presented as an exact encoding of that trigger condition.
- `RejectLargeJump` now initiates the synchronization state (`req_sent`) after discarding an ordinary packet with `Epoch > LastAcceptedEpoch + 1`. This represents the receiver's SHOULD-send-0x40 path and the §5.2.2 recovery trigger at an abstract level.
- `RetransmitSyncReq` now consumes a fresh Sequence Number (`seqNum' = seqNum + 1`) on each retry, and is disabled at the finite model bound `MaxSeq`. This captures the fresh-sequence requirement for retries. It does **not** yet provide a complete history of every encrypted emission, does not model directional key separation, and does not prove global AEAD nonce uniqueness.
- `acceptedPairs` is a bounded anti-duplicate cache for the currently accepted Epoch, not a permanent nonce history. It is cleared when Epoch advances; this is sufficient for the model's replay decision because packets from older Epochs are rejected as stale. It does not establish global AEAD nonce uniqueness.
- The initial 0x40 emission is still abstracted by entering `req_sent`; its concrete packet construction and nonce-history entry are not modeled. The finite `seqNum` convention for the initial 0x40 must be made explicit in a future refinement.

### 2. Root composition

File: `tla_formalization/REFRIG_GDO_Root.tla`

- Added `syncState = "idle"` as a guard to `C_Dispatch`.
- Consequently a transaction may be persisted while Epoch Sync is active, but it cannot be newly dispatched to hardware until synchronization returns to idle.
- `C_Effect` is not blocked by Epoch Sync: it represents completion of an actuation already dispatched before synchronization began. The model does not cancel an already-issued physical command. Whether the implementation must inhibit/stop an in-progress hardware signal is not specified precisely enough by the current abstraction and should be addressed separately.
- A proposed state invariant was removed because it was vacuous: it did not record the temporal relation between dispatch and sync. The operative restriction is the action guard on `C_Dispatch`, not a claimed invariant.

## Not changed

- The `proposedEpoch >= lastAcceptedEpoch` condition remains, as required by v1.4.5 §5.2.2. The previous interim finding demanding strict greater-than is withdrawn.
- AEAD verification, authenticated 0x40/0x41 fields, responder history consistency, explicit Accepted/Rejected/In Progress statuses, the initiator's adoption of Accepted Epoch, key-usage limits, rekey and protected monotonic storage remain abstracted or incomplete.
- The v1.4.5 PDF still renders the soft-rotation threshold as `2■■`; no numerical threshold was guessed or substituted.

## Verification status

At commit `0fd30c35`, the full workflow completed successfully: Epoch baseline (17,762 distinct states), Epoch extended (16,040 distinct states), directed Epoch coverage, Root baseline/mid, Core baseline/extended and Firmware baseline all passed. The Epoch and coverage modules were subsequently restored byte-for-byte from that validated commit after an unnecessary queue refactor was discarded. The final branch head still requires one confirmation run after the documentation/workflow edits.
1. run TLC on the exact final branch head and record its SHA;
2. inspect the Epoch and directed coverage logs, including state counts;
3. retain the documented limits: one sender/receiver abstraction, abstract initial 0x40, no global nonce-emission history, and no cancellation of already-issued physical commands.

The prior 45-minute runs timed out while exploring a permanent accepted-pair history. Restricting that history to the active Epoch reduced the checked state space by several orders of magnitude without reducing the packet-queue semantics.
The earlier TLC results described in the audit apply only to their original commits and are not transferable to these edits.
