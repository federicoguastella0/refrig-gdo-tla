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

These edits have been committed to the branch, but **no TLC run has yet been completed for these new revisions**. No claim of model-checking success is made here. Before relying on the changes:
1. run TLC on the standalone Epoch baseline and directed coverage configurations;
2. run TLC on the Root configuration;
3. inspect counterexamples and state counts;
4. record exact commit SHA, configuration, TLC version and final status.

The earlier TLC results described in the audit apply only to their original commits and are not transferable to these edits.
