# Epoch normative audit — interim findings

Date: 2026-11-17  
Repository branch: `audit/epoch-window-config-alignment`  
Model commit reviewed: `81ad3ee3486ec6cc15b7a3326f3c587ffb46fe98`

## Scope and source provenance

This audit compares `REFRIG_GDO_Epoch.tla` and its directed coverage module with the normative text available in the conversation uploads:

- *Protocollo Refrigerazione GDO v1.3.1*, §3.1–§3.4.
- *Protocollo Refrigerazione GDO v1.4*, §6.3 and its explicit reference to §3 of v1.3.1.
- *Protocollo Refrigerazione GDO v1.4.1*, which identifies the Epoch state machines and the complete authenticated resynchronization procedure as items still to be completed.

The full normative amendment v1.4.5 was not available among the inspected protocol PDFs. Therefore, this is an interim source-based audit, not a certification of alignment with every v1.4.5 amendment. Any v1.4.5 changes to §§3.2–3.4 must be checked before finalizing the model.

## Correct interpretation of the ordinary +1 transition

The earlier concern that `AcceptOrdinary` must always require a completed 0x40/0x41 exchange for `Epoch = LastAcceptedEpoch + 1` is not supported by the available normative source.

Section 3.2 of v1.3.1 states that a packet with `Epoch = LastAcceptedEpoch + 1` may be accepted if AEAD authentication succeeds; the receiver must then update `LastAcceptedEpoch` atomically before processing further messages of that epoch. Section 3.2 separately requires rejection of jumps greater than +1 unless authenticated resynchronization completes successfully. Version 1.4 §6.3 expressly refers back to section 3 of v1.3.1, including the 0x40/0x41 path.

Accordingly:

- Direct acceptance of the next Epoch (+1) is permitted by the inspected normative text, conditional on successful AEAD authentication and durable/atomic state update.
- A jump greater than +1 requires authenticated resynchronization.
- Recovery of persistent state also requires authenticated resynchronization under v1.3.1 §3.4.
- The model comment that AEAD is assumed perfect means authentication is abstracted, not cryptographically verified by TLC.

The current `AcceptOrdinary` rule allowing the current Epoch or current Epoch +1 is therefore directionally consistent with v1.3.1 §3.2. The model does not explicitly represent the AEAD verification state or the durable atomic commit as separate transitions; these are abstraction boundaries that must be stated.

## Traceability matrix

| Normative requirement | Source | Model element | Interim assessment |
|---|---|---|---|
| Nonce is Epoch (32-bit) concatenated with MessageCounter (64-bit) | v1.3.1 §3.1 | `senderEpoch`, `seqNum`, packet pair | Abstract representation; byte encoding not modeled |
| Receiver persists LastAcceptedEpoch | v1.3.1 §3.2–§3.3 | `lastAcceptedEpoch`, `lastAcceptedHighWater` | State represented; durable storage mechanism abstracted |
| Epoch below LastAcceptedEpoch is rejected | v1.3.1 §3.2 | No dedicated stale-Epoch reject action | **Coverage gap:** add explicit stale-Epoch rejection and directed test |
| Same Epoch follows sliding-window rules | v1.3.1 §3.2 | `WindowLow`, `seqHighWater`, `AcceptOrdinary`, `RejectTooOld` | Represented in standalone Epoch model |
| Epoch +1 may be accepted only after AEAD; LastAcceptedEpoch updated atomically before further processing | v1.3.1 §3.2 | `AcceptOrdinary` | Transition represented abstractly; AEAD and atomic persistence are assumptions, not separately modeled |
| Jump greater than +1 is rejected absent successful resynchronization | v1.3.1 §3.2, §3.4 | `RejectLargeJump`, sync actions | Partial: rejection and sync are modeled, but the causal protocol path from a detected large jump to sync is not explicitly represented |
| Epoch update before transmission after reboot; fail-closed on uncertain persistence | v1.3.1 §3.3 | `SenderReboot`, `senderEpoch`, sync state | Partial abstraction; persistence failure/rollback is not modeled |
| Persistent state recovery requires authenticated resynchronization | v1.3.1 §3.4 | `SenderReboot`, sync actions | Reboot forces sync, but there is no distinct persistent-state-recovery/failure state |
| Both peers authenticate; proposer proves key possession and authenticates proposed Epoch | v1.3.1 §3.4 | `ReceiveSyncRequest`, `DeliverSyncResponse`; AEAD assumed perfect | Authentication abstracted; not verified by TLC |
| Proposed Epoch must be strictly greater than LastAcceptedEpoch | v1.3.1 §3.4(3) | `ReceiveSyncRequest` currently uses `proposedEpoch >= lastAcceptedEpoch` | **Concrete mismatch:** guard should be strict `>` for the resynchronization path |
| LastAcceptedEpoch updated atomically/persistently only after successful authentication | v1.3.1 §3.4(4) | `DeliverSyncResponse` | Ordering represented; atomic durable commit abstracted |
| No nonce reuse under same key | v1.3.1 §3.4(5) | `acceptedPairs`, `AlreadyAccepted`, `Inv_NonceUniqueness` | Accepted-history uniqueness represented; complete sender-side nonce generation and key lifecycle are abstracted |
| Failed resynchronization leaves previous state unchanged | v1.3.1 §3.4(6) | `LoseSyncResponse` | Partial: response loss preserves receiver epoch; explicit authentication failure is not modeled |
| Soft-rotation requires synchronization before ordinary traffic | Model/report v1.4.5 claim; verify exact v1.4.5 normative clause | `TriggerSoftRotation`, `syncState`, `pc` | Model enforces sync after rotation; exact normative source clause still to be checked against full v1.4.5 text |

## Findings to address before changing the state-space abstraction

### F1 — Strict monotonicity of resynchronization proposal

In `ReceiveSyncRequest`, the current guard is:

```tla
proposedEpoch >= lastAcceptedEpoch
```

The inspected v1.3.1 §3.4(3) requires the proposed Epoch to be strictly greater. For the authenticated resynchronization action, the guard should therefore be:

```tla
proposedEpoch > lastAcceptedEpoch
```

This should be implemented only after confirming that the full v1.4.5 amendment has not deliberately changed this rule. The directed coverage test should continue to pass after the change.

### F2 — Explicit stale-Epoch rejection

The model has an explicit rejection for a too-large jump and for a too-old Sequence Number, but no dedicated action for `packetEpoch < lastAcceptedEpoch`. The normative text explicitly requires such packets to be discarded. Add a `RejectStaleEpoch` action and a directed coverage case, or document why stale packets are unreachable under the current sender/network abstraction. The former is preferable because the network may retain or reorder datagrams across Epoch changes.

### F3 — Authentication and persistence are abstracted

TLC does not verify AEAD, mutual authentication, flash atomicity, anti-rollback, or key possession. The model currently assumes successful authentication whenever the corresponding protocol action is enabled. The paper must identify these as assumptions and must not describe them as cryptographically verified properties.

### F4 — Large-jump to resynchronization path

The model can reject a large-jump packet and separately model sender-triggered synchronization. It does not explicitly connect the receiver's observation of a large jump to initiation of the 0x40/0x41 exchange. Confirm whether the normative protocol assigns initiation to the sender only, the receiver only, or either peer; then model that exact directionality.

### F5 — Sender-side monotonic persistence and failure

The model represents monotonic Epoch increments but not torn writes, flash rollback, unavailable persistent storage, or an inability to prove continuity. Those cases should either be modeled in a separate persistence/recovery abstraction or listed as implementation-level obligations outside this Epoch state-space model.

## Recommended order of work

1. Obtain/inspect the complete v1.4.5 normative amendment and confirm whether §§3.2–3.4 changed.
2. Correct the strict comparison in the resynchronization guard, if confirmed unchanged.
3. Add stale-Epoch rejection and directed coverage.
4. Add or clarify the large-jump-to-sync transition according to the normative initiator rules.
5. Rerun the small directed coverage configuration.
6. Only then evaluate a state-space reduction such as changing accepted-history representation. Preserve a non-vacuous argument for nonce uniqueness; do not remove the property merely because a set representation makes duplicates impossible by construction.

## Claims permitted at this stage

The directed coverage run previously inspected completed with 18 distinct states and no error for its then-current model. The full Epoch baseline run on the current sequence-queue revision was cancelled before completion. Therefore, no full-state-space pass is claimed for the current Epoch model. This audit document itself is not a TLC verification result.
