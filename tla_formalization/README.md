# REFRIG-GDO TLA+ Formalization (v1.4.5)

Formal models of the safety-critical state machines of the **REFRIG-GDO** protocol
(normative amendment v1.4.5): Epoch / anti-replay, transactional Core with Recovery
Barrier, Firmware Transfer, and a composed Root specification.

These artefacts support the research claim set for **phase 2** (formalization).
They are **safety models** under finite bounds. They do **not** by themselves prove
unrestricted absence of deadlock, liveness, or cryptographic properties of AEAD.

| Item | Value |
|------|--------|
| Protocol revision | v1.4.5 (wire-compatible with v1.4.2–v1.4.4) |
| Tool | TLC (TLA+ tools / `tla2tools.jar`) |
| Focus | Safety invariants; explicit crash windows; history-based properties |
| License suggestion | MIT or CC-BY-4.0 on the models (choose when publishing) |

---

## Layout

```
tla_formalization/          (or repo root after copy)
├── REFRIG_GDO_Epoch.tla      Epoch, anti-replay, soft-rotation, 0x40/0x41
├── REFRIG_GDO_Core.tla       Transactions, Recovery Barrier, physical window
├── REFRIG_GDO_Firmware.tla   Firmware transfer, non-atomic chunk pipeline
├── REFRIG_GDO_Root.tla       Composition under shared Recovery Barrier
├── REFRIG_GDO_Core_NoCrash.tla   Analysis-only: Core without Crash action
├── Epoch.cfg  Core.cfg  Firmware.cfg  Root.cfg  Core_NoCrash.cfg
├── configs/                  Extra bound sets (Root_mid, Root_ext, copies)
├── analysis/                 Notes on analysis aids
└── README.md                 This file
```

---

## Prerequisites

- Java 11+ (17/21 recommended)
- [`tla2tools.jar`](https://github.com/tlaplus/tlaplus/releases) (TLC)

```bash
# example
curl -sL -o tla2tools.jar \
  https://github.com/tlaplus/tlaplus/releases/download/v1.8.0/tla2tools.jar
```

---

## How to run TLC

Run **from this directory** (so module names resolve):

```bash
java -XX:+UseParallelGC -jar tla2tools.jar -workers auto -config Epoch.cfg    REFRIG_GDO_Epoch.tla
java -XX:+UseParallelGC -jar tla2tools.jar -workers auto -config Core.cfg     REFRIG_GDO_Core.tla
java -XX:+UseParallelGC -jar tla2tools.jar -workers auto -config Firmware.cfg REFRIG_GDO_Firmware.tla
java -XX:+UseParallelGC -jar tla2tools.jar -workers auto -config Root.cfg     REFRIG_GDO_Root.tla

# Analysis: functional terminals (Crash disabled)
java -XX:+UseParallelGC -jar tla2tools.jar -workers auto -config Core_NoCrash.cfg REFRIG_GDO_Core_NoCrash.tla
```

Expected successful safety runs end with:

```text
Model checking completed. No error has been found.
```

`Core_NoCrash` with `CHECK_DEADLOCK TRUE` is **expected** to report a deadlock:
that state is the functional terminal (all slots `COMPLETED`, locks free), not a
lock-order bug. See “Deadlock analysis” below.

---

## Models and invariants

### Epoch (`REFRIG_GDO_Epoch.tla`)

| Invariant | Meaning |
|-----------|---------|
| `Inv_NonceUniqueness` | No repeated `<<Epoch, Seq>>` in the **history** `acceptedPairs` |
| `Inv_SoftRotation` | `seqNum` does not exceed soft-rotation threshold without epoch bump |
| `Inv_NoLargeJumpOrdinary` | Ordinary accept only for last or last+1 epoch |
| `Inv_SyncAdvancesEpoch` | Successful sync sets `lastAcceptedEpoch = proposedEpoch` |

Also models: sender reboot, `0x40` request / `0x41` response, loss and retransmit.

### Core (`REFRIG_GDO_Core.tla`)

| Invariant | Meaning |
|-----------|---------|
| `Inv_NoDoubleActuation` | At most one entry per `tid` in **actuationLog** (history) |
| `Inv_PersistBeforeDispatch` | Dispatch implies prior durable commit |
| `Inv_EffectAfterDispatch` | Physical effect only after dispatch |
| `Inv_NoActuationDuringRecovery` | No dispatch/effect phases under Recovery Barrier |
| `Inv_NoDeadlockUnderRecovery` | Under recovery: `recoveryLock` held, `identityLocks = {}` |
| `Inv_AuthorizedResolution` | `RESOLVED` only if resolution evidence was collected |
| `Inv_UniqueIdentity` | At most one non-terminal tx per `(client, appTxId)` |
| `Inv_CompletedImpliesEffectOrResolved` | `COMPLETED` implies effect history or authorised path |

Critical window (crash allowed between steps):  
`Persist → Dispatch → PhysicalEffect → RecordCompletion`.

### Firmware (`REFRIG_GDO_Firmware.tla`)

| Invariant | Meaning |
|-----------|---------|
| `Inv_AtMostOneInProgress` | ≤1 `IN_PROGRESS` transfer per client |
| `Inv_PersistBeforeOffsetAdvance` | Idle pipeline ⇒ no pending durable work |
| `Inv_NoDoubleInstall` | ≤1 install event per tid in **installLog** |
| `Inv_NoInstallBeforeManifest` | Install only if image durable, manifest checked, `COMPLETED` |
| `Inv_RecoveryAbortsInProgress` | Recovery ⇒ no `IN_PROGRESS` left |
| `Inv_ChunkOrderMonotonic` | Durable offsets respect expected order |
| `Inv_NoPartialAfterCrash` | Recovery ⇒ chunk pipeline idle (partial discarded) |

Chunk pipeline: `Write → Verify → Durabilize → AdvanceOffset`.

### Root (`REFRIG_GDO_Root.tla`)

Composes Epoch + Core + Firmware with a **shared** `recoveryFlag` / `recoveryLock`.
Cross-cutting invariants include nonce uniqueness, no double actuation, persist-before-dispatch,
no actuation during recovery, authorised resolution, no double install, shared recovery.

---

## Reference TLC results (indicative)

Recorded on TLC 2026.x, small heap; use as regression baseline, not as a limit theorem.

| Spec | Config (main) | Distinct states (approx.) | Notes |
|------|----------------|---------------------------|--------|
| Epoch | `Epoch.cfg` | ~221 | Safety OK; deadlock if `CHECK_DEADLOCK` at MaxEpoch |
| Core | `Core.cfg` | ~5.6k (small) / ~27k (2 clients) | Safety OK |
| Firmware | `Firmware.cfg` | ~1k–4.5k | Safety OK |
| Root | `Root.cfg` | ~5.9k | Minimal bounds; safety OK |
| Core_NoCrash | `Core_NoCrash.cfg` | — | **Deadlock = functional terminal** |

Larger Root configs (`configs/Root_mid.cfg`, `configs/Root_ext.cfg`) grow past 10⁵–10⁶ states quickly; use for exploration, not as the default CI target.

---

## Deadlock analysis (read before citing)

1. **Bound exhaustion (Epoch)**  
   When `senderEpoch = MaxEpoch` and `seqNum ≥ SoftRotationThreshold`, no further
   epoch bump or send is possible. This is a **finite-model terminal**, not a
   protocol lock-order deadlock. Real SenderEpoch is 32-bit.

2. **Always-enabled Crash (Core / Firmware / Root)**  
   With Crash in `Next`, TLC rarely reports deadlock because a crash transition
   remains enabled. That **masks** “work finished” terminals; it does **not**
   prove absence of concurrency deadlocks in general.

3. **Functional terminal (Core_NoCrash)**  
   With Crash removed, TLC reports deadlock when every slot is `COMPLETED` and
   locks are free. That is the intended “no more work under this bound” state.

4. **`Inv_NoDeadlockUnderRecovery`**  
   Only asserts lock release under the Recovery Barrier. It does **not** prove
   global deadlock-freedom or liveness.

**Do not claim in a paper:** “TLA+ proves the protocol is deadlock-free.”  
**Acceptable claim:** “Under the stated bounds, TLC found no violation of the listed
safety invariants; Recovery Barrier releases Identity locks; functional terminals
with Crash disabled show completed transactions with locks free.”

---

## Modelling decisions

- AEAD is assumed perfect (no forgery modelled).
- Flash layout, CRC polynomials, and exact journal formats are abstracted.
- Soft-rotation threshold and image sizes are reduced for model checking.
- Only **safety** is checked; liveness needs fairness hypotheses and separate properties.
- Single sender in Epoch; multi-sender composition is left to a future refinement of Root.

---

## Mapping to normative text (v1.4.5)

| Normative area | Model |
|----------------|--------|
| §5.2 SenderEpoch, soft-rotation, 0x40/0x41 | `REFRIG_GDO_Epoch.tla` |
| §5.3 mechanisms, lock order, persist-before-actuate | `REFRIG_GDO_Core.tla` |
| §5.4.1 INDETERMINATE resolution | `CollectEvidence` / `ResolveIndeterminate` |
| §5.6 Firmware Transfer | `REFRIG_GDO_Firmware.tla` |
| Cross-machine Recovery Barrier | `REFRIG_GDO_Root.tla` |

---

## Citation (example)

> REFRIG-GDO TLA+ models (v1.4.5), available in this repository. Safety invariants
> checked with TLC under the finite bounds documented in the respective `.cfg` files.

Align the git tag with the protocol revision when you publish, e.g. `formalization-v1.4.5`.

---

## Status

| Phase item | Status |
|------------|--------|
| History-based invariants (non-tautological) | Done |
| Explicit crash windows | Done |
| Distinct lock classes + recovery ordering | Done (bounds still modest) |
| Epoch + Firmware completion | Done |
| Root composition | Done |
| Unrestricted deadlock-freedom / liveness | **Not claimed** |

