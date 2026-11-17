# REFRIG-GDO TLA+ Formalization (v1.4.5)

Formal models of the safety-critical state machines of the **REFRIG-GDO** protocol
(normative amendment v1.4.5): Epoch / anti-replay, transactional Core with Recovery
Barrier, Firmware Transfer, and a composed Root specification.

These artefacts support **phase 2** (formalization). They are **safety models**
under finite bounds. They do **not** prove unrestricted deadlock-freedom, liveness,
or cryptographic correctness of AEAD / manifest signatures.

**Verification status (2026-11-17):** all seven TLC jobs passed on commit
`8f0c8d5a8ac57e7f2f8a1bb3d8683c75093694c9` (GitHub Actions run
[44105632243](https://github.com/federicoguastella0/refrig-gdo-tla/actions/runs/44105632243)).
TLC reported `Model checking completed. No error has been found.` for every
configuration. Full logs and the TLC tool checksum are archived as workflow
artifacts (90-day retention).

| Item | Value |
|------|--------|
| Protocol revision | v1.4.5 (wire-compatible with v1.4.2–v1.4.4) |
| Tool | TLC (`tla2tools.jar`) |
| Focus | Safety invariants; crash windows; history-based properties |
| Repo | https://github.com/federicoguastella0/refrig-gdo-tla |

---

## Layout

```
tla_formalization/
├── REFRIG_GDO_Epoch.tla / Core.tla / Firmware.tla / Root.tla
├── REFRIG_GDO_Epoch_Coverage.tla # directed anti-replay / sync scenario
├── REFRIG_GDO_Core_NoCrash.tla    # analysis: functional terminals
├── *.cfg
├── configs/                       # extra bound sets
├── analysis/
└── README.md
```

---

## How to run TLC

```bash
java -XX:+UseParallelGC -jar tla2tools.jar -workers auto -config Epoch.cfg    REFRIG_GDO_Epoch.tla
java -XX:+UseParallelGC -jar tla2tools.jar -workers auto -config Core.cfg     REFRIG_GDO_Core.tla
java -XX:+UseParallelGC -jar tla2tools.jar -workers auto -config Firmware.cfg REFRIG_GDO_Firmware.tla
java -XX:+UseParallelGC -jar tla2tools.jar -workers auto -config Root.cfg     REFRIG_GDO_Root.tla
```

Success ends with: `Model checking completed. No error has been found.`

---

## TLC results (audit branch, 2026-11-17)

The seven successful results below belong to commit `8f0c8d5...` and the earlier
set-valued pending-packet abstraction. They do **not** validate the later sequence-
queue revision or the directed coverage module. The current audit commit must pass
its own TLC run before new results are recorded.

All seven configurations completed successfully on the historical commit shown above.
The counts below are the **distinct states** reported by TLC; the complete logs
are available in the linked GitHub Actions run artifacts.

| Spec | Configuration | Distinct states | Outcome |
|------|---------------|----------------:|---------|
| Epoch | `Epoch.cfg` (MaxEpoch=3, MaxSeq=4, SRT=4, WindowSize=2) | **5,544,330** | PASSED |
| Epoch | `configs/Epoch_ext.cfg` (MaxEpoch=3, MaxSeq=4, SRT=4, WindowSize=3) | **21,317,026** | PASSED |
| Core | `Core.cfg` | **50,080** | PASSED |
| Core | `configs/Core_ext.cfg` | **287,936** | PASSED |
| Firmware | `Firmware.cfg` | **1,198** | PASSED |
| Root | `Root.cfg` | **17,744** | PASSED |
| Root | `configs/Root_mid.cfg` | **618,734** | PASSED |

TLC generated 8,830,183 states for Epoch baseline and 34,481,327 for Epoch
extended. The searches completed with zero states remaining in the queue.
Environment: TLC 2026.11.15.002146, Eclipse Temurin Java 21.0.13, two TLC workers.
The GitHub Actions workflow records the exact commit SHA, Java/TLC versions,
tool SHA-256, and per-configuration output.

These are finite-state model-checking results for the bounds in the listed
configuration files. They are not proofs for unbounded parameters, cryptographic
correctness, implementation correctness, general liveness, or functional safety.

Normative alignment report: `analysis/NORMATIVE_ALIGNMENT_v1.4.5.md`.

---

## Invariants (what is actually claimed)

### Core
- History-based no double actuation; persist-before-dispatch; effect-after-dispatch
- Permanent identity: consumed at **Persist** (durable), not at Start
- Crash: non-durable `NEW` is dropped; only `PERSISTED+` → `INDETERMINATE` + resource block
- Resolve: **only `AUTHORIZED_OPERATOR`** may close INDETERMINATE (HW evidence is advisory)

### Epoch
- Permanent `acceptedPairs` history (not cleared on sync)
- Network receive queue is a sequence, so distinct datagram occurrences can carry the same `(Epoch, Sequence Number)` and exercise duplicate rejection
- Directed coverage scenario added in `REFRIG_GDO_Epoch_Coverage.tla`; TLC result pending for the latest audit commit
- Epoch / LastAccepted high-water monotonicity
- Sliding-window acceptance guard (`WindowSize`, `WindowLow`, `seqHighWater`); permanent accepted history is used for nonce uniqueness, not constrained to remain inside the moving window.
- `Inv_SeqHighWaterConsistent` checks that the high-water value matches the maximum accepted sequence in the current epoch.
- Soft-rotation discards in-flight ordinary packet (**loss**, not completion)

### Firmware
- Non-atomic chunk pipeline; install only after durable image + **manifest PASS**
- Manifest **FAIL** → `ABORTED`, never install

### Root
- Composition under shared Recovery Barrier; cross-cutting safety invariants.
- **Abstraction boundary:** Root retains a single in-flight ordinary-packet abstraction and does not model the Epoch module's pending-packet set, out-of-order delivery, or sliding-window eviction. Root results therefore do not verify the complete sliding-window behavior; that behavior is checked only by the standalone Epoch model.

### Explicitly **not** claimed
- General deadlock-freedom or liveness
- Cryptographic verification of AEAD / signatures (abstracted)
- Full multi-sender Epoch composition

---

## Audit notes (A–E)

| ID | Topic | Resolution |
|----|--------|------------|
| **A** | INDETERMINATE resolve | Conservative policy: only `AUTHORIZED_OPERATOR`. HW_READBACK_* collectable, not auto-resolving. Documented in Core comments + this README. |
| **B** | Deadlock | `Inv_NoDeadlockUnderRecovery` = lock discipline under barrier only. No general deadlock-freedom claim. |
| **C** | Anti-replay window | Standalone Epoch uses `WindowSize`, `WindowLow`, pending packet set and acceptance guards; Root is explicitly a reduced abstraction. Soft-rotation treats inflight as **lost**. |
| **D** | README vs code | TLC results and exact commit provenance recorded for the seven successful audit-branch configurations. |
| **E** | Identity vs Persist | Identity enters `consumedIdentities` at **Persist**; Start only rejects active/consumed duplicates; crash of `NEW` frees the slot without consuming. |

---

## Mapping to normative text (v1.4.5)

| Area | Model |
|------|--------|
| SenderEpoch, soft-rotation, 0x40/0x41 | `REFRIG_GDO_Epoch.tla` |
| Mechanisms, lock order, persist-before-actuate | `REFRIG_GDO_Core.tla` |
| INDETERMINATE resolution | `CollectEvidence` / `ResolveIndeterminate` |
| Firmware Transfer | `REFRIG_GDO_Firmware.tla` |
| Shared Recovery Barrier | `REFRIG_GDO_Root.tla` |

Full matrix: `analysis/NORMATIVE_ALIGNMENT_v1.4.5.md`.

---

## Citation

> REFRIG-GDO TLA+ models (v1.4.5). Safety invariants checked with TLC under the
> finite bounds in the respective `.cfg` files (results table in README).

The seven listed finite TLC configurations passed on the recorded commit. Do not interpret this as an unbounded proof or as implementation / cryptographic validation.
