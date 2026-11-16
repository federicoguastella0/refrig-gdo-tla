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

## Audit reinforcement status (2026-11-16)

| Item | Status |
|------|--------|
| Permanent identity (`consumedIdentities`) | Done – Core + Root |
| INDETERMINATE + physical resource block + typed evidence | Done – Core + Root |
| Epoch high-water monotonicity + permanent `acceptedPairs` | Done – Epoch + Root |
| Firmware manifest with real pass/fail outcome | Open (point 4) |

Reference TLC (indicative bounds): Core ~65k states; Epoch ~1.7k; Root ~20k (point 2–3 aligned).

**Note:** If module `.tla` files on `main` lag behind the `.cfg` invariants, sync from the local workspace or apply the audit commit before relying on TLC results.

---

## Modelling decisions

- AEAD is assumed perfect (no forgery modelled).
- Flash layout, CRC polynomials, and exact journal formats are abstracted.
- Soft-rotation threshold and image sizes are reduced for model checking.
- Only **safety** is checked; liveness needs fairness hypotheses and separate properties.
- Single sender in Epoch; multi-sender composition is left to a future refinement of Root.

---

## Citation (example)

> REFRIG-GDO TLA+ models (v1.4.5), available in this repository. Safety invariants
> checked with TLC under the finite bounds documented in the respective `.cfg` files.

Align the git tag with the protocol revision when you publish, e.g. `formalization-v1.4.5`.
