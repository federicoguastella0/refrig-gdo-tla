# REFRIG-GDO TLA+ Formalization (v1.4.5)

Formal models of the safety-critical state machines of the **REFRIG-GDO** protocol
(normative amendment v1.4.5): Epoch / anti-replay, transactional Core with Recovery
Barrier, Firmware Transfer, and a composed Root specification.

These artefacts support **phase 2** (formalization). They are **safety models**
under finite bounds. They do **not** prove unrestricted deadlock-freedom, liveness,
or cryptographic correctness of AEAD / manifest signatures.

**Verification status:** the TLC state counts below are historical results reported
for the pre-audit tree. The Epoch configurations and this documentation are being
re-aligned on the audit branch; until TLC is rerun against the exact branch commit,
those counts must not be cited as results for this revision.

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

## Historical TLC results (pre-audit tree, 2026-11-17)

The following counts were recorded in the previous repository state. They are
retained as provenance only; they have **not** been reproduced against this audit
branch and are not evidence that the revised configurations pass.

| Spec | Config bounds (summary) | Distinct states | Outcome |
|------|-------------------------|-----------------|--------|
| **Epoch** | MaxEpoch=3, MaxSeq=4, SRT=2, WindowSize=3 | **62** | PASSED |
| **Core** | Clients={c1}, Resources={res1,res2}, MaxTx=2 | **50 080** | PASSED |
| **Firmware** | Clients={c1}, MaxChunks=2, MaxTransfers=2 | **1 198** | PASSED |
| **Root** | 1 client, 1 resource, MaxTx=1, MaxEpoch=1, … | **17 744** | PASSED |

These numbers describe the earlier tree only. Re-run TLC and archive its complete
output, tool version, Java version, configuration, and exact commit SHA before
reporting them as reproducible results.

### Historical extended bounds (pre-audit tree, 2026-11-17)

| Spec | Config | Distinct states | Outcome |
|------|--------|-----------------|--------|
| Epoch | `configs/Epoch_ext.cfg` (MaxEpoch=4, MaxSeq=6, W=4) | **82** | PASSED |
| Core | `configs/Core_ext.cfg` (2 clients, MaxTx=2) | **287 936** | PASSED |
| Root | `configs/Root_mid.cfg` (MaxEpoch=2, MaxSeq=3, MaxChunks=2) | **618 734** | PASSED |

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
| **D** | README vs code | Historical state counts retained as provenance only; rerun required for this audit branch. |
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

Do not tag this branch as verified until all TLC configurations have been rerun and the logs archived.
