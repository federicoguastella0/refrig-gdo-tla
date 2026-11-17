# Allineamento normativa v1.4.5 ↔ modelli TLA+ (2026-11-17)

Fonte normativa: *Protocollo Refrigerazione GDO v1.4.5* (Normative Amendment).
Modelli: `REFRIG_GDO_{Epoch,Core,Firmware,Root}.tla` (tree locale post-consolidamento A–E).

## Matrice di allineamento

| Requisito normativo | Sezione | Modello | Esito |
|---------------------|---------|---------|--------|
| Quattro meccanismi ordinati; no dispatch finché journal durable | 5.3.1–5.3.2 | Core: Persist → Dispatch → PhysicalEffect → Record; `Inv_PersistBeforeDispatch` | **Allineato** |
| Lock order: Recovery flag → Identity → (resource dopo durable) | 5.3.1 | Core: `CanAcquireIdentity` richiede `~recoveryLock`; resource block post-crash | **Allineato** |
| At-most-once logico / identity serialization | 5.3.1 (2), abstract | Core: identity consumata a **Persist**; Start rifiuta attivi/consumati; `Inv_NoIdentityReuse` | **Allineato** (consumo = durable IN_PROGRESS) |
| Boot: journal replay, poi IN_PROGRESS → INDETERMINATE | 5.3.2 | Core: Crash eleva solo `PERSISTED+`; `NEW` droppato (non durable) | **Allineato** (replay journal astratto) |
| SenderEpoch, soft-rotation, sync prima di nuovo Seq | 5.2.3 | Epoch: `TriggerSoftRotation` + sync obbligatorio; inflight scartato (loss) | **Allineato** |
| 0x40/0x41 accept/reject, window reset on accept | 5.2.2 | Epoch: `DeliverSyncResponse` aggiorna LastAccepted, `seqHighWater'=0`, history permanente | **Allineato** (AEAD astratta) |
| Sliding window anti-replay | 5.2 / 5.3.1 (1) | Epoch: `WindowSize`, `seqHighWater`, `Inv_WithinWindow` | **Allineato** (ampiezza parametrica) |
| INDETERMINATE: solo risoluzione autorizzata; risorsa bloccata fino ad essa | 5.4.1 | Core: solo `AUTHORIZED_OPERATOR`; `blockedResources` fino a Resolve | **Allineato** |
| Condizioni HW minime per COMPLETED | 5.4.1 tabella | Astratte come `HW_READBACK_*` consultive (non auto-resolve) | **Coerente** (policy conservativa dichiarata) |
| Firmware: write→verify→durable→advance; COMPLETED solo post-manifest | 5.6.1–5.6.2 | Firmware: pipeline 4 step; install solo `manifestResult=PASS` | **Allineato** |
| Recovery Barrier: Transfer IN_PROGRESS → ABORTED | 5.6.3 | Firmware/Root Crash | **Allineato** |

## Gap residuali (dichiarati, non bloccanti per fase 2)

1. **Risoluzione operator**: la normativa ammette COMPLETED / ABORTED-FAILED / operazione compensativa; il modello usa `RESOLVED` con outcome registrato, senza ramo compensativo esplicito.
2. **Journal FIFO e magic/checksum**: astratti (commit durable atomico).
3. **AEAD / firma manifest**: assunti perfetti; nessuna proprietà crittografica verificata.
4. **Root**: sottoinsieme Epoch senza `WindowSize` dedicato (finestra completa nel modulo Epoch standalone).
5. **Deadlock-freedom generale**: non rivendicata; solo disciplina lock sotto barrier.

## Conclusioni per il paper

Le proprietà di sicurezza modellate e verificate con TLC (persist-before-actuate, identity@durable, anti-replay history+window, resolve autorizzato, manifest PASS/FAIL) corrispondono ai requisiti vincolanti di v1.4.5 nelle sezioni citate. I gap sono astrazioni dichiarate, non contraddizioni normative.
