# Allineamento normativa v1.4.5 ↔ modelli TLA+ (2026-11-17)

Fonte normativa: *Protocollo Refrigerazione GDO v1.4.5* (Normative Amendment).
Modelli: `REFRIG_GDO_{Epoch,Core,Firmware,Root}.tla` (commit verificato `8f0c8d5a8ac57e7f2f8a1bb3d8683c75093694c9`).

## Matrice di allineamento

| Requisito normativo | Sezione | Modello | Esito |
|---------------------|---------|---------|--------|
| Quattro meccanismi ordinati; no dispatch finché journal durable | 5.3.1–5.3.2 | Core: Persist → Dispatch → PhysicalEffect → Record; `Inv_PersistBeforeDispatch` | **Allineato** |
| Lock order: Recovery flag → Identity → (resource dopo durable) | 5.3.1 | Core: `CanAcquireIdentity` richiede `~recoveryLock`; resource block post-crash | **Allineato** |
| At-most-once logico / identity serialization | 5.3.1 (2), abstract | Core: identity consumata a **Persist**; Start rifiuta attivi/consumati; `Inv_NoIdentityReuse` | **Allineato** (consumo = durable IN_PROGRESS) |
| Boot: journal replay, poi IN_PROGRESS → INDETERMINATE | 5.3.2 | Core: Crash eleva solo `PERSISTED+`; `NEW` droppato (non durable) | **Allineato** (replay journal astratto) |
| SenderEpoch, soft-rotation, sync prima di nuovo Seq | 5.2.3 | Epoch: `TriggerSoftRotation` + sync obbligatorio; inflight scartato (loss) | **Allineato** |
| 0x40/0x41 accept/reject, window reset on accept | 5.2.2 | Epoch: `DeliverSyncResponse` aggiorna LastAccepted, `seqHighWater'=0`, history permanente | **Allineato** (AEAD astratta) |
| Sliding window anti-replay | 5.2 / 5.3.1 (1) | Epoch standalone: `WindowSize`, `WindowLow`, guardie di `AcceptOrdinary` / `RejectTooOld`, `Inv_SeqHighWaterConsistent` | **Modellato e verificato** nei limiti finiti delle due configurazioni Epoch |
| INDETERMINATE: solo risoluzione autorizzata; risorsa bloccata fino ad essa | 5.4.1 | Core: solo `AUTHORIZED_OPERATOR`; `blockedResources` fino a Resolve | **Allineato** |
| Condizioni HW minime per COMPLETED | 5.4.1 tabella | Astratte come `HW_READBACK_*` consultive (non auto-resolve) | **Coerente** (policy conservativa dichiarata) |
| Firmware: write→verify→durable→advance; COMPLETED solo post-manifest | 5.6.1–5.6.2 | Firmware: pipeline 4 step; install solo `manifestResult=PASS` | **Allineato** |
| Recovery Barrier: Transfer IN_PROGRESS → ABORTED | 5.6.3 | Firmware/Root Crash | **Allineato** |

## Copertura mirata anti-replay (aggiunta, verifica in attesa)

Il modello Epoch usa ora una coda di occorrenze (`Seq`) anziché un insieme: ciò
consente di rappresentare due datagrammi distinti con la stessa coppia
`(SenderEpoch, Sequence Number)`. L'azione `DuplicateAcceptedPacket` introduce una
copia già accettata nella coda e `RejectDuplicate` la rimuove senza aggiungerla
nuovamente alla cronologia.

È stato aggiunto `REFRIG_GDO_Epoch_Coverage.tla` con una sequenza diretta che forza:
1. accettazione fuori ordine (Sequence Number 2 prima del numero 1);
2. rifiuto del numero 1 dopo l'avanzamento della finestra;
3. duplicazione di un datagramma già accettato e rifiuto della copia;
4. soft-rotation mentre un pacchetto ordinario è ancora in coda;
5. perdita della risposta 0x41, ritrasmissione 0x40 e completamento della sincronizzazione.

Il modello e la configurazione TLC dedicata sono stati aggiunti al branch di audit.
Il relativo controllo TLC è **in attesa**; non attribuire ancora a questi scenari un
esito verificato. I risultati storici sopra riportati non si applicano alla nuova
rappresentazione a coda né al modulo di copertura.

## Gap residuali (dichiarati, non bloccanti per fase 2)

1. **Risoluzione operator**: la normativa ammette COMPLETED / ABORTED-FAILED / operazione compensativa; il modello usa `RESOLVED` con outcome registrato, senza ramo compensativo esplicito.
2. **Journal FIFO e magic/checksum**: astratti (commit durable atomico).
3. **AEAD / firma manifest**: assunti perfetti; nessuna proprietà crittografica verificata.
4. **Root / finestra anti-replay**: Root mantiene un modello ridotto a singolo pacchetto in-flight (`hasInflight`, `inflightEpoch`, `inflightSeq`). Non modella `pendingPackets`, consegna fuori ordine o sliding-window eviction. Di conseguenza, le verifiche Root non dimostrano il comportamento completo della finestra; la finestra è trattata solo dal modulo Epoch standalone.
5. **Deadlock-freedom generale**: non rivendicata; solo disciplina lock sotto barrier.

## Stato delle verifiche e conclusioni per il paper

Le sette configurazioni TLC (Epoch baseline/extended, Core baseline/extended,
Firmware baseline, Root baseline/mid) erano state eseguite con esito positivo sul
commit storico `8f0c8d5a8ac57e7f2f8a1bb3d8683c75093694c9`. Tali risultati non
verificano la successiva modifica della coda a sequenza né il nuovo modulo di
copertura; il controllo sul commit corrente è ancora in attesa. Per ogni configurazione TLC
ha riportato `Model checking completed. No error has been found.`; i log integrali
sono archiviati come artefatti della [run GitHub Actions 44105632243](https://github.com/federicoguastella0/refrig-gdo-tla/actions/runs/44105632243).
Ambiente: TLC 2026.11.15.002146, Eclipse Temurin Java 21.0.13, due worker TLC.
I conteggi degli stati distinti sono riportati nel README del repository.

Questi risultati coprono esclusivamente gli spazi finiti definiti dai rispettivi
file .cfg. Non dimostrano proprietà per parametri illimitati, correttezza
crittografica, correttezza dell'implementazione, liveness generale o sicurezza
funzionale dell'impianto.

Sul piano della copertura, Core e Firmware rappresentano le rispettive astrazioni
indicate; Epoch standalone modella la finestra scorrevole; Root verifica interazioni
cross-cutting con un modello Epoch deliberatamente ridotto. Non si deve quindi
presentare Root come verifica composizionale della sliding window completa.

Le corrispondenze normative sopra indicate sono una valutazione di allineamento del
modello, non una prova di correttezza dell'implementazione né una certificazione
critto-grafica o di sicurezza funzionale.
