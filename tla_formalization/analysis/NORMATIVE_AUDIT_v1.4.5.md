# Audit normativo completo v1.4.5 ↔ modelli TLA+

Data: 2026-11-17  
Branch esaminato: `audit/epoch-window-config-alignment`  
Fonte normativa: *REFRIG-GDO Protocol – Normative Specification Amendment v1.4.5*, 3 pagine  
Moduli esaminati: `REFRIG_GDO_Epoch.tla`, `REFRIG_GDO_Epoch_Coverage.tla`, `REFRIG_GDO_Core.tla`, `REFRIG_GDO_Firmware.tla`, `REFRIG_GDO_Root.tla`, configurazioni TLC e documentazione di audit.

## 1. Esito esecutivo

La formalizzazione è una base utile e contiene astrazioni coerenti con diversi requisiti della v1.4.5, ma **non è ancora integralmente allineata alla specifica normativa**. In particolare:

1. Il precedente rilievo secondo cui `ReceiveSyncRequest` dovrebbe usare `>` anziché `>=` è **ritirato**: la v1.4.5 §5.2.2 ammette espressamente Proposed Epoch maggiore o uguale all'Epoch locale. La guardia `>=` nel modello standalone è coerente con questa disposizione.
2. Il modello Epoch non formalizza il rifiuto esplicito di Epoch obsoleti, la generazione di `EPOCH_REJECTED`, né il collegamento tra rilevamento di un salto e avvio della sincronizzazione.
3. Il modello Root non sospende le azioni di dispatch/attuazione durante la sincronizzazione Epoch, benché §5.2.2 richieda la sospensione dei comandi attuativi quando viene rilevato un salto > +1 o arrivano ripetuti `EPOCH_REJECTED`.
4. Il modello non dimostra l'unicità del nonce per **tutte** le cifrature e trasmissioni: la proprietà corrente controlla la cronologia dei pacchetti accettati, non i pacchetti persi, i messaggi di sincronizzazione o ogni emissione del mittente.
5. Le regole v1.4.5 di trasferimento firmware sono rappresentate solo in parte: la pipeline write/verify/durable/advance è modellata, ma mancano identità/contenuto dei chunk, gestione del chunk duplicato, conflitto di contenuto allo stesso offset e anti-rollback firmware.
6. La soglia di soft-rotation nella copia PDF fornita è illeggibile: compare come `2■■`. Non è possibile verificare il valore numerico né dedurlo dal modello.

Quindi il giudizio corretto è: **formalizzazione parzialmente allineata, con gap normativi da chiudere prima di dichiarare copertura completa della v1.4.5**. Non è una certificazione del protocollo o dell'implementazione.

## 2. Correzione di un rilievo precedente

L'audit provvisorio aveva riportato come mismatch la guardia:

```tla
proposedEpoch >= lastAcceptedEpoch
```

Il rilievo era basato sulla regola più restrittiva della precedente fonte v1.3.1 §3.4(3). La nuova v1.4.5 §5.2.2, però, riscrive il comportamento del responder: Proposed Epoch è accettabile se è **maggiore o uguale** all'Epoch locale; Accepted Epoch è `max(local, Proposed)`.

Pertanto:
- `>=` è corretto rispetto alla v1.4.5;
- non va cambiato in `>` sulla base della vecchia regola;
- il vecchio finding F1 dell'audit interim è superato e ritirato.

Il modello attuale, tuttavia, semplifica il responder: `ReceiveSyncRequest` controlla la relazione numerica ma non rappresenta esplicitamente la verifica di coerenza con la history, il tag AEAD, i campi di `0x41` o gli status Accepted/Rejected/In Progress.

## 3. Matrice di tracciabilità

Legenda:
- **Rappresentato**: la transizione o proprietà è presente nell'astrazione.
- **Parziale**: esiste una rappresentazione semplificata, ma una o più condizioni normative non sono modellate.
- **Non modellato**: il requisito non compare come transizione/proprietà verificabile.
- **Assunzione**: il modello assume che la condizione sia vera; TLC non la verifica.

| Requisito v1.4.5 | Fonte | Modello / elemento | Esito e limite |
|---|---|---|---|
| SenderEpoch persistente, incrementato dopo reboot e prima di trasmettere | §5.2 | Epoch: `SenderReboot`, `senderEpoch`, `epochHighWater` | **Parziale**: incremento monotono rappresentato; commit NVM, failure e rollback non modellati |
| Sequence Number strettamente crescente per Epoch e direzione, senza wrap | §5.2 | Epoch: `SendOrdinary`, `seqNum` | **Parziale**: contatore monotono nel singolo mittente astratto; direzioni distinte e tutte le emissioni non modellate |
| Epoch < LastAcceptedEpoch scartato con EPOCH_REJECTED | §5.2.1(1) | Epoch: `RejectStaleEpoch` | **Parziale**: il pacchetto stale viene rimosso e la sync è avviata immediatamente; non viene emesso uno status EPOCH_REJECTED distinto e non è modellato il trigger normativo dei rifiuti ripetuti |
| Epoch uguale: sliding-window ordinaria | §5.2.1(2) | Epoch: `WindowLow`, `seqHighWater`, `AcceptOrdinary`, `RejectTooOld` | **Rappresentato** nel modulo Epoch standalone, entro i bound TLC |
| Epoch +1: accettazione solo con AEAD valido e aggiornamento atomico di LastAcceptedEpoch/finestra | §5.2.1(3) | Epoch: ramo +1 di `AcceptOrdinary` | **Parziale**: transizione atomica astratta; AEAD e persistenza atomica sono assunzioni |
| Epoch > LastAcceptedEpoch+1: datagrammi ordinari non accettati; receiver SHOULD inviare 0x40 | §5.2.1(4) | Epoch: `RejectLargeJump` | **Parziale**: il datagramma viene rimosso, ma non viene collegato al trigger di 0x40 |
| 0x40 con Epoch > LastAcceptedEpoch+1 segue il percorso privilegiato e non la regola ordinaria | §5.2.2 | Epoch: `ReceiveSyncRequest` astratta, senza packet queue dedicata | **Parziale**: handshake separato dalla coda ordinaria; non è modellata la distinzione di autenticazione/dispatch del messaggio 0x40 |
| Ogni peer che rileva salto > +1 o ripetuti EPOCH_REJECTED sospende attuazioni e avvia/risponde alla sync | §5.2.2 | Epoch e Root | **Parziale**: Epoch avvia la richiesta dopo un salto > +1 e, in modo conservativo, dopo un singolo stale; Root impedisce nuovi `C_Dispatch` durante sync, ma non annulla un'azione fisica già dispatchata |
| Initiator invia Proposed Epoch e Last Known Peer Epoch | §5.2.2, Initiator(1) | Epoch: `proposedEpoch` | **Parziale**: Last Known Peer Epoch non rappresentato |
| Timeout 0x41: ritrasmettere 0x40 con Sequence Number fresco | §5.2.2, Initiator(2) | Epoch: `LoseSyncResponse`, `RetransmitSyncReq` | **Parziale**: ogni retry incrementa `seqNum` e `syncAttempts`; l'emissione iniziale di 0x40 e la history di tutte le cifrature/trasmissioni non sono rappresentate |
| Accepted: initiator adotta Accepted Epoch, resetta finestra e riprende traffico | §5.2.2, Initiator(3) | Epoch: `DeliverSyncResponse`, `FinishSync` | **Parziale**: aggiornamento lato ricevente rappresentato; adozione separata lato initiator non rappresentata |
| Responder accetta Proposed >= local se coerente con history; Accepted=max(local, Proposed) | §5.2.2, Responder(1–2) | Epoch: guardia `proposedEpoch >= lastAcceptedEpoch` | **Parziale ma guardia coerente**: la coerenza con history è ridotta alla monotonicità; max non è esplicitato, anche se con la guardia attuale equivale a Proposed |
| 0x41 porta Status, Accepted Epoch e Current Local Epoch | §5.2.2, Responder(3) | Epoch: `syncState` | **Non modellato**: payload/status non rappresentati |
| Responder aggiorna atomicamente LastAcceptedEpoch e resetta finestra | §5.2.2, Responder(4) | Epoch: `DeliverSyncResponse`, `seqHighWater'=0` | **Parziale**: ordine astratto; persistenza atomica non modellata |
| Dopo sync, entrambi usano nuovo Epoch come base per +1 | §5.2.2, ultimo capoverso | Epoch: `lastAcceptedEpoch`, `senderEpoch` | **Parziale**: un solo mittente e un solo ricevente astratto; non sono rappresentati due stati peer completi |
| Soft-rotation alla soglia; incrementare e rendere durevole SenderEpoch, completare sync prima di nuovo Seq, ripartire da 0 | §5.2.3 | Epoch: `TriggerSoftRotation` | **Parziale**: ordine logico rappresentato; durability e valore numerico della soglia non verificabili dalla copia PDF |
| Receiver che vede Seq >= soglia emette SEQ_ROTATION_REQUIRED o 0x40 proattivo | §5.2.3 | Epoch | **Non modellato**: nessun evento/azione per 0x000F o sync proattiva lato receiver |
| Limite d'uso per chiave direzionale e rekey prima del limite | §5.2.4 | Epoch | **Non modellato** |
| Divieto wrap 32-bit SenderEpoch; re-provisioning/cambio contesto prima dell'esaurimento | §5.2.4 | Epoch: bound `MaxEpoch` | **Parziale**: il bound finito blocca ulteriori incrementi; nessuna azione di rekey/re-provisioning |
| Rollback SenderEpoch è violazione; senza storage monotono protetto rifiutare comunicazioni | §5.2.4 | Epoch: `epochHighWater` | **Non modellato come failure**: high-water è aggiornato insieme a SenderEpoch e non può divergere nel modello |
| Quattro meccanismi: anti-replay, serialization, persistent commit, actuation | §5.3.1 | Epoch + Core + Firmware | **Parziale**: separazione concettuale presente tra moduli; lock e journal sono astrazioni e non tutti gli stadi sono espliciti |
| Nessun dispatch prima della durabilità IN_PROGRESS | §5.3.1(3–4), §5.3.2 | Core: `Persist`, `Dispatch`, `Inv_PersistBeforeDispatch` | **Rappresentato** come ordine astratto; il commit durable è un singolo passo atomico |
| Lock order Recovery Barrier → Identity → journal → resource dopo commit | §5.3.1 | Core: `CanAcquireIdentity`, `identityLocks`, `recoveryLock` | **Parziale**: test barriera e acquisizione Identity sono atomici nel modello; journal lock e physical-resource lock separati non sono modellati |
| Race-free admission su Recovery Barrier | §5.3.1 | Core: guardie `~recoveryFlag`/ `~recoveryLock` e acquisizione Identity nella stessa azione | **Rappresentato come atomicità di transizione TLA**, non come implementazione concreta di mutex/test-and-set |
| Persistenza di REJECTED prima dell'ACK | §5.3.2 | Core: stato enum REJECTED ma nessuna azione lo assegna | **Non modellato** |
| Journal FIFO, sequence number monotono locale, marker/checksum, batch flush e timeout | §5.3.2 | Core | **Non modellato**; il journal è astratto come commit durevole atomico |
| Boot: replay FIFO, poi IN_PROGRESS residui → INDETERMINATE | §5.3.2 | Core: `Crash` | **Parziale**: NEW non durable è eliminato e PERSISTED+ diventa INDETERMINATE; replay FIFO non è una fase esplicita |
| Risoluzione INDETERMINATE solo da entità autorizzata | §5.4.1(1) | Core: `ResolveIndeterminate`, `Inv_AuthorizedResolution` | **Rappresentato** con policy più restrittiva AUTHORIZED_OPERATOR |
| Esiti COMPLETED, ABORTED/FAILED o operazione compensativa con nuovo TransactionID | §5.4.1(2) | Core: `ResolveOutcome` | **Parziale**: esiti astratti RESOLVED; compensatory operation non modellata; Error Code e nuovo TransactionID non rappresentati |
| Tracciabilità storica con timestamp, authorizer identity e reason | §5.4.1(3) | Core: `resolveOutcome`, `evidenceKind` | **Non modellato integralmente**: non sono memorizzati timestamp, identità concreta dell'autorizzatore e motivazione |
| Risorsa sbloccata solo dopo risoluzione autorizzata | §5.4.1(4) | Core: `blockedResources`, `ResolveIndeterminate` | **Rappresentato** |
| Condizioni hardware minime per COMPLETED | §5.4.1, tabella | Core: `HW_READBACK_ON/OFF` | **Non dimostrato**: tipi di evidenza astratti, nessuna condizione specifica per setpoint/defrost/firmware; il modello non verifica le soglie della tabella |
| Chunk già COMPLETED: ignora/OK se identico | §5.6.1 | Firmware | **Non modellato**: contenuto/identità del chunk non esistono nel modello |
| Stesso offset, contenuto diverso: reject + ABORT Transfer | §5.6.1 | Firmware | **Non modellato**: non sono modellati hash/contenuti per offset |
| Chunk fuori ordine/gap: buffer oppure risposta Unexpected offset | §5.6.1 | Firmware: `WriteChunk` accetta solo `NextExpected` | **Parziale**: strategia no-buffer è implicitamente scelta, ma risposta/errore non modellati |
| Mantenere NextExpectedOffset | §5.6.1 | Firmware: `NextExpected` derivato da `Cardinality(durableOffsets)` | **Rappresentato in forma astratta** per chunk contigui |
| Write → verify → durable → advance offset | §5.6.1 | Firmware: `WriteChunk`, `VerifyChunk`, `DurabilizeChunk`, `AdvanceOffset` | **Rappresentato** come pipeline a passi; il successo della durabilità è assunto nella transizione |
| COMPLETED solo con tutti i chunk durevoli, firma manifest e hash globale validi | §5.6.2 | Firmware: `MarkImageDurable`, `VerifyManifestPass`, `CloseTransfer` | **Parziale**: PASS astrae firma+hash; algoritmo/risultati crittografici non verificati |
| Power loss durante chunk: chunk parziale invalido, ripresa dall'ultimo offset durevole | §5.6.2 | Firmware: `Crash` preserva `durableOffsets`, azzera pipeline | **Rappresentato in forma astratta**; comportamento fisico read-back/CRC e recovery flash non modellati |
| Un solo Transfer IN_PROGRESS per ClientDeviceID | §5.6.3 | Firmware: `activeTransfer`, `Inv_AtMostOneInProgress` | **Rappresentato** |
| Recovery Barrier: IN_PROGRESS → ABORTED o INDETERMINATE se resume deterministico | §5.6.3 | Firmware: `Crash` | **Rappresentato** per policy ABORTED |
| Nuovi chunk per TransferID ABORTED respinti | §5.6.3 | Firmware: `WriteChunk` richiede IN_PROGRESS | **Rappresentato come guardia negativa**, senza risposta/protocol error esplicito |

## 4. Findings prioritari

### E1 — Interblocco attuazione durante Epoch Sync (alta priorità)

La v1.4.5 §5.2.2 impone di sospendere i comandi attuativi in caso di rilevamento di salto > +1 o ripetuti `EPOCH_REJECTED`, durante la procedura di sincronizzazione.

Nel `REFRIG_GDO_Root.tla`, `C_Dispatch` e `C_Effect` sono subordinati alla Recovery Barrier ma non a `syncState` / `epochPc`. Di conseguenza il modello consente, in linea di principio, dispatch/effetto fisico mentre `syncState = "req_sent"` o `"resp_pending"`.

**Correzione da progettare:** definire precisamente la condizione di sospensione e aggiungere un invariant/guardia cross-machine nel Root. Al minimo, un nuovo dispatch deve essere impedito durante Epoch Sync; va poi deciso e documentato come trattare un'azione già dispatchata prima dell'avvio della sync. Non applicare la correzione al Core standalone senza introdurre un'interfaccia di stato Epoch.

### E2 — Rifiuto esplicito di Epoch obsoleto (alta priorità)

`RejectStaleEpoch` rimuove un pacchetto con `e < lastAcceptedEpoch` e avvia immediatamente la sincronizzazione. È un'astrazione conservativa, perché la fonte richiede il trigger dopo rifiuti ripetuti; il modello non registra un contatore né emette uno status `EPOCH_REJECTED` distinto.

**Passo successivo:** modellare il contatore/esito `EPOCH_REJECTED` e il trigger da rifiuti ripetuti; mantenere lo scenario diretto di discard stale come copertura della regola §5.2.1(1).

### E3 — Rilevamento salto e causalità della sincronizzazione (alta priorità)

`RejectLargeJump` rimuove il datagramma e porta il modello nello stato `req_sent`, astrattamente avviando la sincronizzazione. Non costruisce però un pacchetto 0x40 concreto né modella il dispatch privilegiato, l'autenticazione e i ruoli completi dei due peer. Il trigger da rifiuti stale ripetuti resta incompleto.

**Passo successivo:** modellare il trigger da rifiuti stale ripetuti, il dispatch privilegiato di 0x40 e i ruoli initiator/responder dei due peer.

### E4 — Nonce fresco nei retry 0x40 e proprietà di unicità troppo ampia nel nome (alta priorità)

La v1.4.5 §5.2.2 richiede che il retry 0x40 usi un Sequence Number fresco. `RetransmitSyncReq` incrementa `seqNum` a ogni retry, entro il bound finito `MaxSeq`. Tuttavia, l'emissione iniziale di 0x40 è astratta e il modello non mantiene un registro di tutte le emissioni cifrate, dei datagrammi persi, dei messaggi 0x40/0x41 o delle direzioni/chiavi. `acceptedPairs` è soltanto una cache anti-duplicato dell'Epoch corrente, azzerata quando l'Epoch avanza.

**Lavoro residuo:** se si vuole dimostrare l'unicità dei nonce, introdurre un registro delle emissioni per ciascuna direzione/chiave che includa traffico ordinario, 0x40/0x41 e retry. Il modello attuale non dimostra l'unicità globale dei nonce.

### E5 — Soglia soft-rotation non leggibile nella fonte (bloccante per il valore numerico)

Nel PDF v1.4.5 §5.2.3 la soglia è renderizzata come `2■■`. Il valore dell'esponente non è leggibile nella copia ricevuta.

**Azione richiesta sulla specifica:** correggere il PDF/sorgente editoriale affinché l'espressione matematica sia leggibile e non ambigua. Fino ad allora `SoftRotationThreshold` deve restare un parametro astratto; i bound TLC (per esempio 4) sono valori di esplorazione finita e non rappresentano il valore normativo.

### E6 — Rollback, persistenza protetta e key usage/rekey (alta priorità per la pretesa di sicurezza)

`epochHighWater` viene sempre aggiornato insieme a `senderEpoch`; il modello non può raggiungere uno stato di rollback o storage monotono indisponibile. Non esistono contatori di utilizzo chiave, rekey, re-provisioning o terminal refusal. La v1.4.5 §5.2.4 li impone.

**Azione:** aggiungere un modello separato della persistenza/key lifecycle oppure dichiarare questi requisiti come obblighi implementativi non coperti dalla verifica Epoch. Il bound `MaxEpoch` non equivale a un modello di rekey.

### C1 — Esito REJECTED e commit durevole (media)

Core enumera `REJECTED`, ma nessuna azione lo assegna e non esiste un ACK di rifiuto. La v1.4.5 §5.3.2 richiede che lo stato REJECTED sia durevole prima dell'emissione dell'ACK. Va aggiunto un ramo dedicato o dichiarato fuori dallo scope della macchina modellata.

### C2 — Lock order e journal (media)

Il modello rappresenta il controllo Recovery Barrier e l'acquisizione dell'Identity lock nella stessa transizione TLA, insieme al commit PERSISTED. È una buona astrazione atomica dell'ammissione, ma non formalizza journal lock distinto, lock fisico acquisito dopo commit, FIFO, sequence number locale, magic/checksum, batching, flush su deep-sleep/timeout/soglia. Non va descritto come verifica di tali dettagli firmware.

### C3 — INDETERMINATE e condizioni minime COMPLETED (media)

La policy AUTHORIZED_OPERATOR è più restrittiva del minimo “authorized entity” e può essere mantenuta come policy conservativa. Tuttavia il modello non registra authorizer identity, timestamp, reason, error code, compensatory operation o prova diagnostica. `HW_READBACK_ON/OFF` non implementa le condizioni specifiche della tabella §5.4.1. La proprietà verificata è soltanto che la transizione astratta RESOLVED richieda l'etichetta AUTHORIZED_OPERATOR; non è verificata la procedura completa normativa.

### F1 — Gestione contenuto chunk (media)

Firmware modella gli offset contigui e la pipeline di durabilità, ma non il contenuto del chunk. Non può quindi verificare idempotenza di chunk già completati né abort per stesso offset con contenuto diverso. Questi sono requisiti espliciti di §5.6.1.

### F2 — Anti-rollback firmware (media)

La tabella §5.4.1 richiede il controllo anti-rollback della versione firmware prima di dichiarare COMPLETED; §5.6.2 richiede firma manifest e hash globale. Il modello usa un singolo flag `manifestResult = PASS`, senza versione minima/contatore anti-rollback. La proprietà è astratta e non copre il controllo anti-rollback.

### F3 — Recovery Transfer (bassa/medio)

Il modello sceglie sempre ABORTED al Recovery Barrier, opzione ammessa da §5.6.3. Non modella il ramo INDETERMINATE per resume deterministico; ciò non è un mismatch se la specifica di implementazione sceglie di non supportare resume.

## 5. Confini di astrazione da dichiarare nel paper

- AEAD, autenticazione reciproca, verifica firma manifest e hash globale sono assunti come esiti booleani; TLC non dimostra proprietà crittografiche.
- Commit NVM, atomicità fisica, journal FIFO, checksum, wear management e comportamento del flash sono astratti.
- `acceptedPairs` è una cache di coppie accettate per l'Epoch corrente, azzerata all'avanzamento di Epoch; non è un registro di tutte le cifrature emesse e non dimostra l'unicità globale dei nonce.
- Epoch standalone è un modello a singolo mittente/direzione e non una composizione completa di due peer.
- Root usa un singolo pacchetto ordinario in-flight e non verifica la sliding window completa, la consegna out-of-order o l'eviction.
- I parametri finiti TLC non rappresentano le costanti di produzione; la soglia normativa soft-rotation non è leggibile nel PDF fornito.
- Il modello Core non verifica deadlock-freedom generale; `Inv_NoDeadlockUnderRecovery` verifica solo la condizione dichiarata sotto Recovery Barrier.
- I risultati TLC sono verifiche di safety su spazi finiti e configurazioni specifiche; non dimostrano liveness generale, correttezza dell'implementazione, sicurezza funzionale o conformità crittografica.

## 6. Stato delle verifiche TLC

Questo audit è un confronto normativo, non un nuovo risultato TLC.

Per il branch e la revisione del modello qui esaminati:
- sul commit finale `fa96cf04` (workflow `46017532177`), tutte le 8 configurazioni TLC hanno completato con successo;
- Epoch baseline: 77.319 stati generati, 17.762 distinti; Epoch extended: 61.799 generati, 16.040 distinti; entrambi con coda esaurita e nessun errore;
- Epoch directed coverage: 20 stati generati, 18 distinti, nessun errore; Root baseline e Root mid, Core baseline/extended e Firmware baseline hanno anch'essi completato senza errori;
- questi risultati attestano soltanto le proprietà e i bound delle configurazioni finite eseguite; non sanano i gap normativi descritti in questo audit.

Prima di aggiornare i risultati nel README, conservare per ogni run commit SHA, configurazione, versione TLC, conteggi e stato finale.

## 7. Sequenza raccomandata

1. Correggere la fonte v1.4.5 per rendere leggibile la soglia soft-rotation.
2. Formalizzare stale Epoch → EPOCH_REJECTED.
3. Collegare large-jump/repeated EPOCH_REJECTED a sync e sospensione delle attuazioni nel Root.
4. Modellare emissione iniziale e retry 0x40/0x41 con history delle emissioni, se si intende dimostrare l'unicità globale dei nonce.
5. Decidere se rollback/key lifecycle e anti-rollback firmware saranno modelli separati o limiti espliciti della fase attuale.
6. Completare i rami REJECTED e i casi di contenuto chunk, se si intende rivendicare copertura integrale delle sezioni 5.3 e 5.6.
7. Solo dopo le modifiche, rieseguire TLC sulle configurazioni mirate e poi valutare lo state-space completo.

**Conclusione:** il lavoro TLA+ è una base di ricerca concreta, ma la matrice precedente che classificava quasi tutte le aree come “Allineato” era troppo ottimistica. Il passo corretto ora è chiudere i gap sopra elencati e restringere le affermazioni del paper a ciò che i modelli effettivamente rappresentano e TLC ha effettivamente completato.
