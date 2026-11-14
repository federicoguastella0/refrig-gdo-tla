# Analysis aids

Auxiliary models used to classify functional terminal states and bound-exhaustion
behaviour. They are **not** part of the normative safety claim set.

| File (parent dir) | Purpose |
|-------------------|---------|
| `REFRIG_GDO_Core_NoCrash.tla` | Core with Crash/FinishRecovery removed so TLC deadlock detection surfaces “work completed / slots full” terminals |
| `Core_NoCrash.cfg` | Config for the above (`CHECK_DEADLOCK TRUE`) |

Run from the parent directory:

```bash
java -XX:+UseParallelGC -jar tla2tools.jar -config Core_NoCrash.cfg REFRIG_GDO_Core_NoCrash.tla
```
