# Working in TLA+ and TLC

## Spec conventions

These are the conventions the approved `properties/UCn.md` files assume:

- Each spec defines `Init`, `Next`, and `Spec == Init /\ [][Next]_vars`, plus `TypeOK`. Constants and invariants go in the `.cfg` file.
- The auxiliary variables `lastEvent` and `lastFx` record the last step. `lastEvent` is a record with a `kind` tag.
- Transition properties are action properties, `[][Guard => Post]_vars`, checked as `PROPERTY`. State properties are checked as `INVARIANT`.
- Counters are `Int`, so a property like "never below zero" can actually fail in TLC.
- Buggy variants and mutants are `spec/tla/UCn_buggy*.tla`, each with its own `.cfg`.

## Running TLC

- Run `tlc -metadir $TMPDIR/<run> -config <cfg> <tla>`. `env.sh` already moves the JVM temp dir off the read-only `/tmp`.
- TLC stops at the first violation. Give each expected violation its own cfg: buggy variants, witness checks, and non-vacuity (reachability) invariants.
- For each run, record the bounds, states generated, distinct states and wall time. Time runs with `hyperfine`. Every run pays about 1.5 s of JVM start-up (`docs/results/phase0-tlc.md`).

## Liveness (UC4)

Follow `properties/UC4.md` §3-4:

- Fairness is stated explicitly. Delivery needs strong fairness, because drops disable it again and again.
- Use `SPECIFICATION`, not `INIT`/`NEXT`.
- Use no `CONSTRAINT` and no `SYMMETRY`.
- Every antecedent needs a reachability run that TLC must violate, so the property can't be vacuously true.
