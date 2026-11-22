# Go core, services and harness

## Design rules (handover §4)

- Use Go with `chi`, and SQLite through `modernc.org/sqlite` with `CGO_ENABLED=0` (`env.sh` sets it).
- All business logic is the pure function `internal/<uc>/core.Step(state, event) -> (state, effects)`. HTTP and database code stay thin around it. The TLA+ spec and the Bend port both mirror this `Step`.
- Each service is a few hundred lines and owns its own SQLite file. Services talk through an outbox table plus HTTP, with no message broker.
- `internal/sim` injects the clock and the transport. The transport drops, duplicates, delays and reorders messages, and crashes a service at chosen points, all driven by a seed. SQLite serializes writes and would hide races, so faults come from the sim, never from real timing.
- Services bind 127.0.0.1 only.
- Go mutants live in `mutants/<uc>/`.
- `just` recipes: `check-tla`, `prove-bend`, `harness`, `test`, `all`.

## Conformance harness

The Bend proof covers the Bend port, not the Go service. The harness closes that gap:

- Run the same seeded event sequences through the Go core and through the compiled Bend port, then compare final states.
- Write events as space-separated ASCII digits with a final newline, always attach and close stdin, and use a timeout. The Bend port must reject bad input with a nonzero exit. Evidence: `docs/results/phase0-bend-io.md` §9.
- Replay TLC counterexample traces against the Go service as tests. This is best effort; record how hard it was.
