# Experiment log

TLA+ (TLC) vs Bend 2, four use cases. Rules for this file are in `CLAUDE.md` (Process) and `docs/handover.md` section 8. Evidence lives in `docs/results/`; this log is the short index. Every number below is copied from the cited results file (the go version comes from `.nix/env.sh`), except the excerpts marked "Re-run", which are verbatim output of commands re-run for this log. A missing field says "not recorded".

## 1. Soundness alerts

Rule (`CLAUDE.md`): if Bend ever accepts a false statement, record it here first, above everything else.

**Current status: none.** 14 of 14 probes rejected: 12 on the merits and 2 (`unsafe_false`, `open_false`) by the escape-hatch detector, kept as regressions (the source's classification). Each of the 14 probe dirs in `bend/probes/` states a false law, and each `bend PROOF.bend` printed `SOME PROOFS FAIL`. Re-run (verbatim output):

```text
$ source .nix/env.sh && bash bend/probes/run.sh
bad_rec                PASS rejected as expected
dead_mode_leak         PASS rejected as expected
dead_mode_leak_match   PASS rejected as expected
empty_loop             PASS rejected as expected
false_eq               PASS rejected as expected
negative_type          PASS rejected as expected
negative_type_data     PASS rejected as expected
negative_type_fix      PASS rejected as expected
open_false             PASS rejected as expected
succ_eq                PASS rejected as expected
type_in_type           PASS rejected as expected
type_in_type_fix       PASS rejected as expected
unsafe_false           PASS rejected as expected
wrong_witness          PASS rejected as expected
$ echo $?
0
```

Source: `docs/results/phase0-bend-probes.md` (run 2026-11-22T02:09Z). Limits stated there: the checker reports only the first error; `type_in_type*` are Russell-style, not a full Girard/Hurkens paradox; `unsafe_false` and `open_false` test the escape-hatch detector, not the type theory; the probes show specific known attacks are refused and are not a proof of soundness.

**Limitation that applies to every Bend result in this log:** `bend PROOF.bend --verdict` (the recheck with the small kernel proven in Lean) cannot run in this sandbox (no `lean`, `lake` or `clang` on PATH; see `docs/results/phase0-bend-guide.md` section 5). So every `ALL PROOFS CHECK` in this log comes from the plain gate only and is provisional. A probe rejection is the bend2 checker refusing; nothing here tests the Lean kernel.

## 2. Setup

| Item | Value | How pinned | Source |
|---|---|---|---|
| Bend | 2.0.40 | flake input `github:bendlang/bend`, locked rev `0e2f38f759cc830849e489307f3d256a7d148288` (narHash `sha256-gQdsY8fxOgZPiEUJ3qB4foFIeIlXt4GixDCxxj6+SIo=`) in `flake.lock`; devShell, `.nix/env.sh` | phase0-bend-guide.md section 2 |
| TLC | TLC2 Version 2.18 (rev: 5b3286b), nixpkgs `tlaplus-1.8.0` | devShell, `tlc` wrapper from `.nix/env.sh` | phase0-tlc.md |
| Java | OpenJDK 21.0.13.1 (the `java` the `tlc` wrapper execs; not on PATH) | comes with `tlaplus` | phase0-tlc.md |
| hyperfine | 1.20.0 | devShell | phase0-tlc.md |
| clang | 21.1.8 | pinned through the `bend` wrapper (it prepends a Nix clang-wrapper to PATH); not on the `env.sh` PATH | phase0-bend-io.md section 9 |
| go | 1.26.10 | devShell, `.nix/env.sh` PATH (not mentioned in the Phase 0 results files) | `.nix/env.sh` |

Machine as reported by TLC: Linux 6.18.54 amd64, 2 cores, 274MB heap, 1 worker.

`env.sh` workaround: `nix develop` cannot run in this sandbox, so `.nix/env.sh` is hand-built from the devShell derivation; run `source .nix/env.sh` before any tool. The JVM default temp dir `/tmp` is read-only in the sandbox (TLC failed with `FileSystemException: /tmp/tlc-...: Read-only file system`), so `env.sh` exports `JAVA_TOOL_OPTIONS="-Djava.io.tmpdir=${TMPDIR:-/tmp}"`. This makes the JVM print a `Picked up JAVA_TOOL_OPTIONS: ...` line on stderr. TLC runs also use `-metadir $TMPDIR/...`. Also: `~/.bend` is read-only here and `bend-lang.com:443` is blocked (daily version check); `bend` still runs.

Bounds-reporting rule: never shrink TLC bounds or add assumptions silently. Bounds live in the `.cfg` files and every TLC entry states them, plus states generated, distinct states and wall time. Phase 0 bound: `Smoke.cfg` has `CONSTANT N = 10`.

"Cold" caveat: no run so far is a true cold start (OS page cache not dropped, no sudo); see each entry.

## 3. Summary table

Phase 0 rows are not use cases. Times for authoring are the agents' estimates as written in the results files, not measured.

| Use case | Tool | Result | Authoring time | AI / failed iterations | Machine time (cold / warm) | Size (lines) | Walls hit |
|---|---|---|---|---|---|---|---|
| Phase 0: TLC smoke | TLA+ (TLC 2.18) | no error; 12 states generated, 11 distinct, depth 11; false invariant gives a violation (exit 12) | about 10 minutes | 1 AI iteration for the spec, 1 for the environment, 1 revision round; failed iterations not recorded | 1.395 s (1 run) / 1.619 s +- 0.186 s (10 runs) | `Smoke.tla` 22, `Smoke.cfg` 4 | read-only `/tmp`; no true cold measurement |
| Phase 0: Bend guide / escape-hatch audit | Bend 2.0.40 | add_zero proof gives `ALL PROOFS CHECK` (plain gate); `--verdict` could not run | about 1 hour (about 5 minutes for the add_zero trial) | 2 for add_zero; about 8 small experiments for the hatches | not recorded / 385.4 ms +/- 15.7 ms (10 runs) | `LAWS.bend` 6, `PROOF.bend` 10 | `--verdict` impossible (no Lean); `~/.bend` read-only; no `bend-lang.com:443` |
| Phase 0: Bend smoke law + proof | Bend 2.0.40 (plain gate) | `ALL PROOFS CHECK`, 3 laws, no escape hatch; mutants (a) Inc=0 and (b) cap 2 survive | about 10 minutes | AI iterations not recorded; 5 failed proof iterations | not recorded / hyperfine (10 runs, 2 warmups, noisy machine) mean 510.2 ms +/- 217.6 ms and 781.4 ms +/- 87.7 ms, minimum 357.7 ms | `code.bend` 21, `LAWS.bend` 21, `PROOF.bend` 26 | `Event` name clash; termination argument order; affine use; match order |
| Phase 0: Bend I/O spike | Bend 2.0.40 | recommend option A (compiled binary reads events on stdin); option B (events embedded in generated source) works only in chunks; option C (`-o x.mjs` called from JS) works but unpinned | about 25 minutes programs plus about 25 minutes probes and write-up | about 12 edit/run cycles; failed iterations not recorded | not recorded / not a warm figure: mostly `hyperfine --runs 3 -N`, no warm-up (rough): compile 1.5 s; compiled run 5 to 7 ms at 10,000 events; interpreted run about 0.5 s | `print.bend` 6, `args.bend` 26, `stdin.bend` 37, `record.bend` 40 | no stdin effect; list literal breaks between 2,500 and 3,000 elements; interpreted stdin overflow above roughly 20 KB |
| Phase 0: Bend soundness probes | Bend 2.0.40 (plain gate) | 14 of 14 false laws rejected (12 on the merits, 2 detector regressions); `run.sh` exits 0 | about 45 minutes plus about 10 minutes for the EXPECT rework | about 25 `bend` runs; failed iterations not recorded | not recorded / `run.sh` (14 probes) mean 5.550 s ± 0.290 s (about 0.40 s per probe is derived: 5.550 s / 14, includes `run.sh` overhead) | 306 (`*.bend`), `run.sh` 22, `EXPECT` files 26 | one error reported at a time; no tactics; `type_in_type` stopped at Russell version |
| UC1 | TLA+ (TLC 2.18) | no error at the checked bound N=1 (approved 2026-11-23): 1,156,996 distinct, depth 34, 5 min 01 s; **wall** at N=2 (contract bounds, `UC1_wall_n2.cfg`): unfinished after 62 min, 9,079,945 distinct, 4.6M on queue, no violation seen; 15 reach witnesses and 6 mutants violate | about 1 h 20 min (mostly TLC) | 0 failed | not timed with hyperfine; N=1 single run 5 min 01 s | `UC1.tla` 438+, `UC1.cfg` 27, `UC1_wall_n2.cfg` 27 | state-space explosion at N=2 on 2 cores / 1.9 GB |
| UC1 | Bend 2.0.40 (plain gate) | `ALL PROOFS CHECK`, 46 of 46 laws (Inv, P1, P2a, P2b a-d, P3, pins A1-A13 incl. rule D); `spec.bend` and `LAWS.bend` approved 2026-11-23 | about 35 minutes | 12 failed proof iterations | first run 6.97 s / 6.484 s +/- 0.099 s | 3660 (`PROOF.bend` 2634) | affine and erasure rules; no match on computed values |
| UC1 | harness | Go core and Bend port agree on 500 seeded sequences (75,787 events); M1 diverges at event 224 | about 30 min plus review fixes | not recorded | compile 8.2 s / 500-sequence run 10.1 s incl. compile | 739 | Bend I/O: fixed read size, no match on computed values; slow compile |
| UC2 | TLA+ | not started | | | | | |
| UC2 | Bend | not started | | | | | |
| UC2 | harness | not started | | | | | |
| UC3 | TLA+ | not started | | | | | |
| UC3 | Bend | not started | | | | | |
| UC3 | harness | not started | | | | | |
| UC4 | TLA+ | not started | | | | | |
| UC4 | Bend | not started | | | | | |
| UC4 | harness | not started | | | | | |

Stop rule per tier (one use case) and tool: 2 hours of authoring or 15 failed iterations, whichever comes first.

## 4. Entries

Order follows the Phase 0 task order. Recorded times overlap, so the time stamps are not strictly increasing. Evidence is in the linked file.

### 4.1 TLC smoke test

- Date and time: 2026-11-22, about 01:50 to 01:55 UTC.
- Tool: TLA+ (TLC 2.18, OpenJDK 21.0.13.1).
- Use case: Phase 0 smoke test (bounded counter, not a use case).
- What was done: wrote `Smoke.tla` and `Smoke.cfg`, ran TLC with invariants, ran a false-invariant variant to confirm a violation, timed with hyperfine.
- Bounds: `CONSTANT N = 10`, `ASSUME N \in Nat`, invariants `TypeOK` and `Bounded`; no other bounds or assumptions.
- Authoring time: about 10 minutes; 1 AI iteration for the spec plus 1 to fix the environment, then 1 revision round (adding `ASSUME`). Estimates, not measured.
- Machine time (hyperfine): cold 1.395 s (1 run); warm 1.619 s +- 0.186 s (10 runs, 2 warm-up), min 1.441 s, max 1.952 s. No real cold/warm gap; the cold run is only the first measured run. TLC's own wall time on the re-run below: `Finished in 01s`.
- Result: no error; 12 states generated, 11 distinct, depth 11; false invariant gives a violation (exit 12). Re-run (verbatim lines of the TLC output, exit 0):

```text
$ tlc -metadir $TMPDIR/log-tlc -config spec/tla/Smoke.cfg spec/tla/Smoke.tla
Model checking completed. No error has been found.
12 states generated, 11 distinct states found, 0 states left on queue.
The depth of the complete state graph search is 11.
Finished in 01s at (2026-11-22 02:15:28)
```

- Failed iterations: not recorded.
- Size: `Smoke.tla` 22 lines, `Smoke.cfg` 4 lines.
- Friction: `/tmp` read-only (fixed via `JAVA_TOOL_OPTIONS` in `.nix/env.sh`); cannot drop page cache without sudo; `java` not on PATH.
- Details: [docs/results/phase0-tlc.md](docs/results/phase0-tlc.md)

### 4.2 Bend guide, version, proof conventions, escape hatches

- Date and time: 2026-11-22, about 01:55 UTC.
- Tool: Bend 2 (2.0.40).
- Use case: Phase 0 (toolchain, guide and Base capture, proof-convention and escape-hatch survey).
- What was done: regenerated `bend guide`; saved `bend guide effects` and `bend base`; recorded version and flake lock; searched Base for axiom-like items; ran the `--verdict` trial; tested escape hatches (`@unsafe`, `def f?`, `?TODO`, `?goal`, open law, foreign import, PROOF without LAWS import); fetched the upstream AGENTS.md.
- Authoring time: about 1 hour including research; about 5 minutes for the add_zero trial itself. Honest estimate.
- AI iterations: 2 for the add_zero trial; about 8 small experiments for the hatches. Failed iterations: not recorded.
- Machine time (hyperfine `--warmup 2 --runs 10 -N 'bend PROOF.bend'`, add_zero): cold not recorded (no separate cold run); warm mean 385.4 ms +/- 15.7 ms (range 361.7 to 406.7 ms; 10 runs).
- Result: add_zero checks with the plain gate (`ALL PROOFS CHECK`); `--verdict` could not run (no Lean). Output pasted from the results file (the trial dir was in `$TMPDIR`, so it was not re-run):

```text
$ bend PROOF.bend
ALL PROOFS CHECK
Use --verdict for mathematical validity.
(rc 0)
$ HOME=$TMPDIR/fakehome2 bend PROOF.bend --verdict
Error: BendTT infrastructure: the kernel did not build (lean: Executable not found in $PATH: "lean"); --verdict needs Lean v4.34.0 (elan toolchain leanprover/lean4:v4.34.0), or $BENDTT set to a built kernel
(rc 1; ~0.6 s)
```

- Size: `LAWS.bend` 6 lines, `PROOF.bend` 10 lines.
- Friction: `~/.bend` read-only (`EROFS`); no `lean`/`lake`/`clang`, so no `--verdict`; `bend-lang.com:443` blocked; a law-filling def takes no signature; `def f?` and calls to `f?` differ.
- Details: [docs/results/phase0-bend-guide.md](docs/results/phase0-bend-guide.md)

### 4.3 Bend smoke law and proof

- Date and time: 2026-11-22, about 01:58 UTC (final run).
- Tool: Bend 2 (2.0.40), plain gate.
- Use case: Phase 0 smoke (trivial law and proof; a saturating counter).
- What was done: wrote `step` and `run`, three laws, proved them with the LAWS/PROOF convention; checked the gate with a broken proof step and broken code variants; ran four mutants of `step` against the laws.
- Authoring time: about 10 minutes of wall time including reading the guide. Honest estimate.
- AI iterations: not recorded. Failed proof iterations: 5 (stop-rule count). Not counted: 2 `code.bend` compile/termination failures and the deliberate broken-input and mutant runs.
- Machine time: cold not recorded. Warm: hyperfine (10 runs, 2 warmups, noisy machine) mean 510.2 ms +/- 217.6 ms and 781.4 ms +/- 87.7 ms, minimum 357.7 ms. Note: the first single run on a fresh copy took 0.397 s and a second single run 0.396 s; the source says the first is not a cold-start measurement (binary already in the page cache), so it is not entered as cold.
- Result: `ALL PROOFS CHECK` with all three laws proved, no escape hatch (plain gate only, provisional). Re-run (verbatim, exit 0):

```text
$ bend bend/smoke/PROOF.bend
ALL PROOFS CHECK
Use --verdict for mathematical validity.
```

- Gate behaviour: it rejects a broken proof step and several false code variants, but mutants (a) Inc=0 and (b) cap 2 survive, because the laws only state an upper bound plus `Reset -> 0`.
- Size: `code.bend` 21 lines, `LAWS.bend` 21 lines, `PROOF.bend` 26 lines.
- Friction: `type Event` clashes with Base (renamed `Ev`); termination needs the shrinking list leftmost (`run(events, s)`); import alias is local to `LAWS.bend`; scrutinee order in `match`; affine usage needs `+s` and `+e` annotations; law-filling defs take no signature.
- Details: [docs/results/phase0-bend-smoke.md](docs/results/phase0-bend-smoke.md)

### 4.4 Bend I/O spike (harness input and output)

- Date and time: 2026-11-22, about 01:56 to 02:01 UTC.
- Tool: Bend 2 (2.0.40).
- Use case: Phase 0 I/O spike (conformance-harness input and output).
- What was done: wrote `print.bend`, `args.bend`, `stdin.bend`, `record.bend`; ran each interpreted and compiled; grepped Base for stdin and found none; probed embedding (single literal, string literal, chunked list), argv at 10,000 and 100,000, stdin at 10,000 and 100,000, and an `.mjs` build called from Node and Bun.
- Authoring time: about 25 minutes for the programs, about 25 more for the probes and write-up. Honest estimate.
- AI iterations: about 12 edit/run cycles. Failed iterations: not recorded.
- Machine time (`hyperfine --runs 3 -N` unless noted, no warm-up, so these are rough figures and not warm-run figures): cold not recorded (no separate cold run measured); compile of a small program 1.5 s; compiled run 5 to 7 ms at 10,000 events (63 ms at 100,000 on stdin; the 226 ms argv time is from `hyperfine --runs 3 './rec.bin $(cat ev100k.txt) > /dev/null'` and includes the shell and `cat` that build the command line); interpreted run about 0.5 s; option B about 1.3 s.
- Result (option A: compiled binary reads events on stdin; option B: events embedded in the generated `.bend` source; option C: `-o x.mjs` called from JS): option A works and scales to 100,000 events; option B works only in chunks and is slow; option C works but is unpinned; interpreted stdin overflows above roughly 20 KB of input; no Base stdin effect.
- Size: `print.bend` 6, `args.bend` 26, `stdin.bend` 37, `record.bend` 40 lines.
- Friction: no stdin effect; affine `List<String>` from `IO.args`; `match` and destructuring not allowed inside `do`; termination checker order; single-literal limit between 2,500 and 3,000 elements with unhelpful "memory fault" and "stack overflowed" errors; stdin overflow in the interpreted run.
- Details: [docs/results/phase0-bend-io.md](docs/results/phase0-bend-io.md)

### 4.5 Bend soundness probes

- Date and time: 2026-11-22, about 02:11 UTC (final run).
- Tool: Bend 2 (2.0.40), plain gate.
- Use case: Phase 0 soundness probes.
- What was done: 14 probe dirs (false law, genuine proof attempt); `run.sh` runs them all and classifies PASS (rejected) or FAIL (accepted); scratch controls for syntax and for dead-mode acceptance; EXPECT files pin each rejection to the intended error.
- Authoring time: about 45 minutes of wall time including reading the guide, plus about 10 minutes for the EXPECT rework. Honest estimate.
- AI iterations: about 25 `bend` runs while writing; failed iterations not recorded; the Russell attempt (`type_in_type`) took about 10 of them and about 15 minutes, inside the 30-minute cap.
- Machine time (`hyperfine --warmup 1 --runs 5 'bash bend/probes/run.sh'`): cold not recorded; final mean 5.550 s ±  0.290 s (range 5.318 s …  6.004 s, 5 runs); about 0.40 s per probe is derived (5.550 s / 14, includes `run.sh` overhead), not measured per probe; earlier noisy session mean 7.973 s +/- 2.379 s.
- Result: all 14 false laws rejected (12 on the merits, 2 detector regressions: `unsafe_false`, `open_false`); `run.sh` exits 0. No false statement accepted. Plain gate only. The verbatim 14-line re-run output is in section 1.
- Size: `bend/probes/**/*.bend` 306 lines (14 `LAWS.bend` + 14 `PROOF.bend`), `run.sh` 22 lines, 14 `EXPECT` files 26 lines.
- Friction: no tactics, so every attempt is hand-written term syntax; defs are checked in file order; `(x, +eq) = i` gives `an annotated term (cannot infer)`; `In(v, v)` for a free `v` is stuck; the checker prints one error at a time.
- Details: [docs/results/phase0-bend-probes.md](docs/results/phase0-bend-probes.md)

### 4.6 UC1 infrastructure: Go module, justfile, sim package

- Date and time: 2026-11-22, about 10:00 to 10:15 UTC.
- Tool: Go 1.26.10 (no verification tool).
- Use case: UC1 (shared with UC2-UC4).
- What was done: `go.mod` (module `github.com/derangga/learn-formal-verification`, chi v5.5.0) and a `justfile` with `check-tla`, `check-tla-buggy`, `prove-bend`, `harness`, `test`, `all`. `internal/sim`: fake clock, seeded fault network (`Net[M]`: drop, duplicate up to `MaxDup`, reorder, scripted replay mode) and a seeded crasher with a per-service budget.
- Deviation: `modernc.org/sqlite` is not in `go.mod` yet. The sandbox cannot download it (`storage.googleapis.com`, `modernc.org` and `gitlab.com` are not on the managed allowlist). The user will fetch it into the module cache; the services task adds it.
- Known difference from TLA+: the sim bounds duplicates per sent copy, while `UC1.tla` counts `dup[m]` per message value, so Go random runs may duplicate more than TLC allows (Go explores a superset). Documented in `docs/results/uc1-sim.md`.
- Sandbox friction: `just` writes shebang recipes under `XDG_RUNTIME_DIR` (read-only here), so runs in the sandbox need `XDG_RUNTIME_DIR=$TMPDIR`. The Go module cache must be moved to `$TMPDIR` (`GOMODCACHE`, `GOCACHE`, `GOPATH`).
- Result: `go test ./internal/sim/... -count=1` gives `ok  github.com/derangga/learn-formal-verification/internal/sim` (13 tests); `just all` exits 0 on the tree at that point.
- Size: `internal/sim` 584 lines (317 code, 267 tests).
- Details: [docs/results/uc1-sim.md](docs/results/uc1-sim.md)

### 4.7 UC1 Go pure core

- Date and time: 2026-11-22 (start and end in the results file).
- Tool: Go 1.26.10 (unit and seeded property tests).
- Use case: UC1.
- What was done: `internal/uc1/core`: types, `Init`, `Step` (rules F and D, pins A1-A11), helpers and `Inv` from `properties/UC1.md` sections 2-4. Tests `TestInv`, `TestP1NoDoubleCharge`, `TestP2aRefundNeverExceedsCharge`, `TestP2bRefundOnlyFromPaid`, `TestP3TerminalStable`, `TestPin*` for A1-A13, a cross-service rule D test, and non-vacuity counts on the seeded runs (1000 sequences of up to 200 events, N = 2..3; every antecedent fired, lowest count 56 for `WireRefundReq`).
- Mutation sanity (applied, then reverted): M1 fails `TestInv`, `TestP1NoDoubleCharge`, `TestPinChargeReqRecv`, `TestPinProvRecStable`; M2a fails `TestP2bRefundOnlyFromPaid`, `TestP3TerminalStable`, `TestPinRefundOrder`, `TestPinLegalTransitions`. The committed mutant corpus is a later task.
- Result: `go test ./internal/uc1/... -count=1` gives `ok  github.com/derangga/learn-formal-verification/internal/uc1/core`.
- Size: `core.go` 348 lines, `core_test.go` 480 lines.
- Ambiguities resolved by the literal reading: listed in the results file (failed guard gives frame F; `Refund` carries the provider `amt`; non-charge `Wire*` effects carry `A = 0`; A8 replays whatever `d` is).
- Details: [docs/results/uc1-core.md](docs/results/uc1-core.md)

### 4.8 UC1 conformance harness (Go core vs compiled Bend port)

- Date and time: 2026-11-22, from 10:22 UTC (end in the results file).
- Tool: Go test plus the compiled Bend 2.0.40 runner `bend/uc1/main.bend`.
- Use case: UC1.
- What was done: `harness/conformance` builds `main.bend` once, feeds the same seeded event sequences to the Bend binary (stdin, 5 numbers per event) and to the Go core, and compares the final state plus per-effect-kind counts and sums of ids and amounts. A linear scan reports the first divergent event. `TestHarnessCatchesM1` checks that mutant M1 diverges; `TestBendRejectsMalformedInput` checks 14 bad inputs exit nonzero.
- Result: 500 sequences, 75,787 events, Go and Bend agree (`ok  github.com/derangga/learn-formal-verification/harness/conformance`). M1 is caught at seed 4, first divergent event 224 (`ChargeReqRecv o0 a3 Approve`). Coverage counts: out-of-range o 28,456; a = 0 1,611; crashes 3,230 / 3,137; delivered while receiver down 29,591; provider replay 858. Only 2.4% of events produce an effect, so most random events are no-ops.
- Machine time (hyperfine, 3 runs, noisy machine): compile of `main.bend` 8.225 s +/- 1.179 s; 500-sequence test including one compile 10.115 s +/- 0.429 s; one 300-event Bend run 7.8 ms.
- Size: `main.bend` 328 lines, `conformance.go` 325, `conformance_test.go` 86.
- Friction: Bend cannot match on a computed value and has no mutual recursion; `Fail` and `Done` are taken by Base; `File.read` takes a fixed size, so input of 16 MiB or more is rejected; compiling takes 6 to 8 s, well above the Phase 0 estimate of 1.5 s.
- Caveat: the harness was run against `code.bend` as of commit dc3d570. If the proof task edits `code.bend`, the harness must be re-run.
- Details: [docs/results/uc1-harness.md](docs/results/uc1-harness.md)

### 4.9 UC1 Bend port, laws and proofs

- Date and time: 2026-11-22, 10:13 to about 10:48 UTC (`date -u` by the agent).
- Tool: Bend 2.0.40, plain gate.
- Use case: UC1.
- What was done: `spec.bend` (types and every helper the laws read), `code.bend` (the `step` port), `LAWS.bend` (46 laws: `init_inv`, `inv_step`, `inv_run`, P1, P2a, P2b(a)-(d), P3 step and run, and pins for A1-A13 including rule-D and guard-fail pins), `PROOF.bend` (46 `def Laws.*` plus 162 lemmas). `spec.bend` and `LAWS.bend` were committed (dc3d570) before any proof and have not changed since. They are a draft the user has not approved yet. (Update 2026-11-23: the user approved both files, including the added pins and their hypotheses.)
- Orchestrator decisions on the law statements: rule-D pins (`pin_rule_d_order_down`, `pin_rule_d_prov_down`, `pin_rule_d_range`) and guard-fail pins (`pin_place_order_other`, `pin_flush_charge_req_other`, `pin_flush_refund_req_other`, `pin_flush_reply_other`) were added because the contract says "Frame F and rule D apply to every row". Pins take "receiving service up" and "o in range" as hypotheses. A8 is split into five laws.
- Authoring time: about 35 minutes. Failed proof iterations: 12 of 15 (each a `bend PROOF.bend` run with a real error; list in the results file). Not counted: about 9 compile errors in `code.bend` during the port, and one deliberate mutation check.
- Machine time (hyperfine `--warmup 1 --runs 5 -N`): warm 6.484 s +/- 0.099 s; first single run 6.97 s (not a true cold start).
- Result: all 46 laws proved, plain gate only (`--verdict` cannot run). Re-run by the orchestrator (verbatim):

```text
$ bend bend/uc1/PROOF.bend
ALL PROOFS CHECK
Use --verdict for mathematical validity.
rc=0
$ bash bend/probes/run.sh >/dev/null; echo $?
0
```

- Escape-hatch scan: `grep -cE '@unsafe|\?|import "' bend/uc1/PROOF.bend` gives 0; 46 `law` lines and 46 `def Laws.` lines.
- Size: `spec.bend` 390, `code.bend` 203, `LAWS.bend` 433, `PROOF.bend` 2634 lines. Many proof arms were generated with throwaway Python scripts (not committed).
- H3 note: P2b(a), (b), (d), P3, A12 and A13 hold for every state, reachable or not; only `inv_*`, P1, P2a and P2b(c) need `inv`. More in the results file, section 11.
- Friction: erased versus live variables, affine use (`+` on hypotheses that are functions or pairs is rejected), no match on computed values, `case _ _` does not refine, one error reported per run.
- Details: [docs/results/uc1-bend.md](docs/results/uc1-bend.md)

### 4.10 UC1 TLA+ spec (TLC)

- Date and time: 2026-11-22, 10:07 to about 11:30 UTC.
- Tool: TLA+ (TLC 2.18, OpenJDK 21), `-Xmx700m`, 2 workers (heap and workers are not bounds).
- Use case: UC1.
- What was done: `spec/tla/UC1.tla` with the nine contract variables, `Step` for A1-A11 with rules F and D, a bag network with Drop, Duplicate (`DupMax` per message value), reorder, Crash and Restart. Invariants `TypeOK`, `Inv`, `NoDoubleCharge`, `RefundNeverExceedsCharge`; action properties `RefundedOnlyFromPaid`, `TerminalStable` and the 13 pins. 15 reachability witness cfgs and `UC1_buggy` (M1).
- Bounds (`UC1.cfg`, exactly as approved in UC1.md Q11): `N = 2`, `Amounts = {5}`, `DupMax = 2`, `MaxCrashes = 1` per service, `MaxRetries = 2` per order. No CONSTRAINT, no SYMMETRY.
- Result: **wall, not verified.** TLC did not finish `UC1.cfg` at the contract bounds. It was stopped after 62 minutes: `80,850,928 states generated, 9,079,945 distinct states found, 4,644,890 states left on queue`, no violation seen. That is not a pass. Final distinct count, depth and wall time are not recorded. The agent's unmeasured estimate for the full N = 2 space is 10^11 to 10^12 distinct states.
- Context only (scratch cfg, not the contract bound): N = 1 with the other bounds unchanged completes with `No error has been found`, 13,071,033 generated, 1,156,996 distinct, depth 34, 19 min 35 s.
- Non-vacuity: all 15 `UC1_reach_*` cfgs are violated as required (Paid depth 6, Refunded 7, Failed, provider replay 6, replay caused only by a duplicate 6, refund at the provider 9, `WireRefundReq` 8, `WireDeclined` 5, crash 2, and others; details in the results file). The out-of-range half of rule D is not exercised in TLC, because the spec only generates `o` in `OrdIds`.
- Buggy variant: `UC1_buggy` (M1) gives `Error: Invariant NoDoubleCharge is violated.` with a 6-state trace (PlaceOrder, Flush, Duplicate, Deliver, Deliver), 2,340 distinct states, depth 6.
- Authoring time: about 1 hour 20 minutes, mostly waiting on TLC. Failed iterations: 0.
- Machine time: hyperfine not run for `UC1.cfg` (no finished run to time).
- Size: `UC1.tla` 438+ lines, `UC1.cfg` 26 lines.
- Decision needed from the user (bounds change only with approval): SYMMETRY on `OrdIds`, N = 1 as the checked bound, lower `DupMax` or `MaxRetries`, or a bigger machine. A `VIEW` that drops `lastEvent`/`lastFx` is unsound for the action properties as written. Resolved 2026-11-23, see 4.14.
- Friction: the state space at N = 2; a TLC run started with `&` dies when the tool call ends; TLC writes `*_TTrace_*` files into `spec/tla` on a violation (use `-noGenerateSpecTE`).
- Details: [docs/results/uc1-tla.md](docs/results/uc1-tla.md)

### 4.11 UC1 mutants in Go, harness, Bend and TLA+

- Date and time: 2026-11-22, about 10:52 to 11:30 UTC.
- Tools: Go checker tests, conformance harness, Bend 2.0.40 plain gate, TLC 2.18.
- Use case: UC1.
- What was done: the six mutants of UC1.md section 5 (M1, M2a, M2b, M3, M4, M5) written in every tool: `mutants/uc1` (Go step variants plus a checker with `core.Step` as control), `bend/uc1/mutants/<id>/` (mutated `code.bend`, byte-identical `LAWS.bend`, `run.sh` with EXPECT files), `spec/tla/UC1_buggy_m*.tla` (minimal diffs of `UC1.tla`, same bounds as `UC1.cfg`).
- Result: every mutant is rejected by every tool. No survivor.

| Mutant | Go checks that fail | Harness (seed, first divergent event) | Bend first failing lemma | TLA+ violated property (trace states) |
|---|---|---|---|---|
| M1 | A13, A8, Inv, P1 | 4, 224 | `pp_charge_recv` | `NoDoubleCharge` (6) |
| M2a | A12, A6, P2b(a), P2b(b), P3 | 1, 10 | `ps_refund_order_other` | `RefundedOnlyFromPaid` (2) |
| M2b | A10, Inv, P2a | 2, 152 | `sok_step` | `RefundNeverExceedsCharge` (11) |
| M3 | A13, A8, Inv, P1, ProvApplyCharge | 1, 4 (contract events only) | `pp_apply` | `NoDoubleCharge` (8) |
| M4 | A12, A4, Inv, P2b(c), P3 | 1, 47 | `op_pay_ok` | `TerminalStable` (9) |
| M5 | A13, A8 only | 10, 77 | `ps_replay_declined` | `PinProvRecStable` (6) |

- M5 behaves as the contract predicts: P1-P3 and Inv do not catch it, only the A8/A13 pins do (Q7 gap). A TLC run of the non-pin properties on M5 was stopped after about 12 minutes (1,568,242 distinct, no violation), so its survival of P1-P3 in TLA+ is partial evidence; the Go checks show it fully.
- Caveats: Bend reports only the first failing lemma, so it rejects M2b and M4 through `Inv` and M2a and M5 through pins, not through the P-law that section 5 names. Bend M3 stores `pending` in the `amt` field and emits `Charge(o, 0)`, because the frozen files fix `ProvRec` at five fields; Go and TLA+ use a separate field. The M3 and M5 Bend `PROOF.bend` copies were edited (M3 adds a lemma for the new event; M5 splits one case so the failure lands on the bug, not a stale proof shape). Paired with the correct code the M5 edit still checks; the M3 edit could not be validated that way. The harness cannot send `ProvApplyCharge`, so it rejects M3 through the deferred charge, not the race. The M2b A10 run in TLA+ was not done.
- Re-run (orchestrator): `bash bend/uc1/mutants/run.sh` prints PASS for m1 to m5 and exits 0; `just check-tla-buggy` prints `6 buggy spec(s) rejected as expected`.
- Details: [docs/results/uc1-mutants.md](docs/results/uc1-mutants.md)

### 4.12 UC1 services: order and payment provider over outbox plus HTTP

- Date and time: 2026-11-22, about 11:55 to 12:30 UTC.
- Tool: Go 1.26.10, chi v5.5.0, modernc.org/sqlite v1.62.0 (no CGO). The user fetched sqlite into the module cache outside the sandbox; the build runs offline (`GOPROXY=off`).
- Use case: UC1.
- What was done: `services/payment` with an order service and a provider service, each with its own SQLite file. Every request is one transaction (load the slot, `core.Step`, save the half-slot, ledger and outbox rows). Outbound messages go through `internal/sim` `Net`; a single-threaded `Cluster` driver delivers them through the chi handlers in-process (sockets only in the `ListenLocal` test, which binds 127.0.0.1 only). Crash closes the SQLite handle; restart reopens it and the outbox survives. Crash point: after commit, before the next send.
- Result: `go test ./services/... -count=1` passes, 10 tests. Seeded fault runs (200 seeds x 150 steps) assert P1 on ledger rows, P2a and `Inv` after every step; a differential test (100 seeds) checks `Snapshot()` equals the fold of `core.Step` over the applied events. Coverage counts include 43 duplicates delivered, 152 drops, 905 crashes, 71 provider dedupes, 8 refund rows.
- Limits: `synchronous=OFF` is durable only for the simulated crash (clean close), not power loss; services reject requests while down before calling `Step`, which duplicates rule D's up check; the issuer is consulted on every `ChargeReqRecv`, even when `Step` ignores the decision.
- Size: `services/payment` 1,055 lines with tests.
- Friction: the module download needed the user (sandbox allowlist); tests take about 76 s because snapshots open a temporary handle on a crashed service.
- Details: [docs/results/uc1-services.md](docs/results/uc1-services.md)

### 4.13 UC1 replay of TLC traces against the Go services

- Date and time: 2026-11-22, 12:10 to 12:17 UTC (agent timestamps).
- Tools: TLC 2.18 (`-dumpTrace json`), Go test against `services/payment` `Cluster`.
- Use case: UC1.
- What was done: `harness/tlcreplay/gen.sh` (run with `go generate`) dumps JSON traces for the 15 reach witnesses and the 6 buggy specs into `testdata/`. The test maps each TLA+ action to a `Cluster` call (issuer decisions scripted from the trace) and compares slots, up flags and the in-flight message bag after every step.
- Result: all 15 reach traces replay with every state equal. On each buggy trace the correct service leaves the buggy model at the bug step (M1 step 5, M2a step 1, M2b step 10, M3 step 4, M4 step 8, M5 step 5), and the violated property does not occur on the service. A tamper test shows the comparison can fail.
- Not covered: no reach trace contains a Drop or a Restart; `dup`, `crashes`, `retries` and `lastFx` are not compared; the service-side check of `RefundedOnlyFromPaid` covers clauses (a) and (b) only, not (c) and (d) (open finding); M3's `ProvApplyCharge` has no service counterpart and is skipped (reported as a divergence).
- How hard: about 7 minutes of agent time. TLC's JSON trace dump was enough; the friction was mapping a bag of message values onto the sim's indexed copies, and the issuer being consulted on every charge request, which ties the script to the trace shape.
- Details: [docs/results/uc1-replay.md](docs/results/uc1-replay.md)

### 4.14 UC1 TLC checked bound set to N = 1

- Date and time: 2026-11-23, about 01:00 to 01:15 UTC.
- Tool: TLA+ (TLC 2.18), 2 workers, default 274 MB heap (run settings, not bounds).
- Use case: UC1.
- What was done: the user approved N = 1 as the checked bound and N = 2 as a recorded wall. `spec/tla/UC1.cfg` now has `N = 1`. The unchanged N = 2 contract cfg moved to `spec/tla/UC1_wall_n2.cfg`, which `just check-tla` skips (`*_wall*`). The reach and buggy cfgs keep N = 2. The user also approved `spec.bend` and `LAWS.bend` (with the added pins), the TLA+ modelling choices of 4.10 (a no-op RetryTimeout still uses up MaxRetries, client and flush events always enabled, DupMax per message value) and the M3 Bend encoding.
- Bounds: `N = 1`, `Amounts = {5}`, `DupMax = 2`, `MaxCrashes = 1` per service, `MaxRetries = 2` per order. No CONSTRAINT, SYMMETRY or VIEW.
- Result: `Model checking completed. No error has been found.` 13,071,033 generated, 1,156,996 distinct, depth 34, `Finished in 05min 01s`. Same counts as the earlier scratch run, which took 19 min 35 s on 1 worker while sharing the cores.
- Lost coverage: TLC no longer checks two orders at once (interleaved messages, a shared crash budget, rule D with another order's messages in flight). The Bend laws (no bound) and the Go tests (2 or 3 slots) still cover it.
- Details: [docs/results/uc1-tla.md](docs/results/uc1-tla.md), section "Checked bound (N = 1)".

### 4.15 UC2 Go pure core

- Date and time: 2026-11-23, about 03:00 to 03:50 UTC.
- Tool: Go 1.26.10 (reference `Step`, no verification tool).
- Use case: UC2 stock reservation.
- What was done: `internal/uc2/core` `Step` (S0-S9, `int64`, ghost `confirmedAt`/`returned`/`up`), `Inv` and one exported predicate per property, and the 24 Go tests named in `properties/UC2.md` sections 3 and 4. The tests run seeded random event lists (drop, duplicate, reorder, crash, unknown SKUs, 1 to 3 SKUs) with 27 non-vacuity counters that must all fire. After review, S0 is counted per event kind, crash-while-down and restart-while-up are counted, and S11 counts accepted first deliveries (Reserve 1510, Confirm 307, Expire 595). The path is `internal/uc2/core` to match UC1; the bead text said `internal/inventory/core`.
- Authoring time: about 40 minutes (agent estimate, no timer). Failed iterations: 1 (a P1 test asserted all of `Inv`). Review rounds: 1 (3 test and comment fixes).
- Machine time (hyperfine): not recorded. `go test` takes 6.4 s.
- Result: `go vet ./internal/uc2/... ./services/inventory/... && go test ./internal/uc2/... ./services/inventory/... -count=1` gives `ok  github.com/derangga/learn-formal-verification/internal/uc2/core 6.351s` (re-run by the orchestrator).
- Size (lines): `core.go` 435, `core_test.go` 608.
- Friction or walls hit: UC2.md section 5 says M5a (plain unguarded subtraction) is killed by "P1, P2, P1b, S3". In Go only P1 and S3 kill it. With signed counters `available` and `reserved` move by exactly `qty`, so P2 and P1b still hold. The kill table looks wrong for M5a. The contract is frozen, so this goes to the user at checkpoint 4. M7 also breaks P3b in Go, an extra kill. Temporary mutants M1, M2, M5a, M6 and M7 were each killed, then reverted.
- Details: [docs/results/uc2-core.md](docs/results/uc2-core.md)

### 4.16 UC2 inventory service

- Date and time: 2026-11-23, about 03:15 to 04:10 UTC.
- Tool: Go (chi, modernc.org/sqlite, internal/sim).
- Use case: UC2 stock reservation.
- What was done: `services/inventory` runs one transaction per event: load the state, call `core.Step`, save the state and outbox rows. It has its own SQLite file and chi handlers bound to 127.0.0.1. `sim.Net` carries requests and replies, and `sim.Clock` drives `Tick`. A crasher crashes the service after commit. The durable `up` flag is part of the state, and `Tick` and `Restart` reach `Step` while the service is down. Seeded fault runs check P1, P2, `Inv` and P3b on the persisted state. A differential test checks that the persisted state and outbox equal the fold of `core.Step` over the logged events.
- Authoring time: about 35 minutes (agent estimate). Failed iterations: 1 (a test used a crash budget of 0).
- Machine time (hyperfine): not recorded. `go test` takes 36 s.
- Result: `ok  github.com/derangga/learn-formal-verification/services/inventory 35.971s` (same command as 4.15). The `Inv` fault test ran 150 seeds of 150 actions: 1304 duplicates, 1327 drops, 2524 lost events, 356 crashes, 1008 ticks while down, 57 releases. The differential test ran 100 seeds, all equal.
- Size (lines): `service.go` 290, `store.go` 133, `http.go` 72, `service_test.go` 368.
- Friction or walls hit: the UC1 approach, where a down service refuses every request, does not work here, because `Tick` and `Restart` must reach `Step`. The crash is a clean close and reopen, not a power loss (`synchronous(OFF)`, the same setting as UC1). The service rewrites the whole state on every request. Only 30 confirms happened per 150 runs; directed tests cover the confirm path.
- Details: [docs/results/uc2-services.md](docs/results/uc2-services.md)

## 5. Findings so far

Phase 0 observations only, each from the cited results file. None is a verdict on H1, H2 or H3. Every Bend check below is the plain gate; `--verdict` has not run.

- TLC pays JVM start-up on every run, even on an 11-distinct-state model. Warm (10 runs, 2 warm-up): mean 1.619 s, min 1.441 s, max 1.952 s. Cold (1 sample): 1.395 s, which is only the first measured run. The file puts the JVM start-up floor at about 1.4 to 1.5 s. (phase0-tlc.md)
- The plain Bend gate took 385.4 ms +/- 15.7 ms (10 runs, 2 warmups) on add_zero, and about 0.4 s on the small smoke proof (357.7 ms minimum, single runs 0.397 s and 0.396 s). `run.sh` over 14 probes took 5.550 s ± 0.290 s, about 0.40 s per probe (derived). (phase0-bend-guide.md, phase0-bend-smoke.md, phase0-bend-probes.md)
- Authoring-time estimates so far: TLC smoke about 10 minutes, Bend smoke about 10 minutes with 5 failed proof iterations. They are estimates on trivial examples and are not comparable: the Bend figure includes reading the guide. (phase0-tlc.md, phase0-bend-smoke.md)
- Laws that only bound the state let behaviour mutants survive: with an upper-bound law plus `Reset -> 0`, mutants (a) Inc=0 and (b) cap 2 still printed `ALL PROOFS CHECK`. The source's conclusion is that laws must pin the step's effect and every mutant must be run through the gate. (phase0-bend-smoke.md section 5)
- The Bend gate rejected 14 of 14 known false-law attacks (12 on the merits, 2 escape-hatch detector regressions), including termination, affine and dead/live-mode attacks. The source states this is not a proof of soundness. (phase0-bend-probes.md)
- Embedding events in generated Bend source fails past about 2,500 list elements (2,500 passes, 3,000 fails; 10,000 works in 500-element chunks). (phase0-bend-io.md section 6)
- Interpreted stdin overflows above roughly 20 KB of input; the compiled binary does not (100,000 events on stdin took 63 ms). Bend has no Base stdin effect; `File.open("/dev/stdin", "r")` works on Linux. (phase0-bend-io.md sections 4, 5, 8)
- Tested only: a def calling the Base foreign effect `IO.print` still gave `ALL PROOFS CHECK`, and the guide report treats Base's own foreign effects as exempt from the gate (hatch 12). Other effects (`IO.args`, `File.*`) were not tested for this. (phase0-bend-guide.md section 4)
- In Base, F32 and the handle/channel/atomic laws are axioms; the guide report recommends modelling with `Nat`/`U32`. (phase0-bend-guide.md section 7)
- `U32` wraps, so events and state in the Bend port must fit `U32`. (phase0-bend-io.md section 8)

## 6. Entry template

Copy for each new task. Fields follow `docs/handover.md` section 8 and `CLAUDE.md`. Write "not recorded" for any field you do not have.

```markdown
### N.N <task name>

- Date and time:
- Tool:
- Use case:
- What was done:
- Bounds (TLC only), state count, distinct states, wall time:
- Authoring time (spec or proof), AI iterations and how many, failed iterations:
- Machine time (hyperfine), cold:
- Machine time (hyperfine), warm:
- Result (paste the real command and output for any "verified" or "proved" claim; Bend: plain gate only unless `--verdict` ran):
- Size (lines):
- Friction or walls hit:
- Details: link to docs/results/<file>.md
```

Also add or update the row in the summary table (section 3). If a Bend claim is ever accepted when false, record it in section 1 first.
