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
| UC1 | TLA+ | not started | | | | | |
| UC1 | Bend | not started | | | | | |
| UC1 | harness | not started | | | | | |
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
