# Phase 0: TLC smoke test (cold and warm timing)

Date: 2026-11-22. Spec: `spec/tla/Smoke.tla`, config: `spec/tla/Smoke.cfg`.

## Versions

- TLC: `TLC2 Version 2.18 of Day Month 20?? (rev: 5b3286b)` (nixpkgs `tlaplus-1.8.0`, wrapper `tlc` from `.nix/env.sh`; the "Day Month 20??" placeholder is how this nixpkgs build prints its date)
- Java: `/nix/store/w0lnnm3w2hpzs42pfz4464ghzv31v1gn-openjdk-21.0.13.1+2/bin/java -version` (the `java` the `tlc` wrapper execs; it is not on PATH itself). The handover flake sketch listed `jdk17`, but `tlaplus` (TLC 2.18) uses the default JRE, which is OpenJDK 21.0.13.1.

```text
openjdk version "21.0.13.1" 2026-11-17
OpenJDK Runtime Environment (build 21.0.13.1+2-nixos)
OpenJDK 64-Bit Server VM (build 21.0.13.1+2-nixos, mixed mode, sharing)
```

- hyperfine: 1.20.0
- Machine as reported by TLC: Linux 6.18.54 amd64, 2 cores, 274MB heap, 1 worker.

## Bounds

`Smoke.cfg`: `CONSTANT N = 10`. `Smoke.tla` has `ASSUME N \in Nat`. Counter `count` runs 0..N. Invariants: `TypeOK` (`count \in 0..N`), `Bounded` (`count <= N`). No other bounds or assumptions. `Done` is an explicit stutter at `count = N` so TLC does not report a deadlock.

## Sandbox note

TLC writes its parsed standard modules to `java.io.tmpdir`, which defaults to `/tmp`; that is read-only in the sandbox (the first attempt failed with `FileSystemException: /tmp/tlc-...: Read-only file system`). `.nix/env.sh` now exports `JAVA_TOOL_OPTIONS="-Djava.io.tmpdir=${TMPDIR:-/tmp}"`, so sourcing it is enough. This makes the JVM print a `Picked up JAVA_TOOL_OPTIONS: ...` line on stderr, kept in the output below. `-metadir $TMPDIR/...` keeps the states dir out of the repo. Output below was captured with only `source .nix/env.sh` and stdout and stderr redirected to a file, then `echo "exit=$?"`.

## Run: invariants hold

```bash
source .nix/env.sh
mkdir -p $TMPDIR/tlc-smoke
tlc -metadir $TMPDIR/tlc-smoke -config spec/tla/Smoke.cfg spec/tla/Smoke.tla > $TMPDIR/tlc-ok.txt 2>&1; echo "exit=$?" >> $TMPDIR/tlc-ok.txt
```

Output (verbatim, last line is the exit code):

```text
Picked up JAVA_TOOL_OPTIONS: -Djava.io.tmpdir=/tmp/claude-1001
TLC2 Version 2.18 of Day Month 20?? (rev: 5b3286b)
Running breadth-first search Model-Checking with fp 13 and seed -3350163262965645759 with 1 worker on 2 cores with 274MB heap and 64MB offheap memory [pid: 10] (Linux 6.18.54 amd64, N/A 21.0.13.1 x86_64, MSBDiskFPSet, DiskStateQueue).
Parsing file /home/claude/Documents/learn-formal-verification/spec/tla/Smoke.tla
Parsing file /tmp/claude-1001/tlc-18309845763512427209/Naturals.tla (jar:file:/nix/store/8j47ydmq95jl0wifq3jqc6sbylny2xm9-tlaplus-1.8.0/share/java/tla2tools.jar!/tla2sany/StandardModules/Naturals.tla)
Parsing file /tmp/claude-1001/tlc-18309845763512427209/_TLCTrace.tla (jar:file:/nix/store/8j47ydmq95jl0wifq3jqc6sbylny2xm9-tlaplus-1.8.0/share/java/tla2tools.jar!/tla2sany/StandardModules/_TLCTrace.tla)
Parsing file /tmp/claude-1001/tlc-18309845763512427209/TLC.tla (jar:file:/nix/store/8j47ydmq95jl0wifq3jqc6sbylny2xm9-tlaplus-1.8.0/share/java/tla2tools.jar!/tla2sany/StandardModules/TLC.tla)
Parsing file /tmp/claude-1001/tlc-18309845763512427209/TLCExt.tla (jar:file:/nix/store/8j47ydmq95jl0wifq3jqc6sbylny2xm9-tlaplus-1.8.0/share/java/tla2tools.jar!/tla2sany/StandardModules/TLCExt.tla)
Parsing file /tmp/claude-1001/tlc-18309845763512427209/Sequences.tla (jar:file:/nix/store/8j47ydmq95jl0wifq3jqc6sbylny2xm9-tlaplus-1.8.0/share/java/tla2tools.jar!/tla2sany/StandardModules/Sequences.tla)
Parsing file /tmp/claude-1001/tlc-18309845763512427209/FiniteSets.tla (jar:file:/nix/store/8j47ydmq95jl0wifq3jqc6sbylny2xm9-tlaplus-1.8.0/share/java/tla2tools.jar!/tla2sany/StandardModules/FiniteSets.tla)
Semantic processing of module Naturals
Semantic processing of module Sequences
Semantic processing of module FiniteSets
Semantic processing of module TLC
Semantic processing of module TLCExt
Semantic processing of module _TLCTrace
Semantic processing of module Smoke
Starting... (2026-11-22 01:53:29)
Computing initial states...
Finished computing initial states: 1 distinct state generated at 2026-11-22 01:53:29.
Model checking completed. No error has been found.
  Estimates of the probability that TLC did not check all reachable states
  because two distinct states had the same fingerprint:
  calculated (optimistic):  val = 6.0E-19
12 states generated, 11 distinct states found, 0 states left on queue.
The depth of the complete state graph search is 11.
The average outdegree of the complete state graph is 1 (minimum is 0, the maximum 1 and the 95th percentile is 1).
Finished in 01s at (2026-11-22 01:53:29)
exit=0
```

Result: no error, exit 0; 12 states generated, 11 distinct states.

## Run: the invariant is real (false invariant gives a violation)

Variant kept in `$TMPDIR/neg/` only (not in `spec/tla`): `Smoke.tla` with one line changed, `Bounded == count < N` (false once `count` reaches 10); `Smoke.cfg` identical.

```bash
source .nix/env.sh
sed 's/^Bounded == .*/Bounded == count < N  \* deliberately false: count reaches N/' spec/tla/Smoke.tla > $TMPDIR/neg/Smoke.tla
cp spec/tla/Smoke.cfg $TMPDIR/neg/Smoke.cfg
tlc -metadir $TMPDIR/tlc-neg -config $TMPDIR/neg/Smoke.cfg $TMPDIR/neg/Smoke.tla > $TMPDIR/tlc-neg.txt 2>&1; echo "exit=$?" >> $TMPDIR/tlc-neg.txt
```

Output (verbatim, last line is the exit code):

```text
Picked up JAVA_TOOL_OPTIONS: -Djava.io.tmpdir=/tmp/claude-1001
TLC2 Version 2.18 of Day Month 20?? (rev: 5b3286b)
Running breadth-first search Model-Checking with fp 25 and seed 6202353668546046560 with 1 worker on 2 cores with 274MB heap and 64MB offheap memory [pid: 41] (Linux 6.18.54 amd64, N/A 21.0.13.1 x86_64, MSBDiskFPSet, DiskStateQueue).
Parsing file /tmp/claude-1001/neg/Smoke.tla
Parsing file /tmp/claude-1001/tlc-7464378052166550393/Naturals.tla (jar:file:/nix/store/8j47ydmq95jl0wifq3jqc6sbylny2xm9-tlaplus-1.8.0/share/java/tla2tools.jar!/tla2sany/StandardModules/Naturals.tla)
Parsing file /tmp/claude-1001/tlc-7464378052166550393/_TLCTrace.tla (jar:file:/nix/store/8j47ydmq95jl0wifq3jqc6sbylny2xm9-tlaplus-1.8.0/share/java/tla2tools.jar!/tla2sany/StandardModules/_TLCTrace.tla)
Parsing file /tmp/claude-1001/tlc-7464378052166550393/TLC.tla (jar:file:/nix/store/8j47ydmq95jl0wifq3jqc6sbylny2xm9-tlaplus-1.8.0/share/java/tla2tools.jar!/tla2sany/StandardModules/TLC.tla)
Parsing file /tmp/claude-1001/tlc-7464378052166550393/TLCExt.tla (jar:file:/nix/store/8j47ydmq95jl0wifq3jqc6sbylny2xm9-tlaplus-1.8.0/share/java/tla2tools.jar!/tla2sany/StandardModules/TLCExt.tla)
Parsing file /tmp/claude-1001/tlc-7464378052166550393/Sequences.tla (jar:file:/nix/store/8j47ydmq95jl0wifq3jqc6sbylny2xm9-tlaplus-1.8.0/share/java/tla2tools.jar!/tla2sany/StandardModules/Sequences.tla)
Parsing file /tmp/claude-1001/tlc-7464378052166550393/FiniteSets.tla (jar:file:/nix/store/8j47ydmq95jl0wifq3jqc6sbylny2xm9-tlaplus-1.8.0/share/java/tla2tools.jar!/tla2sany/StandardModules/FiniteSets.tla)
Semantic processing of module Naturals
Semantic processing of module Sequences
Semantic processing of module FiniteSets
Semantic processing of module TLC
Semantic processing of module TLCExt
Semantic processing of module _TLCTrace
Semantic processing of module Smoke
Starting... (2026-11-22 01:53:31)
Computing initial states...
Finished computing initial states: 1 distinct state generated at 2026-11-22 01:53:31.
Error: Invariant Bounded is violated.
Error: The behavior up to this point is:
State 1: <Initial predicate>
count = 0

State 2: <Inc line 12, col 8 to line 12, col 38 of module Smoke>
count = 1

State 3: <Inc line 12, col 8 to line 12, col 38 of module Smoke>
count = 2

State 4: <Inc line 12, col 8 to line 12, col 38 of module Smoke>
count = 3

State 5: <Inc line 12, col 8 to line 12, col 38 of module Smoke>
count = 4

State 6: <Inc line 12, col 8 to line 12, col 38 of module Smoke>
count = 5

State 7: <Inc line 12, col 8 to line 12, col 38 of module Smoke>
count = 6

State 8: <Inc line 12, col 8 to line 12, col 38 of module Smoke>
count = 7

State 9: <Inc line 12, col 8 to line 12, col 38 of module Smoke>
count = 8

State 10: <Inc line 12, col 8 to line 12, col 38 of module Smoke>
count = 9

State 11: <Inc line 12, col 8 to line 12, col 38 of module Smoke>
count = 10

11 states generated, 11 distinct states found, 0 states left on queue.
The depth of the complete state graph search is 11.
Finished in 01s at (2026-11-22 01:53:31)
Trace exploration spec path: /tmp/claude-1001/neg/Smoke_TTrace_1795312410.tla
exit=12
```

## Timing

Definition of "cold" used here: a fresh JVM process (the benchmark runs in a new `bash --noprofile --norc`) with an empty metadir (`--prepare` deletes and recreates `$TMPDIR/tlc-bench` before every run, cold and warm alike). The OS page cache was not dropped (no sudo), and TLC had already been run several times in this session before measuring. So "cold" is not a cold disk or a cold machine; it is only the first measured run. "Warm" means the same command after 2 discarded warm-up runs. Every run, cold or warm, starts a new JVM, so every TLC run pays JVM start-up (about 1.4 to 1.5 s floor on this model, which has only 11 states).

Result: the data shows no cold/warm gap. There is one cold sample, and it lies within about 1.2 sigma of the warm mean (see the numbers below).

Script (run as `bash --noprofile --norc $TMPDIR/bench.sh` from the repo root):

```bash
set -e
source .nix/env.sh
CMD='tlc -metadir $TMPDIR/tlc-bench -config spec/tla/Smoke.cfg spec/tla/Smoke.tla'
PREP='rm -rf $TMPDIR/tlc-bench; mkdir -p $TMPDIR/tlc-bench'
echo "### COLD"
hyperfine --runs 1 --prepare "$PREP" --export-json $TMPDIR/cold.json "$CMD"
echo "### WARM"
hyperfine --warmup 2 --runs 10 --prepare "$PREP" --export-json $TMPDIR/warm.json "$CMD"
```

hyperfine output (verbatim):

```text
### COLD
Benchmark 1: tlc -metadir $TMPDIR/tlc-bench -config spec/tla/Smoke.cfg spec/tla/Smoke.tla
  Time (abs ≡):         1.395 s               [User: 1.795 s, System: 0.092 s]
 
### WARM
Benchmark 1: tlc -metadir $TMPDIR/tlc-bench -config spec/tla/Smoke.cfg spec/tla/Smoke.tla
  Time (mean ± σ):      1.619 s ±  0.186 s    [User: 1.925 s, System: 0.106 s]
  Range (min … max):    1.441 s …  1.952 s    10 runs
 
```

Summary: cold (1 run) 1.395 s; warm (10 runs, 2 warm-up) mean 1.619 s +- 0.186 s, min 1.441 s, max 1.952 s. An earlier run of the same benchmark before `ASSUME N \in Nat` was added gave cold 2.054 s and warm mean 1.691 s +- 0.332 s (min 1.471 s, max 2.600 s); it is not pasted here. The two cold samples straddle the warm mean, which is more evidence that run-to-run noise, not cold start, dominates.

## Log entry (for experiment-log.md, handover section 8)

- Date and time: 2026-11-22, about 01:50 to 01:55 UTC.
- Tool: TLA+ (TLC 2.18, OpenJDK 21.0.13.1).
- Use case: Phase 0 smoke test (bounded counter, not a use case).
- What was done: wrote `Smoke.tla` and `Smoke.cfg`, ran TLC with invariants, ran a false-invariant variant to confirm a violation, timed with hyperfine.
- Authoring time: about 10 minutes, 1 AI iteration for the spec itself plus 1 to fix the environment (read-only `/tmp`); then 1 revision round for review fixes (adding `ASSUME`). These are estimates, not measured.
- Machine time: cold 1.395 s (1 run), warm 1.619 s +- 0.186 s (10 runs). No real cold/warm gap (see Timing).
- Result: no error; 12 states generated, 11 distinct, depth 11; false invariant gives a violation (exit 12).
- Size: `Smoke.tla` 22 lines, `Smoke.cfg` 4 lines.
- Friction: JVM temp dir `/tmp` is read-only in the sandbox (fixed via `JAVA_TOOL_OPTIONS` in `.nix/env.sh`); cannot drop the page cache without sudo, so no true cold measurement; `java` is not on PATH, only reachable through the `tlc` wrapper.
