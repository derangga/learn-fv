# Bend 2 and TLA+ compared on two small systems

Written 23 November 2026, after checkpoint 4 (UC2 approved). Git HEAD at writing: `8131d4d`.

## How to read this report

This report compares two tools on two small safety systems: TLA+ with the TLC model checker, and Bend 2 with its proof checker.

We keep three kinds of evidence separate:

- **Measured** means a command ran and produced the number.
- **Estimated** means an agent estimated the value. All authoring times are estimates.
- **Derived** means we calculated the value from recorded numbers. The inputs are shown.

A statement marked **Opinion** is a recommendation, not an experimental result.

Every timing names its machine:

- **2-core VPS:** Linux, 2 CPU cores, and about 1.9 GB of RAM.
- **MacBook M4:** Apple M4, 10 CPU cores, and 16 GiB of memory.

A *bound* is a limit in a TLC configuration file. It can limit the number of orders, IDs, duplicate messages, crashes, retries, or clock ticks. Section 2 defines each bound used in this report.

## 1. Summary

We checked two small systems with two formal verification tools. Both tools found most of the deliberate bugs we introduced. They differed in how they check a system, how much work they need, and what a successful check guarantees.

The main findings are:

1. **Both tools caught almost every mutant they could check.** Bend rejected all 6 UC1 mutants and all 9 UC2 mutants that had Bend versions. TLC rejected all 6 UC1 mutants and 9 of 10 UC2 mutants at the contract bounds. TLC did not finish checking UC2 mutant M2 at that bound. It found the bug at a smaller bound that included duplicate messages.
2. **Bend checks were faster on the 2-core VPS.** Its gates took 6.484 seconds for UC1 and 2.358 seconds for UC2. TLC took 5 minutes 1 second for UC1 at the N=1 bound and 348.943 seconds for UC2 at the reduced bound. These TLC results are single runs, so we do not calculate a speed ratio.
3. **The tools make different guarantees.** A TLC pass covers every state TLC can reach within the configured bounds. A Bend pass covers every input described by the law, if the law is correct. We ran Bend's plain proof checker, but not its stronger `--verdict` recheck.
4. **Bend took longer to write, but reached a first complete pass sooner.** Estimated writing time was 35 minutes for UC1 and 50 minutes for UC2 in Bend. TLA+ took about 15 and 25 minutes. Despite that, the first complete Bend pass came after about 31 minutes for UC1 and 49 minutes 44 seconds for UC2. The corresponding TLA+ times were about 64 and 91 minutes. These elapsed times come from log timestamps and include TLC wait time.
5. **TLC gives a counterexample trace. Bend does not.** TLC shows the sequence of states that leads to a violation. Bend reports the first lemma whose proof no longer checks. A failed Bend proof does not show the faulty event sequence.

TLC did not finish a clean check at either contract bound. We stopped the UC1 run after 62 minutes. The UC2 run stopped after 60 minutes on the VPS. On the MacBook M4, another UC2 run filled the disk after using an 86 GB state store.

Bend has no equivalent model-size bound in these laws. However, we checked only the plain gate, not the stronger `--verdict` recheck. Its results therefore need that qualification.

**Opinion:** Start with TLA+ when you want to find out how a design can fail. Add Bend when you need a claim to hold for every event list and can maintain the proof. Use both when the system is important enough to justify the extra work.

This comparison covers only two safety systems. We did not build UC3, a lease system with a fencing token, or UC4, a liveness check. The results do not support conclusions about either one.

### Results at a glance

Each timing below names its machine and bound. Do not compare results from different machines as if they were measured under the same conditions.

| Criterion | TLA+ with TLC | Bend 2 |
|---|---|---|
| Time per run | UC1 N=1: 5 min 1 s. UC2 reduced bound: 348.943 s. Both on the 2-core VPS, single runs. MacBook M4: 23 s and 28 s, also single runs. | UC1: 6.484 s. UC2: 2.358 s warm. Both on the 2-core VPS. MacBook M4: the full `just prove-bend` command took 5 s in one run. |
| Time to first complete pass | UC1: about 64 min. UC2: about 91 min. Derived from timestamps; includes TLC wait time. | UC1: about 31 min. UC2: 49 min 44 s. Derived from timestamps. |
| Estimated writing time | UC1: about 15 min. UC2: about 25 min. | UC1: about 35 min. UC2: about 50 min. |
| Failed attempts | UC1: 0 failed model checks. UC2: 2 failed model checks in the spec tasks. | UC1: 12 failed proof runs. UC2: 14 failed proof runs. Each task had a limit of 15. |
| Source size | UC1: 444 lines. UC2: 428 lines of TLA+ spec. | UC1: 3,660 lines in total. UC2: 3,145 lines in total. The `PROOF.bend` files contain 2,634 and 2,209 lines. |
| Resources | TLC visited up to 149,567,238 distinct states and used an 86 GB metadir. Two runs filled a disk. Memory use was not recorded. | Disk and memory use were not recorded. CPU use was about one core, derived from user time. |
| Guarantee | Checks every reachable state within the configured bound. Smaller bounds cover fewer cases. | Laws describe all inputs in their scope, if the laws are correct. Only the plain gate ran. Fourteen probes do not prove soundness. |
| Bug reports | Counterexample traces with 2 to 11 states. TLC found bugs in seconds to minutes. UC2 M2 was not found at the contract bound. | Reports the first failing lemma. It does not produce a counterexample trace. Rejected all 6 UC1 and 9 UC2 mutants with Bend versions. |
| Main limitation | The UC1 N=2 and UC2 contract-bound checks did not finish. | Proofs are long and need maintenance. The stronger `--verdict` recheck was not run. |

The source records two different line-count bases for the size comparison. The table above uses the `wc` counts for the TLA+ files and the total Bend source counts. The 7 to 8 times comparison in the original summary uses 471 and 461 as its TLA+ denominators. Treat that ratio as approximate, not as a direct comparison of equivalent files.

## 2. What we compared

### The two systems

We used two systems with different kinds of state and events.

**UC1: idempotent payment**

An order service and a payment provider exchange messages. The system must handle retries, duplicate and late messages, refunds, crashes, and restarts.

**UC2: stock reservation**

Customers can reserve stock, confirm a reservation, or let it expire. The system uses a logical clock and must handle duplicate and out-of-order events, crashes, and restarts.

We planned two more use cases but did not build them:

- **UC3:** a lease system with a fencing token.
- **UC4:** a liveness check on the UC1 flow.

The user decided that two use cases were enough to compare the tools (log 4.23).

### The properties we checked

Each property has a contract name, a TLA+ name, a Bend law, and a Go test. The tables below summarize the coverage recorded in the source files.

| Use case | Contract properties | Tool coverage |
|---|---|---|
| UC1 | P1 `NoDoubleCharge` (charge count is at most 1). P2a `RefundNeverExceedsCharge`. P2b `RefundedOnlyFromPaid` (clauses a to d, in one step). P3 `TerminalStable`. `Inv` is a proposed addition. Pins A1 to A13. | Bend: 46 laws. TLC: 4 invariants (`TypeOK`, `Inv`, `NoDoubleCharge`, and `RefundNeverExceedsCharge`), 2 temporal properties, and 13 pins. |
| UC2 | P1 `NonNegativeAvailable`. P2 `Conservation`. P3 `ExpiredReturnedOnce`. P4 `ExpiredNeverConfirmed`. Proposed additions: P1b `NoOversell`, P3b `ReleasedMatchesReturned`, P4a `ConfirmedBeforeDue`, P4b `ConfirmOnlyBeforeDue`, A1 `CountersMatchRecords`, and A2 `UniqueIdsKnownSku`. Pins S0 to S11. | Bend: 29 laws. P1 has no separate Bend law because the `Nat` type enforces it. TLC: 8 invariants and 14 temporal properties. S11 is derived in TLA+, not checked there. |

A *pin* states the exact result of one event. We added pins because laws that only set upper or lower bounds allowed some mutants to pass.

### Mutants and the test harness

A *mutant* is a copy of a system with one deliberate bug. We used mutants to check whether each tool could reject known faulty behavior. Each mutant was intended to represent the same bug in every tool, although a few implementations differed. Section 8 lists those differences.

The Bend port is compiled into a native binary that reads events from standard input. We sent the same seeded event sequences through the Go core function `Step` and the Bend binary. Then we compared the final state and the count of each effect.

| Use case | Sequences | Events | Result |
|---|---:|---:|---|
| UC1 | 500 | 75,787 | Go and Bend agreed. |
| UC2 | 500 | 75,094 | Go and Bend agreed. |

A TLC trace replay against the Go services exists for UC1 only. The harness is a test, not a proof.

### How the tools work

TLA+ describes a system as states and transitions. TLC is its model checker. It starts from the initial state and explores every reachable state within the limits in a `.cfg` file. It checks the properties at each state.

A *bound* sets those limits. It can restrict the number of orders, IDs, duplicate messages, crashes, retries, or clock ticks.

Bend 2 is a language with a proof checker. A *law* is a statement written in `LAWS.bend`. A *proof* is a term in `PROOF.bend` that the checker accepts or rejects.

The *plain gate* is the command `bend PROOF.bend`. It prints either `ALL PROOFS CHECK` or `SOME PROOFS FAIL`. In this report, a Bend pass means only that the plain gate printed `ALL PROOFS CHECK`. We did not run the stronger `--verdict` recheck, which uses a small kernel proven in Lean.

A *wall* is our term for a point where a tool did not finish or could not perform a task. We record it as an experimental result, not as a failure of the study.

### Bounds used in the experiment

The contract bounds are the limits requested by the frozen property contract. TLC could not finish either contract-bound check. The user approved reduced bounds on 23 November 2026 (log 4.14 and 4.22).

Bend's laws have no equivalent numeric bound. They quantify over any state and any event list within the law's scope.

| Label | Configuration file | Constants |
|---|---|---|
| UC1 contract bound | `UC1_wall_n2.cfg` | 2 orders, `Amounts={5}`, up to 2 copies per message value, 1 crash per service, 2 retries per order, and both issuer decisions. |
| UC1 N=1 bound | `UC1.cfg` | The same constants, but with 1 order. |
| UC2 contract bound | `UC2_wall_contract.cfg` | IDs 1 to 3, SKUs 0 and 1, quantities 1 to 3, TTLs 1 to 2, total stock 3, maximum clock 4, 1 crash, and up to 2 deliveries per message. This creates 42 distinct messages: 36 Reserve, 3 Confirm, and 3 Expire. |
| UC2 reduced bound | `UC2.cfg` | IDs 1 and 2, SKU 0, quantities 1 and 2, TTL 1, total stock 2, maximum clock 2, 1 crash, and no duplicate delivery. |
| UC2 duplicate bound | `UC2_dup.cfg` | ID 1, SKU 0, quantity 1, TTLs 1 and 2, total stock 1, maximum clock 3, 1 crash, and up to 2 deliveries per message. |

None of the five configurations uses `CONSTRAINT`, `SYMMETRY`, or `VIEW`.

Before the 23 November swap, `UC2.cfg` held the contract constants. Log 4.21 and older result files use that earlier meaning. This report uses the configuration names after the swap.

### What the reduced bounds leave out

A successful check at a reduced bound does not cover every case in the contract. The main gaps are:

- **UC1 N=1:** it cannot run two orders at once. It therefore misses interleaved messages, a shared crash budget, and rule D when another order has messages in flight. Bend laws and Go tests still cover two orders.
- **UC2 reduced:** it cannot combine 3 IDs, 2 SKUs, 3 quantities, TTL 2, and duplicate delivery. The reduced configuration has no duplicate delivery. The duplicate configuration uses only one ID, so two records cannot interact.
- **UC2 event coverage:** there is no unknown-SKU event. TTL is always 1 in the reduced configuration. At most two holds can run at once.
- **Crash and restart:** Crash occurs only while the service is up. Restart occurs only while it is down. The model does not exercise the opposite cases in S8 and S9.
- **Invalid requests:** TLC never fires `BadRequest` in UC2 because the configured quantities and TTLs are at least 1. It also never generates an out-of-range order ID in UC1.
- **UC2 M2:** TLC finds the double-release bug only when duplicate messages are enabled.

### Machines and tool versions

| Item | Value |
|---|---|
| 2-core VPS | 2 CPU cores, about 1.9 GB RAM, Linux 6.18.54, NixOS. |
| MacBook M4 | Apple M4, 10 CPU cores, 16 GiB, Darwin 27.2.0. |
| Bend | 2.0.40, flake input `github:bendlang/bend`, locked revision `0e2f38f759cc830849e489307f3d256a7d148288`. |
| TLC | TLC2 2.18, revision `5b3286b`; nixpkgs `tlaplus-1.8.0`. |
| Other tools | OpenJDK 21.0.13.1, hyperfine 1.20.0, clang 21.1.8, Go 1.26.10, and just 1.51.0. |

The brief and log section 2 say that runs before 23 November used the VPS, while runs from that date used the MacBook. The actual record shows a different split. Log entries 4.14 to 4.20 are dated 23 November but ran on the VPS. The first MacBook run is log 4.21 at 09:12 UTC, followed by 4.22. This report follows the log entries, not the dates.

## 3. Execution time

All times in this section are machine time. Authoring time appears in section 5.

### Start-up cost

TLC starts a Java virtual machine for every run. A small smoke model shows the minimum cost we observed on the 2-core VPS.

| Model | First measured run | Warm runs | Notes |
|---|---:|---:|---|
| Smoke, 11 distinct states | 1.395 s, one run | 1.619 s ± 0.186 s, 10 runs with 2 warm-ups. Minimum 1.441 s, maximum 1.952 s. | An earlier pair gave 2.054 s and 1.691 s ± 0.332 s. |

The first run was not a true cold run. We did not clear the page cache because the machine did not have `sudo` access. The recorded start-up floor is about 1.4 to 1.5 seconds.

Bend's start-up floor was lower on the same VPS.

| Run | Result | Source |
|---|---:|---|
| `add_zero` trial, plain gate | 385.4 ms ± 15.7 ms warm. 10 runs, 2 warm-ups. Range: 361.7 to 406.7 ms. | log 4.2 |
| Phase 0 smoke proof | Single runs: 0.397 s and 0.396 s. Hyperfine means: 510.2 ms ± 217.6 ms and 781.4 ms ± 87.7 ms. | log 4.3 |
| 14 soundness probes through `run.sh` | 5.550 s ± 0.290 s, 5 runs with 1 warm-up. About 0.40 s per probe, including script overhead. | log 4.5 |

We did not record a true cold run for either tool. The author found no on-disk proof cache for Bend.

### Time per run

| Run | Machine | Result | Evidence |
|---|---|---|---|
| `bend bend/uc1/PROOF.bend` | 2-core VPS | 6.484 s ± 0.099 s warm. 5 runs with 1 warm-up. User time: 5.600 s. System time: 0.367 s. | Measured. |
| `bend bend/uc2/PROOF.bend` | 2-core VPS | 2.358 s ± 0.143 s warm. 10 runs with 1 warm-up. User time: 2.098 s. System time: 0.169 s. | Measured. |
| UC2 Bend mutants | 2-core VPS | About 0.7 s per mutant, 6.5 s for all nine. | Measured. |
| TLC, UC1 N=1 bound | 2-core VPS | Finished in 5 min 1 s, using 2 workers. | Measured. |
| TLC, UC2 reduced bound | 2-core VPS | 348.943 s in one hyperfine run, using 2 workers. User time: 658.117 s. System time: 2.874 s. A later run finished in 5 min 32 s. | Measured. |
| TLC, UC2 duplicate bound | 2-core VPS | Finished in 41 s. | Measured. |
| `just check-tla`, 4 specs | MacBook M4 | Smoke: 12 states in the command output. UC1 N=1: 23 s. UC2 reduced: 28 s. UC2 duplicate: 3 s. One recipe run each. | Measured. |
| `just prove-bend` | MacBook M4 | Smoke, both gates, 14 probes, and both mutant runs completed in 5 s. One run. | Measured. |

The VPS is the only machine where we timed TLC and Bend in comparable ways. Bend took 2.358 seconds for UC2 and 6.484 seconds for UC1. TLC took 348.943 seconds for the UC2 reduced bound and 5 minutes 1 second for UC1 N=1.

We do not calculate a speed ratio. Each TLC figure comes from a single run.

The 348.943-second result is one hyperfine run, not a separate cold-start measurement. The log places it in a "cold" column, but `uc2-tla.md` says cold and warm runs were not separated.

The 19-minute 35-second UC1 N=1 scratch run used one worker while sharing the two cores with the N=2 run. It ran more slowly, so we do not use it as the main timing.

Do not compare the MacBook TLC times with the VPS Bend times. They come from different machines and different run styles. The log's estimate that the M4 is about six times faster is a rough estimate based on the core counts, not a measured ratio.

### How TLC time grows with the bound

TLC's work depends on the number of reachable states. Adding orders, IDs, duplicate messages, or clock ticks can increase that number quickly.

| Run | Bound | Machine | States generated | Distinct states | Depth | Result |
|---|---|---|---:|---:|---:|---|
| Smoke | Smoke model | 2-core VPS | 12 | 11 | 11 | Passed. |
| UC1 N=1 | UC1 N=1 | 2-core VPS | 13,071,033 | 1,156,996 | 34 | Passed in 5 min 1 s. |
| UC2 reduced | UC2 reduced | 2-core VPS | 16,640,898 | 2,055,926 | 20 | Passed in 348.943 s. |
| UC2 duplicate | UC2 duplicate | 2-core VPS | 2,037,539 | 312,995 | 21 | Passed in 41 s. |
| UC1 N=2 | UC1 contract | 2-core VPS | 80,850,928 | 9,079,945, with 4,644,890 on the queue | Level 16 when stopped | Stopped manually after 62 min. No violation seen. Final count, depth, and time were not recorded. |
| UC2 contract | UC2 contract | 2-core VPS | 80,574,460 | 25,051,664, with 23,427,502 on the queue | Level 8 when stopped | Stopped by `timeout 3600` after 60 min. No violation seen. |
| UC2 contract | UC2 contract | MacBook M4 | 518,943,976 | 149,567,238, with 139,187,624 on the queue | Level 10 when stopped | Aborted after about 48 min because the disk ran out of space. No violation seen. |

Every row marked as passed printed `Model checking completed. No error has been found.` The three stopped rows are not passes. They do not tell us whether the properties hold at those bounds.

Two details help explain the UC1 wall:

- After TLC started writing states to disk, its throughput fell from about 1.5 million to 0.1 million distinct states per minute. The run used a 700 MB heap and 2 workers.
- The agent estimated that N=2 might require between \(10^{11}\) and \(10^{12}\) distinct states, based on the N=1 result. This is an estimate, not a measurement.

Five smaller UC2 scratch bounds also failed to finish. They stopped at levels 10, 10, 15, 14, and 14, after reaching 3.69 million, 1.93 million, 4.44 million, 2.86 million, and 3.03 million distinct states.

UC2 grows quickly because its 42 messages can each be in six states: created zero to two times and in flight zero to two times. The state also tracks `lastEvent` and `lastFx` to meet the contract. UC1 tracks two orders, messages, duplicate counts, crash counts, retry counts, `lastEvent`, and `lastFx`.

### Why Bend time does not grow with a model bound

Bend laws do not use a model-size bound, so the checker does not enumerate a state space. Check time depends on the size and structure of the proof.

UC2's `PROOF.bend` has 2,209 lines and checks in 2.358 seconds. UC1's has 2,634 lines and takes 6.484 seconds. UC1's proofs enumerate slot shapes. UC2's proofs use generic guard Booleans.

A larger system can mean more proof text to write and maintain. It does not add a TLC-style state-space search.

### Harness time

The harness figures below come from the 2-core VPS. We used hyperfine for 3 runs unless noted.

| Item | UC1 | UC2 |
|---|---:|---:|
| Compile `main.bend` | 8.225 s ± 1.179 s. The first version took 6.309 s ± 0.158 s. | 4.880 s ± 0.784 s. |
| Test, including one compile and 500 sequences | 10.115 s ± 0.429 s. | 5.985 s ± 1.242 s. |
| One 300-event Bend run | 7.8 ms ± 1.0 ms, 10 runs. | 2.0 ms ± 0.5 ms. |
| Time per sequence, excluding compile | About 3 ms, derived and noisy. | About 4.5 ms, derived. |
| Binary size | Not recorded. | 152 KB. |

The first Phase 0 estimate put compilation at 1.5 seconds. Actual compilation took 4.880 to 8.225 seconds. Compilation dominates the UC1 harness test, so the test builds the binary once per process with `sync.Once`.

### Time to the first complete pass

This is elapsed time from the task start to the first complete pass. We calculated it from recorded UTC timestamps. It includes writing, AI iterations, and time spent waiting for TLC. It is not machine time.

| Use case | Tool | Start | First complete pass | Elapsed |
|---|---|---|---|---:|
| UC1 | TLA+ | 10:07:12 | 11:11:46, the N=1 scratch run on one worker while sharing the cores | About 64 min |
| UC1 | Bend | 10:13:09 | About 10:44, first `ALL PROOFS CHECK` | About 31 min |
| UC2 | TLA+ | About 03:30 | 05:01:04, reduced bound | About 91 min |
| UC2 | Bend | 03:59:49 | 04:49:33 | 49 min 44 s |

The TLA+ and Bend work windows overlap. The log does not record whether the jobs competed for the two VPS cores.

Other Go timings are included only for context: UC2 core tests took 6.4 seconds, the inventory service tests took 36 seconds, and payment service tests took about 76 seconds.


## 4. Resource use

### Disk

The UC2 contract-bound TLC run on the MacBook M4 grew its metadir (TLC's on-disk state store) to 86 GB and filled the volume. Free space went from 71 GB at the start to 123 MiB at the failure. The run was not capped and free space was not watched. The log calls this "a mistake" (log 4.21). The metadir was deleted afterwards, and 87 GB was free again.

A second incident came in the first batch of UC2 mutant runs. `/tmp/claude-1001` was full. The run for M1b died at level 5 with `Error: when writing the disk (StatePoolWriter.run)` and left a 381 MB metadir. The runs for m3 to m7 and m2 then failed at once. m2 reported `Module-Table lookup failure`, which was the disk (log 4.20, uc2-mutants.md).

The fix since then: run one job at a time, check `df` and stop under 1.5 GB, use `timeout 900`, and delete the metadir after each job. Metadir sizes for the reduced-bound runs are not recorded. After the M4 session of log 4.22, 89 GB was free.

Bend left no recorded disk footprint. The harness compile writes a temp directory of about 120 KB per `go test` run (uc1-harness.md). The UC2 compiled binary is 152 KB.

### Memory

TLC's default is a 274 MB heap and 64 MB off-heap (phase0-tlc.md). The UC1 N=2 run used `-Xmx700m`, and the VPS had about 1.9 GB of RAM (uc1-tla.md). The memory use (RSS) of TLC and of Bend is not recorded. Bend failed on big list literals with "memory fault" and "stack overflowed" (log 4.4).

### CPU

| Run | Machine | User time against wall time | Reading (derived) |
|---|---|---|---|
| TLC, UC2 reduced bound, 2 workers | 2-core VPS | user 658.117 s over 348.943 s wall | About 1.9 cores busy (658.117 / 348.943 = 1.89, user time only) |
| Bend, UC1 gate | 2-core VPS | user 5.600 s of 6.484 s wall | About one core |
| Bend, UC2 gate | 2-core VPS | user 2.098 s of 2.358 s wall | About one core |

TLC's progress rates on the UC2 contract bound were 12,708,836 states per minute generated at level 10 on the MacBook M4 and 1,425,445 per minute at level 8 on the VPS. Those are the last progress lines of two runs. They are not a controlled comparison.

### State counts per run

Finished and stopped runs are in section 3. Reach witnesses (short runs that show a state is reachable) took 14 to 55,119 distinct states for UC1 and 44 to 1,204,950 for UC2. UC1 mutant runs took 6 to 343,923 distinct states. UC2 mutant runs took 9,666 to 1,204,950, and M2 reached 4,546,849 at its 15-minute cap (section 8).

### Cost of the Go to Bend port

The harness needs the Bend port as a native binary. That created these costs (log 4.4, 4.8, phase0-bend-io.md, uc1-harness.md section 5):

| Limit | What happens |
|---|---|
| Compile time | 6 to 8 s for UC1 (8.2 s), against the Phase 0 estimate of 1.5 s. It dominates the UC1 harness test, so it is built once per test process (`sync.Once`) |
| stdin | Bend's Base has no stdin effect. The port reads `/dev/stdin` as a file, which is a Linux path (the Phase 0 note says "Linux-only"). Whether the harness ran or skipped on the MacBook M4 is not recorded |
| Input size | `File.read` takes a fixed size. Input of 16 MiB or more is rejected (exit 1). A 34 MB input takes 6.7 s to reject |
| Numbers | `Nat` is unary, so the harness caps values at 100000. `U32` wraps, so values must fit in `U32` |
| Interpreted stdin | Overflows above roughly 20 KB. The compiled binary does not |
| List literals | A single list literal in generated source breaks between 2,500 and 3,000 elements (2,500 passes, 3,000 fails). 10,000 works in 500-element chunks |
| Argument limit | ARG_MAX is 2,097,152 bytes. 100,000 events took 226 ms on argv and 63 ms on stdin |
| Language gaps | No `match` on a computed value, so each computed Bool or Nat that is matched needs a helper `def`. No mutual recursion: one UC2 compile failure was `bump_at` and `bump` |
| Name clashes | `Fail` and `Done` are taken by Base. `String.lines("a\n")` returns `["a", ""]` |

The compile phase for UC1 `main.bend` needed about 8 compile iterations. Effects are compared as tallies (count and uint32 sums), not as an ordered list (uc1-harness.md section 1, uc2-harness.md section 1). Coverage is thin: only 1,852 of 75,787 UC1 events (2.4 percent) produce an effect. For UC2, 2,526 of 75,094 events (3.4 percent) produce a success effect.

## 5. Authoring effort

All authoring times below are estimated, not measured. An AI agent did all the writing, using scripts, so a human's time could differ. The stop rule was 2 hours or 15 failed iterations per use case and tool. A failed iteration is a failed model check for TLA+ and a failed proof run for Bend. Neither tool reached the stop rule.

### Time and failed iterations

| Task | Writing time (estimated) | Failed iterations | Other |
|---|---|---|---|
| UC1 TLA+ | About 15 min to write, plus 1 syntax and precedence fix before the first run | 0 failed model checks, 2 AI iterations | Session about 73 min (10:07 to about 11:20 UTC), of which about 62 min was waiting for the N=2 run (uc1-tla.md) |
| UC1 Bend | About 35 min (10:13:09 to about 10:48 UTC, including the port and its checks) | 12 of 15 | About 9 compile errors in `code.bend` during the port are not counted. 1 deliberate mutation check is not counted (log 4.9) |
| UC2 TLA+, spec task | About 25 min writing the spec. About 115 min elapsed (03:30 to 05:25 UTC), the rest TLC runs and waiting | 2 failed model checks | About 4 spec edits and 1 review round. Failures: an un-enumerable `expiresAt : Nat` in `TypeOK`, then "Deadlock reached", fixed with a stutter disjunct (log 4.18, uc2-tla.md) |
| UC2 TLA+, mutant task | Included in the mutant task below | 3 | The results file says a `gen.py` syntax error and two infrastructure failures. Log 4.20 says a generator typo plus the disk-full incident. The disk-full incident is not a model check (log 4.20, uc2-mutants.md) |
| UC2 Bend | About 50 min (03:59:49 to 04:49:33 UTC, then 04:50 to 04:55 for checks) | 14 of 15, one left | About 7 compile errors before the law commit are not counted. Most failures were typos in generated text (log 4.17, uc2-bend.md section 5) |

The log summary table gives UC1 TLA+ as "about 1 h 20 min (mostly TLC)". The results file says about 15 min to write. This document uses the 15-minute writing figure and shows the wait separately.

The mutant tasks (log 4.20, uc1-mutants.md, uc2-mutants.md):

| Use case | Wall time (estimated) | Failed iterations |
|---|---|---|
| UC1 mutants, all tools | 10:51:01 to 11:29:54 UTC on 22 November 2026 | not recorded |
| UC2 mutants | About 1.5 h in all: Go about 20 min, Bend about 25 min, TLA+ about 25 min plus runs | Go 0, Bend 1, TLA+ 3 |

Each Bend mutant diff is 2 to 10 lines of `code.bend`. UC2 M4 also changed 2 lines of `spec.bend` and 4 of `PROOF.bend`. Each UC2 TLA+ mutant diff is 6 to 11 lines (M4 is 61). UC1 TLA+ diffs are 7 changed lines (M2a, M2b, M4, M5) and 31 (M3).

### Size

Line counts come from `wc -l` run on 23 November 2026.

| File group | UC1 | UC2 |
|---|---|---|
| TLA+ spec | `UC1.tla` 444, `UC1_buggy.tla` 447 | `UC2.tla` 428 |
| TLC configs | `UC1.cfg` 27, `UC1_wall_n2.cfg` 27, 15 reach cfgs | `UC2.cfg` 33, 30 reach cfgs |
| Bend `spec.bend` | 390 | 550 |
| Bend `code.bend` | 203 | 128 |
| Bend `LAWS.bend` | 433 | 258 |
| Bend `PROOF.bend` | 2,634 | 2,209 |
| Bend total | 3,660 | 3,145 |
| Laws and lemmas | 46 laws, 162 lemmas | 29 laws, 298 lemmas |
| Proof to code ratio | About 13 to 1 | About 17 to 1 |
| Harness | `main.bend` 328, `conformance.go` 325, `conformance_test.go` 75, total 728 | `main.bend` 351, `conformance.go` 427, `conformance_test.go` 101, `harness_test.go` 78, total 957 |

The ratios come from uc1-bend.md section 8 and uc2-bend.md. The log gives UC1 TLA+ as 438 lines and UC1.cfg as 26, and the harness test as 86 lines (total 739). The wc values are used here (section 13).

Bend lines against TLA+ lines (derived from wc): UC1 3,660 against 444 + 27 = 471. UC2 3,145 against 428 + 33 = 461. These counts are not like for like. The TLA+ spec includes the network, crash and `lastEvent` and `lastFx` model. The Bend port has no network (faults are arbitrary event lists), but it carries `spec.bend` helpers and 2.2k to 2.6k lines of proof text.

About 70 percent of UC1 `PROOF.bend` came from small throwaway Python scripts that enumerate slot shapes. The scripts are not committed (uc1-bend.md section 4). Most of UC2 `PROOF.bend` came from throwaway Python templates over the three events, also uncommitted.

### Missing Bend arithmetic in UC2

Bend's Base had none of the four lemma families the UC2 proofs needed (log 4.17, uc2-bend.md section 4).

| Lemma family | Lines | Failed | Time (estimated) |
|---|---|---|---|
| `a + b == c` gives `c - b == a` | 24 | 0 | About 3 min |
| `+` is commutative and associative | 29 | 0 | About 3 min |
| `a <= a + b` | 18 | 0 | About 2 min |
| List sum split at one element | 42 | 0 | About 5 min |
| P3b (released count equals emitted effects) | About 450 | 3 | About 20 min. Needed a generalised induction with an accumulated effect list |

The Nat part is about 130 lines and the list sums, ids and record folds are about 160 lines (uc2-bend.md section 9). TLC pays nothing for the same facts.

Phase 0, for context (log section 3, estimated): TLC smoke about 10 min. Bend smoke about 10 min with 5 failed proof iterations, including reading the guide. Bend guide and escape-hatch audit about 1 hour. I/O spike about 25 min plus about 25 min of probes. Soundness probes about 45 min plus about 10 min.

## 6. Developer experience

Facts come from the log. Judgments are marked "Opinion:".

### Feedback loop

| Tool | Time per check | Machine | Class |
|---|---|---|---|
| Bend gate | 2.4 s (UC2) to 6.5 s (UC1) | 2-core VPS | measured |
| TLC, trivial model | 1.4 to 1.6 s, all JVM start-up | 2-core VPS | measured |
| TLC, checked bounds | 5 min 01 s (UC1 N=1 bound), 348.943 s (UC2 reduced bound) | 2-core VPS | measured |
| TLC, checked bounds | 23 to 28 s | MacBook M4 | measured |
| TLC, mutant counterexamples | 5 s to 3 min 29 s | 2-core VPS | measured |

Sources: log 4.10, uc2-mutants.md, phase0-tlc.md. Opinion: a few seconds per Bend check suits one-lemma-at-a-time work. A TLC loop of about 5 minutes on the VPS is slow for that style. The elapsed times in section 3 show the cost.

### What a failure looks like

TLC prints `Error: Invariant X is violated.` and a numbered counterexample trace. For UC1 M1, the trace is 6 states: PlaceOrder, Flush, Duplicate, Deliver, Deliver. For UC2 M1, the trace is: send Reserve with ttl 1, send Confirm, deliver Reserve, Tick, deliver Confirm, which is accepted at clock == expiresAt (log 4.11, uc2-mutants.md). TLC reports the first violated property in breadth-first order, not the set of all properties a mutant breaks.

Bend prints `SOME PROOFS FAIL` with `expected`, `observed`, a context and a `Location:`. It names one failing definition per run. The log's own verdict: "good for type mismatches, poor for the first error only" (uc1-bend.md section 9). A family of generated proof arms with one bug costs one iteration per bug.

A Bend rejection is not a counterexample. It means the hand proof no longer checks against the changed code (uc2-mutants.md, Caveats). Bend rejected UC1 M2b and M4 through `Inv`, not through the P-law the contract names, because the gate stops at the first failing definition (uc1-mutants.md).

Opinion: for a developer who wants to see what went wrong, a TLC trace is much easier to read than a Bend type-mismatch report.

### Episodes

Bend (log 4.3, 4.5, 4.9, uc2-bend.md section 11):

- `type Event` clashed with Base, so it became `Ev`. A constructor cannot be named `None`.
- Termination needs the shrinking list leftmost.
- Everything is affine, so a proof used twice needs `+h`. Hypotheses whose type is a function or a pair of proofs cannot take `+`.
- No `match` on a computed value. `case _ _` does not refine.
- Rewrite direction: `%e : P` replaces occurrences of the right side by the left. Every helper equation had to be oriented "simple == compound".
- There are no tactics, so every attempt is hand-written term syntax.

TLA+ (uc2-tla.md, log 4.1 to 4.22):

- The first UC2 run died because `expiresAt : Nat` cannot be enumerated in `TypeOK`.
- "Deadlock reached" was fixed with a stutter disjunct. That disjunct hides true deadlocks.
- TLC writes `*_TTrace_*` files next to the spec unless run with `-noGenerateSpecTE`.
- A TLC run started with `&` dies when the tool call ends.

### Tooling and documentation

`bend guide` and `bend base` give the guide and the standard library. The guide says the human writes `LAWS.bend` and the AI does not touch it (phase0-bend-guide.md sections 3 and 4). Bend 2 documentation is new: Bend 2 launched in September 2026 (`docs/handover.md` section 2). The `--verdict` recheck needs Lean v4.34.0, which was not available here.

TLC has a JSON trace dump (`-dumpTrace json`). It made the UC1 trace replay possible. The replay took about 7 minutes of agent time (log 4.13).

### Nix setup

`nix develop` cannot run in the Claude sandbox on the VPS, so `.nix/env.sh` is hand-built (log s2). Known workarounds:

- `/tmp` is read-only for the JVM. `JAVA_TOOL_OPTIONS` fixes it and adds a `Picked up JAVA_TOOL_OPTIONS` line to output.
- `~/.bend` is read-only and `bend-lang.com:443` is blocked, yet bend still runs.
- `just` needs `XDG_RUNTIME_DIR=$TMPDIR`.
- `java` is not on PATH, only through the `tlc` wrapper.

On the MacBook M4, `nix develop` works (log s2), while CLAUDE.md still says to source `env.sh`. The sources disagree on whether `env.sh` is needed on the M4.

### Learning curve

No timed learning figure exists. The Bend smoke time of about 10 minutes includes reading the guide and 5 failed proofs (log 4.3). Opinion: Bend's learning cost is mostly the proof style (affine terms, rewrite direction, no tactics). TLC's is mostly choosing bounds that finish.

## 7. Strength of the guarantee

### What a TLC pass means

A TLC pass means that every reachable state of the model, up to the bound in the `.cfg`, satisfies the listed properties. It does not mean the property holds at two orders in UC1, or at the contract bounds. For every TLC result in this document, the bound is named beside it. Section 2 lists what each bound drops.

### What a Bend pass means

A Bend pass means `ALL PROOFS CHECK` from the plain gate. The law, as written, holds for any state and any list of events, if the law text says what we mean and the checker is sound.

`--verdict` was not run. It rechecks the proof with a small kernel proven in Lean. The sandbox had no `lean`, `lake` or `clang` on PATH, and it needs Lean v4.34.0 (phase0-bend-guide.md section 5, log s1). So every `ALL PROOFS CHECK` here is provisional. Whether `--verdict` could run on the MacBook M4 is not recorded.

A Bend proof is about the Bend port (`code.bend`), not the Go service. The harness closes part of that gap with a sample of 500 seeded sequences per use case. That is a test, not a proof. The TLA+ model is a third, separately written model. Only UC1 has a trace replay (log 4.13), and it does not cover Drop, Restart, `dup`, `crashes`, `retries`, `lastFx` or the P2b clauses (c) and (d) on the service side.

Most UC1 laws hold for every state, reachable or not. P2b (a), (b) and (d), P3, A12, A13 and every pin do not use their `inv` hypothesis. Only the `inv_*` laws, P1, P2a and P2b(c) need `inv` (uc1-bend.md sections 3 and 11). In UC2, no pin, `p1b_take_step`, `p4_expired_stays_step` or `p4b_confirm_guard_step` uses its `h` (uc2-bend.md section 3).

### Escape hatches

The Phase 0 audit listed 13 escape hatches, taken from the guide and from Base, and tested each where it could (phase0-bend-guide.md section 4). They include `@unsafe`, `def f?`, `?TODO`, `?name`, an open law, a foreign import and a proof that does not import LAWS. The plain gate rejects them with `SOME PROOFS FAIL`, with these exceptions:

- Dead-mode code and `Type : Type` are "not detected" by design. Safety rests on the live and dead wall and on the `--verdict` kernel.
- A weakened or wrong law text is "not detected". It is a social convention.
- Base's own foreign effects, such as `IO.print`, are exempt and still print `ALL PROOFS CHECK`.
- The plain gate prints "Use --verdict for mathematical validity".
- Whether `--verdict` rejects hatches 1, 2 and 6 is untested.

A scan of every final proof, `grep -E '@unsafe|\?|import "'` over PROOF, code, spec and LAWS, gives no hits in `bend/uc1` or `bend/uc2`. UC1 has 46 `law` lines and 46 `def Laws.` entries. UC2 has 29 and 29 (uc1-bend.md section 3, uc2-bend.md section 3).

### Soundness probes

14 deliberately false laws were fed to the plain gate. Each printed `SOME PROOFS FAIL`. Twelve were rejected on the merits. Two (`unsafe_false` and `open_false`) were caught by the escape-hatch detector (log s1, phase0-bend-probes.md). `bash bend/probes/run.sh` exits 0. Log section 1 reports no current soundness alerts.

This is not a proof of soundness. Reasons from the record:

- The checker reports one error at a time.
- The `type_in_type*` probes are Russell-style, not a full Girard or Hurkens paradox.
- The two detector probes test the detector, not the type theory.
- Nothing tests the Lean kernel.

### Laws that only bound the state

In Phase 0, a saturating counter with an upper-bound law plus `Reset -> 0` still printed `ALL PROOFS CHECK` for two mutants: (a) Inc=0 and (b) a cap of 2 (log 4.3, phase0-bend-smoke.md section 5). A law that only bounds the state cannot see a mutant that stays inside the bound. UC1 and UC2 fixed this with pinning laws (A1 to A13, S0 to S11) that state each event's exact result.

UC1 M5 is another case of properties that miss a bug. Only the pins A8 and A13 reject M5. P1 to P3 and `Inv` pass because chargeCount stays at 1 (UC1 contract section 5, uc1-mutants.md).

### A hard case that was not tested

Cross-side properties were stated in no tool, by default. Examples: a provider refund implies the order was Paid, Paid implies the provider charged, and there is no charge on a Failed order (UC1 contract section 6, Q7). So the hardest case for H3, an invariant that depends on whether a message was sent, was not exercised (uc1-bend.md section 11).

## 8. Bug-finding results

### How to read the tables

The Go column lists the core checks that fail. The harness column gives the first divergent event as seed and event index. The Bend column gives the first failing lemma, because the gate prints one. The TLC column gives the first violated property in breadth-first order, the length of the trace in states, and the distinct states and time. All TLC times are from the 2-core VPS. The UC1 buggy runs used the UC1 contract bound. They ran concurrently on 2 cores, so their times are inflated (uc1-mutants.md). A TLC kill ends at the first violation, so it is not a pass at that bound.

### UC1 mutants

| Mutant | Go core checks | Harness | Bend | TLC (UC1 contract bound) |
|---|---|---|---|---|
| M1 | Inv, P1, A8, A13 | seed 4, event 224 | `pp_charge_recv` | `NoDoubleCharge`, 6 states, 2,340 distinct, depth 6, 5 s |
| M2a | P2b(a), P2b(b), P3, A6, A12 | seed 1, event 10 | `ps_refund_order_other` | `RefundedOnlyFromPaid`, 2 states, 15 s |
| M2b | P2a, Inv, A10 | seed 2, event 152 | `sok_step` | `RefundNeverExceedsCharge`, 11 states, 343,923 distinct, 154 s |
| M3 | P1, Inv, A8, A13, mutant-only pin | seed 1, event 4 (see note) | `pp_apply` | `NoDoubleCharge`, 8 states, 23,086 distinct, 39 s |
| M4 | P3, A4, A12, Inv, P2b(c) | seed 1, event 47 | `op_pay_ok` | `TerminalStable`, 9 states, 55,242 distinct, 58 s |
| M5 | A8, A13 only | seed 10, event 77 | `ps_replay_declined` | `PinProvRecStable`, 6 states, 2,358 distinct, 27 s |

Notes:

- M3: the harness cannot send `ProvApplyCharge`, so it rejects through the deferred charge, not through the race itself. The UC1 harness cannot drive the real M3 race.
- M5: Bend rejected it only after the M5 proof was repaired, because the unchanged proof failed on a stale lemma shape. A scratch TLC run of the non-pin properties on M5 was stopped at about 12 min with 1,568,242 distinct states and no violation. That is partial evidence of survival. The Go checks carry the claim.
- M3 is not the same encoding everywhere. Bend overloads `amt` to hold `pending` and `Charge` carries 0, because `ProvRec` has five fixed fields in the frozen files. Go and TLA+ keep a separate field. The UC1 M3 Bend `PROOF.bend` edit could not be checked against correct code.

UC1 result: every mutant was rejected by every tool, with no survivor. M5 survives P1 to P3 and `Inv`, as the contract predicts. At that time `just check-tla-buggy` reported 6 buggy specs rejected as expected.

### UC2 mutants

The TLC column uses the UC2 contract bound, except where noted.

| Mutant | Go core checks | Harness | Bend | TLC |
|---|---|---|---|---|
| M1 | P4a, P4b, S5 | seed 19, event 7 | `inv_conf1` | `ConfirmedBeforeDue`, 6 states, 701,932 distinct, 47 s (see note) |
| M1b | S6 | seed 7, event 108 | `inv_exp1` | `PinExpireOk`, 6 states, 1,204,950 distinct, 3 min 29 s |
| M2 | P3, A1, S7, S10, S11 | seed 2, event 120 | `inv_exp2` | Wall at the UC2 contract bound. At the UC2 dup bound: `CountersMatchRecords` (A1), 8 states, 11,017 distinct, 3 s |
| M3 | P3, P4, P4a, P4b, A1, S5, S10, S11 | seed 2, event 11 | `inv_conf1` | `ConfirmedBeforeDue`, 6 states, 701,932 distinct, 2 min 04 s |
| M3b | P4a, P4b, S5 | seed 2, event 11 | `inv_conf2` | `ConfirmedBeforeDue`, 6 states, 2 min 02 s |
| M4 | P1, P1b, P3b, A2, mutant-only commit pin | not sendable (needs mutant-only events) | `Laws.inv_step`, stateless approximation | `NoOversell` (P1b), 4 states, 9,666 distinct, 6 s |
| M5 | P1b, P2, S3 | seed 1, event 79 | `inv_rsv` | `Conservation`, 5 states, 190,368 distinct, 36 s |
| M5a | P1, S3 | seed 1, event 79 (see note) | No Bend version | `NonNegativeAvailable` (P1), 5 states, 34 s |
| M6 | P2, A1, S6 | seed 2, event 93 | `inv_exp2` | `Conservation`, 6 states, 3 min 15 s |
| M7 | P3b, A2, S3, S11 | seed 1, event 73 | `inv_rsv` | `UniqueIdsKnownSku` (A2), 5 states, 32 s |

Notes:

- M1 TLC time: uc2-mutants.md gives 47 s. uc2-tla.md gives 2 min 36 s with other jobs running and 53 s alone. These are different runs.
- M2: no violation in 15 minutes at the UC2 contract bound (13,228,678 generated, 4,546,849 distinct at the cap, killed by timeout, rc 124). The dup-bound kill was a scratch run. After log 4.22, `UC2_buggy_m2.cfg` uses the dup constants, and `just check-tla-buggy` on the MacBook M4 reported 16 buggy specs rejected as expected.
- M4: Bend's frozen `LAWS.bend` fixes `State` at four fields, so there is no `approved` list. The Bend M4 is a stateless approximation: ReserveCommit carries the request and skips the duplicate and stock checks. It needed a 4-line `PROOF.bend` edit, and the other seven matches on `Ev` were untested for M4. The harness cannot send M4 because it needs mutant-only events. `StepM4Contract` agrees on 500 sequences.
- M5a: the Go harness diverges because Go goes negative while Bend's `Nat` cannot. That is not the real bug. There is no Bend version because `Nat` truncates and P1 holds by type.

UC2 totals: Go kills 10 of 10. Bend rejects 9 of 9 (M5a has no version). TLC kills 9 of 10 at the UC2 contract bound (M2 is a wall there, and it is killed at the UC2 dup bound). The harness catches 9 of 9 contract-event mutants (M4 cannot be sent). No mutant survives in Go or Bend.

Harness results, apart from mutants: UC1 500 sequences, 75,787 events, Go and Bend agree. UC2 500 sequences, 75,094 events agree. The UC1 TLC trace replay (log 4.13): all 15 reach traces replay equal. The six buggy traces leave the buggy model at the bug step (M1 step 5, M2a step 1, M2b step 10, M3 step 4, M4 step 8, M5 step 5). M3's `ProvApplyCharge` has no service counterpart.

### Survivors

- Go and Bend: none, in either use case.
- UC2 M2 in TLC: a wall at the UC2 contract bound, not a survivor. It needs a duplicated Expire, so its trace is longer than TLC reached in 15 minutes.
- UC1 M5 survives the properties P1 to P3 and `Inv` by design. Only the pins A8 and A13 reject it (UC1 contract section 5).

### The three contract rows the tools contradicted

The "Killed by" column of `properties/UC2.md` section 5 was left frozen. Log 4.20 and 4.22 record three rows that the tools contradicted:

| Mutant | Tools showed |
|---|---|
| M1b | S7 never fails. The boundary case is Held and Due, so it belongs to S6 |
| M4 | P2 does not fail with signed counters, because the moves cancel |
| M5a | P2 and P1b do not fail. The take is `available - qty` and `reserved + qty`, and one `FxReserved` with the exact qty is emitted |

Extra kills the contract did not list: M2 also S10. M3 also S10 and S11. M4 also A2 and P3b. M7 also P3b. In UC1, the log records no contradicted row. But Bend rejects M2b and M4 through `Inv`, and M2a and M5 through pins, instead of the P-law the contract names.

Log 4.22 notes an unconfirmed decision here: the user's "approve the plan" did not name the option the agent chose for these rows. The agent called it the least invasive and reversible.

### TLC finds bugs where it cannot finish a pass

Every UC1 buggy TLC run used the UC1 contract bound, and every UC2 buggy run used the UC2 contract bound (M2's later swap aside). TLC cannot finish a clean pass at either. Yet it found each shallow bug (a trace of 2 to 11 states) in seconds to minutes. So TLC can be a fast bug finder at a bound where it cannot prove the good spec. The reverse also holds: at those bounds, "no violation" only means "none found yet". M2 shows the limit.

## 9. Walls and failure modes

| Wall | Numbers | Source |
|---|---|---|
| UC1 TLC at the UC1 contract bound | Stopped at 62 min, level 16, 9,079,945 distinct, 4,644,890 on queue. Final figures not recorded | log 4.14, uc1-tla.md |
| UC2 TLC at the UC2 contract bound, 2-core VPS | Stopped at 60 min, level 8, 25,051,664 distinct | uc2-tla.md |
| UC2 TLC at the UC2 contract bound, MacBook M4 | Aborted at about 48 min, level 10, 149,567,238 distinct, 86 GB metadir, disk full | log 4.21 |
| UC2 M2 at the UC2 contract bound | No violation in 15 min, 4,546,849 distinct | uc2-mutants.md |
| UC1 M5 non-pin properties at the UC1 contract bound | Stopped at about 12 min, 1,568,242 distinct, no violation | uc1-mutants.md |
| Five reduced UC2 scratch bounds | None finished. Levels 10, 10, 15, 14, 14 | uc2-tla.md |
| Five UC2 reach witnesses | Did not hit in 150 s at the UC2 contract bound, so they needed reduced constants: ConfirmNotHeld, ExpireNotHeld, ExpireDupNotHeld, ConfirmDupNotHeld, ExpireNotHeldAfterConfirm | log 4.18 |
| Unreachable behaviour in TLC | UC2 `BadRequest`. UC1 out-of-range order ids. Crash only while up, Restart only while down | uc1-tla.md, uc2-tla.md |
| Disk-full incidents | 2 (section 4) | log 4.20, 4.21 |
| Bend I/O | No stdin effect, `U32` wrap, `Nat` cap 100000 in the harness, 16 MiB read cap, list literal limit 2,500 to 3,000, interpreted stdin about 20 KB, compile 5 to 8 s | section 4 |
| Bend unprovable properties | None recorded. All 46 and 29 laws proved on the plain gate. The nearest thing to a wall: UC2 14 of 15 failed iterations (typos in generated text), UC1 12 of 15, and P3b at about 450 lines and about 20 min | log 4.9, 4.17 |
| Bend scope gaps | UC2 port has one stock (`State.stock`, not `List<Stock>`). No `p1` law (holds by type, and the obligation moved to three `Nat.sub` calls, two needing A1 plus the list-sum split lemma). UC2 M5a no Bend version. UC2 M4 stateless. UC1 M3 different encoding. Every number capped at `U32` or 100000 in the harness | uc2-bend.md section 10, section 4 |
| `--verdict` | Could not run (no Lean) | log s1 |
| TLC reductions not applied | A `VIEW` dropping `lastEvent` and `lastFx` is unsound for the action properties as written. `SYMMETRY` on `OrdIds` would halve N=2 at best. Neither was applied, because it needs the user's approval | uc1-tla.md |
| Stutter disjunct in UC2 `Next` | Hides true deadlocks | uc2-tla.md |
| `just check-tla-buggy` | Did not finish while `UC2_buggy_m2.cfg` stayed at the UC2 contract bound. Fixed by log 4.22 | log 4.22 |

## 10. Cost of change and maintenance

No timed rule-change experiment exists in the repo (not recorded). Any claim that one tool is cheaper to change is opinion, with the episodes below as evidence.

### Changing a rule in TLA+

Edit `Step` in the spec and, if needed, a `.cfg`, then re-run. No figure is recorded for a timed rule change. Bound swaps were done by moving cfg files (log 4.14, 4.22). `just check-tla` plus `just check-tla-buggy` took 7.5 min on the MacBook M4. Each swap needed the user's approval, as the project rule says: change a bound only with approval, and log it.

### Changing a rule in Bend

The law text is frozen before any proof starts. UC1 `spec.bend` and `LAWS.bend` were committed as dc3d570 before any proof, and UC2's as 5c5c144. The user approved them after the fact on 23 November 2026. Changing a law or a type means editing frozen files and redoing proofs. Episodes:

- UC1 M3 needed a sixth `ProvRec` field. That "breaks about 190 sites in frozen or approved files", so the mutant overloads `amt` instead (uc1-mutants.md).
- UC2 M4 needed new events. Every `match` on `Ev` in `PROOF.bend` then becomes non-exhaustive (the unedited proof fails with `this match doesn't cover ...`). The answer was a stateless approximation and a 4-line proof edit.
- UC2 `LAWS.bend` fixes `State` at four fields.

A Bend datatype change ripples through hand-written case analyses. Opinion: a rule change costs far less in TLA+ than in Bend on this evidence, mainly because there are no hand-written cases to redo.

### Keeping three artefacts in step

One contract produced three separately written artefacts: the Go core, the Bend port and the TLA+ spec.

- The harness compares the Go core and the Bend port only, on 500 seeded sequences per use case. It must be re-run if a proof task edits `code.bend` (log 4.8).
- TLA+ was compared against the Go services only by the UC1 trace replay.
- No Bend-against-TLA+ mechanical check is recorded.

### The frozen-contract workflow

`properties/UCn.md` is approved and frozen before any TLA+, Bend or harness work (checkpoint 2). Departures are listed. For UC2 Bend they are: one stock, pins that quantify over witness counters, rejection pins that use `*_reason` functions, and P3b as a fold over every record (uc2-bend.md section 10). Mismatches with the contract are recorded, not edited (log 4.20, 4.22). Bounds change only with approval.

### Maintenance pain points

- Laws and proofs are bound to constructor field counts.
- `just prove-bend` globs `bend/uc*/PROOF.bend`, so mutant proofs need their own `run.sh`.
- A `*_buggy*` cfg must produce a violation, and a cfg without that name needs its own module.
- `*_wall*` cfgs are skipped by `just check-tla`.

## 11. Fit by property type

This section lists only what the data supports. Liveness (UC4) and the fencing token (UC3) were not tested. The data says nothing about them.

| Property type | TLA+ with TLC | Bend |
|---|---|---|
| Safety invariants (UC1 P1 chargeCount at most 1, UC2 P2 conservation) | Checked in every reachable state up to the bound | Proved for any state and list, through an inductive `Inv`. It needed extra conjuncts. UC1: `outRefund` implies `Refunded` was "necessary, not decoration". UC2: A1 and A2 make `Nat.sub` safe |
| Idempotence and duplicates | `Duplicate(m)` of an in-flight message, at most `DupMax` or `MaxCopies` times. UC2 S11 is derived from S2 to S7, not checked | Repeated events in a list. UC2 S11 (`pin_dup_idempotent`, 9 lemmas that rewrite `step(s, e)` twice) passed on the first try |
| Conservation and arithmetic (UC2 P2, P1b, P3b) | Costs nothing extra | Worked, but needed the missing Nat and list-sum lemmas (section 5) |
| Ordering, reordering, loss | Models a network with drop, duplicate and reorder, plus crash and restart. Reorder and "state changed, effect lost" are reachable because Flush events are separate | Models faults as an arbitrary event list: a repeated event is a duplicate, an absent one a drop, and order is reorder. It includes never-sent messages, so it is stronger (UC1 contract section 2) |
| Transition properties and pins | Action properties with `lastEvent` and `lastFx` helper variables. P3b needed a history variable `emitted` | One law per event and case. P3b needed a generalised induction |
| Counterexamples to false claims | A trace | The first failing lemma |
| Cross-side properties (UC1 Q7) | Not stated | Not stated |

## 12. Reproducibility

Pinned versions are in section 2. The Nix flake is `flake.nix` with `flake.lock`. `.nix/env.sh` is hand-built where `nix develop` cannot run (log s2). Run `source .nix/env.sh` first in such a shell.

### Commands behind the headline numbers

| Figure | Command |
|---|---|
| Bend gates | `bend bend/uc1/PROOF.bend`, `bend bend/uc2/PROOF.bend`, `bend bend/smoke/PROOF.bend` |
| Bend gate timing | `hyperfine --warmup 1 --runs 5 -N 'bend bend/uc1/PROOF.bend'` for UC1, and `--runs 10` for UC2 |
| 14 soundness probes | `bash bend/probes/run.sh` (must exit 0) |
| Bend mutants | `bash bend/uc1/mutants/run.sh`, `bash bend/uc2/mutants/run.sh` |
| All Bend checks | `just prove-bend` |
| TLC, one spec | `tlc -metadir $TMPDIR/<run> -config spec/tla/<X>.cfg spec/tla/<X>.tla`, adding `-noGenerateSpecTE` |
| TLC, all checked bounds | `just check-tla` |
| TLC, all buggy specs | `just check-tla-buggy` |
| Harness | `just harness`, or `go test ./harness/...` |
| UC2 mutant harness | `go test -count=1 ./mutants/uc2/ ./harness/uc2conformance/` |
| UC2 contract-bound wall | `timeout 3600 tlc -noGenerateSpecTE -workers auto -metadir $TMPDIR/w60 -config spec/tla/UC2_wall_contract.cfg spec/tla/UC2.tla` |

Do not re-run the UC2 contract-bound wall without a disk cap. It filled the disk once (86 GB) and `/tmp` once.

### What depends on the machine

- Every TLC timing, `-workers auto` (2 workers on the VPS, 10 cores on the MacBook M4), and TLC progress rates.
- Bend gate timing. VPS noise was large: the smoke hyperfine sigma reached 217.6 ms.
- The harness read of `/dev/stdin`, which is a Linux path, and compile times.

What does not depend on the machine: state counts and depth for finished TLC runs, and `ALL PROOFS CHECK` or `SOME PROOFS FAIL` results.

### Stale text in the repo

- The README still says UC2 waits for checkpoint 4, and that `UC2.cfg` holds the contract bounds while `UC2_proposed*.cfg` await approval. Log 4.22 swapped them.
- `uc2-bend.md` still says the laws are a draft pending approval. They were approved in log 4.22.
- `uc1-tla.md` and `uc2-tla.md` use pre-swap cfg names in the body.
- Log section 2 says `env.sh` is not needed on the MacBook M4, and CLAUDE.md says to source it.

## 13. Threats to validity

### 13.1 Threats

- One author. An AI agent wrote the contract refinements, specs, laws, proofs, mutants and harness in sessions, with the user approving at checkpoints. The same author wrote the TLA+ properties and the Bend laws from one contract, so a misreading of the contract could be shared by both. Opinion: this is an inference, not a recorded event.
- Small systems. Two state-machine use cases, one stock in Bend, and 2 to 3 orders in tests. Both are safety use cases.
- Estimates against measurements. All authoring times are agent estimates (the log's section 3 header says so). Some include TLC wait time.
- Different machines. Section 2 and 3 explain the split. MacBook M4 figures are single runs.
- Reduced bounds. They were chosen after the contract bounds failed to finish. The agent proposed them and the user approved them (log 4.14, 4.22). Section 2 lists what they drop.
- Plain gate only. No `--verdict`. 14 probes are not a soundness proof.
- Noise. UC1 mutant TLC runs "concurrently on 2 cores, so wall times are inflated". The UC2 reach sweep ran in parallel. UC2 M1 took 2 min 36 s with other jobs and 53 s alone. Hyperfine run counts range from 1 to 10. The smoke Bend hyperfine had sigma 217.6 ms on a "noisy machine".
- No true cold run anywhere. The page cache was never dropped.
- The stop rule counts only failed checks and proofs. Compile errors and typos in generators are not counted (about 9 UC1 and about 7 UC2 Bend compile errors before the law commit). The counts also differ in definition across tools.
- Bend proofs are largely generated by uncommitted scripts (about 70 percent of UC1 `PROOF.bend`). Generator typos drove UC2's 14 failures.
- Mutants are the same bug in spirit, not byte for byte, in every tool (UC1 M3, UC2 M4 and M5a). The kill sets are asymmetric: TLC reports the first property in breadth-first order and Bend the first failing lemma.
- UC3 and UC4 were not built. Nothing here tests them.

### 13.2 Oddities in the record

We added this subsection because several log items change numbers and the reader should know which figure to trust.

| Oddity | What this document did |
|---|---|
| Machine boundary by date, not entry (section 2) | Split by log entry |
| Line counts drift: log says `UC1.tla` 438 and `UC1.cfg` 26, wc says 444 and 27. The harness test was 86 lines in log 4.8, and is now 75, because it imports `mutants.StepM1`. `ls spec/tla` shows 45 reach cfgs (15 UC1 and 30 UC2) | Used wc and ls |
| UC1 reach witnesses: "11 files" and "15" both appear in uc1-tla.md | Used 15 (matches `ls`) |
| 348.943 s sits in a "cold" column in log section 3, but uc2-tla.md says cold and warm were not separated | Reported as one hyperfine run |
| UC1 TLA+ authoring: "about 1 h 20 min" (log 4.10 and section 3) against "about 15 min to write" (uc1-tla.md) | Used 15 min and showed the wait separately |
| UC2 reduced bound has two durations: `Finished in 05min 48s` and 348.943 s hyperfine (05:01 UTC), and `Finished in 05min 32s` (06:31 UTC re-run). Log 4.18 quotes 5 min 32 s next to the hyperfine figure | Reported the hyperfine figure and the re-run apart |
| UC2 M1 TLC time: 47 s, 2 min 36 s and 53 s | Different runs, all three stated |
| Smoke state count: 11 distinct on the VPS (log 4.1, phase0-tlc.md), 12 distinct in the MacBook M4 `just check-tla` output (log 4.22). The record does not explain the difference | Both stated |
| UC2 TLA+ failed iterations: 2 (log 4.18) and 3 (log 4.20, one of them the disk-full incident) | Reported separately, never summed |
| Log 4.22: an unconfirmed decision on the three contradicted contract rows | Stated in section 8 |
| Log section 5 "Findings so far" still says "None is a verdict on H1, H2 or H3" and covers Phase 0 only | Not used |

## 14. Hypotheses H1 to H3

The wording below is copied from `docs/handover.md` section 1.

### H1

"Bend can cover the use cases TLA+ covers. We measure the price and find where it stops working."

Verdict, first sentence: supported for UC1 and UC2. Verdict, second sentence: inconclusive.

Evidence for coverage: all 46 UC1 laws and all 29 UC2 laws printed `ALL PROOFS CHECK` on the plain gate. Bend rejected 6 of 6 UC1 mutants and 9 of 9 UC2 mutants. Price: section 5.

Limits of the coverage claim:

- P1 in UC2 has no law (it holds by type).
- The UC2 port has one stock.
- M5a has no Bend version, and M4 is stateless.
- UC1 M3 uses a different encoding.
- Cross-side properties were stated in no tool.
- `--verdict` was not run.

Evidence for "where it stops": no proof wall was hit in two state-machine use cases (12 and 14 failed iterations against a limit of 15). The places where Bend did stop were I/O (the harness) and port scope, not proof power. UC3 (fencing) and UC4 (liveness) would be the real test.

### H2

"Bend's checker is faster per run, but authoring cost (writing proofs) dominates the total. TLC may reach a result sooner on small models because it needs no proof."

Verdict, per clause:

1. "Bend's checker is faster per run": supported at the recorded sizes. On the 2-core VPS the Bend gate took 6.484 s (UC1) and 2.358 s (UC2). TLC took 5 min 01 s (UC1 N=1 bound) and 348.943 s (UC2 reduced bound). On the trivial model, Bend took about 0.4 s against 1.4 to 1.6 s of JVM start-up. The limit: the TLC figures are single runs.
2. "authoring cost (writing proofs) dominates the total": not supported by this data. Writing time was larger for Bend (about 35 and 50 min against about 15 and 25 min, estimated, with 7 to 8 times the lines, derived in section 1). But the elapsed time to the first complete pass was shorter for Bend in both use cases: about 31 against about 64 min in UC1, and 49 min 44 s against about 91 min in UC2 (derived from log timestamps, section 3). The TLA+ windows include TLC run time, and the log does not record the order of every run inside them. The walls came alongside or after the first pass: UC1's N=2 run took about 62 min in parallel with the N=1 run, UC2's 60-minute wall ran after the reduced-bound pass (05:25 to 06:25 against a pass at 05:01), and the 86 GB attempt (log 4.21) came hours later. They add TLC cost, not time to the first pass.
3. "TLC may reach a result sooner on small models because it needs no proof": supported for time to a runnable result (writing time). Not supported for time to a first complete pass at these sizes.

Limit of all three: an AI agent wrote the proofs with scripts, so a human's authoring time could differ. Every authoring time is an estimate.

### H3

"Bend proves a claim for all event sequences, while TLC only covers the bounds we set."

Verdict: supported for UC1 and UC2.

Evidence: Bend laws have no bound on slots, ids, totals or list length, and most UC1 laws hold for every state. TLC covered the UC1 N=1 bound and the UC2 reduced and dup bounds, with the coverage losses listed in section 2.

Limits:

- "All sequences" holds for the port and the law text as written, and only on the plain gate.
- The TLA+ network model (messages in flight) and the Bend event-list model are different models.
- The contract bounds were walls, so TLC never completed a pass at them.

## 15. Recommendations

Everything in this section is opinion, grounded in sections 3 to 11.

Use TLA+ alone when:

- the question is "does this design break?" in a small model.
- a counterexample trace is the product you want.
- the rules change often.
- the property is one TLC can check at a bound your team accepts. TLC found every UC1 mutant and nine of the ten UC2 mutants in seconds to minutes. UC2 M2 was found only at the smaller UC2 dup bound (section 8).

Use Bend alone when:

- the claim must hold for every list of events and every size.
- the port is small and pure.
- someone will own the proof text. The UC1 and UC2 proofs were about 3,000 lines each and about 70 percent of UC1's was script-generated.

Use both when:

- TLA+ finds bugs fast at a small bound, and Bend then closes the "for all" gap, with the harness checking that the port matches the real code. Both tools rejected every mutant they could be given in UC1 and UC2, with these exceptions: UC2 M5a has no Bend version, Bend M4 is a stateless stand-in, and UC2 M2 was a TLC wall at the contract bound (section 8). They differed most on cost.

If the project resumes:

- UC3 (fencing token) and UC4 (liveness) are the two tests this data cannot answer. Draw no conclusion about them from UC1 and UC2.
- Measure what is missing (see "Not recorded"). Run `--verdict` if a Lean v4.34.0 setup becomes available.
- Ask for approval before running TLC at a contract bound again. Cap disk use, run one job at a time, and use `timeout`.

## 16. Appendix

### A. TLC runs

See the table in section 3 (state counts, depth, time and machine for each run) and the walls in section 9.

### B. Bend gate runs

| Run | Machine | Mean or single | Runs | Source |
|---|---|---|---|---|
| `add_zero` trial | 2-core VPS | 385.4 ms +/- 15.7 ms | 10, 2 warm-up | log 4.2 |
| Phase 0 smoke, single | 2-core VPS | 0.397 s, 0.396 s | 1 each | log 4.3 |
| Phase 0 smoke, hyperfine | 2-core VPS | 510.2 ms +/- 217.6 ms and 781.4 ms +/- 87.7 ms | 10, 2 warm-up | log 4.3 |
| 14 probes | 2-core VPS | 5.550 s +/- 0.290 s | 5, 1 warm-up | log 4.5 |
| UC1 gate | 2-core VPS | 6.484 s +/- 0.099 s | 5, 1 warm-up | log 4.9 |
| UC2 gate | 2-core VPS | 2.358 s +/- 0.143 s | 10, 1 warm-up | log 4.17 |
| `just prove-bend` | MacBook M4 | 5 s wall | 1 | log s2 |

### C. Phase 0 harness I/O spike

Run with `hyperfine --runs 3 -N`, no warm-up, rough (log 4.4, phase0-bend-io.md):

| Case | Time |
|---|---|
| Compiled run, 10,000 events | 5 to 7 ms |
| Compiled run, 100,000 events on stdin | 63 ms |
| Interpreted | About 0.5 s |
| Embedded events | About 1.3 s |

### D. Glossary

| Term | Meaning |
|---|---|
| TLA+ | A language for writing a system as states and steps |
| TLC | The model checker for TLA+. It visits every reachable state up to the limits in a `.cfg` file |
| Bend 2 | A language with a proof checker |
| Law | A statement a human writes in `LAWS.bend` |
| Proof | A term in `PROOF.bend` that the checker accepts or rejects |
| Plain gate | `bend PROOF.bend`, which prints `ALL PROOFS CHECK` or `SOME PROOFS FAIL` |
| `--verdict` | A stronger recheck by a small kernel proven in Lean. Never run here |
| Bound | The limits in a TLC `.cfg`: number of orders, duplicates, crashes and so on |
| Contract bound | The bound the frozen contract asks for |
| Mutant | A copy of the code with one deliberate bug. A tool is good if it rejects it |
| Pin | A law that states the exact result of one event |
| Wall | A point where a tool did not finish or could not do something. Recorded as a result |
| Metadir | TLC's on-disk folder for visited states |
| Hyperfine | A command-line benchmark tool that runs a command several times |
| Harness | The test that feeds the same seeded events to the Go core and the compiled Bend port and compares the results |
| Reach witness | A short TLC run that shows a target state is reachable |
| Trace | The list of states TLC prints from the start to a violation |

### E. Source index

| Figure | Source |
|---|---|
| Machines and tool versions | log s2, phase0-tlc.md |
| UC1 N=1 bound run (1,156,996 distinct, 5 min 01 s) | log 4.14, uc1-tla.md |
| UC2 reduced bound run (2,055,926 distinct, 348.943 s) | uc2-tla.md |
| UC2 dup bound run (312,995 distinct, 41 s) | uc2-tla.md |
| M4 TLC timings (23 s, 28 s, 3 s) and 7.5 min | log 4.22 |
| UC1 N=2 stopped run | uc1-tla.md |
| UC2 contract bound runs, VPS and M4, 86 GB | uc2-tla.md, log 4.21 |
| JVM start-up | phase0-tlc.md |
| Bend gate timings | log 4.9, 4.17, uc1-bend.md section 7, uc2-bend.md section 7 |
| 14 probes | log 4.5, log s1, phase0-bend-probes.md |
| Escape-hatch audit | phase0-bend-guide.md section 4 |
| Harness timings | uc1-harness.md section 4, uc2-harness.md section 5 |
| Bend I/O limits | log 4.4, phase0-bend-io.md |
| Authoring times | log s3, log 4.9, 4.10, 4.17, 4.18, 4.20, uc1-tla.md, uc2-tla.md, uc1-bend.md, uc2-bend.md |
| Line counts | `wc -l`, 23 November 2026 |
| Lemma families and P3b | log 4.17, uc2-bend.md sections 4 and 9 |
| UC1 mutant table | log 4.11, uc1-mutants.md |
| UC2 mutant table | log 4.20, uc2-mutants.md |
| Contract rows contradicted | UC2 contract section 5, log 4.20, 4.22 |
| UC1 trace replay | log 4.13 |
| UC3 and UC4 not built | log 4.23 |
| Disk-full incidents | log 4.20, 4.21 |
| Hypotheses | `docs/handover.md` section 1 |

## Not recorded

This list shows what to measure next.

- Memory use (RSS or heap) for TLC and Bend runs.
- Disk footprint of the Bend gate, and the metadir sizes of the reduced-bound TLC runs.
- A true cold run for any tool (the page cache was never dropped).
- Hyperfine for TLC UC1 N=1 bound. A warm figure for TLC UC2 reduced bound (one run only). Hyperfine for the MacBook M4 TLC runs (single recipe runs).
- Per-file Bend timings on the MacBook M4 (only the whole `just prove-bend`, 5 s).
- Final state counts, depth and wall time at the UC1 contract bound and the UC2 contract bound (the runs never finished).
- `--verdict`, on either machine (no Lean). Whether it could run on the MacBook M4.
- Whether the compiled harness (`/dev/stdin`) ran or skipped on the MacBook M4. Log section 2 says only that `go test ./...` passed.
- Trace replay for UC2, and any mechanical comparison of Bend against TLA+.
- Failed-iteration counts for the Phase 0 spikes, the UC1 harness and the UC1 mutants, and AI iteration counts for most Bend tasks.
- A timed rule-change experiment in either tool.
- A human-time measurement of authoring (all authoring figures are agent estimates).
- Timing and state counts for UC1 TLC with SYMMETRY or any other approved reduction (never run).
- The TLC `UC1_buggy_m2b` A10 run (not done), and the UC1 M3 Bend proof edit checked against correct code (not possible).
- The harness binary size for UC1.
- Any UC3 or UC4 result (not built).
