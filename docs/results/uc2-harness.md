# UC2 conformance harness: Go core vs compiled Bend

- Authoring time: about 20 minutes, Mon Nov 23 2026.
- Tool: Bend 2.0.40 (compiled binary, stdin), Go test (standard library only).
- Failed iterations: 1 (one Bend compile error, see Friction). Go side compiled and passed first run. Stop rule not near.

## 1. Design

Same shape as `docs/results/uc1-harness.md`. The Bend proofs are about `bend/uc2/code.bend`, not `internal/uc2/core`. The
harness feeds the same seeded event sequences to a Go step function and to a compiled Bend binary and compares the final
state and the effect tallies. I/O rules from `docs/results/phase0-bend-io.md` §9.

```text
TestConformanceUC2 -> BuildBend (once per process: bend bend/uc2/main.bend -o <tmp>/uc2.bin; skip if no bend)
                   -> Run -> for seed 1..K: Find(bin, step, seed, len)
Find -> GenEvents(seed) -> Compare -> BendRun (Encode, stdin pipe written and closed, 20 s timeout, exit code checked)
                                   -> GoRun (core.Init, fold step, tally effects, Serialise)
Find -> on mismatch: linear scan of prefixes -> Divergence{seed, total, len, prefix, event, state before, bend line, go line}
FindFirst(bin, step, seeds, len) -> first seed with a Divergence
main.bend: main -> read /dev/stdin -> exec -> split ' ' -> nums -> groups -> mk_ev -> run_fx (folds Code.step) -> show
```

- `bend/uc2/main.bend` imports `./spec.bend` and `./code.bend` and edits neither. It folds `Code.step` itself (`run_fx`, the same
  fold as `Code.run`) so it can tally effects. The stock is `Spec.init(0, total)`: one stock, sku 0 (the Bend port has a single
  `stock` field).
- Pluggable core: `uc2conformance.StepFn` has the type of `core.Step`. `Find`, `FindFirst` and `Run` take it.
- Effects are compared as tallies, not as an ordered list: for each of FxReserved, FxConfirmed, FxReleased and each of the
  8 reject reasons (11 slots), the count and the wrapping uint32 sums of id, qty and expiresAt (`tally.<Name>`, `.id`, `.qty`, `.exp`).
  Qty is summed for FxReserved and FxReleased only, expiresAt for FxReserved only (Go leaves the other fields zero or unused).
  Two effect lists with swapped ids that keep the same sums would pass.
- Divergence report: the linear prefix scan (as UC1) gives the first failing prefix, the event at its end and both lines.
- Generator: total is 0 (1 in 10), 100000 (1 in 10) or 1..8; 1..len events (default 300); kind Reserve 30%, Confirm 20%,
  Expire 20%, Tick 20%, Crash 5%, Restart 5%; ids from 0..11 (duplicates, unknown ids, reordering are frequent); Reserve has
  sku 1 (unknown) 1 in 8, qty 0 or 100000 (1 in 12 each) else 1..4, ttl 0 or 100000 (1 in 12 each) else 1..4. Unused fields are 0.
  All values stay far below 2^31 (the largest is 100000). Seeds 1..K (default 500), flags `-seeds` and `-len`.

## 2. Encoding

One line on stdin: `T` then five numbers per event, ASCII digits, single spaces, final newline.

| field | meaning | values |
|---|---|---|
| T | initial total of the stock (sku 0) | 0..100000 |
| kind | Go `Kind` | 0 Reserve, 1 Confirm, 2 Expire, 3 Tick, 4 Crash, 5 Restart |
| id | reservation id | 0..100000 (Reserve, Confirm, Expire) |
| sku | sku | 0..100000 (Reserve) |
| qty | quantity | 0..100000 (Reserve) |
| ttl | time to live | 0..100000 (Reserve) |

The 100000 cap exists because Bend `Nat` is unary. Output, one line: `up clock stock.sku stock.total stock.available
stock.reserved stock.sold`, then per record in insertion order `r<i>.id sku qty status expiresAt confirmedAt returned`
(status 0 Held, 1 Confirmed, 2 Expired), then the 11 `tally.<Name>` groups (FxReserved, FxConfirmed, FxReleased, BadRequest,
UnknownSku, DuplicateId, InsufficientStock, UnknownReservation, NotHeld, TooLate, NotYet). `up` is 0 or 1.

Malformed input exits 1 with `error=...`: non-digit, empty token (double space, tab, CR), sign, number above 100000 or above U32,
input of 16 MiB or more, kind > 5, field count not 5 per event, empty input, more than one line. `TestBendRejectsMalformedInput`
checks 14 such inputs for a clean nonzero exit (an `*exec.ExitError`, not a timeout kill).

## 3. Commands and output

```
$ source .nix/env.sh && export GOCACHE=$TMPDIR/gocache GOMODCACHE=/tmp/claude-1001/gomodcache GOPROXY=off XDG_RUNTIME_DIR=$TMPDIR
$ bend bend/uc2/main.bend -o $TMPDIR/uc2.bin        # no output: compiles clean
$ printf '5 0 1 0 2 3 0 2 0 9 2 3 0 0 0 0 3 0 0 0 0 2 1 0 0 0 1 2 0 0 0 0 3 1 1 1 0 1 0 0 1\n' | $TMPDIR/uc2.bin
up=1 clock=2 stock.sku=0 stock.total=5 stock.available=3 stock.reserved=2 stock.sold=0 r0.id=1 r0.sku=0 r0.qty=2 r0.status=0 r0.expiresAt=3 r0.confirmedAt=0 r0.returned=0 tally.FxReserved=1 ... tally.BadRequest=1 tally.BadRequest.id=1 ...
$ printf '5 6 0 0 0 0\n' | $TMPDIR/uc2.bin; echo rc=$?
error=bad kind
rc=1
```

```
$ go vet ./... && go test -count=1 -v ./harness/uc2conformance/        (state and tally lines shortened)
=== RUN   TestConformanceUC2
    conformance_test.go:22: compared 500 sequences, 75094 events: Go core and Bend agree
    conformance_test.go:24: coverage: {Effects:[1611 244 671 25918] Rejects:[2030 1257 1977 5428 12639 1646 698 243] Crashes:3681 Restarts:3755 Ticks:15044 EventsDown:24170 QtyZero:1015 TtlZero:1091 SkuOther:1534 ConfirmAtDue:53 ExpireAtDue:46 DuplicateTries:2736}
--- PASS: TestConformanceUC2 (4.77s)
=== RUN   TestHarnessCatchesLocalM1
    conformance_test.go:80: local M1 caught:
        divergence: seed=19 total=100000 sequence length=53
        first failing prefix: 8 events (every shorter prefix agrees); the divergent event is index 7 = {Kind:Confirm ID:11 Sku:0 Qty:0 Ttl:0} (Confirm)
--- PASS: TestHarnessCatchesLocalM1 (0.05s)
=== RUN   TestBendRejectsMalformedInput
--- PASS: TestBendRejectsMalformedInput (0.02s)
PASS
ok  	github.com/derangga/learn-formal-verification/harness/uc2conformance	4.843s
```

`go test -count=1 ./harness/... ./mutants/uc2/...`: all `ok` (harness/conformance 7.981s, tlcreplay 0.281s, uc2conformance 7.729s,
mutants/uc2 6.039s). `just harness`: `ok ... harness/uc2conformance 10.292s` and `harness/conformance 10.726s`, all packages ok, 12.7 s wall.

### Coverage (500 sequences, 75094 events)

The test fails if any of these is zero (for runs of 10000 events or more).

| what | count |
|---|---|
| FxReserved / FxConfirmed / FxReleased / FxRejected | 1611 / 244 / 671 / 25918 |
| BadRequest | 2030 |
| UnknownSku | 1257 |
| DuplicateId | 1977 |
| InsufficientStock | 5428 |
| UnknownReservation | 12639 |
| NotHeld | 1646 |
| TooLate | 698 |
| NotYet | 243 |
| Crash / Restart | 3681 / 3755 |
| Tick | 15044 |
| Reserve, Confirm or Expire delivered while down | 24170 |
| Reserve with qty 0 / ttl 0 / sku 1 | 1015 / 1091 / 1534 |
| Reserve of an existing id | 2736 |
| Confirm of a Held record with expiresAt == clock | 53 |
| Expire of a Held record with expiresAt == clock | 46 |

Go and Bend agree on all 500 sequences on the first run. No divergence between the Go core and the Bend port was found.
Only 3.4 percent of events produce a success effect (2526 of 75094); UnknownReservation dominates the rejects (12639) because
ids are drawn from 12 values and most are not yet reserved, and 32 percent of events arrive while the service is down.
The boundary cases (clock == expiresAt) fire 53 and 46 times, enough for M1 and M1b.

### Non-vacuity: local M1 (Confirm accepts at clock <= expiresAt)

`TestHarnessCatchesLocalM1` uses a local `stepM1` (core.Step run one tick back for the one boundary case, ConfirmedAt fixed up)
and asserts a divergence on a Confirm event. First catch: seed 19, event index 7 (see output above). Bend rejects TooLate and keeps the
record Held with `reserved=1`; the mutant confirms (`reserved=0 sold=1 status=1 confirmedAt=2`, `tally.FxConfirmed=1`).

## 4. Mutants through the harness

`mutants/uc2/harness_test.go` sends each part-B mutant whose events are all contract events through `FindFirst` (seeds 1..500, len 300).
The Bend side is the correct port, so a divergence means the harness rejects the mutant.

```
$ go test -count=1 -v ./mutants/uc2/ -run Harness      (differing keys shortened)
M1:  harness rejects: seed=19 first divergent event index 7   = Confirm ID:11
M1b: harness rejects: seed=7  first divergent event index 108 = Expire ID:11
M2:  harness rejects: seed=2  first divergent event index 120 = Expire ID:6
M3:  harness rejects: seed=2  first divergent event index 11  = Confirm ID:8
M3b: harness rejects: seed=2  first divergent event index 11  = Confirm ID:8
M5:  harness rejects: seed=1  first divergent event index 79  = Reserve ID:11 Qty:100000 Ttl:1
M5a: harness rejects: seed=1  first divergent event index 79  = Reserve ID:11 Qty:100000 Ttl:1
M6:  harness rejects: seed=2  first divergent event index 93  = Expire ID:7
M7:  harness rejects: seed=1  first divergent event index 73  = Reserve ID:5 Qty:2 Ttl:1
--- PASS: TestHarnessRejectsMutants (4.54s)
M4: not catchable by this harness ... 500 sequences agree
--- PASS: TestHarnessCannotSeeM4 (0.90s)
ok  	github.com/derangga/learn-formal-verification/mutants/uc2	5.447s
```

| mutant | caught | seed | first divergent event (index) | what differs from Bend |
|---|---|---|---|---|
| M1 | yes | 19 | 7, Confirm 11 at clock == expiresAt | Bend: TooLate, Held. Go: Confirmed, sold+1 |
| M1b | yes | 7 | 108, Expire 11 at clock == expiresAt | Bend: Expired, FxReleased. Go: NotYet, still Held |
| M2 | yes | 2 | 120, Expire 6 on a non-Held Due record | Bend: NotHeld. Go: second release (returned=2) |
| M3 | yes | 2 | 11, Confirm 8 (Held, Due) | Bend: TooLate. Go: Confirmed |
| M3b | yes | 2 | 11, Confirm 8 (Held, Due) | same event as M3: the first catch is a Held and Due record, which M3 and M3b both mishandle |
| M5 | yes | 1 | 79, Reserve qty 100000 over available | Bend: InsufficientStock. Go: accepted, available truncated to 0 |
| M5a | yes | 1 | 79, same event | Go: available = -10 (Bend has no negative Nat, so this diverges for a different reason than the real bug) |
| M6 | yes | 2 | 93, Expire 7 | `stock.reserved`: Bend 1, Go 3 (leak) |
| M7 | yes | 1 | 73, Reserve id 5 duplicate | Bend: DuplicateId. Go: second record |
| M4 | not run | none | none | needs mutant-only events (ReserveCheck kind 6, ReserveCommit kind 7); the Bend runner rejects kind > 5. Its contract-alphabet view `StepM4Contract` equals core.Step and agreed on all 500 sequences |

M4 is a check-then-act race whose interleaving is only expressible with events outside the contract. The harness cannot see it by
construction; TLA+ and the Go checker (part B) are the tools for it. M5a is caught only because Go goes negative while Bend's Nat cannot;
the harness compares final states, so any mutant that makes Go differ from the correct port is caught, whether or not Bend could host the bug.

## 5. Numbers and timing

- Compared: 500 sequences, 75094 events (average 150 per sequence), all agree on state and tallies.
- Compile of `main.bend`: hyperfine `--runs 3`: 4.880 s +- 0.784 s (UC1: 8.2 s).
- `TestConformanceUC2` (500 seeds, one compile included): 5.985 s +- 1.242 s (hyperfine, 3 runs, warm cache). `-args -seeds 1 -len 1` (about one compile):
  3.720 s +- 0.074 s. Per sequence excluding compile: (5.985 - 3.720) / 499 = 4.5 ms.
- One Bend run of a 300-event input: 2.0 ms +- 0.5 ms (hyperfine -N, 10 runs; awk-generated input, total 5).
- Compiled binary: 152 KB.

## 6. Friction

- One failed compile: `bump_at` called `bump` and `bump` called `bump_at` (mutual recursion). Defs are checked in file order,
  so it was rejected ("a def whose body is implemented before the def is used"). Fix: one def that matches the list, then the
  index (`case 0n` / `case 1n+p`). Nothing else failed; the rest was adapted from the UC1 runner.
- Variable-length state: UC1 printed a fixed slot list; UC2 records are a list, so `show_ress` prints `r<i>` per record in insertion order.
  Bend `put_res` and Go both keep positions, and the two orders agreed on all 500 sequences.
- The tallies are a `List<Tot>` of 11 slots indexed by a unary Nat, which avoids a record type with 11 fields.
- The Bend runner takes total, not a stock list: it fixes sku 0 like the port, so UnknownSku events (sku 1) are the only multi-sku behaviour tested.
- Go uses int64, Bend Nat is unary; the generator never exceeds 100000, so the sums are exact and compared as uint32 on both sides.
- A local M1 is easy: run `core.Step` one tick back for the one boundary case and fix `ConfirmedAt`.

## 7. Size

`bend/uc2/main.bend` 351 lines; `harness/uc2conformance/conformance.go` 427; `conformance_test.go` 101; `mutants/uc2/harness_test.go` 78.
Standard library only.
