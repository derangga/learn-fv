# UC1 conformance harness: Go core vs compiled Bend

- Start: Sun Nov 22 10:22:13 UTC 2026
- End: Sun Nov 22 10:32:41 AM UTC 2026 (after review fixes)
- Tool: Bend 2.0.40 (compiled binary, stdin), Go test (standard library only).

## 1. Design

The Bend proofs are about `bend/uc1/code.bend`, not the Go service. The harness feeds the same seeded event sequences to
the Go step function and to a compiled Bend binary, and compares the final state. Follows `docs/results/phase0-bend-io.md` §9.

```text
TestConformanceUC1 -> BuildBend (once per test process, 2 min timeout: bend bend/uc1/main.bend -o <tmp>/uc1.bin; skip if no bend)
                   -> Run -> for seed 1..K: Find(bin, step, seed, len)
Find -> GenEvents(seed) -> Compare -> BendRun (Encode, stdin pipe written and closed, 20 s timeout, exit code checked)
                                   -> GoRun (fold step from core.Init(N), total effects, Serialise)
Find -> on mismatch: linear scan of prefixes -> Divergence{seed, N, len, prefix, event, state before, bend line, go line}
main.bend: main -> read /dev/stdin -> exec -> split ' ' -> nums -> groups -> mk_ev -> run_fx (folds Code.step) -> show
```

- `bend/uc1/main.bend` imports `./spec.bend` and `./code.bend` and edits neither. It folds `Code.step` itself (`run_fx`),
  the same fold as `Code.run`, so it can also count effects. It does not call `Code.run`.
- Pluggable core: `conformance.StepFn` has the type of `core.Step`. `Run(t, bin, step, seeds, maxLen)` and
  `Find(bin, step, seed, maxLen)` take it, so the mutants task passes a mutant step and expects a divergence
  (`Find` returns the `Divergence` instead of failing). `BuildBend(t)` compiles the binary and skips when `bend` is missing.
- Effects: compared as per-kind totals: the count, the sum of the order ids and the sum of the amounts
  (`fx.<Kind>`, `fx.<Kind>.o`, `fx.<Kind>.a`; sums are wrapping uint32 on both sides). A missing, extra or wrong-kind effect, or a wrong
  id or amount, diverges even if the state agrees. It is still not an ordered list: two effects with swapped ids that keep the same
  sums would pass.
- Divergence report: on a final-state mismatch the harness scans prefixes 1, 2, ... linearly and reports the first failing prefix
  (every shorter prefix agrees), the event at its end, the Bend state before it, and both lines for that prefix. This costs up to
  one binary run per event, only on failure.
- Compile: `BuildBend` compiles once per test process (sync.Once) with a 2 minute timeout, into a temp directory that is not
  removed (about 120 KB per `go test` run).
- Input size: `File.read` is capped at 16 MiB; `main.bend` treats input of 16 MiB or more as an error (exit 1, "input too large")
  instead of truncating. Checked with a 34 MB and a 20 MB input (both exit 1); the cost is one `String.length` pass.
- Generator: N in 2..3; 1..len events (default 300); kind uniform over the 12 Go kinds; o in 0..N+1 (so out of range occurs);
  amount 0 (1 in 8), 100000 (1 in 8) or 1..4; d both; svc both; Crash and Restart included. Fields a kind does not use are 0.
  Seeds are 1..K (default 500), flags `-seeds` and `-len`.

## 2. Encoding

One line on stdin: `N` then five numbers per event, ASCII digits, single spaces, final newline.

| field | meaning | values |
|---|---|---|
| N | slot count | 0..100000 |
| kind | Go `Kind` | 0 PlaceOrder, 1 RetryTimeout, 2 FlushChargeReq, 3 FlushRefundReq, 4 PaymentApproved, 5 PaymentDeclined, 6 RefundOrder, 7 ChargeReqRecv, 8 RefundReqRecv, 9 FlushReply, 10 Crash, 11 Restart |
| o | order id | 0..100000 (unused for Crash, Restart) |
| a | amount | 0..100000 (used by PlaceOrder, ChargeReqRecv) |
| d | decision | 0 Approve, 1 Decline (used by ChargeReqRecv) |
| svc | service | 0 OrderSvc, 1 Provider (used by Crash, Restart) |

The 100000 cap exists because Bend `Nat` is unary. Output (one line): `orderUp provUp`, then per slot `s<i>.status`
(0 None/NoOrder, 1 AwaitingPayment, 2 Paid, 3 Failed, 4 Refunded), `amount outCharge outRefund rec` (0 NoRec, 1 Approved,
2 Declined) `chargeCount refundCount amt outReply`, then, for each of WireChargeReq, WireRefundReq, WireApproved, WireDeclined, Charge, Refund:
`fx.<Kind>` (count), `fx.<Kind>.o` and `fx.<Kind>.a` (sums). Bools are 0 or 1.

Malformed input exits 1 with `error=...` on stderr: non-digit, empty token (double space, tab, CR), sign, number above 100000
or above U32, input of 16 MiB or more, kind > 11, d > 1, svc > 1, field count not a multiple of 5, empty input, more than one line.
`TestBendRejectsMalformedInput` checks 14 such inputs for a clean nonzero exit (an `*exec.ExitError`, and not a timeout kill).

## 3. Commands and output

```
$ source .nix/env.sh && export GOMODCACHE=$TMPDIR/gomodcache GOCACHE=$TMPDIR/gocache GOPATH=$TMPDIR/gopath GOTOOLCHAIN=local XDG_RUNTIME_DIR=$TMPDIR
$ bend bend/uc1/main.bend -o $TMPDIR/m.bin        # no output: compiles clean
$ printf '2 0 0 5 0 0 2 0 0 0 0 7 0 5 0 0 9 0 0 0 0 9 0 0 0 0\n' | ./m.bin
orderUp=1 provUp=1 s0.status=1 s0.amount=5 s0.outCharge=0 s0.outRefund=0 s0.rec=1 s0.chargeCount=1 s0.refundCount=0 s0.amt=5 s0.outReply=0 s1.status=0 s1.amount=0 s1.outCharge=0 s1.outRefund=0 s1.rec=0 s1.chargeCount=0 s1.refundCount=0 s1.amt=0 s1.outReply=0 fx.WireChargeReq=1 fx.WireChargeReq.o=0 fx.WireChargeReq.a=5 fx.WireRefundReq=0 fx.WireRefundReq.o=0 fx.WireRefundReq.a=0 fx.WireApproved=1 fx.WireApproved.o=0 fx.WireApproved.a=0 fx.WireDeclined=0 fx.WireDeclined.o=0 fx.WireDeclined.a=0 fx.Charge=1 fx.Charge.o=0 fx.Charge.a=5 fx.Refund=0 fx.Refund.o=0 fx.Refund.a=0
$ printf '2 12 0 0 0 0\n' | ./m.bin; echo rc=$?
error=bad kind, decision or service
rc=1
$ ./m.bin < 34MB-input; echo rc=$?
error=input too large (16 MiB or more)
rc=1
```

```
$ go vet ./harness/... && go test -count=1 -v ./harness/...      (divergence lines shortened)
=== RUN   TestConformanceUC1
    conformance_test.go:22: compared 500 sequences, 75787 events: Go core and Bend agree
    conformance_test.go:24: coverage: {OutOfRangeO:28456 ZeroAmount:1611 Crash:[3230 3137] Restart:[3159 3198] DeliveredDown:29591 ChargeReplay:858 Declines:3221 EffectsProduced:1852}
--- PASS: TestConformanceUC1 (9.55s)
=== RUN   TestHarnessCatchesM1
    conformance_test.go:61: mutant M1 caught:
        divergence: seed=4 N=3 sequence length=257
        first failing prefix: 225 events (every shorter prefix agrees); the divergent event is index 224 = {Kind:ChargeReqRecv O:0 A:3 D:Approve Svc:OrderSvc} (ChargeReqRecv)
--- PASS: TestHarnessCatchesM1 (0.95s)
=== RUN   TestBendRejectsMalformedInput
--- PASS: TestBendRejectsMalformedInput (0.09s)
PASS
ok  	github.com/derangga/learn-formal-verification/harness/conformance	10.589s
```

`just harness`: `ok  github.com/derangga/learn-formal-verification/harness/conformance  13.466s` (15.3 s wall with `time`). The binary
is now compiled once, so the three tests share one compile.

### Coverage (500 sequences, 75787 events)

The test fails if any of these is zero. Crash and Restart are `[OrderSvc Provider]`.

| what | count |
|---|---|
| events with o out of range (>= N) | 28456 |
| PlaceOrder or ChargeReqRecv with a = 0 | 1611 |
| Crash [OrderSvc Provider] | 3230, 3137 |
| Restart [OrderSvc Provider] | 3159, 3198 |
| event delivered while its receiver is down | 29591 |
| ChargeReqRecv replay (a > 0, in range, provider up, rec != NoRec) | 858 |
| ChargeReqRecv with Decline | 3221 |
| effects produced | 1852 |

Only 1852 effects in 75787 events (2.4 percent): most events are no-ops because of the down services, out-of-range ids and the
uniform kind choice. Effects are exercised, but a generator biased toward the happy path would reach deeper states.

### Non-vacuity: mutant M1 (ChargeReqRecv approve ignores rec)

`TestHarnessCatchesM1` uses a local `m1Step` and asserts a divergence is found. Reported at seed 4 (first seed that catches it):

```
divergence: seed=4 N=3 sequence length=257
first failing prefix: 225 events (every shorter prefix agrees); the divergent event is index 224 = {Kind:ChargeReqRecv O:0 A:3 D:Approve Svc:OrderSvc} (ChargeReqRecv)
```

The Bend line has `s0.chargeCount=1 s0.amt=4 fx.Charge=1`; the mutant has `s0.chargeCount=2 s0.amt=3 fx.Charge=2`. Bend keeps
the idempotent record; the mutant charges a second time.

## 4. Numbers and timing

- Compared: 500 sequences, 75787 events (average 152 events per sequence, N in 2..3), all agree on state and effect counts.
- Compile of `main.bend` after the fixes: hyperfine `--runs 3`: 8.225 s +- 1.179 s (the first version measured 6.309 s +- 0.158 s; the
  effect sums and the size check made it larger and the machine is noisy). Phase 0 spike programs took 1.5 s.
- `TestConformanceUC1 -seeds 500` (one compile included): 10.115 s +- 0.429 s. `-seeds 1 -len 1` (about one compile): 8.733 s +- 2.253 s.
  Per sequence, excluding compile: about (10.1 - 8.7) / 499 = 3 ms, with large noise (earlier measurement 4.7 ms).
- One Bend run of a 300-event input: 7.8 ms +- 1.0 ms (hyperfine, 10 runs, `-N`).
- `just harness` (three tests, one shared compile): 9.9 s; 13.5 s and 15.3 s wall in an earlier run.
- The coverage check only fails for runs of 10000 events or more, so `-seeds 1 -len 1` still passes.

## 5. Friction

- Bend `match` cannot scrutinise a computed value ("give it its own def"), and defs are checked in file order, so no mutual
  recursion: every `match f(x)` became a helper def that takes the computed value as an argument (`only_line`, `solve_with`,
  `num_then`, `ev_or_bad`, `step_cnt`). The run loop carries the (state, counts) pair as one argument for the same reason.
- Quantities: a value used twice needs `+` (`+k`, `+i`); list types stored in a data field or passed on must be `+List`;
  `+U32` is rejected (U32 is not a datatype) while `+n` in the pattern works. Each fix came from an error message, about
  8 compile iterations.
- `Fail` and `Done` are taken by Base, so the result type uses `Err` and `Okay`.
- `String.lines("a\n")` returns `["a", ""]`, so a single line with its final newline needed an explicit trailing-empty check.
- `U32.read` accepts only digits; "+2", "-1" and "" all give None, so they are rejected (good). Values above U32 are rejected too.
- No stdin effect: reads `/dev/stdin` as a file (Linux only), per Phase 0 §9(d). 
- Out-of-range `o` and `a` are capped at 100000 because `Nat` is unary; the harness generator stays far below.
- The `bend -o` compile (6.3 s) dominates the test; it now happens once per `go test` process.
- `U32.show` and `String.length` on large inputs are linear passes; a 34 MB input takes 6.7 s to reject.

## 6. Size

`bend/uc1/main.bend` 328 lines; `harness/conformance/conformance.go` 325; `conformance_test.go` 86. Standard library only.
