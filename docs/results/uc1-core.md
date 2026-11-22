# UC1 pure core (`internal/uc1/core`)

Start: Sun Nov 22 10:10:14 UTC 2026. End: Sun Nov 22 10:12:10 UTC 2026 (plus results write-up).

## What was built

- `internal/uc1/core/core.go` (348 lines): types and enums from `properties/UC1.md` section 2 (numeric values in contract table order from 0, each with `String()`), `Init`, `Step`, `Get`, `St`, `Pr`, `Od`, `IsTerminal`, `Inv`. Standard library only. `Step` clones the slice, so its input is never mutated. Rule D is checked before the event rule; `Crash` and `Restart` skip it.
- `internal/uc1/core/core_test.go` (377 lines): `TestInv`, `TestP1NoDoubleCharge`, `TestP2aRefundNeverExceedsCharge`, `TestP2bRefundOnlyFromPaid` (clauses a to d), `TestP3TerminalStable`, 11 pins A1 to A11 (`TestPinPlaceOrder` ... `TestPinCrashRestart`), `TestPinLegalTransitions` (A12), `TestPinProvRecStable` (A13), and `TestHelpersAbsentSlot`.
  - Property tests: seeded `math/rand/v2` PCG, 1000 sequences of 0 to 200 events, N = 2 or 3, `a` in {0,1,5,7}, `o` up to N+1 (out of range), both `d`, both services, every event kind including Crash and Restart.
  - Pins check the exact resulting state (so frame F), exact effects, non-mutation of the input, and rule D (receiver down, `o` out of range, `o = 2^32-1`). Pre-states have distinctive content in the neighbouring slots.

## Commands and output

```
$ go vet ./internal/... && go test ./internal/uc1/...
ok  	github.com/derangga/learn-formal-verification/internal/uc1/core	0.460s

$ go test -v ./internal/uc1/...   (tail)
--- PASS: TestInv, TestP1NoDoubleCharge, TestP2aRefundNeverExceedsCharge, TestP2bRefundOnlyFromPaid,
    TestP3TerminalStable, TestPinPlaceOrder, TestPinRetryTimeout, TestPinFlushChargeReq,
    TestPinPaymentApproved, TestPinPaymentDeclined, TestPinRefundOrder, TestPinFlushRefundReq,
    TestPinChargeReqRecv, TestPinFlushReply, TestPinRefundReqRecv, TestPinCrashRestart,
    TestPinLegalTransitions, TestPinProvRecStable, TestHelpersAbsentSlot
PASS
ok  	github.com/derangga/learn-formal-verification/internal/uc1/core	0.413s

$ just test
ok  	github.com/derangga/learn-formal-verification/internal/sim	0.008s
ok  	github.com/derangga/learn-formal-verification/internal/uc1/core	(cached)
```

## Mutation sanity (applied temporarily, reverted, `diff` against the saved original is empty)

M1 (`ChargeReqRecv` with `d = Approve` ignores `rec`; implemented by deleting the `rec != NoRec` case, so a Decline on a recorded order also overwrites `rec`):

```
--- FAIL: TestInv (0.00s)
--- FAIL: TestP1NoDoubleCharge (0.00s)
    core_test.go:84: seq 5 step 69: order 1 chargeCount=2 Charge effects=2
--- FAIL: TestPinChargeReqRecv (0.00s)
--- FAIL: TestPinProvRecStable (0.00s)
    core_test.go:359: {ChargeReqRecv 2 5 Approve OrderSvc}: rec Declined -> Approved
```

M2a (`RefundOrder` without the `Paid` check):

```
--- FAIL: TestP2bRefundOnlyFromPaid (0.00s)
    core_test.go:115: (a) {RefundOrder 0 7 Approve Provider} order 0
--- FAIL: TestP3TerminalStable (0.00s)
    core_test.go:135: {RefundOrder 1 7 Decline OrderSvc} changed terminal order 1: {Status:Failed ...} -> {Status:Refunded ...}
--- FAIL: TestPinRefundOrder (0.00s)
--- FAIL: TestPinLegalTransitions (0.00s)
    core_test.go:348: {RefundOrder 1 1 Approve OrderSvc}: Failed -> Refunded
```

So the property tests are not vacuous.

## Ambiguities resolved (literal reading)

1. Path: `internal/uc1/core` (contract) rather than the tracker's `internal/payment/core`.
2. A guard that fails (PlaceOrder with `a = 0` or status not `None`; FlushChargeReq/FlushRefundReq with the flag false; FlushReply with `outReply` false or `rec = NoRec`) gives frame F with no effects. The contract states F only for some of these; F is the general rule.
3. `Refund(o, amt)` uses the provider's stored `amt`. Effects without an amount (`WireRefundReq`, `WireApproved`, `WireDeclined`) have `A = 0`. `WireChargeReq` carries the order's `amount`.
4. A8, `rec != NoRec`: `outReply := true` regardless of `a > 0` (a = 0 is F first), `d`, or whether `a` matches the stored amount.
5. A10 `RefundReqRecv` is allowed on any order status; it depends only on provider fields.
6. `Crash`/`Restart` ignore `o`, `a`, `d`. An invalid `Svc` value changes nothing. An out-of-range enum value in `Kind` (e.g. 12) is treated as F with no effects, since `Step` must be total.
7. Rule D with `o >= len(Slots)` is compared as `uint64`, so `o = 2^32-1` is out of range, not wrapped.
8. `Step` returns a fresh slice copy even for no-op results; `fx` is nil when empty.
9. `Inv` ranges over in-range slots only; `FlushReply` with `outReply = true` and `rec = NoRec` is not excluded by `Inv` (the contract does not list it), so the F reading in item 2 applies.
10. The `TestP1` effects count is per run, for every `Charge` effect; `Step` is given arbitrary event lists (never-sent messages included), as in the Bend model.
11. M1 as I applied it removed the whole `rec != NoRec` branch (the contract wording covers only `d = Approve`); the kill result is the same for the named tests.

## Review round: rule D cross-service, non-vacuity, extra pins

Test-only changes to `core_test.go` (`core.go` unchanged; line counts now `core.go` 348, `core_test.go` see `wc -l`).

- `TestRuleDOtherServiceDown`: for each of the 10 non-crash event kinds, a state where the event takes effect (checked: result differs from input); with only the non-receiving service down the result and effects must equal the both-up result. Verified by temporary mutants, both reverted (`diff` against saved original empty):
  - order events also require `ProvUp`: `--- FAIL: TestRuleDOtherServiceDown`, `{PlaceOrder 1 5 Approve OrderSvc} with other service down: ...`
  - provider events also require `OrderUp`: `--- FAIL: TestRuleDOtherServiceDown`, `{ChargeReqRecv 1 5 Approve OrderSvc} with other service down: ...`
- Non-vacuity: every seeded property test (Inv, P1, P2a, P2b, P3, A12, A13) counts antecedents over its runs and `t.Fatalf`s if any is 0. Counts (steps/states, summed over each test's 1000 sequences):

```
TestInv                  paid=16104 failed=26174 refunded=9708  charge=572 refund=280 wireRefund=68 onTerminal=2703 replay=728
TestP1NoDoubleCharge     paid=16394 failed=24966 refunded=10494 charge=570 refund=273 wireRefund=70 onTerminal=2813 replay=741
TestP2aRefund...         paid=16593 failed=26252 refunded=9248  charge=590 refund=280 wireRefund=62 onTerminal=2545 replay=751
TestP2bRefundOnlyFromPaid paid=15619 failed=25407 refunded=8256  charge=608 refund=290 wireRefund=56 onTerminal=2526 replay=722
TestP3TerminalStable     paid=15519 failed=27155 refunded=8725  charge=594 refund=298 wireRefund=60 onTerminal=2641 replay=746
TestPinLegalTransitions  paid=15586 failed=29400 refunded=9537  charge=609 refund=283 wireRefund=66 onTerminal=2779 replay=734
TestPinProvRecStable     paid=16438 failed=28196 refunded=10313 charge=596 refund=287 wireRefund=79 onTerminal=2868 replay=678
```
  paid/failed/refunded count slot-states after each step; charge/refund/wireRefund count effects; onTerminal counts order events (service up, o in range) applied to a Failed or Refunded order; replay counts `ChargeReqRecv` with `a > 0`, provider up, `rec != NoRec`.
- New pins: A8 `a=0` with `rec=Declined` and with `NoRec` + `Decline`; A9 `rec=Declined`, `outReply=false`; `TestInv` bad case `rec=Declined, chargeCount=1`.
- `go vet ./internal/...` clean; `go test ./internal/uc1/... -count=1 -v` all PASS, final line `ok  .../internal/uc1/core 0.146s`.
