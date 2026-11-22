# UC1 mutants (M1, M2a, M2b, M3, M4, M5)

Start: 2026-11-22 10:51:01 UTC. End: 2026-11-22 11:29:54 UTC.
Contract: `properties/UC1.md` section 5 (frozen). Each mutant is the same bug in Go (`mutants/uc1`), Bend (`bend/uc1/mutants/<mid>`) and TLA+ (`spec/tla/UC1_buggy*.tla`), with one exception: M3 is not written the same way in every tool (Bend stores `pending` in the `amt` field and `Charge` carries 0, because `ProvRec`'s arity is fixed by the frozen `LAWS.bend`/`PROOF.bend`; Go and TLA+ use a separate `pending` field). M1 in TLA+ is `UC1_buggy.tla` (written by another task). Nothing in `properties/`, `LAWS.bend`, `spec.bend`, `code.bend`, `PROOF.bend`, `internal/`, `UC1.tla` was edited.

TLC bounds (every TLA+ row): `N = 2`, `Amounts = {5}`, `DupMax = 2`, `MaxCrashes = 1`, `MaxRetries = 2`, copied from `UC1.cfg`. Bend has no bound. Go: seeded random runs (1000 sequences of up to 200 events, 2 or 3 slots, `o` up to `n+1`, `a` in {0,1,5,7}) plus an enumerated pin check (see Go below). The Bend gate is the plain `bend PROOF.bend`; `--verdict` cannot run here (Lean missing, see `docs/agent/bend.md`).

## Result table

"Rejected" means the tool printed a failure for a check the bug breaks. No mutant survived any tool, except as the M5 row says (the designed outcome).

| Mutant | Go checks that fail (all Go checks listed) | Harness: first divergent event (Bend = correct port) | Bend gate: first failing lemma (laws that depend on it) | TLA+ violated property (trace length in states) |
|---|---|---|---|---|
| M1 no idempotency check | Inv, P1, A8, A13 | seed 4, event 224 `ChargeReqRecv{o=0,a=3,Approve}` | `pp_charge_recv` (inv_step, inv_run, p1_step, p1_run, p2a_step, p2a_run, p3_run) | `NoDoubleCharge` in `UC1_buggy`, 6 states (other task; rerun by `just check-tla-buggy` below) |
| M2a refund without status check | P2b(a), P2b(b), P3, A6, A12 | seed 1, event 10 `RefundOrder{o=0}` | `ps_refund_order_other` (pin_refund_order_other) | `RefundedOnlyFromPaid`, 2 states (Init, `RefundOrder` on a `None` order) |
| M2b refund without `refundCount < chargeCount` | P2a, Inv, A10 | seed 2, event 152 `RefundReqRecv{o=0}` | `sok_step` (inv_step, inv_run, p1_*, p2a_*, p3_run) | `RefundNeverExceedsCharge`, 11 states |
| M3 check-then-act race | P1, Inv, A8, A13, plus the mutant-only `ProvApplyCharge` pin (slot with pending 1, compared with `core.Step`, which ignores the event) | contract events only: seed 1, event 4 `ChargeReqRecv{o=2,a=2,Approve}` (see note) | `pp_apply` (same law set as M1) | `NoDoubleCharge`, 8 states |
| M4 late `PaymentApproved` sets Paid | P3, A4, A12, Inv, P2b(c) | seed 1, event 47 `PaymentApproved{o=0}` | `op_pay_ok` (same law set as M1) | `TerminalStable`, 9 states |
| M5 dedupe only on Approved | A8, A13 only (Inv, P1, P2a, P2b(a)-(d), P3, A12 pass) | seed 10, event 77 `ChargeReqRecv{o=0,a=1,Approve}` | `ps_replay_declined` (pin_charge_req_recv_replay_declined) | `PinProvRecStable` (A13), 6 states; `PinChargeReqRecv` (A8) also violated, 6 states. A scratch run of the non-killing properties (TypeOK, Inv, P1, P2a, P2b, P3) on M5 was stopped at about 12 min with no violation (1,568,242 distinct states, depth 13, queue still 900,511): partial, not a proof of survival; the Go checks carry that claim |

## Go (`mutants/uc1`)

Files: `mutants.go` (the six steps), `checker_test.go` (checks), `harness_test.go` (harness). `go test ./mutants/...`.

- Each mutant is `func(core.State, core.Event) (core.State, []core.Effect)`: it handles only the buggy case and delegates everything else to `core.Step`. `StepM1`, `StepM2a`, `StepM2b`, `StepM4`, `StepM5`.
- M3 needs a mutant-only field and event. `core.ProvRec` has no `pending`, so `M3State` is `core.State` plus a `Pending []uint32` parallel to `Slots`, and `StepM3(M3State, core.Event) (M3State, []core.Effect)` has a different signature. The extra event is `ProvApplyCharge = core.Restart + 1`, a `Kind` outside the contract enum, defined only in the mutant package; `core.Step` treats it as an unknown event (returns a copy). `StepM3Contract` is the stateless projection to `core.State` (drops `pending`) used by the harness. One decision beyond section 5: `ChargeReqRecv` in M3 also stores `amt := a`, because `ProvApplyCharge(o)` carries no amount and `Charge` needs one.
- The checker re-implements, outside `internal/uc1/core`, Inv, P1 (chargeCount and `Charge` effects per order), P2a, P2b(a) to (d), P3, A12 and A13 over the seeded random runs, and the pins A1 to A11 as an enumerated comparison with `core.Step`: slot 1 of 2 over every combination of status, amount {0,5}, both outbox flags, rec, chargeCount 0..2, refundCount 0..2, amt {0,5}, outReply, all four up/down combinations, every contract event on `o` in {1, 7}, `a` in {0,5}, both decisions (17,280 slot/up states x 96 events = 1,658,880 comparisons per machine, each calling `Step` for mutant and core). `core.Step` itself is the control: no check fails on it (`TestMutantsRejectedByChecks/core`).
- Each mutant has two lists in `expect`: checks that must fail and checks that must pass. The test fails if either list is wrong, so the table above is asserted, not just printed.

```
$ go test ./mutants/... -run Checks -v | grep 'failing checks'
core: failing checks: []
M1:   failing checks: [A13 A8 Inv P1]
M2a:  failing checks: [A12 A6 P2b(a) P2b(b) P3]
M2b:  failing checks: [A10 Inv P2a]
M3:   failing checks: [A13 A8 Inv P1 ProvApplyCharge (mutant-only; core.Step ignores it)]
M4:   failing checks: [A12 A4 Inv P2b(c) P3]
M5:   failing checks: [A13 A8]
ok  github.com/derangga/learn-formal-verification/mutants/uc1  30.686s
```

Verbatim first failures: M5 `A8`: `ChargeReqRecv o=1 a=5 d=Approve on {Rec:Declined ...}: got {Rec:Approved ChargeCount:1 ... OutReply:true} [{Charge 1 5}] want {Rec:Declined ... OutReply:true} []`; M5 `A13`: `ChargeReqRecv order 1: rec Declined -> Approved`; M2a `P3`: `RefundOrder changed terminal order 1: {Failed 5 true false} -> {Refunded 5 true true}`; M2b `P2a`: `after RefundReqRecv: order 0 refund 2 > charge 1`; M4 `P3`: `PaymentApproved changed terminal order 1: {Failed 5 false false} -> {Paid 5 false false}`; M3 `P1`: `after ProvApplyCharge: order 0 chargeCount=2`.

Beyond section 5's "killed by" lists, the checks also found: M1 and M3 break A13 (a `Declined` record flips to `Approved` when a second approve arrives); M4 breaks `Inv` (a refunded order with `outRefund` set goes back to `Paid`) and P2b(c); M2b breaks `Inv`. M5 is killed only by A8 and A13, as the contract says: `Inv`, P1, P2a, P2b and P3 pass because `chargeCount` stays 1 (a charge on a `Failed` order is a cross-side bug).

## Harness (`conformance.Find(bin, step, seed, 300)`, seeds 1 to 500)

`go test ./mutants/... -run Harness -v` (about 19 s). The Bend side is the correct port, so a divergence means the harness rejects the mutant. First seed with a divergence, bisected to the first failing prefix; the full `Divergence` text (both state lines) is in the test log:

| Mutant | seed | N | sequence length | first divergent event index | event |
|---|---|---|---|---|---|
| M1 | 4 | 3 | 257 | 224 | `ChargeReqRecv{O:0 A:3 D:Approve}` (Go chargeCount 2, Bend 1) |
| M2a | 1 | 3 | 88 | 10 | `RefundOrder{O:0}` (Go status 4 Refunded, Bend 0 None) |
| M2b | 2 | 2 | 187 | 152 | `RefundReqRecv{O:0}` (Go refundCount 2, Bend 1) |
| M3 contract only | 1 | 3 | 88 | 4 | `ChargeReqRecv{O:2 A:2 D:Approve}` (Go rec 0 NoRec, Bend rec 1 Approved) |
| M4 | 1 | 3 | 88 | 47 | `PaymentApproved{O:0}` (Go status 2 Paid, Bend 0 None) |
| M5 | 10 | 2 | 149 | 77 | `ChargeReqRecv{O:0 A:1 D:Approve}` (Go rec 1, chargeCount 1; Bend rec 2 Declined, chargeCount 0) |

Control: `core.Step` agrees with Bend on seeds 1 to 20. M1 is also `TestHarnessCatchesM1` in `harness/conformance/conformance_test.go`, which now imports `mutants.StepM1` instead of carrying its own copy.

M3 note: the correct Bend runner cannot receive `ProvApplyCharge`, so the harness is only partly applicable. I drove the contract alphabet only (`StepM3Contract`: `ChargeReqRecv` Approve on `NoRec` only counts a pending apply). The divergence at the first approved request is real, but it comes from the deferral, not from the race (two applies). The race itself is outside the harness's reach: it would need `ProvApplyCharge` in `main.bend`, which would not be the correct port any more.

## Bend (`bend/uc1/mutants/<mid>`, `bash bend/uc1/mutants/run.sh`)

Layout: each directory has copies of `spec.bend`, `code.bend` (mutated), `LAWS.bend` and `PROOF.bend`, plus `EXPECT` (substring of the first error, naming the lemma) and `DIFFERS` (files allowed to differ from `bend/uc1/*.bend`). `LAWS.bend` imports `./spec.bend` and `./code.bend`, so the mutant code has to sit next to a copy of `LAWS.bend`; the copies are byte-identical to the approved files and `run.sh` checks that with `cmp` (LAWS.bend must be identical in every directory; any other file differing must be listed in `DIFFERS`). `main.bend` is not copied, so the harness binary is the correct port. Bend prints the first failing definition only, so "first failing lemma" is what the gate gives; the laws in brackets are the ones whose proofs call that lemma, found by walking the call graph of `PROOF.bend`. The gate checks definitions in file order, and `Laws.inv_step` starts at line 586, so a failure at an earlier line is reported first even when later laws fail too.

```
$ bash bend/uc1/mutants/run.sh; echo rc=$?
m1     PASS rejected as expected (Location: pp_charge_recv)
m2a    PASS rejected as expected (Location: ps_refund_order_other)
m2b    PASS rejected as expected (Location: sok_step)
m3     PASS rejected as expected (Location: pp_apply)
m4     PASS rejected as expected (Location: op_pay_ok)
m5     PASS rejected as expected (Location: ps_replay_declined)
rc=0
```

What each mutant changes (diff against the approved file) and the gate's first error (verbatim lines):

- **M1** `code.bend`, `charge_recv`: both replay cases (`Approved` and `Declined`) now match `Approve` and approve and charge again (`1n+cc`, `Charge`), so `d = Approve` ignores `rec` as in Go `StepM1` and `UC1_buggy.tla`; `Decline` keeps the replay. First error unchanged (`pp_charge_recv`, the `Approved` case comes first). Gate: `SOME PROOFS FAIL`, expected `{ppk(fp(Code.charge_recv(Spec.ProvRec{Spec.Approved{}, cc, rc, am, orr}, k, 1n+pa, d))) == True{} : Bool}`, observed `{Bool.and(Cmp.is_eq(Nat.cmp(cc, 1n)), Cmp.is_le(Nat.cmp(rc, cc))) == True{} : Bool}`, `Location: pp_charge_recv`. Meaning: the provider part of `inv` (chargeCount = 1 when Approved) is not preserved, so `inv_step` and everything built on it fails.
- **M2a** `refund_order`: the pattern `OrdRec{Paid{}, ...}` became `OrdRec{x, ...}`. Gate: expected `(Spec.Slot{Spec.OrdRec{Spec.NoOrder{}, am, oc, orf}, pv}, [])`, observed `(Spec.Slot{Spec.OrdRec{Spec.Refunded{}, am, oc, True{}}, pv}, [])`, `Location: ps_refund_order_other`. This is the pin A6 "any other status: F" (`pin_refund_order_other`). The gate stops there, so P2b and P3 are not reported separately; Go and TLA+ show them failing.
- **M2b** `refund_recv`: the guard argument `Nat.is_lt(refund_count, charge_count)` became `True{}`. Gate: expected `{ppk(fp(Code.refund_pick(pv, k, True{}))) == True{} : Bool}`, observed `... refund_pick(pv, k, Cmp.is_lt(...))`, `Location: sok_step` (the `Inv` chain: `refundCount <= chargeCount` is no longer preserved).
- **M3** needs a new event and a pending count, which `LAWS.bend` forbids changing. Changes: `spec.bend` gets the constructor `ProvApplyCharge{o: Nat}` in `Ev` and a case in `ev_idx`; `code.bend` gets `apply_charge`, a `slot_step` case, a `step1` case; `charge_recv` with `NoRec` and `Approve` now only adds 1 to `pending`. **`pending` is kept in the `amt` field**, because `ProvRec` has five fields that `LAWS.bend` and `PROOF.bend` construct and match by position (a sixth field breaks about 190 sites in frozen or approved files). So in Bend M3 `amt` means "pending" while `rec = NoRec` and "pending still to apply" afterwards; the charge amount is lost and `Charge` carries 0. Go and TLA+ keep a separate `pending` field. No killing law reads `amt`, but this is a different encoding of the same bug, not the same state. `PROOF.bend` gets one lemma `pp_apply` and one case in `sok_step` for the new event. `pp_apply` is split branch by branch like `pp_charge_recv` (NoRec or Declined with zero counts: `{==}`; nonzero counts: `ft_absurd`; `amt = 0`: `hp`), so that only the branch `rec = Approved`, `pending >= 1` is left with the attempt `hp`; a correct apply guarded on `NoRec` would pass this lemma. This edit is only partly validated: paired with the correct `code.bend` the M3 `PROOF.bend` fails on an undefined name (`apply_charge`, `ProvApplyCharge`), so I did not show that the added lemma and case are harmless to the other laws; the evidence is the gate's rejection at the `Approved` branch of `pp_apply` itself. Gate: expected `{Bool.and(Cmp.is_eq(Nat.cmp(cc, 0n)), Cmp.is_le(Nat.cmp(rc, 1n+cc))) == True{} : Bool}`, observed `{Bool.and(Cmp.is_eq(Nat.cmp(cc, 1n)), Cmp.is_le(Nat.cmp(rc, cc))) == True{} : Bool}`, `Location: pp_apply`, source line `case Spec.ProvRec{Spec.Approved{}, cc, rc, 1n+pm, orr}:` (EXPECT pins this line). The apply from `Approved` with `chargeCount = 1` and `pending >= 1` (reachable: two requests, one apply) gives `chargeCount = 2`, which is what `inv_step` cannot hold.
- **M4** `pay_ok`: the pattern `OrdRec{AwaitingPayment{}, ...}` became `OrdRec{x, ...}`. Gate: expected `{False{} == True{} : Bool}`, observed `{True{} == True{} : Bool}`, `Location: op_pay_ok` (case `Refunded` with `outRefund`: the `Paid` result breaks `outRefund => Refunded` in `inv`, so Bend rejects M4 through `Inv`, earlier than P3).
- **M5** `charge_recv`: a `Declined` record with `Approve` now approves and charges. The unchanged `PROOF.bend` fails first in `pp_charge_recv`, but only because the hand proof matches the old code shape: `Inv` still holds for M5 (a `Declined` slot has chargeCount 0, the result is `Approved` with chargeCount 1). I treated that as plumbing and fixed it: `pp_charge_recv` in the M5 `PROOF.bend` has the `Declined` case split into `Approve` (three sub-cases, like `NoRec`) and `Decline`. With that, `inv_step`, `inv_run`, P1, P2a and P3 proofs get past the lemma, and the gate fails at `ps_replay_declined`, line 1211, below `Laws.inv_step` (586) and all lemmas before it. Gate: expected `(Spec.Slot{od, Spec.ProvRec{Spec.Declined{}, cc, rc, am, True{}}}, [])`, observed `Code.with_prov(Code.charge_recv(Spec.ProvRec{Spec.Declined{}, cc, rc, am, orr}, o, 1n+pa, d), od)`, `Location: ps_replay_declined`. That is `pin_charge_req_recv_replay_declined` (A8). A13 (`pin_prov_rec_stable`) also fails but is not reached; the Go and TLA+ rows show it.

`just prove-bend` globs `bend/uc*/PROOF.bend`, so it does not pick up the mutant proofs; `run.sh` is the gate for them (a justfile change is for the orchestrator).

## TLA+ (`spec/tla/UC1_buggy_m2a`, `_m2b`, `_m3`, `_m4`, `_m5`)

Each `.tla` is the current committed `UC1.tla` (re-based after it changed: tighter `TypeOK`, four new Reach invariants) with a minimal diff (7 changed lines for M2a, M2b, M4, M5, 31 for M3); `TypeOK` is kept as in `UC1.tla`, except that M3 adds `pending : Nat` to the provider record (the mutant-only field); `diff spec/tla/UC1.tla spec/tla/UC1_buggy_<m>.tla` shows it. The `.cfg` has the bounds of `UC1.cfg` and the one property section 5 names first. Command: `tlc -metadir $TMPDIR/<run> -config spec/tla/UC1_buggy_<m>.cfg spec/tla/UC1_buggy_<m>.tla`. These five ran concurrently on 2 cores, so wall times are inflated.

| Mutant | Cfg property | TLC output | States generated / distinct | Trace (states) and actions | Wall |
|---|---|---|---|---|---|
| M2a | `PROPERTY RefundedOnlyFromPaid` | `Error: Action property RefundedOnlyFromPaid is violated.` | 6 / 6 | 2: Init, `RefundOrder` | 15 s |
| M2b | `INVARIANT RefundNeverExceedsCharge` | `Error: Invariant RefundNeverExceedsCharge is violated.` | 2,395,142 / 343,923 | 11: PlaceOrder, Flush, Deliver, Flush, Deliver, RefundOrder, Flush, Duplicate, Deliver, Deliver | 154 s |
| M3 | `INVARIANT NoDoubleCharge` | `Error: Invariant NoDoubleCharge is violated.` | 142,679 / 23,086 | 8: PlaceOrder, Flush, Duplicate, Deliver, Deliver, ProvApplyCharge, ProvApplyCharge | 39 s |
| M4 | `PROPERTY TerminalStable` | `Error: Action property TerminalStable is violated.` | 327,163 / 55,242 | 9: PlaceOrder, Flush, Deliver, Flush, Duplicate, Deliver, RefundOrder, Deliver | 58 s |
| M5 | `PROPERTY PinProvRecStable` | `Error: Action property PinProvRecStable is violated.` | 9,822 / 2,358 | 6: PlaceOrder, Flush, Duplicate, Deliver, Deliver | 27 s |

M3 in TLA+ (`UC1_buggy_m3`): `DefProv` gets `pending |-> 0`, `TypeOK` gets `pending : Int`, `Step` gets a `ProvApplyCharge` case (provider event, so rule D uses `provUp`), `Next` gets `\E o \in OrdIds : ProvApplyCharge(o)`, `EventSet` gets the kind. The M3 trace is the expected one: a duplicated charge request, two deliveries (both see `NoRec`), two applies.

Secondary checks (scratch cfgs in `$TMPDIR/cfg`, same bounds, same `.tla`; not committed because a cfg named `*_buggy*` must produce a violation and a cfg without that name needs its own module):

| Scratch cfg | Mutant | Result |
|---|---|---|
| `PinRefundOrder` (A6) | M2a | violated, 2 states |
| `TerminalStable` (P3) | M2a | violated, 7 states |
| `PinPaymentApproved` (A4) | M4 | violated, 9 states |
| `PinLegalTransitions` (A12) | M4 | violated, 9 states |
| `PinChargeReqRecv` (A8) | M5 | violated, 6 states |
| TypeOK, Inv, NoDoubleCharge, RefundNeverExceedsCharge, RefundedOnlyFromPaid, TerminalStable | M5 | stopped at 11:20 UTC (about 12 min), no violation yet, 1,568,242 distinct states (not finished; same wall as `UC1.cfg` at N=2) |

The `PinRefundReqRecv` (A10) TLA+ run for M2b was not done.

`just check-tla-buggy`:

```
== tlc (expect violation) UC1_buggy
Error: Invariant NoDoubleCharge is violated.
== tlc (expect violation) UC1_buggy_m2a
Error: Action property RefundedOnlyFromPaid is violated.
== tlc (expect violation) UC1_buggy_m2b
Error: Invariant RefundNeverExceedsCharge is violated.
== tlc (expect violation) UC1_buggy_m3
Error: Invariant NoDoubleCharge is violated.
== tlc (expect violation) UC1_buggy_m4
Error: Action property TerminalStable is violated.
== tlc (expect violation) UC1_buggy_m5
Error: Action property PinProvRecStable is violated.
check-tla-buggy: 6 buggy spec(s) rejected as expected
rc=0
```

`mutants` tests: `go test ./mutants/...` and `go test ./harness/conformance -run 'HarnessCatchesM1|BendRejectsMalformedInput'` pass (13.4 s).

## Surprises and caveats

- M4's counterexample in TLA+ needs 9 states, M2b's 11: the refund/duplicate depth, not the mutation, drives the TLC cost (154 s for M2b against 6 states for M2a).
- Bend rejects M4 and M2b through `Inv`, not through the P3/P2a laws section 5 names, because the gate stops at the first failing definition and `inv_step` comes first. P3 and P2a are broken too (Go, TLA+); Bend just does not say.
- M5 is the one mutant where the unchanged Bend proof fails for the wrong reason (stale lemma shape) and has to be repaired before the gate speaks about the real law. A mutant is not "rejected" just because `PROOF.bend` stops checking; I checked each first error against Go's list of failing checks (`Inv` fails for M1, M2b, M3, M4 in Go; for M5 it does not, which is why the M5 proof was repaired).
- M3 is not the same bug encoding in every tool: Go and TLA+ carry a separate `pending` field, Bend overloads `amt` (and `Charge` carries 0). The harness cannot drive the real race.
- Bend M2a, M5: the gate names a pin (A6, A8), which is what section 5 lists for those two (M2a: "and A6, A12"; M5: "A8, A13 only"). It does not name P2b or A13.
- TLC left `*_TTrace_*.tla/.bin` files in `spec/tla/` during runs (my runs predate the `-noGenerateSpecTE` note); they were deleted after the last run (`git status --short spec/tla` shows none).
