# UC4: liveness on the UC1 payment flow

Status: DRAFT for approval. After approval this file is frozen. It reuses `properties/UC1.md` section 2 verbatim (state model, events, effects, outboxes, TLA+ variables `slots, orderUp, provUp, net, dup, crashes, retries, lastEvent, lastFx`). **Proposed addition (not in handover)** marks what the user can accept or reject one by one. UC1 pins are written "UC1 A8"; UC4's own fairness assumptions are `FA1` to `FA5` so the ids do not collide.

## 1. Scope

L1 is the handover's only UC4 property: a payment that succeeded at the provider ends up recorded in the order service. "Succeeded at the provider" is the idempotency record `pr(s,o).rec = Approved`. "Recorded" is order status `Paid`, or `Refunded` (reachable only from `Paid`). The flow is UC1's: `PlaceOrder`, `RetryTimeout`, `FlushChargeReq`, `ChargeReqRecv`, `FlushReply`, `PaymentApproved`, with `Drop`, `Duplicate`, `Crash`, `Restart` as faults. Recovery is UC1's "UC4 support": a lost reply is recovered by `RetryTimeout` re-queuing the request, and the provider replays the stored result through `outReply` (no new charge). Out of scope: refund liveness (UC1 Q4), `Declined` orders, any other liveness.

## 2. L1 stated precisely

Plain English: if the provider has approved the charge for order `o`, then the order service has `o` as `Paid` or `Refunded` now or at some later point, under the fairness assumptions of section 3.

```tla
ProvApproved(o) == slots[o].prov.rec = "Approved"                       \* pr(s,o).rec = Approved
Recorded(o)     == slots[o].ord.status \in {"Paid", "Refunded"}         \* st(s,o) in {Paid, Refunded}
ApprovedEventuallyRecorded == \A o \in OrderId : ProvApproved(o) ~> Recorded(o)
```

`P ~> Q` is `[](P => <>Q)`. Both sides are state predicates over UC1 variables only; no new state field.

Consequent: `{Paid, Refunded}`, not `Paid`. `ProvApproved` stays true forever (UC1 A13), and after `Paid -> Refunded` (UC1 A6) `st = Paid` never holds again, so `ProvApproved ~> st = Paid` would be false at every post-refund state on a correct model. `Recorded` is stable (UC1 A12). It still needs `Paid` first, because `Refunded` is reachable only from `Paid`; a refund that skips `Paid` (UC1 M2a) is caught by UC1 P2b, not by L1. `Failed` is not recorded: `rec = Approved` with `st = Failed` violates L1 (L-M3).

Names: TLA+ property `ApprovedEventuallyRecorded` (`PROPERTY`). Bend: the bounded-progress laws of section 5 (L1 itself is not expressible). Go: `TestL1ApprovedEventuallyRecorded`.

## 3. Fairness assumptions

TLC must check L1 under `Spec`; under `Init /\ [][Next]_vars` any liveness property fails by stuttering. Action names: UC1 events as actions (`RetryTimeout(o)`, `FlushChargeReq(o)`, `FlushReply(o)`, `Crash(svc)`, `Restart(svc)`), `Deliver(m)`, `Drop(m)`, `Duplicate(m)`. **Proposed addition (not in handover):** these TLA+ definitions, new in UC4: `Svcs == {OrderSvc, Provider}`; `Msgs` the message values of UC1 section 2; `Min(a,b)`; `Deliver(m)` = remove a copy of `m` from `net` and run the matching receive event, where a down receiver only consumes the copy (UC1 rule D) so `Deliver` is enabled whenever `net[m] > 0`; service events (`PlaceOrder`, `RetryTimeout`, `Flush*`, `RefundOrder`, `Crash`) are enabled only while their service is up, `Restart(svc)` only while it is down.

```tla
fvars == <<slots, orderUp, provUp, net, dup, crashes, retries>>      \* vars without lastEvent, lastFx
FairMsgs == {ChargeReq(o, a) : o \in OrderId, a \in Amounts} \cup {Approved(o) : o \in OrderId}
Fairness ==
  /\ \A svc \in Svcs :  WF_fvars(Restart(svc))                                              \* FA1
  /\ \A o \in OrderId : WF_fvars(RetryTimeout(o))                                           \* FA3
  /\ \A o \in OrderId : WF_fvars(FlushChargeReq(o)) /\ WF_fvars(FlushReply(o))               \* FA4
  /\ \A m \in FairMsgs : SF_fvars(Deliver(m))                                               \* FA5
Spec == Init /\ [][Next]_vars /\ Fairness       \* Next contains Crash(svc) guarded by crashes[svc] < MaxCrashes (FA2)
```

`lastEvent` and `lastFx` are history only, and they are in `vars`, so a `RetryTimeout` that changes only them is a real step of `Next`. Fairness therefore uses the subscript `fvars` (UC4 choice): an action counts as enabled for fairness only if it can change the other seven variables. `Spec` is machine closed: every conjunct is on a subaction of `Next` (stronger subscript, same action). `PlaceOrder`, `RefundOrder`, `Drop`, `Duplicate`, `Crash`, refund and `Declined` deliveries get no fairness: they are environment choices or irrelevant to L1.

| Id | Assumption (formula) | Plain English | Excludes | Why realistic | WF or SF |
|---|---|---|---|---|---|
| FA1 | `\A svc: WF_fvars(Restart(svc))` | a crashed service is restarted | a service down forever | a supervisor restarts it | WF: once down, only `Restart` ends it, so it stays enabled until taken |
| FA2 | **Proposed addition (not in handover):** not in `Fairness`; the guard `crashes[svc] < MaxCrashes` inside `Crash(svc)` in `Next`, so `<>[]~Crash(svc)` | only finitely many crashes | a crash loop where each restarted service crashes before its next step | faults have a last occurrence | not a fairness formula. WF on `Restart` alone does not give L1 under a crash loop (F3), so **L1 is claimed only under FA2**; this narrows what L1 says, and the alternative is Q2 |
| FA3 | `\A o: WF_fvars(RetryTimeout(o))`, no cap (section 4) | "retries keep happening" | an order service whose timer never fires or that gives up | UC1 `Step` has no cap | WF. UC1 A2 guards only on `AwaitingPayment`, but a retry that changes nothing in `fvars` is not enabled for fairness (it only rewrites `lastEvent`, `lastFx`): enabled means `AwaitingPayment`, order up, and (`outCharge = false` or `retries[o] < MaxRetries`). A pending row is cleared by `FlushChargeReq` (FA4), which re-enables the next retry, so retries repeat forever |
| FA4 | **Proposed addition (not in handover):** `\A o: WF_fvars(FlushChargeReq(o)) /\ WF_fvars(FlushReply(o))` | a pending outbox row is eventually put on the wire while the service is up | an outbox poller that never runs | the outbox exists to be polled | WF: the flag stays true until the flush itself clears it; after FA1 and FA2 the service is up from some point on |
| FA5 | **Proposed addition (not in handover):** `\A m \in FairMsgs: SF_fvars(Deliver(m))` | fair-lossy link: a message present in `net` infinitely often is delivered | a network that drops every copy of every retransmission | the standard retransmission assumption; infinitely many drops stay allowed | SF, not WF: `Drop(m)` disables `Deliver(m)`, so `FlushChargeReq; Drop; RetryTimeout; FlushChargeReq; Drop; ...` leaves `Deliver(m)` enabled only intermittently. WF needs continuous enablement, is vacuous there, and L1 fails on that run |

FA5 needs no "delivered while up": a copy consumed by a down service satisfies `Deliver`. After FA1 and FA2 the services are up from some point on, and by FA3 and FA4 fresh copies keep coming, so a later delivery is effective.

Informal argument that FA1 to FA5 give L1: suppose `ProvApproved(o)` and `st(o)` stays `AwaitingPayment` forever. FA3 and FA4 put `ChargeReq(o,a)` on `net` infinitely often; FA5 delivers it infinitely often; each delivery with `rec = Approved` sets `outReply` (UC1 A8); FA4 flushes it, putting `Approved(o)` on `net` infinitely often; FA5 delivers it; `PaymentApproved` gives `Paid` (UC1 A4). Contradiction. The remaining case, `st = Failed` with `rec = Approved`, rests on a cross-side fact ("no approval after a decline") that UC1 Q7 says no UC1 property checks and that Bend cannot state; only TLC's L1 run covers it (mutant L-M3). Each assumption is shown necessary by a mutant in section 7 (F1 to F3).

## 4. TLC model for liveness

**Decision (UC1 section 2 "UC4 support"): lift `MaxRetries`, keep `Drop` unbounded.**
- **Proposed addition (not in handover):** `RetryTimeout` loses its `retries[o] < MaxRetries` guard. `retries[o]` stays in `vars` (same nine-tuple) but saturates: `retries'[o] = Min(retries[o] + 1, MaxRetries)`. `MaxRetries = 2` is then only the saturation value, not a bound on behaviour.
- `Drop` has no budget; FA5 says infinitely many drops cannot hide a message re-sent infinitely often. A drop budget with a retry cap is worse: after the budget the network is perfect, so L1 holds by construction, and the cap must be set above the budget for L1 to be true at all.
- `Crash` keeps its UC1 budget `MaxCrashes`, restated as FA2.

**Proposed addition (not in handover):** `NetCap = 3` (`1 + DupMax`), a model constant. Retries re-send the same `ChargeReq(o,a)` each round, so without a cap copies pile up in `net` and the state space is infinite; the cap does bind. `Wire*` adds a copy only while `net[m] < NetCap`, otherwise the new copy is dropped on send (a `Drop` UC1 already allows). `Duplicate(m)` is disabled while `net[m] = NetCap`, so `dup[m]` is not incremented; `dup[m] < DupMax` stays as in UC1. `TypeOK` bag bound becomes `net[m] \in 0..NetCap`. Other bounds as UC1 Q11: `N = 2`, `Amounts = {5}`, `DupMax = 2`, `MaxCrashes = 1` per service, both `d` values explored.

`spec/tla/UC4.cfg`:

```
SPECIFICATION Spec
CONSTANTS N = 2  Amounts = {5}  DupMax = 2  NetCap = 3  MaxCrashes = 1  MaxRetries = 2
INVARIANT TypeOK Inv
PROPERTY ApprovedEventuallyRecorded
CHECK_DEADLOCK FALSE
```

Pitfalls:
1. **`CONSTRAINT` / `ACTION_CONSTRAINT`** cut successors, so lassos vanish. None used; every bound is inside the spec.
2. **`SYMMETRY`** is unsound for liveness in TLC. Not used, even if `UC1.cfg` uses it; `N = 2`.
3. **Stuttering and deadlock**: fairness is what rules out useless stuttering runs; terminal states have nothing enabled, so `CHECK_DEADLOCK FALSE`.
4. **`INIT`/`NEXT` instead of `SPECIFICATION`** silently drops fairness.
5. **Fairness on an action that never fires** is vacuous; the reach runs below show each fair action fires.
6. **Vacuous truth**: `ProvApproved(o) ~> Recorded(o)` holds if `ProvApproved` is unreachable. **Proposed addition (not in handover):** `UC4_reach` runs. TLC stops at the first violation, so each invariant is its own run with its own cfg (`UC4_reach_<Name>.cfg`, `SpecR` below, same constants and bounds, `INVARIANT <Name>` only); **every run must report that invariant violated**, and a run that finishes clean fails the task. Invariants (`net[m]` is the bag count; `st` is not defined in TLA+, use `slots[o].ord.status`; `lastFx` is a sequence of effects. Shape UC4 requires of `lastEvent`, which UC1.md does not fix, Q4: a record with a `kind` tag and the UC1 section 2 field names, e.g. `[kind |-> "ChargeReqRecv", o |-> o, a |-> a, d |-> d]`, `[kind |-> "PaymentApproved", o |-> o]`, `[kind |-> "Crash", svc |-> svc]`):
   - `NoApproved == \A o: ~ProvApproved(o)`.
   - `NoApprovedUnrecorded == \A o: ~(ProvApproved(o) /\ ~Recorded(o))` (the antecedent holds while the consequent does not yet).
   - `NoLostReply == \A o: ~(ProvApproved(o) /\ slots[o].ord.status = "AwaitingPayment" /\ ~slots[o].prov.outReply /\ net[Approved(o)] = 0)`.
   - `NoReplay == \A o: ~(lastEvent.kind = "ChargeReqRecv" /\ lastEvent.o = o /\ lastFx = <<>> /\ provUp /\ ProvApproved(o) /\ slots[o].prov.outReply)`: a replay, not a first approval (that has `Charge` in `lastFx`) and not a down-service consume (`provUp`).
   - `NoPaymentApprovedEffect == \A o: ~(lastEvent.kind = "PaymentApproved" /\ lastEvent.o = o /\ slots[o].ord.status = "Paid")`.
   - `NoRecovery`: needs history. `UC4_reach.tla` EXTENDS `UC4` and cannot reuse `Spec` or `vars`; it defines `LostReply(o) == ProvApproved(o) /\ slots[o].ord.status = "AwaitingPayment" /\ ~slots[o].prov.outReply /\ net[Approved(o)] = 0`, `varsR == <<vars, lostOnce>>`, `InitR == Init /\ lostOnce = [o \in OrderId |-> FALSE]`, `NextR == Next /\ lostOnce' = [o \in OrderId |-> lostOnce[o] \/ LostReply(o)']`, `SpecR == InitR /\ [][NextR]_varsR`. Reach runs use `SPECIFICATION SpecR` and need no fairness: they ask only whether a state is reachable. `NoRecovery == \A o: ~(lostOnce[o] /\ Recorded(o))` must be violated: recovery after a truly lost reply (no copy in `net`, nothing pending) really runs.
   - `NoRefundedApproved == \A o: ~(ProvApproved(o) /\ slots[o].ord.status = "Refunded")` (the `Refunded` branch of `Recorded` is reachable);
   - one per fair action, `lastEvent.kind \notin {"RetryTimeout"}` and likewise for `FlushChargeReq`, `FlushReply`, `Restart`: `NoRetryFired`, `NoFlushChargeReq`, `NoFlushReply`, `NoRestart`.
7. **Cost**: record state count, distinct states, wall time and workers in every result.

## 5. Bend: what can and cannot be asked

Bend is total, with no temporal logic, infinite traces or coinduction. A law speaks about finite event lists. Faults are an arbitrary list (UC1 section 2), so "every list reaches `Paid`" is false (`[]` never pays); fairness must be part of the list as a schedule. **Proposed addition (not in handover):** Bend-only helpers `run_fx(events, s) -> List<Effect>` (effects of `run`, in order) and:

```text
recovery_trace(s,o) = [Restart(OrderSvc), Restart(Provider), RetryTimeout(o), FlushChargeReq(o),
                       ChargeReqRecv(o, od(s,o).amount, Approve), FlushReply(o), PaymentApproved(o)]   (K = 7)
```

The restarts stand for FA1, `RetryTimeout` for FA3, the flushes for FA4, the two receive events for FA5 (one request and one reply get through). `d` is ignored when `rec != NoRec`.

| Law | Statement (shape) | What it gives |
|---|---|---|
| `l1_recovery_trace` | **Proposed addition (not in handover):** for s, o, h (`inv(s)`), `pr(s,o).rec == Approved`, `st(s,o) == AwaitingPayment`, `Nat.is_le(1n, od(s,o).amount) == True{}`: (i) `has(run_fx(take(4n, recovery_trace(s,o)), s), WireChargeReq(o, od(s,o).amount)) == True{}`, (ii) `has(run_fx(take(6n, recovery_trace(s,o)), s), WireApproved(o)) == True{}`, (iii) `st(run(recovery_trace(s,o), s), o) == Paid` | from any such state, whatever the outbox flags, `orderUp`, `provUp`, one fair round of 7 steps gives `Paid`. (i) and (ii) say the two deliveries were sent, not invented; Bend has no `net`, so without them the law also holds on L-M1 and L-M2 |
| `l1_recovery_after_faults` | **Proposed addition (not in handover):** for xs, s, o, h: let `t = run(xs, s)`; given the hypotheses of `l1_recovery_trace` on `t`, `st(run(xs ++ recovery_trace(t,o), s), o) == Paid` | any prefix of faults, then one clean round. Needs `run_append`, `inv_run` (UC1) |
| `l1_recorded_stable` | **Proposed addition (not in handover):** for xs, s, o, h: `st(s,o)` in `{Paid, Refunded}` gives `st(run(xs,s),o)` in `{Paid, Refunded}` | `Recorded` is stable (UC1 A12); supports the choice of consequent |
| `l1_antecedent_reachable` | **Proposed addition (not in handover):** `run([PlaceOrder(0n,5n), FlushChargeReq(0n), ChargeReqRecv(0n,5n,Approve), FlushReply(0n)], init(2n))` has `rec = Approved`, `st = AwaitingPayment`, `outReply = false` | concrete witness that the hypotheses are satisfiable (reply sent, then lost) |
| `l1_lost_reply_recovers` | **Proposed addition (not in handover):** the same list `++ recovery_trace(.., 0n)` ends with `st(.., 0n) == Paid` | concrete end-to-end witness |

Wall, recorded as a result (handover: "A recorded wall is a valid result"). Bend cannot express: (1) `<>` and `~>`, only a fixed-length schedule; (2) FA1 to FA5, in particular fair loss (no `net`, no infinite runs); (3) "every fair schedule reaches `Paid`": only "this schedule does", the universal statement over lists is false; (4) that the antecedent is reachable in the real flow (the witness law covers one list); (5) cross-side facts such as "`Approved` never coexists with `Failed`": event lists contain never-sent `PaymentDeclined`, so it needs a sent-ness hypothesis (UC1 Q7). L-M3 therefore passes every Bend law here. The Bend result for UC4 is a bounded-progress theorem about `Step`, not L1.

## 6. Go test

`TestL1ApprovedEventuallyRecorded`, on the pure core with the seeded sim transport (`internal/sim`), seeds `1..500`, `N = 3` orders. Orders 0 and 1 use an always-`Approve` issuer; order 2 uses a Decline-then-Approve issuer (first answer `Decline`, later answers `Approve`), so UC1 M5 / L-M3 is reachable: correct code replays `Declined`, the mutant re-asks and approves. Phase 1 (fault phase, 200 scheduler steps): random `Drop`, `Duplicate`, delay and reorder, `Crash`, `Restart`, `RetryTimeout`, `Flush*`, delivery, and a `RefundOrder` for order 1 at a random step (it takes effect only if the order is `Paid` by then). Phase 2 (faults stop; this is the fairness assumption): no drops, duplicates or new crashes; every down service restarted (FA1, FA2); then a round-robin scheduler runs `Flush*`, delivers every message each tick, and fires `RetryTimeout` for each order still `AwaitingPayment` every 3 ticks (FA3 to FA5), at most 30 ticks. Assertion at the end: for every order with provider `rec = Approved`, `Recorded` (`st` in `{Paid, Refunded}`). A failure prints the seed. Non-vacuity, asserted or the test fails as vacuous: (a) at the end of phase 1, at least 10% of seeds have an order `Approved` and still `AwaitingPayment`; (b) at least one seed lost a reply and recovered by retry (more than one `WireChargeReq` for the order); (c) counter `lateRequestAfterFailed`: at least one seed delivered a `ChargeReqRecv` for order 2 after order 2 was already `Failed`; (d) counter `refundedApproved`: at least one seed ends with order 1 `Refunded` and `rec = Approved`, so the `Refunded` branch of `Recorded` is exercised. The Go kill of L-M3 is by seed coverage, not guaranteed per seed: the mutant leaves `Failed` with `rec = Approved` only on seeds where the late approval follows `Declined` (counter (c)); if (c) is zero over all seeds the test fails as vacuous. A finite run shows only that this fault-then-quiet schedule never leaves an approved order unrecorded.

## 7. Mutants

Each is the same bug in every tool where it can be written; "killed by" counts only when the named check fails on the mutant.

| Id | Bug | Killed by | Expected counterexample |
|---|---|---|---|
| L-M1 | **Proposed addition (not in handover):** `RetryTimeout` is a no-op once `retries[o] >= K`, `K = 1`. TLA+ uses the UC1 variable `retries`; Go and Bend use a mutant-only field `retried : Nat` in `OrdRec` (as UC1 M3 does), incremented by each effective `RetryTimeout`; same `K` in all three (needs `K <= MaxRetries`) | TLC L1; Bend `l1_recovery_trace` (i) (a state with `retried = 1` satisfies the hypotheses and sends nothing); Go test | expected shape, not an exact trace: a lasso reached after `PlaceOrder, FlushChargeReq, Deliver (approve), FlushReply, Drop(Approved), RetryTimeout, FlushChargeReq, Drop(ChargeReq)` in which `rec = Approved` and `st = AwaitingPayment` forever. The no-op retries leave `fvars` unchanged, so fairness does not force them; TLC may report a self-loop on a state where only `lastEvent`/`lastFx` change, or a short cycle of no-op retries. UC1's cap caveat made concrete |
| L-M2 | **Proposed addition (not in handover):** provider replay disabled: `ChargeReqRecv` with `rec != NoRec` leaves `outReply` unchanged (UC1 A8 broken) | TLC L1; Bend `l1_recovery_trace` (ii); Go test. UC1 safety properties pass it | cycle lasso: reply dropped once, then `RetryTimeout, FlushChargeReq, Deliver(ChargeReq)` repeat with `outReply = false` and no `Approved(o)` ever sent |
| L-M3 | **Proposed addition (not in handover):** UC1 M5: provider dedupes only on `Approved`, so a request after `Declined` approves | TLC L1; Go test (order 2); UC1 A8, A13. Not Bend (section 5 wall) | `ChargeReq` duplicated, first copy declined, `Declined` delivered, order `Failed`, second copy delivered and approved: `rec = Approved`, `st = Failed`, stutter |
| L-M4 | **Proposed addition (not in handover):** restart loses outbox rows (`Restart(Provider)` sets `outReply := false`, `Restart(OrderSvc)` sets `outCharge := false`; "restart skips the outbox scan") | UC1 A11 only. **Expected to survive L1** in TLC and Go: retries re-create the rows | none. Recorded result: L1 does not depend on outbox durability while FA3 holds |
| F1 | **Proposed addition (not in handover):** `WF_fvars(Deliver(m))` instead of `SF` | TLC L1 | expected shape: after an approval and `Drop(Approved)`, a cycle `RetryTimeout; FlushChargeReq; Drop(ChargeReq)` with `Deliver` never taken. Shows FA5 needs SF |
| F2 | **Proposed addition (not in handover):** drop `WF_fvars(Restart(svc))` | TLC L1 | expected shape: a cycle with the provider down from some point on, in which WF forces `RetryTimeout`, `FlushChargeReq` and a `Deliver` that the down provider only consumes. Shows FA1 |
| F3 | **Proposed addition (not in handover):** `Crash` without its budget (`crashes` saturating) | TLC L1 | expected shape: a cycle containing `Crash` and `Restart` of a service, with deliveries landing while it is down and `Recorded` never reached. Shows FA2 (alternative: SF on every service-up action, Q2) |

A killed mutant must print its counterexample in the result report; L-M4 is reported as a survivor.

## 8. Assumptions and open questions

Each default is already used above. Answer "ok" or change it.

1. **Consequent.** Default `st in {Paid, Refunded}` (section 2). `st = Paid` alone is false on correct models after a refund, so it is not an option.
2. **Crash model.** Default: finitely many crashes (FA2) plus WF on `Restart`, and L1 is claimed only under that. Alternative: unbounded crashes with SF on every service-up action (`Flush*`, `RetryTimeout`, `Deliver`): stronger, heavier TLC run.
3. **Drop.** Default: unbounded, tamed by SF on delivery (FA5). Alternative: a drop budget with `MaxRetries` above it (L1 true almost by construction; not recommended).
4. **Retry guard hook and `lastEvent` shape.** UC4 needs `lastEvent` as the tagged record above. TLA+ cannot redefine an operator of an extended module, so either `UC1.tla` exposes the retry guard and counter update as operators that `UC4.cfg` replaces with `<-`, or `UC4.tla` is a separate module repeating `Next`. Default: separate module; differences limited to the retry guard, the saturating counter, `NetCap`, the `Crash` guard.
5. **`NetCap`, saturation, `UC4_reach` runs, Bend helpers, F1 to F3.** All **Proposed addition (not in handover)**; default accept.
6. **Refund and Declined liveness.** Default out of scope (UC1 Q4); no fairness on refund actions. Add L2 "a declined payment is eventually `Failed`" or a refund L3 on request.
7. **`Inv` and amounts.** `Inv` (UC1 section 3) lacks "`st != None` implies `amount > 0`", so `l1_recovery_trace` carries it as a hypothesis. Default: keep the hypothesis; the alternative is one more `Inv` conjunct in `UC1.md`.
8. **Go phase lengths** (200 steps, 30 ticks, retry every 3 ticks, 500 seeds, 10%): defaults, not part of the property.
9. **Bound statement.** Every result restates `N = 2`, `Amounts = {5}`, `DupMax = 2`, `NetCap = 3`, `MaxCrashes = 1`, `MaxRetries = 2` (saturation only). L1 is checked only inside them; Bend and Go do not check L1 itself.
