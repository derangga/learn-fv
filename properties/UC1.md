# UC1: idempotent payment (order service and payment provider, with retries)

Status: DRAFT for approval. After approval this file is frozen; TLA+ (`spec/tla/UC1.tla`), the Bend port (`bend/uc1/`) and the Go core (`internal/uc1/core`) must implement exactly what is written here. **Proposed addition (not in handover)** marks what the user can accept or reject one by one.

## 1. Scope

Two services: the order service (owns orders, asks for payment, retries, requests refunds) and the payment provider service (owns the charge ledger and the idempotency record). They talk over an outbox table plus HTTP. A message can be dropped, duplicated, delayed or reordered, and either service can crash and restart; a crash between "state committed" and "message sent" is a reachable state. In scope: one payment per order, retries, duplicate and late messages, refund, crash and restart. Out of scope: partial refunds, several payments per order, cancel, currency, authentication, real card networks, clocks. Liveness is UC4's, but the model must not make UC4's L1 false (section 2, "UC4 support"). Amounts are integers in minor units.

## 2. State model (shared by TLA+, Bend, Go)

Names are the contract. Go: type or const (`uint32` for every number, values stay below 2^32). TLA+: record or string. Bend: datatype or constructor (every number is a `Nat`).

**State** `S = { slots, orderUp, provUp }`. `slots` is a fixed-length sequence of `Slot` indexed by `OrderId = 0..N-1` (Go slice, Bend `List<Slot>`, TLA+ function; never a map, so equality needs no function extensionality). `Step` never reads `N`: an `o` with `o >= length(s.slots)` is outside (rule D, section 3). `N` only fixes the length built by `Init`.
- `Slot = { ord, prov }`.
- `ord : OrdRec = { status, amount, outCharge, outRefund }` (order service side)
  - `status : Status = None | AwaitingPayment | Paid | Failed | Refunded` (`None` = order does not exist)
  - `amount : Nat` (minor units, 0 while `None`)
  - `outCharge, outRefund : Bool` = pending outbox rows "charge request" and "refund request" for this order.
- `prov : ProvRec = { rec, chargeCount, refundCount, amt, outReply }` (provider side)
  - `rec : Res = NoRec | Approved | Declined` is the idempotency record. The idempotency key is the order id: at most one record per order.
  - `chargeCount` = ledger rows "money taken", `refundCount` = ledger rows "money returned", `amt` = amount of the charge, `outReply : Bool` = pending outbox row "send the stored result". **Proposed addition (not in handover):** the `outReply` replay, i.e. a duplicate or retried request re-queues the stored result instead of producing a new charge.
- `orderUp, provUp : Bool`.
- `Init`: every slot `{ord={None,0,false,false}, prov={NoRec,0,0,0,false}}`, both services up.
- Helpers (same names in all three tools): `get(s,o)` = the `Slot` at index `o`, or, when `o >= length(s.slots)`, the default slot `{ord={None,0,false,false}, prov={NoRec,0,0,0,false}}` (the same value as in `Init`); `st(s,o)` = `get(s,o).ord.status`; `pr(s,o)` = `get(s,o).prov`; `od(s,o)` = `get(s,o).ord`; so for an absent slot `st` is `None`, flags are false and counts are 0; `is_terminal(x) = x in {Failed, Refunded}`. `Paid` is not terminal (it can be refunded). Bend also needs `has(fx, ef) : Bool` (effect list membership).

**Durable vs lost.** Everything in `S` except `orderUp`/`provUp` is durable (SQLite): orders, ledger, idempotency record and both outboxes survive `Crash`. Lost on crash: nothing in `S`; messages delivered to a down service are consumed with no effect (they are lost), and nothing can be sent while down.

**Events** (each is one atomic `Step`):

| Event | Fields | Received by | Meaning |
|---|---|---|---|
| `PlaceOrder` | o, a | order svc | client creates an order for `a` > 0 minor units; queues the charge request row |
| `RetryTimeout` | o | order svc | retry timer fired; queues the charge request row again |
| `FlushChargeReq` | o | order svc | sender moves the pending charge request row onto the wire |
| `FlushRefundReq` | o | order svc | sender moves the pending refund request row onto the wire |
| `PaymentApproved` | o | order svc | provider's reply delivered (may be duplicate or late) |
| `PaymentDeclined` | o | order svc | provider's reply delivered (may be duplicate or late) |
| `RefundOrder` | o | order svc | client asks for a refund |
| `ChargeReqRecv` | o, a, d | provider | charge request delivered. **Proposed addition (not in handover):** `d` in {Approve, Decline} is the card issuer's answer, an environment choice used only when `rec = NoRec`, so `Step` stays deterministic |
| `RefundReqRecv` | o | provider | refund request delivered |
| `FlushReply` | o | provider | sender moves the pending reply row onto the wire |
| `Crash` / `Restart` | svc in {OrderSvc, Provider} | n/a | service stops / starts again with durable state intact |

**Proposed addition (not in handover):** the three `Flush*` events as separate events. The handover asks for an outbox plus HTTP; making the send its own event is what makes "persisted but not yet sent" reachable in TLA+ and Bend.

**Effects** (list returned by `Step`): `WireChargeReq(o,a)`, `WireRefundReq(o)`, `WireApproved(o)`, `WireDeclined(o)` (a message goes on the wire) and `Charge(o,a)`, `Refund(o,a)` (ledger rows, written in the same transaction as the state change).

**Step** `Step(s, e) -> (s', fx)` is total and deterministic. Section 4 gives each event exactly.

**Network (outside `Step`).** In TLA+ the wire is a variable `net`, a bag of messages (`ChargeReq(o,a)`, `Approved(o)`, `Declined(o)`, `RefundReq(o)`). Each `Wire*` effect adds a copy. A delivery action picks any message in `net` (that is delay and reorder), removes one copy and runs `Step` on the matching delivery event. Drop = `Drop(m)` removes a copy. Duplicate = `Duplicate(m)` adds a copy, at most `DupMax` times per message. In Go the sim transport does the same, seeded. In Bend there is no `net`: faults are an arbitrary event list (a repeated event is a duplicate, an absent one a drop, order is reorder), which includes never-sent messages and is stronger.

**TLA+ declarations.** Constants: `N`, `Amounts`, `DupMax`, `MaxCrashes`, `MaxRetries` (the last three are model bounds, not part of `Step`). Variables: `slots, orderUp, provUp, net, dup, crashes, retries, lastEvent, lastFx` with `vars` the tuple of all nine; `dup` counts duplicates per message, `crashes` and `retries` count used budget, `lastEvent`/`lastFx` record the `Step` just taken so action properties can name it. `TypeOK` fixes every variable's type (statuses, bag counts within bounds, bools). Invariants are `INVARIANT`, all pins and transition properties are action properties `[][Guard => Post]_vars` checked as `PROPERTY`.

**Bend declarations.** Types `Status`, `Res`, `OrdRec`, `ProvRec`, `Slot`, `State`, `Event`, `Effect` with the constructors above (one constructor per event and per effect). Functions: `step(s,e) -> (State, List<Effect>)`, `fst`, `run(events, s) -> State` (folds `step` head first, effects dropped), `get`, `st`, `pr`, `od`, `is_terminal`, `has`, `init(n) -> State` and `inv(s) -> Bool`. Constant `N = 2n` (used only by `init`; `step` does not know `N`, rule D is by `length(s.slots)`). Laws quantify over any `s : State`, any `e : Event`, any `o : Nat`, and take `inv(s) == True{}` as hypothesis `h` wherever stated; conclusions use `Nat.is_le(..) == True{}` and equalities.

**UC4 support.** The approval can be recovered without a new charge: `RetryTimeout` has no cap in `Step` and works whenever the order is `AwaitingPayment`; a retried request reaches the provider, which sets `outReply` again and re-sends the stored result. So if a reply is lost, the order service can still reach `Paid` whenever messages eventually get through, under UC4's fairness. The retry bound for TLC is `MaxRetries`, a model bound, not a `Step` rule. Caveat for UC4: a TLC cap on retries combined with unbounded `Drop` makes L1 false in the model (every request and reply can be dropped once retries run out), so UC4's cfg must lift `MaxRetries` or bound `Drop`. That is UC4's decision, not this file's.

## 3. Properties

Frame rule **F** (used by every pin and law): in `Step`, every field not named in a "Result" is unchanged (every other slot, the other half of the same slot, `orderUp`, `provUp`, all outbox flags) and `fx = []` unless stated. Rule **D**: if the receiving service is down or `o >= length(s.slots)`, the result is F with `fx = []`.

`Inv(s)` (**Proposed addition (not in handover)** as a contract property; it is a proof lemma in Bend either way): for every `o` in range: provider side, `pr(s,o).chargeCount = 1` if `pr(s,o).rec = Approved` else `0`, and `pr(s,o).refundCount <= pr(s,o).chargeCount`; order side, `od(s,o).outRefund = true` implies `st(s,o) = Refunded`, and `od(s,o).outCharge = true` implies `st(s,o) != None`. The provider conjuncts give P1 and P2a; the order conjuncts are needed for P2b(c). Each conjunct is preserved by every event: A1 and A2 set `outCharge` only with a non-`None` status; A6 sets `outRefund` and `Refunded` together; A7 only clears; status never returns to `None` or leaves `Refunded`; `Init` has all flags false. Names: TLA+ invariant `Inv`, Bend `inv`, Go `TestInv`. Bend laws `init_inv` (`inv(init(N)) == True{}`), `inv_step` (for s, e, h: `inv(fst(step(s,e)))`), `inv_run` (for events, s, h). **Every per-event law below takes `h: inv(s) == True{}` as hypothesis**, because `chargeCount <= 1` alone is not preserved by one event.

| Id | Plain English | Precise statement | Kind | TLA+ | Bend law (shape) | Go test |
|---|---|---|---|---|---|---|
| P1 | An order is never charged more than once, even with retries and duplicate messages. | for all o: `pr(s,o).chargeCount <= 1` | safety invariant | `NoDoubleCharge` | `p1_step`: for s, e, o, h: `is_le(pr(fst(step(s,e)),o).chargeCount, 1n) == True{}`. `p1_run`: same for `run(events,s)` | `TestP1NoDoubleCharge` (seeded fault runs; also `Charge` effects per order <= 1) |
| P2a | A refund is only recorded against an order that was charged. | for all o: `pr(s,o).refundCount <= pr(s,o).chargeCount` | safety invariant | `RefundNeverExceedsCharge` | `p2a_step`, `p2a_run`, shaped as P1 with `is_le(refundCount, chargeCount)` | `TestP2aRefundNeverExceedsCharge` |
| P2b | A refund is only requested on an order that was paid. | with `(s',fx) = Step(s,e)`, for all o: (a) `st(s,o) != Refunded` and `st(s',o) = Refunded` imply `st(s,o) = Paid`; (b) `od(s,o).outRefund = false` and `od(s',o).outRefund = true` imply `st(s,o) = Paid`; (c) `WireRefundReq(o)` in `fx` implies `st(s,o) = Refunded`; (d) `Refund(o,x)` in `fx` implies `pr(s,o).rec = Approved` | transition property | `RefundedOnlyFromPaid` | `p2b_a` to `p2b_d`: for s, e, o, h: each clause over `step(s,e)` (uses `has`). Single step only; the any-list guarantee for refunds is P2a | `TestP2bRefundOnlyFromPaid` |
| P3 | Terminal order states never change. | with `(s',fx) = Step(s,e)`, for all o: `is_terminal(st(s,o))` implies `st(s',o) = st(s,o)`. **Proposed addition (not in handover):** and `od(s',o).amount = od(s,o).amount` | transition property | `TerminalStable` | `p3_step`: for s, e, o, h: `is_terminal(st(s,o)) == True{}` gives `(st(fst(step(s,e)),o), od(fst(step(s,e)),o).amount) == (st(s,o), od(s,o).amount)`. `p3_run`: same for `run(events,s)` (induction on the list) | `TestP3TerminalStable` |

**Proposed addition (not in handover):** the split of the handover's P2 into P2a (provider) and P2b (order); together they keep P2's content.

Reading: "charged" is counted at the provider ledger (`chargeCount`). "Paid" in P2b(a) to (c) is order status `Paid`. Clause (d) reads "paid" as provider `rec = Approved`, not order status `Paid`; the cross-side reading is Q7.

## 4. Step-effect (pinning) laws

**Proposed addition (not in handover)**, all of A1 to A13. Phase 0 showed that invariant-only laws let wrong step functions pass (`docs/results/phase0-bend-smoke.md` section 5). Naming rule: pin `Name` is TLA+ action property `PinName`, Bend law `pin_<name_in_snake_case>`, Go test `TestPinName`. Shape of A1 to A11: for s, event fields, h: guard, then `step(s,e) == (<new state>, <fx>)`. Shape of A12 and A13 (transition constraints over any event): for s, e, o, h: `inv(s) == True{}`, then `R(s, fst(step(s,e)), o) == True{}` where `R` is a Bool function (`legal_transition`, `rec_stable`) built from the sentences in the Result column. Frame F and rule D apply to every row; "up" = the receiving service is up.

| Id | Name | Event, guard | Result |
|---|---|---|---|
| A1 | `PlaceOrder` | `PlaceOrder(o,a)`, `a > 0`, `st = None` | `status := AwaitingPayment, amount := a, outCharge := true` |
| A2 | `RetryTimeout` | `st = AwaitingPayment` | `outCharge := true` (any other status: F) |
| A3 | `FlushChargeReq` | `outCharge = true` | `outCharge := false`; fx = `[WireChargeReq(o, amount)]` |
| A4 | `PaymentApproved` | `st = AwaitingPayment` | `status := Paid` (any other status: F) |
| A5 | `PaymentDeclined` | `st = AwaitingPayment` | `status := Failed` (any other status: F) |
| A6 | `RefundOrder` | `st = Paid` | `status := Refunded, outRefund := true` (any other status: F) |
| A7 | `FlushRefundReq` | `outRefund = true` | `outRefund := false`; fx = `[WireRefundReq(o)]` |
| A8 | `ChargeReqRecv` | `ChargeReqRecv(o,a,d)`, `a > 0` | `rec = NoRec, d = Approve`: `rec := Approved, chargeCount := chargeCount + 1, amt := a, outReply := true`; fx = `[Charge(o,a)]`. `rec = NoRec, d = Decline`: `rec := Declined, outReply := true`. `rec != NoRec`: `outReply := true` only (stored result is replayed later, no new charge). `a = 0`: F |
| A9 | `FlushReply` (replay is a Proposed addition (not in handover), see section 2) | `outReply = true`, `rec != NoRec` | `outReply := false`; fx = `[WireApproved(o)]` if `rec = Approved`, `[WireDeclined(o)]` if `Declined` |
| A10 | `RefundReqRecv` | `rec = Approved`, `refundCount < chargeCount` | `refundCount := refundCount + 1`; fx = `[Refund(o, amt)]` (otherwise F) |
| A11 | `CrashRestart` | `Crash(svc)` / `Restart(svc)` | `Crash`: that service's `up := false`; `Restart`: `up := true`. Rule D does not apply |
| A12 | `LegalTransitions` | any event | `st` changes only along `None -> AwaitingPayment`, `AwaitingPayment -> Paid`, `AwaitingPayment -> Failed`, `Paid -> Refunded` |
| A13 | `ProvRecStable` | any event | `rec` changes only `NoRec -> Approved` or `NoRec -> Declined`; `chargeCount` and `refundCount` never decrease. Provider-side analogue of P3; it is what makes the idempotency record sound |

## 5. Mutants this contract must catch

Each mutant is one bug written the same way in TLA+ (`spec/tla/UC1_buggy*.tla`), Go (`mutants/uc1/`, a variant of the pure core) and Bend (`bend/uc1/mutants/`); all three must reject it where possible. "Killed by" counts a mutant as killed only when the named check fails on it.

| Id | Bug | Killed by | How |
|---|---|---|---|
| M1 | Remove the idempotency check: `ChargeReqRecv` with `d = Approve` ignores `rec`, adds 1 to `chargeCount` and emits `Charge` every time | P1 (and `Inv`, A8) | a retried or duplicated request gives `chargeCount = 2` |
| M2a | Refund without a status check: `RefundOrder` sets `Refunded` and queues the refund row in any status | P2b(a), P3 (from `Failed`) (and A6, A12) | refund on `AwaitingPayment` or `Failed` |
| M2b | **Proposed addition (not in handover):** provider refund without the `refundCount < chargeCount` guard | P2a (and A10) | duplicated `RefundReqRecv` gives `refundCount = 2 > chargeCount = 1` |
| M3 | Check-then-act race. Mutant-only field `pending : Nat` in `ProvRec` and mutant-only event `ProvApplyCharge(o)`, present in all three tools (in Go as a variant core with the extra event, not a real concurrent race). Mutant `ChargeReqRecv` with `rec = NoRec` and `d = Approve` only adds 1 to `pending`; `ProvApplyCharge` with `pending > 0` subtracts 1, adds 1 to `chargeCount`, sets `rec := Approved` and emits `Charge`. The contract's alphabet is unchanged | P1 (and `Inv`) | two copies both check while `rec = NoRec`, so two applies give `chargeCount = 2` |
| M4 | **Proposed addition (not in handover):** a late `PaymentApproved` sets `Paid` without the `AwaitingPayment` guard | P3 (and A4, A12) | reachable: reply duplicated, order paid, refunded, duplicate reply sets `Paid` again |
| M5 | **Proposed addition (not in handover):** provider dedupes only on `Approved`, so a request arriving after `Declined` can approve and charge | A8, A13 only | no P1 to P3 or `Inv` violation (`chargeCount` stays 1): a charge on a `Failed` order. It is rejected by all three tools only if A8 and A13 are accepted, and shows that P1 to P3 miss a cross-side bug (see Q7) |

M1, M2a, M3 and M4 are killed by P1 to P3 together with `Inv` as a lemma, without the other pins. M2b needs P2a, which is an original property; it is marked only because the mutant is new.

## 6. Assumptions and open questions

Each default is already used above. Answer "ok" or change it.

1. **Provider dedupe.** Default: idempotency key = order id, one payment per order, no separate key field.
2. **Where "charged" is counted.** Default: at the provider ledger. Order `Paid` is only the order service's belief.
3. **Terminal states.** Default: `Failed` and `Refunded` terminal, `Paid` not, no `Cancelled`, no retry after `Failed`. Is that your P3?
4. **Refund flow. Proposed addition (not in handover):** the order flips to `Refunded` at once and the provider refund is asynchronous via the outbox. A lost refund request is never resent by `Step`, so a refund can stay half done; that is a liveness gap left out of L1. Accept, or add a refund retry?
5. **Retry cap.** Default: no cap in `Step` (a cap would make L1 false by construction once the budget is spent: approval lost, no more requests). TLC bounds retries with `MaxRetries`. If you want a real cap, say what happens after it (for example a status-poll event).
6. **Crash model.** Default: a crash loses only messages in flight to the down service and the chance to send; durable state and outboxes survive. "Persisted but not sent" is reachable because `Flush*` is its own event.
7. **Cross-side properties.** Under the default none is checked anywhere in this contract. In particular P2's cross-side reading, "a provider refund implies the order was `Paid`", is not checked: P2a is provider-only and P2b is order-only. Likewise "`Paid` implies provider charged" and "no charge on a `Failed` order" (M5 shows the gap). In Bend they would need a sent-ness hypothesis because event lists contain never-sent messages. Option: add TLA+/Go-only invariants `PaidImpliesCharged`, `RefundImpliesRefunded` (`refundCount > 0` implies `st = Refunded`), `NoChargeOnFailed`. Add, or leave to UC4?
8. **Issuer decision as event field `d`.** **Proposed addition (not in handover).** Default: accept.
9. **`DupMax`. Proposed addition (not in handover):** per-message duplication bound for TLC. Default accept.
10. **`Inv` and pins A1 to A13.** Default accept all. `Inv` strengthens P1 and P2a, it does not weaken them. If you reject `Inv` as a contract property it stays as a proof lemma.
11. **TLC bounds (proposed, in `UC1.cfg`).** `N = 2`, `Amounts = {5}`, `DupMax = 2`, `MaxCrashes = 1` per service, `MaxRetries = 2` per order, both `d` values explored. Every result must restate these. Bend has no bound.
