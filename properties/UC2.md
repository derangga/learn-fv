# UC2: stock reservation (inventory service)

Status: DRAFT for approval. After approval this file is frozen; the TLA+ spec, the Bend port and laws, and the Go core and tests all implement it. Source: `docs/handover.md` section 5, UC2 P1 to P4 (refined, none dropped or weakened). Anything not in the handover is marked "Proposed addition (not in handover)".

## 1. Scope

The inventory service holds stock counters per SKU and hands out time-limited reservations. Clients (a checkout flow) send `Reserve` and `Confirm`; a timer outside the core sends `Expire`. The wire can drop, duplicate, delay and reorder messages, and the service can crash and restart. The core is the pure function `Step(state, event) -> (state, effects)`. Time is an injected logical clock (`Tick`); no wall clock appears anywhere. In scope: counter safety, expiry, confirm-vs-expiry races, duplicate and reordered delivery, crash and restart. Out of scope: payment, client cancel, SKU creation or restock, liveness (a dropped `Expire` leaves stock reserved; that is not a violation here), SQLite and outbox details.

## 2. State model (shared by TLA+, Bend, Go)

```text
Status  = Held | Confirmed | Expired
Stock   { sku, total, available, reserved, sold }                      all stored, none derived
Res     { id, sku, qty, status, expiresAt, confirmedAt, returned }
State   { up, clock, stocks: List<Stock>, reservations: List<Res> }
```

Types. Every number is an integer. TLA+ uses `Int` and Go uses `int64`, so a buggy `Step` can drive a counter below zero and P1 can fail. Bend uses `Nat` for every number field and `Bool` for `up`; there a counter cannot be negative by type (see P1). `Status`, `Event` (Bend name `Ev`, because Base declares `Event`), effect and reject-reason constructors are the same in all tools, and every constructor name is unique across all four (a clash would break a Bend datatype): `Status` = `Held | Confirmed | Expired`, events as listed below, effects all carry the prefix `Fx`. Harness and tests keep every value below 2^31 so the `Nat` to `U32` crossing never wraps.

- `total` never changes. `available`, `reserved`, `sold` are stored counters, not derived (else P2 is a tautology). Init for a stock: `available = total`, `reserved = sold = 0`; `up = True`, `clock = 0`, no reservations.
- `expiresAt = clock + ttl` when `Reserve` is accepted. **Proposed addition (not in handover):** ghost fields `confirmedAt` (the `clock` when `Confirm` was accepted, else 0) and `returned` (how many times this record's `qty` was added back to `available`), and the flag `up`. All three exist in every tool.
- Derived names used below, defined once. `Due(s, r) == r.expiresAt <= s.clock`. `HeldQty(s, k)` = sum of `r.qty` over `r` in `s.reservations` with `r.sku == k.sku` and `r.status == Held`; `ConfirmedQty(s, k)` the same with `Confirmed`. `s'` is the state part of `Step(s, e)`; `fx` its effects.
- `Frame(s, s', named)`: every field of `s'` not listed in `named` equals the same field of `s`, including all other stocks and records, their list order, `up` and `clock`. "Unchanged" means `Frame` with nothing named and `fx == []`, unless the row lists an effect.
- Subtraction trap: Bend `Nat.sub` truncates at 0 and hides an underflow. No statement in this file uses `-`; they use `+`, `<=` and equalities `a' + q == a`. `Step` computes `x - q` only in a branch that establishes `q <= x` (guard for `Reserve`; A1 and P2 for `Confirm` and `Expire`); each `-` in the port carries a comment naming that guard.

Events consumed by `Step`:

| Event | Fields | Meaning |
|---|---|---|
| `Reserve` | `id, sku, qty, ttl` | hold `qty` of `sku` for `ttl` ticks; client-chosen `id` is the idempotency key |
| `Confirm` | `id` | turn a held reservation into a sale |
| `Expire` | `id` | timer says the reservation's time ran out |
| `Tick` | none | `clock' = clock + 1` |
| `Crash` | none | the service stops |
| `Restart` | none | the service starts again with durable state |

How event lists are formed (the fault model): drop = the event is absent; duplicate = the same event appears twice or more; delay and reorder = any order. `Crash` and `Restart` are ordinary events in the list. TLA+ generates these lists from a network of in-flight messages (drop, duplicate, reorder); Bend laws and Go tests quantify over arbitrary lists.

Crash model (consistent with UC1: an up flag). Durable, survives `Crash`: all of `State` (SQLite), including `clock`. Lost: effects in flight (the reply or outbox message not yet sent, so a client may never see `FxReserved`), and any in-memory timer (pending `Expire` messages; a timer is outside the core, so `Expire` is just another event that may never arrive). A crash after persist but before the reply leaves is therefore "state changed, effect lost". While `up == False`, every event except `Tick` and `Restart` is lost: unchanged, `fx == []`. `Tick` is applied while down: time passes during an outage. Properties never depend on effect delivery, so P1 to P4 hold under any loss; TLA+ models the loss with an `inflight` set that `Crash` clears, and `Step`'s emitted effects are still recorded for P3b.

**Proposed addition (not in handover): effect vocabulary.** `FxReserved{id, sku, qty, expiresAt}`, `FxConfirmed{id}`, `FxReleased{id, qty}` (stock returned to `available`), `FxRejected{id, reason}` with `reason` in `BadRequest | UnknownSku | DuplicateId | InsufficientStock | UnknownReservation | NotHeld | TooLate | NotYet`. A rejected event changes no state.

Bend names (types fixed here; Pair is `A & B`): `init(sku: Nat, total: Nat) -> State`; `step(s: State, e: Ev) -> State & List<Effect>`; `st(r: State & List<Effect>) -> State` (first part); `fx(r: State & List<Effect>) -> List<Effect>` (second part); `run(events: List<Ev>, s: State) -> State` (fold of `st . step`, head first; `events` leftmost for the termination checker); `run_fx(events: List<Ev>, s: State) -> List<Effect>` (all effects, in order); `inv(s: State) -> Bool`; `released_count(id: Nat, es: List<Effect>) -> Nat`. `inv` is the Bool form of `Inv` below.

## 3. Properties

`Inv` = P1 and P2 and P3 and P4a and A1 and A2 (P4a, A1, A2 are in the proposed table and section 4). Bend `inv` omits P1, which holds by type. Invariants are checked in every reachable state, transitions on every step. Every per-event law, here and in section 4, has `Inv(s)` as a hypothesis (a single property is not inductive alone); Bend shape: `for s: State; for e: Ev; for h: {inv(s) == True{} : Bool}; {<conclusion>}`. Invariant lifts to lists: `for events: List<Ev>; for s: State; for h: {inv(s) == True{} : Bool}; {pN(run(events, s)) == True{} : Bool}`. Init must satisfy `Inv` in all three tools: TLA+ checks `Inv` as an `INVARIANT` (TLC tests it on the initial state), Bend law `init_inv: for sku: Nat; for t: Nat; {inv(init(sku, t)) == True{} : Bool}`, Go test `TestInitSatisfiesInv`. Transition properties are per-event laws; list coverage comes from the invariant `_run` laws. Expected missing lemmas (record the cost): `a + b == c` gives `c - b == a`; `+` commutative and associative; `a <= a + b`; a list-sum split at one element.

"Expired" has two readings: status `Expired` (the `Expire` event was applied), or `Due` (time passed). **Decision: P3 and P4 use the status reading.** The `Due` reading is open question 1; its properties are P4a and P4b below.

Handover properties:

| Id | Plain English | Precise statement | Kind | TLA+ | Bend law | Go test |
|---|---|---|---|---|---|---|
| P1 | available stock never goes below zero | for every `k` in `s.stocks`: `k.available >= 0` (signed counters in TLA+ and Go) | safety invariant | `NonNegativeAvailable` | none alone: in `Nat` it holds by type. The Bend counterpart is `p1b_take_step` + `p2_conservation_step`/`_run` + mutant M5. H1 observation, record it | `TestP1NonNegativeAvailable` |
| P2 | available + reserved + sold always equals the total | for every `k`: `k.available + k.reserved + k.sold == k.total` | safety invariant | `Conservation` | `p2_conservation_step`, `p2_conservation_run` | `TestP2Conservation` |
| P3 | an expired reservation returns its stock exactly once | for every `r` in `s.reservations`: `r.returned == 1` if `r.status == Expired`, else `r.returned == 0`. `returned` is incremented in the one branch of `Step` that adds `r.qty` to `available`, and nowhere else | safety invariant | `ExpiredReturnedOnce` | `p3_once_step`, `p3_once_run` | `TestP3ExpiredReturnsOnce` |
| P4 | a reservation cannot be confirmed after it expired | for every `s`, `e`, `r`: if `r.status == Expired` in `s` then `r.status == Expired` in `s'` (so no `Confirm` revives it) | transition | `ExpiredNeverConfirmed` | `p4_expired_stays_step` (per event) | `TestP4ExpiredNeverConfirmed` |

**Proposed addition (not in handover)**, each tied to a handover property:

| Id | Plain English | Precise statement | Kind | TLA+ | Bend law | Go test |
|---|---|---|---|---|---|---|
| P1b | stock is only taken by an accepted `Reserve`, by exactly `qty`, with no truncation | for `k` in `s.stocks`, `k'` the same `sku` in `s'`: if `k'.available < k.available` then `e == Reserve{id, k.sku, qty, ttl}`, `fx == [FxReserved{id, sku, qty, s.clock + ttl}]` (`id, sku, qty, ttl` are the fields of that `Reserve` event `e`) and `k'.available + qty == k.available` | transition | `NoOversell` | `p1b_take_step` | `TestP1bNoOversell` |
| P3b | the counter is real: it equals the effects emitted | for any `events`, with `s0 == init(sku, t)`: for every `r` in `run(events, s0).reservations`, `released_count(r.id, run_fx(events, s0)) == r.returned`, and every such effect has `qty == r.qty`. Counts emitted effects, not delivered ones. TLA+ needs a history variable `emitted` (bag of effects, never cleared by `Crash`) | safety invariant over history | `ReleasedMatchesReturned` | `p3b_released_count_run` (hardest law; if infeasible record a wall) | `TestP3bReleasedEffectCount` |
| P4a | confirmed in time (the `Due` reading of P4) | for every `r`: `r.status == Confirmed` implies `r.confirmedAt < r.expiresAt` | safety invariant | `ConfirmedBeforeDue` | `p4a_before_due_step`, `p4a_before_due_run` | `TestP4aConfirmedBeforeDue` |
| P4b | the same, as a step rule | for every `s`, `e`, `r`: if `r.status != Confirmed` in `s` and `== Confirmed` in `s'`, then in `s` `r.status == Held` and `not Due(s, r)` | transition | `ConfirmOnlyBeforeDue` | `p4b_confirm_guard_step` | `TestP4bConfirmOnlyBeforeDue` |

## 4. Step-effect (pinning) laws and strengthening: Proposed addition (not in handover)

Phase 0 showed that a law that only bounds state lets wrong step functions pass. Each row pins one event in one case. TLA+ mechanism: `Next` sets auxiliary variables `lastEvent` (the event just consumed) and `lastFx` (its effects), as in UC1; every pin and every transition property is an action property `[][lastEvent' = E /\ guard => post]_vars` checked as a TLC `PROPERTY`. Bend: one per-event law each, equalities over `step(s, e)` with `Inv` as hypothesis. Names are TLA+ / Bend / Go.

| Id | Event and case | Pinned effect | Names |
|---|---|---|---|
| A1 | invariant | for every `k`: `k.reserved == HeldQty(s, k)` and `k.sold == ConfirmedQty(s, k)` | `CountersMatchRecords` / `a1_counters_step`, `a1_counters_run` / `TestA1CountersMatchRecords` |
| A2 | invariant | reservation ids are pairwise distinct; every `r.sku` equals some `k.sku` | `UniqueIdsKnownSku` / `a2_unique_step`, `a2_unique_run` / `TestA2UniqueIds` |
| S0 | any event but `Tick`, `Restart`, with `up == False` | unchanged | `PinDown` / `pin_down` / `TestPinDown` |
| S1 | `Tick` (up or down) | `Frame(.., {clock})`, `clock' == clock + 1`, `fx == []` | `PinTick` / `pin_tick` / `TestPinTick` |
| S2 | `Reserve{id,sku,qty,ttl}`, up, accepted: `qty >= 1`, `ttl >= 1`, stock `k` exists for `sku`, no `r.id == id`, `qty <= k.available` | `Frame(.., {k.available, k.reserved, reservations})`; `k.available' + qty == k.available`; `k.reserved' == k.reserved + qty`; one record appended at the end: `Res{id, sku, qty, Held, clock + ttl, 0, 0}`; `fx == [FxReserved{id, sku, qty, clock + ttl}]` | `PinReserveOk` / `pin_reserve_ok` / `TestPinReserveOk` |
| S3 | `Reserve`, up, rejected | unchanged; `fx == [FxRejected{id, c}]`, `c` the first failing check in order: `BadRequest` (`qty == 0` or `ttl == 0`), `UnknownSku`, `DuplicateId` (id exists in any status), `InsufficientStock` (`qty > k.available`). `qty == k.available` is accepted; `qty == k.available + 1` is rejected | `PinReserveRejected` / `pin_reserve_rejected` / `TestPinReserveRejected` |
| S4 | `Confirm{id}`, up, record `r` is `Held` and `not Due` | `Frame(.., {r.status, r.confirmedAt, k.reserved, k.sold})`; `r.status' == Confirmed`, `r.confirmedAt' == clock`; `k.reserved' + r.qty == k.reserved`; `k.sold' == k.sold + r.qty`; `fx == [FxConfirmed{id}]` | `PinConfirmOk` / `pin_confirm_ok` / `TestPinConfirmOk` |
| S5 | `Confirm{id}`, up, rejected | unchanged; `fx == [FxRejected{id, c}]`: no record `UnknownReservation`; status not `Held` `NotHeld`; `Held` and `Due` `TooLate` (stays `Held` until its `Expire` arrives) | `PinConfirmRejected` / `pin_confirm_rejected` / `TestPinConfirmRejected` |
| S6 | `Expire{id}`, up, record `r` is `Held` and `Due` | `Frame(.., {r.status, r.returned, k.available, k.reserved})`; `r.status' == Expired`, `r.returned' == r.returned + 1`; `k.available' == k.available + r.qty`; `k.reserved' + r.qty == k.reserved`; `fx == [FxReleased{id, r.qty}]` | `PinExpireOk` / `pin_expire_ok` / `TestPinExpireOk` |
| S7 | `Expire{id}`, up, rejected | unchanged; `fx == [FxRejected{id, c}]`: no record `UnknownReservation`; status not `Held` `NotHeld` (the duplicate-delivery case); `Held` and `not Due` `NotYet` | `PinExpireRejected` / `pin_expire_rejected` / `TestPinExpireRejected` |
| S8 | `Crash` | `Frame(.., {up})`, `up' == False`, `fx == []` (also when already down) | `PinCrash` / `pin_crash` / `TestPinCrash` |
| S9 | `Restart` | `Frame(.., {up})`, `up' == True`, `fx == []` (also when already up) | `PinRestart` / `pin_restart` / `TestPinRestart` |
| S10 | any event | `total` of every stock and `id, sku, qty, expiresAt` of every record never change; a `Confirmed` or `Expired` record keeps its status | `FieldsStable` / `pin_stable` / `TestPinStable` |
| S11 | duplicate delivery of `Reserve`, `Confirm` or `Expire` | `st(step(st(step(s, e)), e)) == st(step(s, e))`. TLA+ needs no history variable: it follows from S2 to S7, because an accepted event leaves a record that makes the same event rejected-unchanged. Bend and Go also check the two-step form directly. `Tick` is excluded | `DupFollowsFromPins` (derived) / `pin_dup_idempotent` / `TestPinDuplicateDelivery` |

A1, A2 and P4a are auxiliary: `Inv` needs them to be inductive (they make `x - qty` safe and P2 non-trivial). If the user rejects any of them as contract properties, they stay as proof lemmas (auxiliary invariants in `inv`), so P1 to P4 remain provable.

## 5. Mutants this contract must catch

Each is the same bug in TLA+ (`spec/tla/UC2_buggy*.tla`), Go (`mutants/uc2/`) and Bend (`bend/uc2/mutants/`). Source: M1 and M4 are from handover section 7 (off-by-one in reservation expiry; check-then-act race). M7 is the handover's "remove the idempotency check", applied here. Everything else is a **Proposed addition (not in handover)**. P1 kills only where counters are signed (TLA+, Go).

| Id | Mutant | Killed by |
|---|---|---|
| M1 | off-by-one: `Confirm` accepts when `clock <= expiresAt` (handover section 7) | P4a, P4b, S5. Not P4 (status reading) |
| M1b | `Expire` requires `clock > expiresAt` | S6, S7 |
| M2 | double release: `Expire` requires only that the record exists and is `Due`, not status `Held`. A second `Expire` on an `Expired` record does everything S6 does again: `available += qty`, `reserved` reduced by `qty`, `returned += 1` (now 2), a second `FxReleased{id, qty}`. P2 still holds (the two moves cancel) and so does P3b (counter and effects agree at 2) | P3, A1, S7, S11 |
| M3 | `Confirm` only requires that the record exists (no status check, no `Due` check; it must drop both, since an `Expired` record is always `Due`). It does everything S4 does (status `Confirmed`, `reserved` reduced by `qty`, `sold += qty`), so an `Expired` record becomes `Confirmed` | P4, P3, P4a, P4b, A1, S5. P2 kills it in Bend only (truncation of `reserved`); with signed counters the moves cancel and P2 holds |
| M3b | `Confirm` checks `Held` but not `Due` (confirm after the clock passed) | P4a, P4b, S5 |
| M4 | check-then-act race (handover section 7), same in all tools via mutant-only events: `ReserveCheck{id,sku,qty,ttl}` tests `qty <= available` and appends the request to a mutant-only `approved` list without changing counters; `ReserveCommit{id}` takes an approved request and applies S2 without re-checking. Lists `[Check 1, Check 2, Commit 1, Commit 2]` oversell | P1 (TLA+, Go), P1b, P2 |
| M5 | unguarded truncated subtraction: `available := Nat.sub(available, qty)` in Bend; TLA+ `IF available >= qty THEN available - qty ELSE 0`; Go `if a >= q { a - q } else { 0 }` | P2, P1b, S3. Not P1 (the counter stays at 0) |
| M5a | unguarded plain subtraction (TLA+ `Int`, Go `int64`; no Bend counterpart since `Nat` truncates) | P1, P2, P1b, S3 |
| M6 | leak: `Expire` adds to `available` but does not reduce `reserved` | P2, A1, S6 |
| M7 | duplicate `Reserve` with an existing id is accepted and appends a second `Held` record with the same id (takes `qty` again, subject to `qty <= available`, emits a second `FxReserved`). Counters stay balanced, so P1, P2, P1b and A1 all hold | A2, S3, S11 |

## 6. Assumptions and open questions (each with a proposed default)

1. "Expired": status `Expired` or `Due`? Default: status for P3 and P4 (section 3). If you choose `Due`, P4a and P4b are promoted into P4, and M1 and M3b are then killed by P4 itself. Under the status reading they are killed only by the proposed P4a, P4b.
2. Expiry boundary. Default: expired from tick `expiresAt` on (`Due`: `expiresAt <= clock`); `Confirm` needs `clock < expiresAt`, `Expire` needs `Due`; exact complements.
3. Confirm and `Expire` racing. Default: lazy expiry. `Confirm` at or after `expiresAt` is rejected `TooLate`, nothing changes, the record stays `Held` (stock stays in `reserved`) until its `Expire` arrives. A `Confirm` before `expiresAt` makes a later `Expire` `NotHeld`. P2 holds in either order.
4. Crash model. Default: `Crash` and `Restart` are events with an `up` flag; state is durable; in-flight effects and in-memory timers are lost; `Tick` runs while down. Alternative, a departure from handover section 6: no `Crash` or `Restart` event, crash read as a drop or duplicate of one event. Cheaper, but it cannot express "state changed, reply lost" or time passing during an outage.
5. Client cancel. Default: out of scope (no `Cancel`, no `Cancelled`); it would add a second release path.
6. Duplicate `Confirm` or `Reserve`. Default: the second is `FxRejected` (`NotHeld`, `DuplicateId`) even if the first reply was lost. Alternative: replay the first reply. S11 holds either way.
7. SKUs. Default: the contract is per SKU over `stocks: List<Stock>`; TLC and the Bend port use exactly one stock (sku 0), events for another sku get `UnknownSku`; the frame for several SKUs is tested in Go only.
8. TLC bounds (in `UC2.cfg`, restated in every result): 1 SKU, `total = 3`, ids `1..3`, `qty` in `1..3`, `ttl` in `1..2`, `clock <= 4`, each message delivered at most twice, at most 1 `Crash` per behaviour, messages may be dropped or reordered. Bend and Go lists have no such bound; Bend proofs hold for any `total`.
