import Base
import ./spec.bend as Spec
import ./code.bend as Code

# UC2 laws: a translation of properties/UC2.md sections 3 and 4.
# Draft pending user approval; departures listed in docs/results/uc2-bend.md.
# Every per-event law has Inv(s) as hypothesis `h`. Counter changes are stated in additive form:
# the new counter is a variable (a2, r2) with `a2 + qty == available`, never a subtraction.

# Init satisfies Inv.
law init_inv:
  for sku: Nat
  for t: Nat
  {Spec.inv(Spec.init(sku, t)) == True{} : Bool}

# Inv is preserved by every event.
law inv_step:
  for +s: Spec.State
  for +e: Spec.Ev
  for h: {Spec.inv(s) == True{} : Bool}
  {Spec.inv(Spec.st(Code.step(s, e))) == True{} : Bool}

# Inv is preserved by any event list.
law inv_run:
  for events: List<Spec.Ev>
  for +s: Spec.State
  for h: {Spec.inv(s) == True{} : Bool}
  {Spec.inv(Code.run(events, s)) == True{} : Bool}

# P1b: available drops only by an accepted Reserve, by exactly qty, with the one FxReserved.
law p1b_take_step:
  for +s: Spec.State
  for +e: Spec.Ev
  for h: {Spec.inv(s) == True{} : Bool}
  for hl: {Nat.is_lt(Spec.k_avail(Spec.stock_of(Spec.st(Code.step(s, e)))), Spec.k_avail(Spec.stock_of(s))) == True{} : Bool}
  {Spec.p1b(s, e, Code.step(s, e)) == True{} : Bool}

# P2: available + reserved + sold == total (one event).
law p2_conservation_step:
  for +s: Spec.State
  for +e: Spec.Ev
  for h: {Spec.inv(s) == True{} : Bool}
  {Spec.p2(Spec.st(Code.step(s, e))) == True{} : Bool}

# P2: available + reserved + sold == total (any event list).
law p2_conservation_run:
  for events: List<Spec.Ev>
  for +s: Spec.State
  for h: {Spec.inv(s) == True{} : Bool}
  {Spec.p2(Code.run(events, s)) == True{} : Bool}

# P3: returned is 1 on Expired records, 0 on the rest (one event).
law p3_once_step:
  for +s: Spec.State
  for +e: Spec.Ev
  for h: {Spec.inv(s) == True{} : Bool}
  {Spec.p3(Spec.st(Code.step(s, e))) == True{} : Bool}

# P3: returned is 1 on Expired records, 0 on the rest (any event list).
law p3_once_run:
  for events: List<Spec.Ev>
  for +s: Spec.State
  for h: {Spec.inv(s) == True{} : Bool}
  {Spec.p3(Code.run(events, s)) == True{} : Bool}

# P4a: a Confirmed record has confirmedAt < expiresAt (one event).
law p4a_before_due_step:
  for +s: Spec.State
  for +e: Spec.Ev
  for h: {Spec.inv(s) == True{} : Bool}
  {Spec.p4a(Spec.st(Code.step(s, e))) == True{} : Bool}

# P4a: a Confirmed record has confirmedAt < expiresAt (any event list).
law p4a_before_due_run:
  for events: List<Spec.Ev>
  for +s: Spec.State
  for h: {Spec.inv(s) == True{} : Bool}
  {Spec.p4a(Code.run(events, s)) == True{} : Bool}

# A1: reserved == HeldQty, sold == ConfirmedQty (one event).
law a1_counters_step:
  for +s: Spec.State
  for +e: Spec.Ev
  for h: {Spec.inv(s) == True{} : Bool}
  {Spec.a1(Spec.st(Code.step(s, e))) == True{} : Bool}

# A1: reserved == HeldQty, sold == ConfirmedQty (any event list).
law a1_counters_run:
  for events: List<Spec.Ev>
  for +s: Spec.State
  for h: {Spec.inv(s) == True{} : Bool}
  {Spec.a1(Code.run(events, s)) == True{} : Bool}

# A2: ids pairwise distinct, every record sku is the stock's (one event).
law a2_unique_step:
  for +s: Spec.State
  for +e: Spec.Ev
  for h: {Spec.inv(s) == True{} : Bool}
  {Spec.a2(Spec.st(Code.step(s, e))) == True{} : Bool}

# A2: ids pairwise distinct, every record sku is the stock's (any event list).
law a2_unique_run:
  for events: List<Spec.Ev>
  for +s: Spec.State
  for h: {Spec.inv(s) == True{} : Bool}
  {Spec.a2(Code.run(events, s)) == True{} : Bool}

# P4: an Expired record stays Expired (so no Confirm revives it).
law p4_expired_stays_step:
  for +s: Spec.State
  for +e: Spec.Ev
  for h: {Spec.inv(s) == True{} : Bool}
  for +id: Nat
  for hx: {Spec.status_is(Spec.res_of(s), id, Spec.Expired{}) == True{} : Bool}
  {Spec.status_is(Spec.res_of(Spec.st(Code.step(s, e))), id, Spec.Expired{}) == True{} : Bool}

# P3b: for every record of the final state, the returned counter equals the FxReleased effects emitted, each with the record's qty.
law p3b_released_count_run:
  for events: List<Spec.Ev>
  for +sku: Nat
  for +t: Nat
  {Spec.released_ok(Spec.res_of(Code.run(events, Spec.init(sku, t))), Code.run_fx(events, Spec.init(sku, t))) == True{} : Bool}

# P4b: a record becomes Confirmed only from Held and not Due.
law p4b_confirm_guard_step:
  for +s: Spec.State
  for +e: Spec.Ev
  for h: {Spec.inv(s) == True{} : Bool}
  for +id: Nat
  for +r: Spec.Res
  for hf: {Spec.find_res(Spec.res_of(s), id) == Spec.Got{r} : Spec.Look}
  for hn: {Spec.st_eq(Spec.r_status(r), Spec.Confirmed{}) == False{} : Bool}
  for hs: {Spec.status_is(Spec.res_of(Spec.st(Code.step(s, e))), id, Spec.Confirmed{}) == True{} : Bool}
  {(Spec.r_status(r), Nat.is_le(Spec.r_exp(r), Spec.clock_of(s))) == (Spec.Held{}, False{}) : Spec.Status & Bool}

# S0: while down, every event but Tick and Restart is unchanged with no effects.
law pin_down:
  for +s: Spec.State
  for +e: Spec.Ev
  for h: {Spec.inv(s) == True{} : Bool}
  for he: {Spec.not_tick_restart(e) == True{} : Bool}
  for hu: {Spec.up_of(s) == False{} : Bool}
  {Code.step(s, e) == (s, Nil{}) : Spec.State & List<Spec.Effect>}

# S1: Tick (up or down) only advances the clock.
law pin_tick:
  for +s: Spec.State
  for h: {Spec.inv(s) == True{} : Bool}
  {Code.step(s, Spec.Tick{}) == (Spec.State{Spec.up_of(s), Nat.add(Spec.clock_of(s), 1n), Spec.stock_of(s), Spec.res_of(s)}, Nil{}) : Spec.State & List<Spec.Effect>}

# S2: an accepted Reserve takes qty, appends one Held record, emits FxReserved.
law pin_reserve_ok:
  for +s: Spec.State
  for +id: Nat
  for +sku: Nat
  for +qty: Nat
  for +ttl: Nat
  for +a2: Nat
  for h: {Spec.inv(s) == True{} : Bool}
  for hu: {Spec.up_of(s) == True{} : Bool}
  for hq: {Nat.is_lt(0n, qty) == True{} : Bool}
  for ht: {Nat.is_lt(0n, ttl) == True{} : Bool}
  for hk: {Nat.is_eq(sku, Spec.k_sku(Spec.stock_of(s))) == True{} : Bool}
  for hd: {Spec.find_res(Spec.res_of(s), id) == Spec.NoRes{} : Spec.Look}
  for hl: {Nat.is_le(qty, Spec.k_avail(Spec.stock_of(s))) == True{} : Bool}
  for ha: {Nat.add(a2, qty) == Spec.k_avail(Spec.stock_of(s)) : Nat}
  {Code.step(s, Spec.Reserve{id, sku, qty, ttl}) == (Spec.State{Spec.up_of(s), Spec.clock_of(s), Spec.Stock{Spec.k_sku(Spec.stock_of(s)), Spec.k_total(Spec.stock_of(s)), a2, Nat.add(Spec.k_rsv(Spec.stock_of(s)), qty), Spec.k_sold(Spec.stock_of(s))}, List.append(&2, Spec.Res, Spec.res_of(s), Spec.Res{id, sku, qty, Spec.Held{}, Nat.add(Spec.clock_of(s), ttl), 0n, 0n} <> Nil{})}, Spec.FxReserved{id, sku, qty, Nat.add(Spec.clock_of(s), ttl)} <> Nil{}) : Spec.State & List<Spec.Effect>}

# S3: a rejected Reserve changes nothing and emits FxRejected with the first failing check.
law pin_reserve_rejected:
  for +s: Spec.State
  for +id: Nat
  for +sku: Nat
  for +qty: Nat
  for +ttl: Nat
  for h: {Spec.inv(s) == True{} : Bool}
  for hu: {Spec.up_of(s) == True{} : Bool}
  for hn: {Spec.reserve_ok_g(s, id, sku, qty, ttl) == False{} : Bool}
  {Code.step(s, Spec.Reserve{id, sku, qty, ttl}) == (s, Spec.FxRejected{id, Spec.reserve_reason(s, id, sku, qty, ttl)} <> Nil{}) : Spec.State & List<Spec.Effect>}

# S4: an accepted Confirm moves qty from reserved to sold and marks the record Confirmed at clock.
law pin_confirm_ok:
  for +s: Spec.State
  for +id: Nat
  for +sku: Nat
  for +qty: Nat
  for +exp: Nat
  for +cf: Nat
  for +ret: Nat
  for +r2: Nat
  for h: {Spec.inv(s) == True{} : Bool}
  for hu: {Spec.up_of(s) == True{} : Bool}
  for hf: {Spec.find_res(Spec.res_of(s), id) == Spec.Got{Spec.Res{id, sku, qty, Spec.Held{}, exp, cf, ret}} : Spec.Look}
  for hd: {Nat.is_le(exp, Spec.clock_of(s)) == False{} : Bool}
  for hr: {Nat.add(r2, qty) == Spec.k_rsv(Spec.stock_of(s)) : Nat}
  {Code.step(s, Spec.Confirm{id}) == (Spec.State{Spec.up_of(s), Spec.clock_of(s), Spec.Stock{Spec.k_sku(Spec.stock_of(s)), Spec.k_total(Spec.stock_of(s)), Spec.k_avail(Spec.stock_of(s)), r2, Nat.add(Spec.k_sold(Spec.stock_of(s)), qty)}, Spec.put_res(Spec.res_of(s), id, Spec.Res{id, sku, qty, Spec.Confirmed{}, exp, Spec.clock_of(s), ret})}, Spec.FxConfirmed{id} <> Nil{}) : Spec.State & List<Spec.Effect>}

# S5: a rejected Confirm changes nothing; UnknownReservation, NotHeld or TooLate.
law pin_confirm_rejected:
  for +s: Spec.State
  for +id: Nat
  for h: {Spec.inv(s) == True{} : Bool}
  for hu: {Spec.up_of(s) == True{} : Bool}
  for hn: {Spec.confirm_ok_g(s, id) == False{} : Bool}
  {Code.step(s, Spec.Confirm{id}) == (s, Spec.FxRejected{id, Spec.confirm_reason(s, id)} <> Nil{}) : Spec.State & List<Spec.Effect>}

# S6: an accepted Expire returns qty to available, marks the record Expired, returned + 1.
law pin_expire_ok:
  for +s: Spec.State
  for +id: Nat
  for +sku: Nat
  for +qty: Nat
  for +exp: Nat
  for +cf: Nat
  for +ret: Nat
  for +r2: Nat
  for h: {Spec.inv(s) == True{} : Bool}
  for hu: {Spec.up_of(s) == True{} : Bool}
  for hf: {Spec.find_res(Spec.res_of(s), id) == Spec.Got{Spec.Res{id, sku, qty, Spec.Held{}, exp, cf, ret}} : Spec.Look}
  for hd: {Nat.is_le(exp, Spec.clock_of(s)) == True{} : Bool}
  for hr: {Nat.add(r2, qty) == Spec.k_rsv(Spec.stock_of(s)) : Nat}
  {Code.step(s, Spec.Expire{id}) == (Spec.State{Spec.up_of(s), Spec.clock_of(s), Spec.Stock{Spec.k_sku(Spec.stock_of(s)), Spec.k_total(Spec.stock_of(s)), Nat.add(Spec.k_avail(Spec.stock_of(s)), qty), r2, Spec.k_sold(Spec.stock_of(s))}, Spec.put_res(Spec.res_of(s), id, Spec.Res{id, sku, qty, Spec.Expired{}, exp, cf, Nat.add(ret, 1n)})}, Spec.FxReleased{id, qty} <> Nil{}) : Spec.State & List<Spec.Effect>}

# S7: a rejected Expire changes nothing; UnknownReservation, NotHeld or NotYet.
law pin_expire_rejected:
  for +s: Spec.State
  for +id: Nat
  for h: {Spec.inv(s) == True{} : Bool}
  for hu: {Spec.up_of(s) == True{} : Bool}
  for hn: {Spec.expire_ok_g(s, id) == False{} : Bool}
  {Code.step(s, Spec.Expire{id}) == (s, Spec.FxRejected{id, Spec.expire_reason(s, id)} <> Nil{}) : Spec.State & List<Spec.Effect>}

# S8: Crash sets up to False, nothing else (also when already down).
law pin_crash:
  for +s: Spec.State
  for h: {Spec.inv(s) == True{} : Bool}
  {Code.step(s, Spec.Crash{}) == (Spec.State{False{}, Spec.clock_of(s), Spec.stock_of(s), Spec.res_of(s)}, Nil{}) : Spec.State & List<Spec.Effect>}

# S9: Restart sets up to True, nothing else (also when already up).
law pin_restart:
  for +s: Spec.State
  for h: {Spec.inv(s) == True{} : Bool}
  {Code.step(s, Spec.Restart{}) == (Spec.State{True{}, Spec.clock_of(s), Spec.stock_of(s), Spec.res_of(s)}, Nil{}) : Spec.State & List<Spec.Effect>}

# S10: total, id, sku, qty, expiresAt never change; Confirmed and Expired keep their status.
law pin_stable:
  for +s: Spec.State
  for +e: Spec.Ev
  for h: {Spec.inv(s) == True{} : Bool}
  {Spec.stable(s, Spec.st(Code.step(s, e))) == True{} : Bool}

# S11: delivering a Reserve, Confirm or Expire twice equals delivering it once.
law pin_dup_idempotent:
  for +s: Spec.State
  for +e: Spec.Ev
  for h: {Spec.inv(s) == True{} : Bool}
  for hd: {Spec.dupable(e) == True{} : Bool}
  {Spec.st(Code.step(Spec.st(Code.step(s, e)), e)) == Spec.st(Code.step(s, e)) : Spec.State}
