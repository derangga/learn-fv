import Base

# UC2 port of properties/UC2.md sections 2 to 4: types and every helper the laws read.
# Deviations (all literal-equivalent, see docs/results/uc2-bend.md):
#  - Base owns `Event`, so the event type is `Ev`.
#  - One stock (UC2.md 6.7): `State.stock` is a single `Stock`, not `List<Stock>`.
#    Events for another sku get UnknownSku.
#  - `st` and `fx` live here; `run` and `run_fx` live in code.bend (they call `step`,
#    and code.bend imports this file).
#  - `inv` is one Bool built from P2, P3, P4a, A1, A2 (P1 holds by type in Nat).
#  - Per-record checks of P3, P4a and A2 (sku part) share one fold, `all_rec`, selected by `Facet`.

type Status is Data:
  Held{}
  Confirmed{}
  Expired{}

type Reason is Data:
  BadRequest{}
  UnknownSku{}
  DuplicateId{}
  InsufficientStock{}
  UnknownReservation{}
  NotHeld{}
  TooLate{}
  NotYet{}

type Stock is Data:
  Stock{sku: Nat, total: Nat, available: Nat, reserved: Nat, sold: Nat}

type Res is Data:
  Res{id: Nat, sku: Nat, qty: Nat, status: Status, expiresAt: Nat, confirmedAt: Nat, returned: Nat}

type Look is Data:
  NoRes{}
  Got{r: Res}

type State is Data:
  State{up: Bool, clock: Nat, stock: Stock, reservations: +List<Res>}

type Ev is Data:
  Reserve{id: Nat, sku: Nat, qty: Nat, ttl: Nat}
  Confirm{id: Nat}
  Expire{id: Nat}
  Tick{}
  Crash{}
  Restart{}
  ReserveCheck{id: Nat, sku: Nat, qty: Nat, ttl: Nat}
  ReserveCommit{id: Nat, sku: Nat, qty: Nat, ttl: Nat}

type Effect is Data:
  FxReserved{id: Nat, sku: Nat, qty: Nat, expiresAt: Nat}
  FxConfirmed{id: Nat}
  FxReleased{id: Nat, qty: Nat}
  FxRejected{id: Nat, reason: Reason}

# which per-record property all_rec checks
type Facet is Data:
  PThree{}
  PFourA{}
  PSku{}

# ---------------------------------------------------------------- projections
def up_of(s: State) -> Bool:
  match s:
    case State{u, c, k, rs}:
      u

def clock_of(s: State) -> Nat:
  match s:
    case State{u, c, k, rs}:
      c

def stock_of(s: State) -> Stock:
  match s:
    case State{u, c, k, rs}:
      k

def res_of(s: State) -> +List<Res>:
  match s:
    case State{u, c, k, rs}:
      rs

def k_sku(k: Stock) -> Nat:
  match k:
    case Stock{a, b, c, d, e}:
      a

def k_total(k: Stock) -> Nat:
  match k:
    case Stock{a, b, c, d, e}:
      b

def k_avail(k: Stock) -> Nat:
  match k:
    case Stock{a, b, c, d, e}:
      c

def k_rsv(k: Stock) -> Nat:
  match k:
    case Stock{a, b, c, d, e}:
      d

def k_sold(k: Stock) -> Nat:
  match k:
    case Stock{a, b, c, d, e}:
      e

def r_id(r: Res) -> Nat:
  match r:
    case Res{a, b, c, d, e, f, g}:
      a

def r_sku(r: Res) -> Nat:
  match r:
    case Res{a, b, c, d, e, f, g}:
      b

def r_qty(r: Res) -> Nat:
  match r:
    case Res{a, b, c, d, e, f, g}:
      c

def r_status(r: Res) -> Status:
  match r:
    case Res{a, b, c, d, e, f, g}:
      d

def r_exp(r: Res) -> Nat:
  match r:
    case Res{a, b, c, d, e, f, g}:
      e

def r_conf(r: Res) -> Nat:
  match r:
    case Res{a, b, c, d, e, f, g}:
      f

def r_ret(r: Res) -> Nat:
  match r:
    case Res{a, b, c, d, e, f, g}:
      g

def st(r: State & List<Effect>) -> State:
  match r:
    case (a, b):
      a

def fx(r: State & List<Effect>) -> List<Effect>:
  match r:
    case (a, b):
      b

# -------------------------------------------------------------------- helpers
def st_eq(a: Status, b: Status) -> Bool:
  match a b:
    case Held{} Held{}:
      True{}
    case Confirmed{} Confirmed{}:
      True{}
    case Expired{} Expired{}:
      True{}
    case _ _:
      False{}

def look_none(l: Look) -> Bool:
  match l:
    case NoRes{}:
      True{}
    case Got{_}:
      False{}

# first record with this id
def find_pick(+h: Res, g: Bool, rest: Look) -> Look:
  match g:
    case True{}:
      Got{h}
    case False{}:
      rest

def find_res(rs: +List<Res>, +id: Nat) -> Look:
  match rs:
    case Nil{}:
      NoRes{}
    case +h <> t:
      find_pick(h, Nat.is_eq(r_id(h), id), find_res(t, id))

# replace the first record with this id by x
def put_pick(g: Bool, h: Res, x: Res, t: +List<Res>, rest: +List<Res>) -> +List<Res>:
  match g:
    case True{}:
      x <> t
    case False{}:
      h <> rest

def put_res(rs: +List<Res>, +id: Nat, +x: Res) -> +List<Res>:
  match rs:
    case Nil{}:
      Nil{}
    case +h <> +t:
      put_pick(Nat.is_eq(r_id(h), id), h, x, t, put_res(t, id, x))

# sum of qty over records of one sku in one status (HeldQty, ConfirmedQty)
def sum_pick(g: Bool, q: Nat, rest: Nat) -> Nat:
  match g:
    case True{}:
      Nat.add(q, rest)
    case False{}:
      rest

def qty_sum(rs: +List<Res>, +sku: Nat, +x: Status) -> Nat:
  match rs:
    case Nil{}:
      0n
    case +h <> t:
      sum_pick(Bool.and(Nat.is_eq(r_sku(h), sku), st_eq(r_status(h), x)), r_qty(h), qty_sum(t, sku, x))

def held_qty(rs: +List<Res>, +sku: Nat) -> Nat:
  qty_sum(rs, sku, Held{})

def confirmed_qty(rs: +List<Res>, +sku: Nat) -> Nat:
  qty_sum(rs, sku, Confirmed{})

# r.confirmedAt < r.expiresAt when Confirmed
def p4a_rec(x: Status, cf: Nat, exp: Nat) -> Bool:
  match x:
    case Confirmed{}:
      Nat.is_lt(cf, exp)
    case _:
      True{}

# r.returned == 1 when Expired, else 0
def p3_rec(x: Status, ret: Nat) -> Bool:
  match x:
    case Expired{}:
      Nat.is_eq(ret, 1n)
    case _:
      Nat.is_eq(ret, 0n)

def rec_pick(f: Facet, ksku: Nat, sku: Nat, x: Status, exp: Nat, cf: Nat, ret: Nat) -> Bool:
  match f:
    case PThree{}:
      p3_rec(x, ret)
    case PFourA{}:
      p4a_rec(x, cf, exp)
    case PSku{}:
      Nat.is_eq(sku, ksku)

def rec_ok(f: Facet, ksku: Nat, r: Res) -> Bool:
  match r:
    case Res{i, sku, q, x, exp, cf, ret}:
      rec_pick(f, ksku, sku, x, exp, cf, ret)

def all_rec(+f: Facet, +ksku: Nat, rs: +List<Res>) -> Bool:
  match rs:
    case Nil{}:
      True{}
    case +h <> t:
      Bool.and(rec_ok(f, ksku, h), all_rec(f, ksku, t))

def has_id(rs: +List<Res>, +id: Nat) -> Bool:
  match rs:
    case Nil{}:
      False{}
    case +h <> t:
      Bool.or(Nat.is_eq(r_id(h), id), has_id(t, id))

# reservation ids pairwise distinct
def uniq(rs: +List<Res>) -> Bool:
  match rs:
    case Nil{}:
      True{}
    case +h <> +t:
      Bool.and(Bool.not(has_id(t, r_id(h))), uniq(t))

# the status of the (first) record with this id is x
def look_is(l: Look, x: Status) -> Bool:
  match l:
    case NoRes{}:
      False{}
    case Got{r}:
      st_eq(r_status(r), x)

def status_is(rs: +List<Res>, +id: Nat, x: Status) -> Bool:
  look_is(find_res(rs, id), x)

# -------------------------------------------------------------------- invariant
# P2: available + reserved + sold == total
def p2(s: State) -> Bool:
  match s:
    case State{u, c, Stock{ksku, tot, av, rv, sd}, rs}:
      Nat.is_eq(Nat.add(Nat.add(av, rv), sd), tot)

# P3: every record's returned is 1 if Expired, else 0
def p3(s: State) -> Bool:
  match s:
    case State{u, c, Stock{ksku, tot, av, rv, sd}, rs}:
      all_rec(PThree{}, ksku, rs)

# P4a: every Confirmed record has confirmedAt < expiresAt
def p4a(s: State) -> Bool:
  match s:
    case State{u, c, Stock{ksku, tot, av, rv, sd}, rs}:
      all_rec(PFourA{}, ksku, rs)

# A1: reserved == HeldQty, sold == ConfirmedQty
def a1(s: State) -> Bool:
  match s:
    case State{u, c, Stock{+ksku, tot, av, rv, sd}, +rs}:
      Bool.and(Nat.is_eq(rv, held_qty(rs, ksku)), Nat.is_eq(sd, confirmed_qty(rs, ksku)))

# A2: ids pairwise distinct, every record's sku is the stock's sku
def a2(s: State) -> Bool:
  match s:
    case State{u, c, Stock{+ksku, tot, av, rv, sd}, +rs}:
      Bool.and(uniq(rs), all_rec(PSku{}, ksku, rs))

# Inv without P1 (P1 holds by type in Nat)
def inv(+s: State) -> Bool:
  Bool.and(p2(s), Bool.and(p3(s), Bool.and(p4a(s), Bool.and(a1(s), a2(s)))))

def init(sku: Nat, +total: Nat) -> State:
  State{True{}, 0n, Stock{sku, total, total, 0n, 0n}, Nil{}}

def rc_hit(g: Bool, rest: Nat) -> Nat:
  match g:
    case True{}:
      1n+rest
    case False{}:
      rest

def rc_pick(x: Effect, id: Nat, rest: Nat) -> Nat:
  match x:
    case FxReleased{i, q}:
      rc_hit(Nat.is_eq(i, id), rest)
    case _:
      rest

# ------------------------------------------------------------- effect helpers
def released_count(es: +List<Effect>, +id: Nat) -> Nat:
  match es:
    case Nil{}:
      0n
    case x <> t:
      rc_pick(x, id, released_count(t, id))

def rq_hit(g: Bool, v: Bool) -> Bool:
  match g:
    case True{}:
      v
    case False{}:
      True{}

def rq_pick(x: Effect, id: Nat, q: Nat) -> Bool:
  match x:
    case FxReleased{i, qq}:
      rq_hit(Nat.is_eq(i, id), Nat.is_eq(qq, q))
    case _:
      True{}

# every FxReleased for id carries qty q
def released_qty_ok(es: +List<Effect>, +id: Nat, +q: Nat) -> Bool:
  match es:
    case Nil{}:
      True{}
    case x <> t:
      Bool.and(rq_pick(x, id, q), released_qty_ok(t, id, q))

def eff_eq(a: Effect, b: Effect) -> Bool:
  match a b:
    case FxReserved{i1, s1, q1, x1} FxReserved{i2, s2, q2, x2}:
      Bool.and(Bool.and(Nat.is_eq(i1, i2), Nat.is_eq(s1, s2)), Bool.and(Nat.is_eq(q1, q2), Nat.is_eq(x1, x2)))
    case FxConfirmed{i1} FxConfirmed{i2}:
      Nat.is_eq(i1, i2)
    case FxReleased{i1, q1} FxReleased{i2, q2}:
      Bool.and(Nat.is_eq(i1, i2), Nat.is_eq(q1, q2))
    case _ _:
      False{}

def fx_one2(x: Effect, t: List<Effect>, ef: Effect) -> Bool:
  match t:
    case Nil{}:
      eff_eq(x, ef)
    case _:
      False{}

# fx is exactly [ef]
def fx_one(fx: List<Effect>, ef: Effect) -> Bool:
  match fx:
    case Nil{}:
      False{}
    case x <> t:
      fx_one2(x, t, ef)

def p1b_ev(e: Ev, +s: State, s2: State, f: List<Effect>) -> Bool:
  match e:
    case Reserve{id, +sku, +qty, ttl}:
      Bool.and(Bool.and(Nat.is_eq(sku, k_sku(stock_of(s))), fx_one(f, FxReserved{id, sku, qty, Nat.add(clock_of(s), ttl)})), Nat.is_eq(Nat.add(k_avail(stock_of(s2)), qty), k_avail(stock_of(s))))
    case _:
      False{}

# P1b for one step: if available dropped, the event was an accepted Reserve of exactly the
# amount that disappeared, with the one FxReserved effect.
def p1b(+s: State, +e: Ev, r: State & List<Effect>) -> Bool:
  match r:
    case (s2, f):
      p1b_ev(e, s, s2, f)

# ------------------------------------------------- rejection reasons, in check order
def reserve_ok_g(+s: State, +id: Nat, +sku: Nat, +qty: Nat, +ttl: Nat) -> Bool:
  Bool.and(Bool.and(Nat.is_lt(0n, qty), Nat.is_lt(0n, ttl)), Bool.and(Nat.is_eq(sku, k_sku(stock_of(s))), Bool.and(look_none(find_res(res_of(s), id)), Nat.is_le(qty, k_avail(stock_of(s))))))

# first failing check: BadRequest, UnknownSku, DuplicateId, InsufficientStock
def rsv_why(g1: Bool, g2: Bool, g3: Look, g4: Bool) -> Reason:
  match g1 g2 g3 g4:
    case False{} _ _ _:
      BadRequest{}
    case True{} False{} _ _:
      UnknownSku{}
    case True{} True{} Got{_} _:
      DuplicateId{}
    case _ _ _ _:
      InsufficientStock{}

def reserve_reason(+s: State, +id: Nat, +sku: Nat, +qty: Nat, +ttl: Nat) -> Reason:
  rsv_why(Bool.and(Nat.is_lt(0n, qty), Nat.is_lt(0n, ttl)), Nat.is_eq(sku, k_sku(stock_of(s))), find_res(res_of(s), id), Nat.is_le(qty, k_avail(stock_of(s))))

# Confirm accepted: record Held and not Due
def conf_acc(l: Look, +c: Nat) -> Bool:
  match l:
    case NoRes{}:
      False{}
    case Got{Res{i, sk, q, Held{}, exp, cf, ret}}:
      Bool.not(Nat.is_le(exp, c))
    case Got{_}:
      False{}

def confirm_ok_g(+s: State, +id: Nat) -> Bool:
  conf_acc(find_res(res_of(s), id), clock_of(s))

# UnknownReservation, NotHeld, TooLate (Held and Due)
def conf_why(l: Look, c: Nat) -> Reason:
  match l:
    case NoRes{}:
      UnknownReservation{}
    case Got{Res{i, sk, q, Held{}, exp, cf, ret}}:
      TooLate{}
    case Got{_}:
      NotHeld{}

def confirm_reason(+s: State, +id: Nat) -> Reason:
  conf_why(find_res(res_of(s), id), clock_of(s))

# Expire accepted: record Held and Due
def exp_acc(l: Look, +c: Nat) -> Bool:
  match l:
    case NoRes{}:
      False{}
    case Got{Res{i, sk, q, Held{}, exp, cf, ret}}:
      Nat.is_le(exp, c)
    case Got{_}:
      False{}

def expire_ok_g(+s: State, +id: Nat) -> Bool:
  exp_acc(find_res(res_of(s), id), clock_of(s))

# UnknownReservation, NotHeld, NotYet (Held and not Due)
def exp_why(l: Look, c: Nat) -> Reason:
  match l:
    case NoRes{}:
      UnknownReservation{}
    case Got{Res{i, sk, q, Held{}, exp, cf, ret}}:
      NotYet{}
    case Got{_}:
      NotHeld{}

def expire_reason(+s: State, +id: Nat) -> Reason:
  exp_why(find_res(res_of(s), id), clock_of(s))

# ------------------------------------------------------------ event classes, S10
# S0 covers every event but Tick and Restart
def not_tick_restart(e: Ev) -> Bool:
  match e:
    case Tick{}:
      False{}
    case Restart{}:
      False{}
    case _:
      True{}

# S11 covers Reserve, Confirm and Expire
def dupable(e: Ev) -> Bool:
  match e:
    case Reserve{_, _, _, _}:
      True{}
    case Confirm{_}:
      True{}
    case Expire{_}:
      True{}
    case _:
      False{}

# a Held record may become anything; a Confirmed or Expired record keeps its status
def stat_ok(a: Status, b: Status) -> Bool:
  match a b:
    case Held{} _:
      True{}
    case Confirmed{} Confirmed{}:
      True{}
    case Expired{} Expired{}:
      True{}
    case _ _:
      False{}

# id, sku, qty, expiresAt never change; status rule above
def rec_stable(a: Res, b: Res) -> Bool:
  match a b:
    case Res{i1, s1, q1, x1, e1, c1, r1} Res{i2, s2, q2, x2, e2, c2, r2}:
      Bool.and(Bool.and(Nat.is_eq(i1, i2), Nat.is_eq(s1, s2)), Bool.and(Bool.and(Nat.is_eq(q1, q2), Nat.is_eq(e1, e2)), stat_ok(x1, x2)))

# records of xs keep their positions in ys (ys may have more at the end)
def recs_stable(xs: +List<Res>, ys: +List<Res>) -> Bool:
  match xs ys:
    case Nil{} _:
      True{}
    case h <> t Nil{}:
      False{}
    case h <> t h2 <> t2:
      Bool.and(rec_stable(h, h2), recs_stable(t, t2))

# S10
def stable(+s: State, +s2: State) -> Bool:
  Bool.and(Nat.is_eq(k_total(stock_of(s)), k_total(stock_of(s2))), recs_stable(res_of(s), res_of(s2)))

# P3b as a fold: every record has released_count == returned and every FxReleased for it carries its qty
def released_ok2(rs: +List<Res>, +fxs: +List<Effect>) -> Bool:
  match rs:
    case Nil{}:
      True{}
    case +h <> t:
      Bool.and(Bool.and(Nat.is_eq(released_count(fxs, r_id(h)), r_ret(h)), released_qty_ok(fxs, r_id(h), r_qty(h))), released_ok2(t, fxs))

# Effect is Data, so a plain list can be rebuilt as a reusable one
def fx_data(es: List<Effect>) -> +List<Effect>:
  match es:
    case Nil{}:
      Nil{}
    case x <> t:
      x <> fx_data(t)

def released_ok(rs: +List<Res>, fxs: List<Effect>) -> Bool:
  released_ok2(rs, fx_data(fxs))
