import Base
import ./spec.bend as Spec

# UC2 executable step. Mirrors internal/uc2/core/core.go (commit f0c3ea8).
# Every guard is computed first and passed to a helper that matches on it
# (Bend cannot match on a computed value). Everything the laws read is in spec.bend.

def rej(+s: Spec.State, id: Nat, c: Spec.Reason) -> Spec.State & List<Spec.Effect>:
  (s, Spec.FxRejected{id, c} <> Nil{})

# S0: while down, every event except Tick and Restart is lost
def gate(up: Bool, +s: Spec.State, r: Spec.State & List<Spec.Effect>) -> Spec.State & List<Spec.Effect>:
  match up:
    case False{}:
      (s, Nil{})
    case True{}:
      r

# ---------------------------------------------------------------------- Reserve
def reserve_acc(s: Spec.State, +id: Nat, +sku: Nat, +qty: Nat, +ttl: Nat) -> Spec.State & List<Spec.Effect>:
  match s:
    case Spec.State{up, +clk, Spec.Stock{ksku, tot, av, rv, sd}, rs}:
      # Nat.sub guard: qty <= available (g4 of `rsv`, checked just before)
      (Spec.State{up, clk, Spec.Stock{ksku, tot, Nat.sub(av, qty), Nat.add(rv, qty), sd}, List.append(&2, Spec.Res, rs, Spec.Res{id, sku, qty, Spec.Held{}, Nat.add(clk, ttl), 0n, 0n} <> Nil{})}, Spec.FxReserved{id, sku, qty, Nat.add(clk, ttl)} <> Nil{})

# g1: qty >= 1 and ttl >= 1; g2: the sku is the stock's; g3: id lookup; g4: qty <= available
def rsv(g1: Bool, g2: Bool, g3: Spec.Look, g4: Bool, +s: Spec.State, +id: Nat, sku: Nat, qty: Nat, ttl: Nat) -> Spec.State & List<Spec.Effect>:
  match g1 g2 g3 g4:
    case False{} _ _ _:
      rej(s, id, Spec.BadRequest{})
    case True{} False{} _ _:
      rej(s, id, Spec.UnknownSku{})
    case True{} True{} Spec.Got{_} _:
      rej(s, id, Spec.DuplicateId{})
    case True{} True{} Spec.NoRes{} False{}:
      rej(s, id, Spec.InsufficientStock{})
    case True{} True{} Spec.NoRes{} True{}:
      reserve_acc(s, id, sku, qty, ttl)

def reserve(+s: Spec.State, +id: Nat, +sku: Nat, +qty: Nat, +ttl: Nat) -> Spec.State & List<Spec.Effect>:
  rsv(Bool.and(Nat.is_lt(0n, qty), Nat.is_lt(0n, ttl)), Nat.is_eq(sku, Spec.k_sku(Spec.stock_of(s))), Spec.find_res(Spec.res_of(s), id), Nat.is_le(qty, Spec.k_avail(Spec.stock_of(s))), s, id, sku, qty, ttl)

# ---------------------------------------------------------------------- Confirm
def confirm_acc(s: Spec.State, +id: Nat, sku: Nat, +qty: Nat, exp: Nat, ret: Nat) -> Spec.State & List<Spec.Effect>:
  match s:
    case Spec.State{up, +clk, Spec.Stock{ksku, tot, av, rv, sd}, rs}:
      # Nat.sub guard: A1 gives reserved == HeldQty >= qty, and the record is Held
      (Spec.State{up, clk, Spec.Stock{ksku, tot, av, Nat.sub(rv, qty), Nat.add(sd, qty)}, Spec.put_res(rs, id, Spec.Res{id, sku, qty, Spec.Confirmed{}, exp, clk, ret})}, Spec.FxConfirmed{id} <> Nil{})

def conf2(x: Spec.Status, due: Bool, +s: Spec.State, +id: Nat, sku: Nat, qty: Nat, exp: Nat, ret: Nat) -> Spec.State & List<Spec.Effect>:
  match x due:
    case Spec.Held{} False{}:
      confirm_acc(s, id, sku, qty, exp, ret)
    case Spec.Held{} True{}:
      rej(s, id, Spec.TooLate{})
    case Spec.Confirmed{} _:
      rej(s, id, Spec.NotHeld{})
    case Spec.Expired{} _:
      rej(s, id, Spec.NotHeld{})

def conf1(l: Spec.Look, +s: Spec.State, +id: Nat) -> Spec.State & List<Spec.Effect>:
  match l:
    case Spec.NoRes{}:
      rej(s, id, Spec.UnknownReservation{})
    case Spec.Got{Spec.Res{i, sku, qty, x, +exp, cf, ret}}:
      conf2(x, Nat.is_le(exp, Spec.clock_of(s)), s, id, sku, qty, exp, ret)

def confirm(+s: Spec.State, +id: Nat) -> Spec.State & List<Spec.Effect>:
  conf1(Spec.find_res(Spec.res_of(s), id), s, id)

# ----------------------------------------------------------------------- Expire
def expire_acc(s: Spec.State, +id: Nat, sku: Nat, +qty: Nat, exp: Nat, cf: Nat, +ret: Nat) -> Spec.State & List<Spec.Effect>:
  match s:
    case Spec.State{up, clk, Spec.Stock{ksku, tot, av, rv, sd}, rs}:
      # Nat.sub guard: A1 gives reserved == HeldQty >= qty, and the record is Held
      (Spec.State{up, clk, Spec.Stock{ksku, tot, Nat.add(av, qty), Nat.sub(rv, qty), sd}, Spec.put_res(rs, id, Spec.Res{id, sku, qty, Spec.Expired{}, exp, cf, Nat.add(ret, 1n)})}, Spec.FxReleased{id, qty} <> Nil{})

def exp2(x: Spec.Status, due: Bool, +s: Spec.State, +id: Nat, sku: Nat, qty: Nat, exp: Nat, cf: Nat, ret: Nat) -> Spec.State & List<Spec.Effect>:
  match x due:
    case Spec.Held{} True{}:
      expire_acc(s, id, sku, qty, exp, cf, ret)
    case Spec.Held{} False{}:
      rej(s, id, Spec.NotYet{})
    case Spec.Confirmed{} _:
      rej(s, id, Spec.NotHeld{})
    case Spec.Expired{} _:
      rej(s, id, Spec.NotHeld{})

def exp1(l: Spec.Look, +s: Spec.State, +id: Nat) -> Spec.State & List<Spec.Effect>:
  match l:
    case Spec.NoRes{}:
      rej(s, id, Spec.UnknownReservation{})
    case Spec.Got{Spec.Res{i, sku, qty, x, +exp, cf, ret}}:
      exp2(x, Nat.is_le(exp, Spec.clock_of(s)), s, id, sku, qty, exp, cf, ret)

def expire(+s: Spec.State, +id: Nat) -> Spec.State & List<Spec.Effect>:
  exp1(Spec.find_res(Spec.res_of(s), id), s, id)

# ------------------------------------------------------------------------- step
def step(+s: Spec.State, +e: Spec.Ev) -> Spec.State & List<Spec.Effect>:
  match e:
    case Spec.Reserve{id, sku, qty, ttl}:
      gate(Spec.up_of(s), s, reserve(s, id, sku, qty, ttl))
    case Spec.Confirm{id}:
      gate(Spec.up_of(s), s, confirm(s, id))
    case Spec.Expire{id}:
      gate(Spec.up_of(s), s, expire(s, id))
    case Spec.Tick{}:
      (Spec.State{Spec.up_of(s), Nat.add(Spec.clock_of(s), 1n), Spec.stock_of(s), Spec.res_of(s)}, Nil{})
    case Spec.Crash{}:
      (Spec.State{False{}, Spec.clock_of(s), Spec.stock_of(s), Spec.res_of(s)}, Nil{})
    case Spec.Restart{}:
      (Spec.State{True{}, Spec.clock_of(s), Spec.stock_of(s), Spec.res_of(s)}, Nil{})

# events come first: the checker wants the shrinking argument leftmost.
def run(events: List<Spec.Ev>, +s: Spec.State) -> Spec.State:
  match events:
    case Nil{}:
      s
    case e <> t:
      run(t, Spec.st(step(s, e)))

def run_fx(events: List<Spec.Ev>, +s: Spec.State) -> List<Spec.Effect>:
  match events:
    case Nil{}:
      Nil{}
    case +e <> t:
      List.append(&1, Spec.Effect, Spec.fx(step(s, e)), run_fx(t, Spec.st(step(s, e))))
