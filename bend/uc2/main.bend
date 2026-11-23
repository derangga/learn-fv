import Base
import ./spec.bend as Spec
import ./code.bend as Code

# Conformance runner for harness/uc2conformance. One line on stdin:
#   T  k id sku qty ttl  k id sku qty ttl  ...   (ASCII digits, single spaces)
# T is the initial total of the one stock (its sku is 0, as in the Bend port:
# Spec.init(0, T)). Every event has five fields; unused ones are 0. k is the Go
# Kind number (0 Reserve, 1 Confirm, 2 Expire, 3 Tick, 4 Crash, 5 Restart).
# Every number is capped at 100000 (Nat is unary). Anything else (non-digit,
# overflow, bad k, field count not 5 per event, not exactly one line) exits 1.
# Output: one `key=value` line: the final State and, per effect kind and per
# reject reason, the count and the wrapping U32 sums of id, qty and expiresAt.
# Input of 16 MiB or more is an error (File.read would truncate it).
# Status numbers follow Go: Held 0, Confirmed 1, Expired 2. Reason numbers follow
# Go: BadRequest 0 .. NotYet 7. Tally slots: 0 FxReserved, 1 FxConfirmed,
# 2 FxReleased, 3+r FxRejected with reason r.

type Parse is Data:
  Bad{msg: String}
  Good{evs: +List<Spec.Ev>}

type Nums is Data:
  BadNum{msg: String}
  GoodNums{ns: +List<Nat>}

# count and U32 (wrapping) sums of id, qty, expiresAt
type Tot is Data:
  Tot{n: Nat, sid: U32, sq: U32, se: U32}

# ------------------------------------------------------------------- input
def cap() -> U32:
  100000

def capped(n: U32, ok: Bool) -> Maybe<&2, Nat>:
  match ok:
    case True{}:
      Some{U32.to_nat(n)}
    case False{}:
      None{}

def conv(m: Maybe<&2, U32>) -> Maybe<&2, Nat>:
  match m:
    case None{}:
      None{}
    case Some{+n}:
      capped(n, U32.is_le(n, cap()))

def cons_num(n: Nat, r: Nums) -> Nums:
  match r:
    case BadNum{m}:
      BadNum{m}
    case GoodNums{ns}:
      GoodNums{n <> ns}

def num_then(m: Maybe<&2, Nat>, r: Nums) -> Nums:
  match m:
    case None{}:
      BadNum{"bad number"}
    case Some{n}:
      cons_num(n, r)

def nums(ws: List<&2, String>) -> Nums:
  match ws:
    case Nil{}:
      GoodNums{Nil{}}
    case w <> t:
      num_then(conv(U32.read(w)), nums(t))

def mk_ev(k: Nat, id: Nat, sku: Nat, qty: Nat, ttl: Nat) -> Spec.Ev:
  match k:
    case 0n:
      Spec.Reserve{id, sku, qty, ttl}
    case 1n:
      Spec.Confirm{id}
    case 2n:
      Spec.Expire{id}
    case 3n:
      Spec.Tick{}
    case 4n:
      Spec.Crash{}
    case _:
      Spec.Restart{}

def cons_ev(e: Spec.Ev, r: Parse) -> Parse:
  match r:
    case Bad{m}:
      Bad{m}
    case Good{es}:
      Good{e <> es}

def ev_or_bad(ok: Bool, e: Spec.Ev, r: Parse) -> Parse:
  match ok:
    case True{}:
      cons_ev(e, r)
    case False{}:
      Bad{"bad kind"}

# groups of five numbers, one event each; leftover numbers are an error
def groups(ns: +List<Nat>) -> Parse:
  match ns:
    case Nil{}:
      Good{Nil{}}
    case +k <> r1:
      match r1:
        case Nil{}:
          Bad{"incomplete event"}
        case id <> r2:
          match r2:
            case Nil{}:
              Bad{"incomplete event"}
            case sku <> r3:
              match r3:
                case Nil{}:
                  Bad{"incomplete event"}
                case qty <> r4:
                  match r4:
                    case Nil{}:
                      Bad{"incomplete event"}
                    case ttl <> r5:
                      ev_or_bad(Nat.is_lt(k, 6n), mk_ev(k, id, sku, qty, ttl), groups(r5))

# ------------------------------------------------------------------- run
def tot(t: Tot, id: Nat, q: Nat, e: Nat) -> Tot:
  match t:
    case Tot{n, a, b, c}:
      Tot{1n+n, U32.add(a, U32.from_nat(id)), U32.add(b, U32.from_nat(q)), U32.add(c, U32.from_nat(e))}

def zero() -> Tot:
  Tot{0n, 0, 0, 0}

def zeros(+k: Nat) -> List<Tot>:
  match k:
    case 0n:
      Nil{}
    case 1n+p:
      zero() <> zeros(p)

# add (id, q, e) to tally slot i
def bump(ts: List<Tot>, +i: Nat, id: Nat, q: Nat, e: Nat) -> List<Tot>:
  match ts:
    case Nil{}:
      Nil{}
    case h <> t:
      match i:
        case 0n:
          tot(h, id, q, e) <> t
        case 1n+p:
          h <> bump(t, p, id, q, e)

def rn(x: Spec.Reason) -> Nat:
  match x:
    case Spec.BadRequest{}:
      0n
    case Spec.UnknownSku{}:
      1n
    case Spec.DuplicateId{}:
      2n
    case Spec.InsufficientStock{}:
      3n
    case Spec.UnknownReservation{}:
      4n
    case Spec.NotHeld{}:
      5n
    case Spec.TooLate{}:
      6n
    case Spec.NotYet{}:
      7n

def count(c: List<Tot>, f: Spec.Effect) -> List<Tot>:
  match f:
    case Spec.FxReserved{id, sku, qty, exp}:
      bump(c, 0n, id, qty, exp)
    case Spec.FxConfirmed{id}:
      bump(c, 1n, id, 0n, 0n)
    case Spec.FxReleased{id, qty}:
      bump(c, 2n, id, qty, 0n)
    case Spec.FxRejected{id, r}:
      bump(c, Nat.add(3n, rn(r)), id, 0n, 0n)

def count_all(fx: List<Spec.Effect>, c: List<Tot>) -> List<Tot>:
  match fx:
    case Nil{}:
      c
    case f <> t:
      count_all(t, count(c, f))

def fold_step(r: Spec.State & List<Spec.Effect>, c: List<Tot>) -> Spec.State & List<Tot>:
  match r:
    case (s, fx):
      (s, count_all(fx, c))

def step_cnt(r: Spec.State & List<Tot>, e: Spec.Ev) -> Spec.State & List<Tot>:
  match r:
    case (s, c):
      fold_step(Code.step(s, e), c)

# same fold as Code.run, keeping the effect tallies. events first (termination)
def run_fx(events: +List<Spec.Ev>, r: Spec.State & List<Tot>) -> Spec.State & List<Tot>:
  match events:
    case Nil{}:
      r
    case e <> t:
      run_fx(t, step_cnt(r, e))

# ------------------------------------------------------------------- output
def bit(x: Bool) -> String:
  match x:
    case True{}:
      "1"
    case False{}:
      "0"

def status_n(x: Spec.Status) -> String:
  match x:
    case Spec.Held{}:
      "0"
    case Spec.Confirmed{}:
      "1"
    case Spec.Expired{}:
      "2"

def show_res(+i: Nat, r: Spec.Res) -> String:
  match r:
    case Spec.Res{id, sku, qty, x, exp, cf, ret}:
      " r" ++ Nat.show(i) ++ ".id=" ++ Nat.show(id) ++ " r" ++ Nat.show(i) ++ ".sku=" ++ Nat.show(sku) ++ " r" ++ Nat.show(i) ++ ".qty=" ++ Nat.show(qty) ++ " r" ++ Nat.show(i) ++ ".status=" ++ status_n(x) ++ " r" ++ Nat.show(i) ++ ".expiresAt=" ++ Nat.show(exp) ++ " r" ++ Nat.show(i) ++ ".confirmedAt=" ++ Nat.show(cf) ++ " r" ++ Nat.show(i) ++ ".returned=" ++ Nat.show(ret)

def show_ress(rs: +List<Spec.Res>, +i: Nat) -> String:
  match rs:
    case Nil{}:
      ""
    case h <> t:
      show_res(i, h) ++ show_ress(t, 1n+i)

def tally_name(i: Nat) -> String:
  match i:
    case 0n:
      "FxReserved"
    case 1n:
      "FxConfirmed"
    case 2n:
      "FxReleased"
    case 3n:
      "BadRequest"
    case 4n:
      "UnknownSku"
    case 5n:
      "DuplicateId"
    case 6n:
      "InsufficientStock"
    case 7n:
      "UnknownReservation"
    case 8n:
      "NotHeld"
    case 9n:
      "TooLate"
    case _:
      "NotYet"

def show_tot(+name: String, t: Tot) -> String:
  match t:
    case Tot{n, a, b, c}:
      " tally." ++ name ++ "=" ++ Nat.show(n) ++ " tally." ++ name ++ ".id=" ++ U32.show(a) ++ " tally." ++ name ++ ".qty=" ++ U32.show(b) ++ " tally." ++ name ++ ".exp=" ++ U32.show(c)

def show_tots(ts: List<Tot>, +i: Nat) -> String:
  match ts:
    case Nil{}:
      ""
    case h <> t:
      show_tot(tally_name(i), h) ++ show_tots(t, 1n+i)

def show(r: Spec.State & List<Tot>) -> String:
  match r:
    case (Spec.State{u, c, Spec.Stock{sku, tl, av, rv, sd}, rs}, ts):
      "up=" ++ bit(u) ++ " clock=" ++ Nat.show(c) ++ " stock.sku=" ++ Nat.show(sku) ++ " stock.total=" ++ Nat.show(tl) ++ " stock.available=" ++ Nat.show(av) ++ " stock.reserved=" ++ Nat.show(rv) ++ " stock.sold=" ++ Nat.show(sd) ++ show_ress(rs, 0n) ++ show_tots(ts, 0n)

def finish(total: Nat, es: +List<Spec.Ev>) -> String:
  show(run_fx(es, (Spec.init(0n, total), zeros(11n))))

type Out is Data:
  Err{msg: String}
  Okay{line: String}

def solve_with(total: Nat, p: Parse) -> Out:
  match p:
    case Bad{m}:
      Err{m}
    case Good{es}:
      Okay{finish(total, es)}

def solve(ns: +List<Nat>) -> Out:
  match ns:
    case Nil{}:
      Err{"missing total"}
    case n <> t:
      solve_with(n, groups(t))

def solve_nums(r: Nums) -> Out:
  match r:
    case BadNum{m}:
      Err{m}
    case GoodNums{ns}:
      solve(ns)

def only_line(l: String, empty: Bool) -> Out:
  match empty:
    case True{}:
      solve_nums(nums(String.split(l, ' ')))
    case False{}:
      Err{"expected exactly one line"}

# one line, with or without its final newline (split gives a trailing "")
def one_line(ls: List<&2, String>) -> Out:
  match ls:
    case l <> Nil{}:
      only_line(l, True{})
    case l <> e <> Nil{}:
      only_line(l, String.is_empty(e))
    case _:
      Err{"expected exactly one line"}

def exec_ok(text: String, big: Bool) -> Out:
  match big:
    case True{}:
      Err{"input too large (16 MiB or more)"}
    case False{}:
      one_line(String.lines(text))

# File.read stops at 16 MiB; input that fills it may have been cut, so it is an error
def exec(+text: String) -> Out:
  exec_ok(text, Nat.is_ge(String.length(text), 16777216n))

def emit(o: Out) -> IO(Unit):
  match o:
    case Err{m}:
      IO.die(Unit, 1, "error=" ++ m)
    case Okay{line}:
      IO.print(line)

def done(r: File & Result<&1, &1, U32 & String, String>) -> IO(Unit):
  (f, res) = r
  do IO<Unit>:
    text : String <- IO.pass(String, res)
    File.close(f)
    emit(exec(text))

def main() -> IO(Unit):
  do IO<Unit>:
    f : File <- IO.try(File, File.open("/dev/stdin", "r"))
    r : File & Result<&1, &1, U32 & String, String> <- File.read(f, 16777216)
    done(r)
