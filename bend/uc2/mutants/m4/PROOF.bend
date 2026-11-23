import Base
import ./spec.bend as Spec
import ./code.bend as Code
import ./LAWS.bend as Laws

# ================================================================ Bool plumbing
def Disc(b: Bool, G: Type) -> Type:
  match b:
    case False{}:
      Unit
    case True{}:
      G

def ft_absurd(-G: Type, h: {False{} == True{} : Bool}) -> G:
  %h : Disc(_, G)
  Unit{}

def Disc2(b: Bool, G: Type) -> Type:
  match b:
    case True{}:
      Unit
    case False{}:
      G

def tf_absurd(-G: Type, h: {True{} == False{} : Bool}) -> G:
  %h : Disc2(_, G)
  Unit{}

def and_l(+a: Bool, +b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case False{}:
      ft_absurd({False{} == True{} : Bool}, h)
    case True{}:
      {==}

def and_r(+a: Bool, +b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case False{}:
      ft_absurd({b == True{} : Bool}, h)
    case True{}:
      h

def and_i(+a: Bool, +b: Bool, ha: {a == True{} : Bool}, hb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  match a:
    case False{}:
      ft_absurd({Bool.and(False{}, b) == True{} : Bool}, ha)
    case True{}:
      hb

# ================================================================ Nat lemmas (Base has none of these)
def trN(-a: Nat, -b: Nat, -c: Nat, ab: {a == b : Nat}, bc: {b == c : Nat}) -> {a == c : Nat}:
  Equal.trans(Nat, a, b, c, ab, bc)

def symN(-a: Nat, -b: Nat, e: {a == b : Nat}) -> {b == a : Nat}:
  Equal.sym(Nat, a, b, e)

# a == a + 0
def az(+a: Nat) -> {a == Nat.add(a, 0n) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %az(p) : {1n+p == 1n+_ : Nat}
      {==}

# 1 + (a + b) == a + (1 + b)
def as_(+a: Nat, +b: Nat) -> {1n+Nat.add(a, b) == Nat.add(a, 1n+b) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %as_(p, b) : {1n+1n+Nat.add(p, b) == 1n+_ : Nat}
      {==}

# a + b == b + a
def ac(+a: Nat, +b: Nat) -> {Nat.add(a, b) == Nat.add(b, a) : Nat}:
  match a:
    case 0n:
      az(b)
    case 1n+p:
      %as_(b, p) : {1n+Nat.add(p, b) == _ : Nat}
      %ac(p, b) : {1n+Nat.add(p, b) == 1n+_ : Nat}
      {==}

# a + (b + c) == (a + b) + c
def aa(+a: Nat, +b: Nat, +c: Nat) -> {Nat.add(a, Nat.add(b, c)) == Nat.add(Nat.add(a, b), c) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %aa(p, b, c) : {1n+Nat.add(p, Nat.add(b, c)) == 1n+_ : Nat}
      {==}

def cong_add_l(+a: Nat, +b: Nat, +c: Nat, +e: {a == b : Nat}) -> {Nat.add(a, c) == Nat.add(b, c) : Nat}:
  %e : {Nat.add(a, c) == Nat.add(_, c) : Nat}
  {==}

def cong_add_r(+a: Nat, +b: Nat, +c: Nat, +e: {a == b : Nat}) -> {Nat.add(c, a) == Nat.add(c, b) : Nat}:
  %e : {Nat.add(c, a) == Nat.add(c, _) : Nat}
  {==}

def sub_zero(+a: Nat) -> {Nat.sub(a, 0n) == a : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      {==}

# (a + b) - b == a
def sub_add_cancel(+a: Nat, +b: Nat) -> {Nat.sub(Nat.add(a, b), b) == a : Nat}:
  match b:
    case 0n:
      %az(a) : {Nat.sub(_, 0n) == a : Nat}
      sub_zero(a)
    case 1n+q:
      %as_(a, q) : {Nat.sub(_, 1n+q) == a : Nat}
      sub_add_cancel(a, q)

# a <= b gives (b - a) + a == b
def le_sub_add(+a: Nat, +b: Nat, +h: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.add(Nat.sub(b, a), a) == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      %az(q) : {1n+_ == 1n+q : Nat}
      {==}
    case 1n+p 0n:
      ft_absurd({Nat.add(Nat.sub(0n, 1n+p), 1n+p) == 0n : Nat}, h)
    case 1n+p 1n+q:
      %as_(Nat.sub(q, p), p) : {_ == 1n+q : Nat}
      %le_sub_add(p, q, h) : {1n+Nat.add(Nat.sub(q, p), p) == 1n+_ : Nat}
      {==}

def eq_refl(+a: Nat) -> {Nat.is_eq(a, a) == True{} : Bool}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      eq_refl(p)

def eq_prop(+a: Nat, +b: Nat, +h: {Nat.is_eq(a, b) == True{} : Bool}) -> {a == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      ft_absurd({0n == 1n+q : Nat}, h)
    case 1n+p 0n:
      ft_absurd({1n+p == 0n : Nat}, h)
    case 1n+p 1n+q:
      %eq_prop(p, q, h) : {1n+p == 1n+_ : Nat}
      {==}

def eq_back(+a: Nat, +b: Nat, +e: {a == b : Nat}) -> {Nat.is_eq(a, b) == True{} : Bool}:
  %e : {Nat.is_eq(a, _) == True{} : Bool}
  eq_refl(a)

def eq_sym_b(+a: Nat, +b: Nat) -> {Nat.is_eq(a, b) == Nat.is_eq(b, a) : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      eq_sym_b(p, q)

def lt_of_not_le(+a: Nat, +b: Nat, +h: {Nat.is_le(a, b) == False{} : Bool}) -> {Nat.is_lt(b, a) == True{} : Bool}:
  match a b:
    case 0n 0n:
      tf_absurd({Nat.is_lt(0n, 0n) == True{} : Bool}, h)
    case 0n 1n+q:
      tf_absurd({Nat.is_lt(1n+q, 0n) == True{} : Bool}, h)
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      lt_of_not_le(p, q, h)

def lt_irrefl(+a: Nat) -> {Nat.is_lt(a, a) == False{} : Bool}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      lt_irrefl(p)

# a <= a + b, in the form needed: a + b < a is false
def lt_add_false(+a: Nat, +b: Nat) -> {Nat.is_lt(Nat.add(a, b), a) == False{} : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p _:
      lt_add_false(p, b)

def pd(n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+p:
      p

# (a + c == b + c) gives a == b
def add_cancel_r(+a: Nat, +b: Nat, +c: Nat, +h: {Nat.add(a, c) == Nat.add(b, c) : Nat}) -> {a == b : Nat}:
  match c:
    case 0n:
      trN(a, Nat.add(a, 0n), b, az(a), trN(Nat.add(a, 0n), Nat.add(b, 0n), b, h, symN(b, Nat.add(b, 0n), az(b))))
    case 1n+q:
      add_cancel_r(a, b, q, Equal.cong(Nat, Nat, x => pd(x), 1n+Nat.add(a, q), 1n+Nat.add(b, q), trN(1n+Nat.add(a, q), Nat.add(a, 1n+q), 1n+Nat.add(b, q), as_(a, q), trN(Nat.add(a, 1n+q), Nat.add(b, 1n+q), 1n+Nat.add(b, q), h, symN(1n+Nat.add(b, q), Nat.add(b, 1n+q), as_(b, q))))))

# ================================================================ more Nat shuffles
# (a + q) + b == (b + q) + a
def add_sw3(+a: Nat, +b: Nat, +q: Nat) -> {Nat.add(Nat.add(a, q), b) == Nat.add(Nat.add(b, q), a) : Nat}:
  %aa(a, q, b) : {_ == Nat.add(Nat.add(b, q), a) : Nat}
  %aa(b, q, a) : {Nat.add(a, Nat.add(q, b)) == _ : Nat}
  %ac(a, q) : {Nat.add(a, Nat.add(q, b)) == Nat.add(b, _) : Nat}
  %symN(Nat.add(b, Nat.add(a, q)), Nat.add(Nat.add(b, a), q), aa(b, a, q)) : {Nat.add(a, Nat.add(q, b)) == _ : Nat}
  %ac(a, b) : {Nat.add(a, Nat.add(q, b)) == Nat.add(_, q) : Nat}
  %aa(a, b, q) : {Nat.add(a, Nat.add(q, b)) == _ : Nat}
  %ac(b, q) : {Nat.add(a, _) == Nat.add(a, Nat.add(b, q)) : Nat}
  {==}

# (a + b) + c == (a + c) + b
def sw(+a: Nat, +b: Nat, +c: Nat) -> {Nat.add(Nat.add(a, b), c) == Nat.add(Nat.add(a, c), b) : Nat}:
  %aa(a, b, c) : {_ == Nat.add(Nat.add(a, c), b) : Nat}
  %aa(a, c, b) : {Nat.add(a, Nat.add(b, c)) == _ : Nat}
  %ac(b, c) : {Nat.add(a, Nat.add(b, c)) == Nat.add(a, _) : Nat}
  {==}

def sub_wit(+x: Nat, +q: Nat, +a2: Nat, +ha: {Nat.add(a2, q) == x : Nat}) -> {Nat.sub(x, q) == a2 : Nat}:
  %ha : {Nat.sub(_, q) == a2 : Nat}
  sub_add_cancel(a2, q)

# P2 arithmetic, one lemma per event. h is the old sum, the goal the new one.
def p2_rsv(+a2: Nat, +q: Nat, +rv: Nat, +sd: Nat, +tot: Nat, +h: {Nat.add(Nat.add(Nat.add(a2, q), rv), sd) == tot : Nat}) -> {Nat.add(Nat.add(a2, Nat.add(rv, q)), sd) == tot : Nat}:
  %symN(Nat.add(a2, Nat.add(rv, q)), Nat.add(Nat.add(a2, q), rv), trN(Nat.add(a2, Nat.add(rv, q)), Nat.add(Nat.add(a2, rv), q), Nat.add(Nat.add(a2, q), rv), aa(a2, rv, q), sw(a2, rv, q))) : {Nat.add(_, sd) == tot : Nat}
  h

def p2_conf(+av: Nat, +r2: Nat, +q: Nat, +sd: Nat, +tot: Nat, +h: {Nat.add(Nat.add(av, Nat.add(r2, q)), sd) == tot : Nat}) -> {Nat.add(Nat.add(av, r2), Nat.add(sd, q)) == tot : Nat}:
  %symN(Nat.add(Nat.add(av, r2), Nat.add(sd, q)), Nat.add(Nat.add(Nat.add(av, r2), sd), q), aa(Nat.add(av, r2), sd, q)) : {_ == tot : Nat}
  %symN(Nat.add(Nat.add(Nat.add(av, r2), sd), q), Nat.add(Nat.add(Nat.add(av, r2), q), sd), sw(Nat.add(av, r2), sd, q)) : {_ == tot : Nat}
  %aa(av, r2, q) : {Nat.add(_, sd) == tot : Nat}
  h

def p2_exp(+av: Nat, +q: Nat, +r2: Nat, +sd: Nat, +tot: Nat, +h: {Nat.add(Nat.add(av, Nat.add(r2, q)), sd) == tot : Nat}) -> {Nat.add(Nat.add(Nat.add(av, q), r2), sd) == tot : Nat}:
  %trN(Nat.add(av, Nat.add(r2, q)), Nat.add(av, Nat.add(q, r2)), Nat.add(Nat.add(av, q), r2), cong_add_r(Nat.add(r2, q), Nat.add(q, r2), av, ac(r2, q)), aa(av, q, r2)) : {Nat.add(_, sd) == tot : Nat}
  h

# ================================================================ more Bool lemmas
def not_f(+a: Bool, +h: {a == False{} : Bool}) -> {Bool.not(a) == True{} : Bool}:
  match a:
    case False{}:
      {==}
    case True{}:
      tf_absurd({Bool.not(True{}) == True{} : Bool}, h)

def not_t(+a: Bool, +h: {Bool.not(a) == True{} : Bool}) -> {a == False{} : Bool}:
  match a:
    case False{}:
      {==}
    case True{}:
      ft_absurd({True{} == False{} : Bool}, h)

def or_ff(+a: Bool, +b: Bool, +ha: {a == False{} : Bool}, +hb: {b == False{} : Bool}) -> {Bool.or(a, b) == False{} : Bool}:
  match a:
    case False{}:
      hb
    case True{}:
      tf_absurd({Bool.or(True{}, b) == False{} : Bool}, ha)

def or_f_l(+a: Bool, +b: Bool, +h: {Bool.or(a, b) == False{} : Bool}) -> {a == False{} : Bool}:
  match a:
    case False{}:
      {==}
    case True{}:
      tf_absurd({True{} == False{} : Bool}, h)

def or_f_r(+a: Bool, +b: Bool, +h: {Bool.or(a, b) == False{} : Bool}) -> {b == False{} : Bool}:
  match a:
    case False{}:
      h
    case True{}:
      tf_absurd({b == False{} : Bool}, h)

def or_f(+a: Bool) -> {a == Bool.or(a, False{}) : Bool}:
  match a:
    case False{}:
      {==}
    case True{}:
      {==}

def or_assoc(+a: Bool, +b: Bool, +c: Bool) -> {Bool.or(Bool.or(a, b), c) == Bool.or(a, Bool.or(b, c)) : Bool}:
  match a:
    case False{}:
      {==}
    case True{}:
      {==}

def and_f_r(+a: Bool) -> {Bool.and(a, False{}) == False{} : Bool}:
  match a:
    case False{}:
      {==}
    case True{}:
      {==}

# ================================================================ Look
def DiscL(l: Spec.Look, G: Type) -> Type:
  match l:
    case Spec.NoRes{}:
      Unit
    case Spec.Got{_}:
      G

def nr_absurd(-G: Type, -r: Spec.Res, h: {Spec.NoRes{} == Spec.Got{r} : Spec.Look}) -> G:
  %h : DiscL(_, G)
  Unit{}

def DiscL2(l: Spec.Look, G: Type) -> Type:
  match l:
    case Spec.Got{_}:
      Unit
    case Spec.NoRes{}:
      G

def gt_absurd(-G: Type, -r: Spec.Res, h: {Spec.Got{r} == Spec.NoRes{} : Spec.Look}) -> G:
  %h : DiscL2(_, G)
  Unit{}

def got_r(l: Spec.Look, d: Spec.Res) -> Spec.Res:
  match l:
    case Spec.NoRes{}:
      d
    case Spec.Got{r}:
      r

def got_inj(+h: Spec.Res, +r: Spec.Res, +e: {Spec.Got{h} == Spec.Got{r} : Spec.Look}) -> {h == r : Spec.Res}:
  Equal.cong(Spec.Look, Spec.Res, l => got_r(l, h), Spec.Got{h}, Spec.Got{r}, e)

def snoc(rs: +List<Spec.Res>, x: Spec.Res) -> +List<Spec.Res>:
  List.append(&2, Spec.Res, rs, x <> Nil{})

# ================================================================ all_rec
def all_snoc(+f: Spec.Facet, +k: Nat, +rs: +List<Spec.Res>, +x: Spec.Res, +h1: {Spec.all_rec(f, k, rs) == True{} : Bool}, +h2: {Spec.rec_ok(f, k, x) == True{} : Bool}) -> {Spec.all_rec(f, k, snoc(rs, x)) == True{} : Bool}:
  match rs:
    case Nil{}:
      and_i(Spec.rec_ok(f, k, x), True{}, h2, {==})
    case +h <> +t:
      and_i(Spec.rec_ok(f, k, h), Spec.all_rec(f, k, snoc(t, x)), and_l(Spec.rec_ok(f, k, h), Spec.all_rec(f, k, t), h1), all_snoc(f, k, t, x, and_r(Spec.rec_ok(f, k, h), Spec.all_rec(f, k, t), h1), h2))

def all_pp(+g: Bool, +f: Spec.Facet, +k: Nat, +h: Spec.Res, +x: Spec.Res, +t: +List<Spec.Res>, +rest: +List<Spec.Res>, +hh: {Spec.rec_ok(f, k, h) == True{} : Bool}, +ht: {Spec.all_rec(f, k, t) == True{} : Bool}, +hx: {Spec.rec_ok(f, k, x) == True{} : Bool}, +hr: {Spec.all_rec(f, k, rest) == True{} : Bool}) -> {Spec.all_rec(f, k, Spec.put_pick(g, h, x, t, rest)) == True{} : Bool}:
  match g:
    case True{}:
      and_i(Spec.rec_ok(f, k, x), Spec.all_rec(f, k, t), hx, ht)
    case False{}:
      and_i(Spec.rec_ok(f, k, h), Spec.all_rec(f, k, rest), hh, hr)

def all_put(+f: Spec.Facet, +k: Nat, +rs: +List<Spec.Res>, +id: Nat, +x: Spec.Res, +h1: {Spec.all_rec(f, k, rs) == True{} : Bool}, +h2: {Spec.rec_ok(f, k, x) == True{} : Bool}) -> {Spec.all_rec(f, k, Spec.put_res(rs, id, x)) == True{} : Bool}:
  match rs:
    case Nil{}:
      {==}
    case +h <> +t:
      all_pp(Nat.is_eq(Spec.r_id(h), id), f, k, h, x, t, Spec.put_res(t, id, x), and_l(Spec.rec_ok(f, k, h), Spec.all_rec(f, k, t), h1), and_r(Spec.rec_ok(f, k, h), Spec.all_rec(f, k, t), h1), h2, all_put(f, k, t, id, x, and_r(Spec.rec_ok(f, k, h), Spec.all_rec(f, k, t), h1), h2))

def all_fp(+g: Bool, +f: Spec.Facet, +k: Nat, +h: Spec.Res, +r: Spec.Res, +rest: Spec.Look, +hh: {Spec.rec_ok(f, k, h) == True{} : Bool}, +hf: {Spec.find_pick(h, g, rest) == Spec.Got{r} : Spec.Look}, ih: {rest == Spec.Got{r} : Spec.Look} -> {Spec.rec_ok(f, k, r) == True{} : Bool}) -> {Spec.rec_ok(f, k, r) == True{} : Bool}:
  match g:
    case True{}:
      %got_inj(h, r, hf) : {Spec.rec_ok(f, k, _) == True{} : Bool}
      hh
    case False{}:
      ih(hf)

def all_find(+f: Spec.Facet, +k: Nat, +rs: +List<Spec.Res>, +id: Nat, +r: Spec.Res, +h1: {Spec.all_rec(f, k, rs) == True{} : Bool}, +hf: {Spec.find_res(rs, id) == Spec.Got{r} : Spec.Look}) -> {Spec.rec_ok(f, k, r) == True{} : Bool}:
  match rs:
    case Nil{}:
      nr_absurd({Spec.rec_ok(f, k, r) == True{} : Bool}, r, hf)
    case +h <> +t:
      all_fp(Nat.is_eq(Spec.r_id(h), id), f, k, h, r, Spec.find_res(t, id), and_l(Spec.rec_ok(f, k, h), Spec.all_rec(f, k, t), h1), hf, hf2 => all_find(f, k, t, id, r, and_r(Spec.rec_ok(f, k, h), Spec.all_rec(f, k, t), h1), hf2))

# ================================================================ has_id and uniq
def hid_snoc(+rs: +List<Spec.Res>, +x: Spec.Res, +j: Nat) -> {Bool.or(Spec.has_id(rs, j), Nat.is_eq(Spec.r_id(x), j)) == Spec.has_id(snoc(rs, x), j) : Bool}:
  match rs:
    case Nil{}:
      %or_f(Nat.is_eq(Spec.r_id(x), j)) : {Nat.is_eq(Spec.r_id(x), j) == _ : Bool}
      {==}
    case +h <> +t:
      %hid_snoc(t, x, j) : {Bool.or(Bool.or(Nat.is_eq(Spec.r_id(h), j), Spec.has_id(t, j)), Nat.is_eq(Spec.r_id(x), j)) == Bool.or(Nat.is_eq(Spec.r_id(h), j), _) : Bool}
      or_assoc(Nat.is_eq(Spec.r_id(h), j), Spec.has_id(t, j), Nat.is_eq(Spec.r_id(x), j))

def hid_snoc_f(+t: +List<Spec.Res>, +x: Spec.Res, +j: Nat, +h1: {Spec.has_id(t, j) == False{} : Bool}, +h2: {Nat.is_eq(Spec.r_id(x), j) == False{} : Bool}) -> {Spec.has_id(snoc(t, x), j) == False{} : Bool}:
  %hid_snoc(t, x, j) : {_ == False{} : Bool}
  or_ff(Spec.has_id(t, j), Nat.is_eq(Spec.r_id(x), j), h1, h2)

def eq_f_sym(+a: Nat, +b: Nat, +h: {Nat.is_eq(a, b) == False{} : Bool}) -> {Nat.is_eq(b, a) == False{} : Bool}:
  %eq_sym_b(a, b) : {_ == False{} : Bool}
  h

def uniq_snoc(+rs: +List<Spec.Res>, +x: Spec.Res, +h1: {Spec.uniq(rs) == True{} : Bool}, +h2: {Spec.has_id(rs, Spec.r_id(x)) == False{} : Bool}) -> {Spec.uniq(snoc(rs, x)) == True{} : Bool}:
  match rs:
    case Nil{}:
      {==}
    case +h <> +t:
      and_i(Bool.not(Spec.has_id(snoc(t, x), Spec.r_id(h))), Spec.uniq(snoc(t, x)), not_f(Spec.has_id(snoc(t, x), Spec.r_id(h)), hid_snoc_f(t, x, Spec.r_id(h), not_t(Spec.has_id(t, Spec.r_id(h)), and_l(Bool.not(Spec.has_id(t, Spec.r_id(h))), Spec.uniq(t), h1)), eq_f_sym(Spec.r_id(h), Spec.r_id(x), or_f_l(Nat.is_eq(Spec.r_id(h), Spec.r_id(x)), Spec.has_id(t, Spec.r_id(x)), h2)))), uniq_snoc(t, x, and_r(Bool.not(Spec.has_id(t, Spec.r_id(h))), Spec.uniq(t), h1), or_f_r(Nat.is_eq(Spec.r_id(h), Spec.r_id(x)), Spec.has_id(t, Spec.r_id(x)), h2)))

def hp_pick(+g: Bool, +h: Spec.Res, +x: Spec.Res, +t: +List<Spec.Res>, +rest: +List<Spec.Res>, +id: Nat, +j: Nat, +hg: {Nat.is_eq(Spec.r_id(h), id) == g : Bool}, +hx: {Spec.r_id(x) == id : Nat}, +ih: {Spec.has_id(rest, j) == Spec.has_id(t, j) : Bool}) -> {Spec.has_id(Spec.put_pick(g, h, x, t, rest), j) == Spec.has_id(h <> t, j) : Bool}:
  match g:
    case True{}:
      %trN(Spec.r_id(x), id, Spec.r_id(h), hx, symN(Spec.r_id(h), id, eq_prop(Spec.r_id(h), id, hg))) : {Bool.or(Nat.is_eq(Spec.r_id(x), j), Spec.has_id(t, j)) == Bool.or(Nat.is_eq(_, j), Spec.has_id(t, j)) : Bool}
      {==}
    case False{}:
      %ih : {Bool.or(Nat.is_eq(Spec.r_id(h), j), Spec.has_id(rest, j)) == Bool.or(Nat.is_eq(Spec.r_id(h), j), _) : Bool}
      {==}

def hid_put(+rs: +List<Spec.Res>, +id: Nat, +x: Spec.Res, +j: Nat, +hx: {Spec.r_id(x) == id : Nat}) -> {Spec.has_id(Spec.put_res(rs, id, x), j) == Spec.has_id(rs, j) : Bool}:
  match rs:
    case Nil{}:
      {==}
    case +h <> +t:
      hp_pick(Nat.is_eq(Spec.r_id(h), id), h, x, t, Spec.put_res(t, id, x), id, j, {==}, hx, hid_put(t, id, x, j, hx))

def up_pick(+g: Bool, +h: Spec.Res, +x: Spec.Res, +t: +List<Spec.Res>, +rest: +List<Spec.Res>, +id: Nat, +hg: {Nat.is_eq(Spec.r_id(h), id) == g : Bool}, +hx: {Spec.r_id(x) == id : Nat}, +ih1: {Spec.uniq(rest) == Spec.uniq(t) : Bool}, +ih2: {Spec.has_id(rest, Spec.r_id(h)) == Spec.has_id(t, Spec.r_id(h)) : Bool}) -> {Spec.uniq(Spec.put_pick(g, h, x, t, rest)) == Spec.uniq(h <> t) : Bool}:
  match g:
    case True{}:
      %trN(Spec.r_id(x), id, Spec.r_id(h), hx, symN(Spec.r_id(h), id, eq_prop(Spec.r_id(h), id, hg))) : {Bool.and(Bool.not(Spec.has_id(t, Spec.r_id(x))), Spec.uniq(t)) == Bool.and(Bool.not(Spec.has_id(t, _)), Spec.uniq(t)) : Bool}
      {==}
    case False{}:
      %ih2 : {Bool.and(Bool.not(Spec.has_id(rest, Spec.r_id(h))), Spec.uniq(rest)) == Bool.and(Bool.not(_), Spec.uniq(t)) : Bool}
      %ih1 : {Bool.and(Bool.not(Spec.has_id(rest, Spec.r_id(h))), Spec.uniq(rest)) == Bool.and(Bool.not(Spec.has_id(rest, Spec.r_id(h))), _) : Bool}
      {==}

def uniq_put(+rs: +List<Spec.Res>, +id: Nat, +x: Spec.Res, +hx: {Spec.r_id(x) == id : Nat}) -> {Spec.uniq(Spec.put_res(rs, id, x)) == Spec.uniq(rs) : Bool}:
  match rs:
    case Nil{}:
      {==}
    case +h <> +t:
      up_pick(Nat.is_eq(Spec.r_id(h), id), h, x, t, Spec.put_res(t, id, x), id, {==}, hx, uniq_put(t, id, x, hx), hid_put(t, id, x, Spec.r_id(h), hx))

def fn_pick(+g: Bool, +h: Spec.Res, +t: +List<Spec.Res>, +id: Nat, +hg: {Nat.is_eq(Spec.r_id(h), id) == g : Bool}, +hf: {Spec.find_pick(h, g, Spec.find_res(t, id)) == Spec.NoRes{} : Spec.Look}, ih: {Spec.find_res(t, id) == Spec.NoRes{} : Spec.Look} -> {Spec.has_id(t, id) == False{} : Bool}) -> {Bool.or(Nat.is_eq(Spec.r_id(h), id), Spec.has_id(t, id)) == False{} : Bool}:
  match g:
    case True{}:
      gt_absurd({Bool.or(Nat.is_eq(Spec.r_id(h), id), Spec.has_id(t, id)) == False{} : Bool}, h, hf)
    case False{}:
      or_ff(Nat.is_eq(Spec.r_id(h), id), Spec.has_id(t, id), hg, ih(hf))

def fn_hid(+rs: +List<Spec.Res>, +id: Nat, +h: {Spec.find_res(rs, id) == Spec.NoRes{} : Spec.Look}) -> {Spec.has_id(rs, id) == False{} : Bool}:
  match rs:
    case Nil{}:
      {==}
    case +h2 <> +t:
      fn_pick(Nat.is_eq(Spec.r_id(h2), id), h2, t, id, {==}, h, hf2 => fn_hid(t, id, hf2))

def look_none_t(+l: Spec.Look, +h: {Spec.look_none(l) == True{} : Bool}) -> {l == Spec.NoRes{} : Spec.Look}:
  match l:
    case Spec.NoRes{}:
      {==}
    case Spec.Got{r}:
      ft_absurd({Spec.Got{r} == Spec.NoRes{} : Spec.Look}, h)

# ================================================================ qty_sum
def cn(+r: Spec.Res, k: Nat, y: Spec.Status) -> Nat:
  Spec.sum_pick(Bool.and(Nat.is_eq(Spec.r_sku(r), k), Spec.st_eq(Spec.r_status(r), y)), Spec.r_qty(r), 0n)

def sp_cn(+g: Bool, +q: Nat, +Q: Nat) -> {Nat.add(Spec.sum_pick(g, q, 0n), Q) == Spec.sum_pick(g, q, Q) : Nat}:
  match g:
    case False{}:
      {==}
    case True{}:
      %az(q) : {Nat.add(_, Q) == Nat.add(q, Q) : Nat}
      {==}

def qs_cons(+h: Spec.Res, +t: +List<Spec.Res>, +k: Nat, +y: Spec.Status) -> {Nat.add(cn(h, k, y), Spec.qty_sum(t, k, y)) == Spec.qty_sum(h <> t, k, y) : Nat}:
  sp_cn(Bool.and(Nat.is_eq(Spec.r_sku(h), k), Spec.st_eq(Spec.r_status(h), y)), Spec.r_qty(h), Spec.qty_sum(t, k, y))

def qsn_pick(+g: Bool, +q: Nat, +A: Nat, +B: Nat, +c: Nat, +ih: {Nat.add(B, c) == A : Nat}) -> {Nat.add(Spec.sum_pick(g, q, B), c) == Spec.sum_pick(g, q, A) : Nat}:
  match g:
    case True{}:
      %ih : {Nat.add(Nat.add(q, B), c) == Nat.add(q, _) : Nat}
      symN(Nat.add(q, Nat.add(B, c)), Nat.add(Nat.add(q, B), c), aa(q, B, c))
    case False{}:
      ih

def qs_snoc(+rs: +List<Spec.Res>, +k: Nat, +y: Spec.Status, +x: Spec.Res) -> {Nat.add(Spec.qty_sum(rs, k, y), cn(x, k, y)) == Spec.qty_sum(snoc(rs, x), k, y) : Nat}:
  match rs:
    case Nil{}:
      {==}
    case +h <> +t:
      qsn_pick(Bool.and(Nat.is_eq(Spec.r_sku(h), k), Spec.st_eq(Spec.r_status(h), y)), Spec.r_qty(h), Spec.qty_sum(snoc(t, x), k, y), Spec.qty_sum(t, k, y), cn(x, k, y), qs_snoc(t, k, y, x))

def qp_pick(+g: Bool, +h: Spec.Res, +x: Spec.Res, +t: +List<Spec.Res>, +rest: +List<Spec.Res>, +r: Spec.Res, +k: Nat, +y: Spec.Status, +id: Nat, +hf: {Spec.find_pick(h, g, Spec.find_res(t, id)) == Spec.Got{r} : Spec.Look}, ih: {Spec.find_res(t, id) == Spec.Got{r} : Spec.Look} -> {Nat.add(Spec.qty_sum(rest, k, y), cn(r, k, y)) == Nat.add(Spec.qty_sum(t, k, y), cn(x, k, y)) : Nat}) -> {Nat.add(Spec.qty_sum(Spec.put_pick(g, h, x, t, rest), k, y), cn(r, k, y)) == Nat.add(Spec.qty_sum(h <> t, k, y), cn(x, k, y)) : Nat}:
  match g:
    case True{}:
      %got_inj(h, r, hf) : {Nat.add(Spec.qty_sum(x <> t, k, y), cn(_, k, y)) == Nat.add(Spec.qty_sum(h <> t, k, y), cn(x, k, y)) : Nat}
      %qs_cons(x, t, k, y) : {Nat.add(_, cn(h, k, y)) == Nat.add(Spec.qty_sum(h <> t, k, y), cn(x, k, y)) : Nat}
      %qs_cons(h, t, k, y) : {Nat.add(Nat.add(cn(x, k, y), Spec.qty_sum(t, k, y)), cn(h, k, y)) == Nat.add(_, cn(x, k, y)) : Nat}
      add_sw3(cn(x, k, y), cn(h, k, y), Spec.qty_sum(t, k, y))
    case False{}:
      %qs_cons(h, rest, k, y) : {Nat.add(_, cn(r, k, y)) == Nat.add(Spec.qty_sum(h <> t, k, y), cn(x, k, y)) : Nat}
      %qs_cons(h, t, k, y) : {Nat.add(Nat.add(cn(h, k, y), Spec.qty_sum(rest, k, y)), cn(r, k, y)) == Nat.add(_, cn(x, k, y)) : Nat}
      %aa(cn(h, k, y), Spec.qty_sum(rest, k, y), cn(r, k, y)) : {_ == Nat.add(Nat.add(cn(h, k, y), Spec.qty_sum(t, k, y)), cn(x, k, y)) : Nat}
      %aa(cn(h, k, y), Spec.qty_sum(t, k, y), cn(x, k, y)) : {Nat.add(cn(h, k, y), Nat.add(Spec.qty_sum(rest, k, y), cn(r, k, y))) == _ : Nat}
      %ih(hf) : {Nat.add(cn(h, k, y), Nat.add(Spec.qty_sum(rest, k, y), cn(r, k, y))) == Nat.add(cn(h, k, y), _) : Nat}
      {==}

def qs_put(+rs: +List<Spec.Res>, +id: Nat, +x: Spec.Res, +r: Spec.Res, +k: Nat, +y: Spec.Status, +hf: {Spec.find_res(rs, id) == Spec.Got{r} : Spec.Look}) -> {Nat.add(Spec.qty_sum(Spec.put_res(rs, id, x), k, y), cn(r, k, y)) == Nat.add(Spec.qty_sum(rs, k, y), cn(x, k, y)) : Nat}:
  match rs:
    case Nil{}:
      nr_absurd({Nat.add(0n, cn(r, k, y)) == Nat.add(0n, cn(x, k, y)) : Nat}, r, hf)
    case +h <> +t:
      qp_pick(Nat.is_eq(Spec.r_id(h), id), h, x, t, Spec.put_res(t, id, x), r, k, y, id, hf, hf2 => qs_put(t, id, x, r, k, y, hf2))

# ================================================================ state shapes and Inv parts
def mkS(u: Bool, c: Nat, ksku: Nat, tot: Nat, av: Nat, rv: Nat, sd: Nat, rs: +List<Spec.Res>) -> Spec.State:
  Spec.State{u, c, Spec.Stock{ksku, tot, av, rv, sd}, rs}

def reserve_mk(u: Bool, +clk: Nat, ksku: Nat, tot: Nat, a2: Nat, rv: Nat, sd: Nat, rs: +List<Spec.Res>, +id: Nat, +sku: Nat, +qty: Nat, +ttl: Nat) -> Spec.State & List<Spec.Effect>:
  (mkS(u, clk, ksku, tot, a2, Nat.add(rv, qty), sd, snoc(rs, Spec.Res{id, sku, qty, Spec.Held{}, Nat.add(clk, ttl), 0n, 0n})), Spec.FxReserved{id, sku, qty, Nat.add(clk, ttl)} <> Nil{})

def confirm_mk(u: Bool, +clk: Nat, ksku: Nat, tot: Nat, av: Nat, r2: Nat, sd: Nat, rs: +List<Spec.Res>, +id: Nat, sku: Nat, +qty: Nat, exp: Nat, ret: Nat) -> Spec.State & List<Spec.Effect>:
  (mkS(u, clk, ksku, tot, av, r2, Nat.add(sd, qty), Spec.put_res(rs, id, Spec.Res{id, sku, qty, Spec.Confirmed{}, exp, clk, ret})), Spec.FxConfirmed{id} <> Nil{})

def expire_mk(u: Bool, clk: Nat, ksku: Nat, tot: Nat, av: Nat, r2: Nat, sd: Nat, rs: +List<Spec.Res>, +id: Nat, sku: Nat, +qty: Nat, exp: Nat, cf: Nat, +ret: Nat) -> Spec.State & List<Spec.Effect>:
  (mkS(u, clk, ksku, tot, Nat.add(av, qty), r2, sd, Spec.put_res(rs, id, Spec.Res{id, sku, qty, Spec.Expired{}, exp, cf, Nat.add(ret, 1n)})), Spec.FxReleased{id, qty} <> Nil{})

def i_p2(+s: Spec.State, +h: {Spec.inv(s) == True{} : Bool}) -> {Spec.p2(s) == True{} : Bool}:
  and_l(Spec.p2(s), Bool.and(Spec.p3(s), Bool.and(Spec.p4a(s), Bool.and(Spec.a1(s), Spec.a2(s)))), h)

def i_p3(+s: Spec.State, +h: {Spec.inv(s) == True{} : Bool}) -> {Spec.p3(s) == True{} : Bool}:
  and_l(Spec.p3(s), Bool.and(Spec.p4a(s), Bool.and(Spec.a1(s), Spec.a2(s))), and_r(Spec.p2(s), Bool.and(Spec.p3(s), Bool.and(Spec.p4a(s), Bool.and(Spec.a1(s), Spec.a2(s)))), h))

def i_p4a(+s: Spec.State, +h: {Spec.inv(s) == True{} : Bool}) -> {Spec.p4a(s) == True{} : Bool}:
  and_l(Spec.p4a(s), Bool.and(Spec.a1(s), Spec.a2(s)), and_r(Spec.p3(s), Bool.and(Spec.p4a(s), Bool.and(Spec.a1(s), Spec.a2(s))), and_r(Spec.p2(s), Bool.and(Spec.p3(s), Bool.and(Spec.p4a(s), Bool.and(Spec.a1(s), Spec.a2(s)))), h)))

def i_a1(+s: Spec.State, +h: {Spec.inv(s) == True{} : Bool}) -> {Spec.a1(s) == True{} : Bool}:
  and_l(Spec.a1(s), Spec.a2(s), and_r(Spec.p4a(s), Bool.and(Spec.a1(s), Spec.a2(s)), and_r(Spec.p3(s), Bool.and(Spec.p4a(s), Bool.and(Spec.a1(s), Spec.a2(s))), and_r(Spec.p2(s), Bool.and(Spec.p3(s), Bool.and(Spec.p4a(s), Bool.and(Spec.a1(s), Spec.a2(s)))), h))))

def i_a2(+s: Spec.State, +h: {Spec.inv(s) == True{} : Bool}) -> {Spec.a2(s) == True{} : Bool}:
  and_r(Spec.a1(s), Spec.a2(s), and_r(Spec.p4a(s), Bool.and(Spec.a1(s), Spec.a2(s)), and_r(Spec.p3(s), Bool.and(Spec.p4a(s), Bool.and(Spec.a1(s), Spec.a2(s))), and_r(Spec.p2(s), Bool.and(Spec.p3(s), Bool.and(Spec.p4a(s), Bool.and(Spec.a1(s), Spec.a2(s)))), h))))

def i_mk(+s: Spec.State, +h2: {Spec.p2(s) == True{} : Bool}, +h3: {Spec.p3(s) == True{} : Bool}, +h4: {Spec.p4a(s) == True{} : Bool}, +h5: {Spec.a1(s) == True{} : Bool}, +h6: {Spec.a2(s) == True{} : Bool}) -> {Spec.inv(s) == True{} : Bool}:
  and_i(Spec.p2(s), Bool.and(Spec.p3(s), Bool.and(Spec.p4a(s), Bool.and(Spec.a1(s), Spec.a2(s)))), h2, and_i(Spec.p3(s), Bool.and(Spec.p4a(s), Bool.and(Spec.a1(s), Spec.a2(s))), h3, and_i(Spec.p4a(s), Bool.and(Spec.a1(s), Spec.a2(s)), h4, and_i(Spec.a1(s), Spec.a2(s), h5, h6))))

def trB(-a: Bool, -b: Bool, -c: Bool, ab: {a == b : Bool}, bc: {b == c : Bool}) -> {a == c : Bool}:
  Equal.trans(Bool, a, b, c, ab, bc)

def sp0_t(+g: Bool, +q: Nat, +hg: {g == True{} : Bool}) -> {Spec.sum_pick(g, q, 0n) == q : Nat}:
  match g:
    case False{}:
      ft_absurd({0n == q : Nat}, hg)
    case True{}:
      %az(q) : {_ == q : Nat}
      {==}

def sp0_f(+g: Bool, +q: Nat, +hg: {g == False{} : Bool}) -> {Spec.sum_pick(g, q, 0n) == 0n : Nat}:
  match g:
    case False{}:
      {==}
    case True{}:
      tf_absurd({Nat.add(q, 0n) == 0n : Nat}, hg)

def cn_hit(+r: Spec.Res, +k: Nat, +y: Spec.Status, +hg: {Bool.and(Nat.is_eq(Spec.r_sku(r), k), Spec.st_eq(Spec.r_status(r), y)) == True{} : Bool}) -> {cn(r, k, y) == Spec.r_qty(r) : Nat}:
  sp0_t(Bool.and(Nat.is_eq(Spec.r_sku(r), k), Spec.st_eq(Spec.r_status(r), y)), Spec.r_qty(r), hg)

def cn_miss(+r: Spec.Res, +k: Nat, +y: Spec.Status, +hg: {Bool.and(Nat.is_eq(Spec.r_sku(r), k), Spec.st_eq(Spec.r_status(r), y)) == False{} : Bool}) -> {cn(r, k, y) == 0n : Nat}:
  sp0_f(Bool.and(Nat.is_eq(Spec.r_sku(r), k), Spec.st_eq(Spec.r_status(r), y)), Spec.r_qty(r), hg)

def ret_one(+ret: Nat, +h: {Nat.is_eq(ret, 0n) == True{} : Bool}) -> {Nat.is_eq(Nat.add(ret, 1n), 1n) == True{} : Bool}:
  %symN(ret, 0n, eq_prop(ret, 0n, h)) : {Nat.is_eq(Nat.add(_, 1n), 1n) == True{} : Bool}
  {==}


# the Held counter after replacing record r (Held, qty q) by x (not Held)
def held_put(+rs: +List<Spec.Res>, +id: Nat, +x: Spec.Res, +r: Spec.Res, +k: Nat, +q: Nat, +rv: Nat, +r2: Nat, +hf: {Spec.find_res(rs, id) == Spec.Got{r} : Spec.Look}, +hr: {Nat.add(r2, q) == rv : Nat}, +eqrv: {rv == Spec.qty_sum(rs, k, Spec.Held{}) : Nat}, +cnR: {cn(r, k, Spec.Held{}) == q : Nat}, +cnX: {cn(x, k, Spec.Held{}) == 0n : Nat}) -> {Nat.is_eq(r2, Spec.qty_sum(Spec.put_res(rs, id, x), k, Spec.Held{})) == True{} : Bool}:
  eq_back(r2, Spec.qty_sum(Spec.put_res(rs, id, x), k, Spec.Held{}), symN(Spec.qty_sum(Spec.put_res(rs, id, x), k, Spec.Held{}), r2, add_cancel_r(Spec.qty_sum(Spec.put_res(rs, id, x), k, Spec.Held{}), r2, q, trN(Nat.add(Spec.qty_sum(Spec.put_res(rs, id, x), k, Spec.Held{}), q), Nat.add(Spec.qty_sum(Spec.put_res(rs, id, x), k, Spec.Held{}), cn(r, k, Spec.Held{})), Nat.add(r2, q), cong_add_r(q, cn(r, k, Spec.Held{}), Spec.qty_sum(Spec.put_res(rs, id, x), k, Spec.Held{}), symN(cn(r, k, Spec.Held{}), q, cnR)), trN(Nat.add(Spec.qty_sum(Spec.put_res(rs, id, x), k, Spec.Held{}), cn(r, k, Spec.Held{})), Nat.add(Spec.qty_sum(rs, k, Spec.Held{}), cn(x, k, Spec.Held{})), Nat.add(r2, q), qs_put(rs, id, x, r, k, Spec.Held{}, hf), trN(Nat.add(Spec.qty_sum(rs, k, Spec.Held{}), cn(x, k, Spec.Held{})), Spec.qty_sum(rs, k, Spec.Held{}), Nat.add(r2, q), trN(Nat.add(Spec.qty_sum(rs, k, Spec.Held{}), cn(x, k, Spec.Held{})), Nat.add(Spec.qty_sum(rs, k, Spec.Held{}), 0n), Spec.qty_sum(rs, k, Spec.Held{}), cong_add_r(cn(x, k, Spec.Held{}), 0n, Spec.qty_sum(rs, k, Spec.Held{}), cnX), symN(Spec.qty_sum(rs, k, Spec.Held{}), Nat.add(Spec.qty_sum(rs, k, Spec.Held{}), 0n), az(Spec.qty_sum(rs, k, Spec.Held{})))), trN(Spec.qty_sum(rs, k, Spec.Held{}), rv, Nat.add(r2, q), symN(rv, Spec.qty_sum(rs, k, Spec.Held{}), eqrv), symN(Nat.add(r2, q), rv, hr))))))))


# confirm: the Confirmed counter gains q
def sold_put_c(+rs: +List<Spec.Res>, +id: Nat, +x: Spec.Res, +r: Spec.Res, +k: Nat, +q: Nat, +sd: Nat, +hf: {Spec.find_res(rs, id) == Spec.Got{r} : Spec.Look}, +eqsd: {sd == Spec.qty_sum(rs, k, Spec.Confirmed{}) : Nat}, +cnR: {cn(r, k, Spec.Confirmed{}) == 0n : Nat}, +cnX: {cn(x, k, Spec.Confirmed{}) == q : Nat}) -> {Nat.is_eq(Nat.add(sd, q), Spec.qty_sum(Spec.put_res(rs, id, x), k, Spec.Confirmed{})) == True{} : Bool}:
  eq_back(Nat.add(sd, q), Spec.qty_sum(Spec.put_res(rs, id, x), k, Spec.Confirmed{}), trN(Nat.add(sd, q), Nat.add(Spec.qty_sum(rs, k, Spec.Confirmed{}), q), Spec.qty_sum(Spec.put_res(rs, id, x), k, Spec.Confirmed{}), cong_add_l(sd, Spec.qty_sum(rs, k, Spec.Confirmed{}), q, eqsd), trN(Nat.add(Spec.qty_sum(rs, k, Spec.Confirmed{}), q), Nat.add(Spec.qty_sum(rs, k, Spec.Confirmed{}), cn(x, k, Spec.Confirmed{})), Spec.qty_sum(Spec.put_res(rs, id, x), k, Spec.Confirmed{}), cong_add_r(q, cn(x, k, Spec.Confirmed{}), Spec.qty_sum(rs, k, Spec.Confirmed{}), symN(cn(x, k, Spec.Confirmed{}), q, cnX)), trN(Nat.add(Spec.qty_sum(rs, k, Spec.Confirmed{}), cn(x, k, Spec.Confirmed{})), Nat.add(Spec.qty_sum(Spec.put_res(rs, id, x), k, Spec.Confirmed{}), cn(r, k, Spec.Confirmed{})), Spec.qty_sum(Spec.put_res(rs, id, x), k, Spec.Confirmed{}), symN(Nat.add(Spec.qty_sum(Spec.put_res(rs, id, x), k, Spec.Confirmed{}), cn(r, k, Spec.Confirmed{})), Nat.add(Spec.qty_sum(rs, k, Spec.Confirmed{}), cn(x, k, Spec.Confirmed{})), qs_put(rs, id, x, r, k, Spec.Confirmed{}, hf)), trN(Nat.add(Spec.qty_sum(Spec.put_res(rs, id, x), k, Spec.Confirmed{}), cn(r, k, Spec.Confirmed{})), Nat.add(Spec.qty_sum(Spec.put_res(rs, id, x), k, Spec.Confirmed{}), 0n), Spec.qty_sum(Spec.put_res(rs, id, x), k, Spec.Confirmed{}), cong_add_r(cn(r, k, Spec.Confirmed{}), 0n, Spec.qty_sum(Spec.put_res(rs, id, x), k, Spec.Confirmed{}), cnR), symN(Spec.qty_sum(Spec.put_res(rs, id, x), k, Spec.Confirmed{}), Nat.add(Spec.qty_sum(Spec.put_res(rs, id, x), k, Spec.Confirmed{}), 0n), az(Spec.qty_sum(Spec.put_res(rs, id, x), k, Spec.Confirmed{}))))))))


# expire: the Confirmed counter is unchanged
def sold_put_e(+rs: +List<Spec.Res>, +id: Nat, +x: Spec.Res, +r: Spec.Res, +k: Nat, +sd: Nat, +hf: {Spec.find_res(rs, id) == Spec.Got{r} : Spec.Look}, +eqsd: {sd == Spec.qty_sum(rs, k, Spec.Confirmed{}) : Nat}, +cnR: {cn(r, k, Spec.Confirmed{}) == 0n : Nat}, +cnX: {cn(x, k, Spec.Confirmed{}) == 0n : Nat}) -> {Nat.is_eq(sd, Spec.qty_sum(Spec.put_res(rs, id, x), k, Spec.Confirmed{})) == True{} : Bool}:
  eq_back(sd, Spec.qty_sum(Spec.put_res(rs, id, x), k, Spec.Confirmed{}), trN(sd, Spec.qty_sum(rs, k, Spec.Confirmed{}), Spec.qty_sum(Spec.put_res(rs, id, x), k, Spec.Confirmed{}), eqsd, trN(Spec.qty_sum(rs, k, Spec.Confirmed{}), Nat.add(Spec.qty_sum(rs, k, Spec.Confirmed{}), cn(x, k, Spec.Confirmed{})), Spec.qty_sum(Spec.put_res(rs, id, x), k, Spec.Confirmed{}), trN(Spec.qty_sum(rs, k, Spec.Confirmed{}), Nat.add(Spec.qty_sum(rs, k, Spec.Confirmed{}), 0n), Nat.add(Spec.qty_sum(rs, k, Spec.Confirmed{}), cn(x, k, Spec.Confirmed{})), az(Spec.qty_sum(rs, k, Spec.Confirmed{})), cong_add_r(0n, cn(x, k, Spec.Confirmed{}), Spec.qty_sum(rs, k, Spec.Confirmed{}), symN(cn(x, k, Spec.Confirmed{}), 0n, cnX))), trN(Nat.add(Spec.qty_sum(rs, k, Spec.Confirmed{}), cn(x, k, Spec.Confirmed{})), Nat.add(Spec.qty_sum(Spec.put_res(rs, id, x), k, Spec.Confirmed{}), cn(r, k, Spec.Confirmed{})), Spec.qty_sum(Spec.put_res(rs, id, x), k, Spec.Confirmed{}), symN(Nat.add(Spec.qty_sum(Spec.put_res(rs, id, x), k, Spec.Confirmed{}), cn(r, k, Spec.Confirmed{})), Nat.add(Spec.qty_sum(rs, k, Spec.Confirmed{}), cn(x, k, Spec.Confirmed{})), qs_put(rs, id, x, r, k, Spec.Confirmed{}, hf)), trN(Nat.add(Spec.qty_sum(Spec.put_res(rs, id, x), k, Spec.Confirmed{}), cn(r, k, Spec.Confirmed{})), Nat.add(Spec.qty_sum(Spec.put_res(rs, id, x), k, Spec.Confirmed{}), 0n), Spec.qty_sum(Spec.put_res(rs, id, x), k, Spec.Confirmed{}), cong_add_r(cn(r, k, Spec.Confirmed{}), 0n, Spec.qty_sum(Spec.put_res(rs, id, x), k, Spec.Confirmed{}), cnR), symN(Spec.qty_sum(Spec.put_res(rs, id, x), k, Spec.Confirmed{}), Nat.add(Spec.qty_sum(Spec.put_res(rs, id, x), k, Spec.Confirmed{}), 0n), az(Spec.qty_sum(Spec.put_res(rs, id, x), k, Spec.Confirmed{}))))))))

def inv_r_acc(+u: Bool, +clk: Nat, +ksku: Nat, +tot: Nat, +av: Nat, +rv: Nat, +sd: Nat, +rs: +List<Spec.Res>, +id: Nat, +sku: Nat, +qty: Nat, +ttl: Nat, +a2: Nat, +h: {Spec.inv(mkS(u, clk, ksku, tot, av, rv, sd, rs)) == True{} : Bool}, +ha: {Nat.add(a2, qty) == av : Nat}, +hk: {Nat.is_eq(sku, ksku) == True{} : Bool}, +hd: {Spec.find_res(rs, id) == Spec.NoRes{} : Spec.Look}) -> {Spec.inv(Spec.st(reserve_mk(u, clk, ksku, tot, a2, rv, sd, rs, id, sku, qty, ttl))) == True{} : Bool}:
  i_mk(Spec.st(reserve_mk(u, clk, ksku, tot, a2, rv, sd, rs, id, sku, qty, ttl)), eq_back(Nat.add(Nat.add(a2, Nat.add(rv, qty)), sd), tot, p2_rsv(a2, qty, rv, sd, tot, trN(Nat.add(Nat.add(Nat.add(a2, qty), rv), sd), Nat.add(Nat.add(av, rv), sd), tot, cong_add_l(Nat.add(Nat.add(a2, qty), rv), Nat.add(av, rv), sd, cong_add_l(Nat.add(a2, qty), av, rv, ha)), eq_prop(Nat.add(Nat.add(av, rv), sd), tot, i_p2(mkS(u, clk, ksku, tot, av, rv, sd, rs), h))))), all_snoc(Spec.PThree{}, ksku, rs, Spec.Res{id, sku, qty, Spec.Held{}, Nat.add(clk, ttl), 0n, 0n}, i_p3(mkS(u, clk, ksku, tot, av, rv, sd, rs), h), {==}), all_snoc(Spec.PFourA{}, ksku, rs, Spec.Res{id, sku, qty, Spec.Held{}, Nat.add(clk, ttl), 0n, 0n}, i_p4a(mkS(u, clk, ksku, tot, av, rv, sd, rs), h), {==}), and_i(Nat.is_eq(Nat.add(rv, qty), Spec.qty_sum(snoc(rs, Spec.Res{id, sku, qty, Spec.Held{}, Nat.add(clk, ttl), 0n, 0n}), ksku, Spec.Held{})), Nat.is_eq(sd, Spec.qty_sum(snoc(rs, Spec.Res{id, sku, qty, Spec.Held{}, Nat.add(clk, ttl), 0n, 0n}), ksku, Spec.Confirmed{})), eq_back(Nat.add(rv, qty), Spec.qty_sum(snoc(rs, Spec.Res{id, sku, qty, Spec.Held{}, Nat.add(clk, ttl), 0n, 0n}), ksku, Spec.Held{}), trN(Nat.add(rv, qty), Nat.add(Spec.qty_sum(rs, ksku, Spec.Held{}), cn(Spec.Res{id, sku, qty, Spec.Held{}, Nat.add(clk, ttl), 0n, 0n}, ksku, Spec.Held{})), Spec.qty_sum(snoc(rs, Spec.Res{id, sku, qty, Spec.Held{}, Nat.add(clk, ttl), 0n, 0n}), ksku, Spec.Held{}), trN(Nat.add(rv, qty), Nat.add(Spec.qty_sum(rs, ksku, Spec.Held{}), qty), Nat.add(Spec.qty_sum(rs, ksku, Spec.Held{}), cn(Spec.Res{id, sku, qty, Spec.Held{}, Nat.add(clk, ttl), 0n, 0n}, ksku, Spec.Held{})), cong_add_l(rv, Spec.qty_sum(rs, ksku, Spec.Held{}), qty, eq_prop(rv, Spec.qty_sum(rs, ksku, Spec.Held{}), and_l(Nat.is_eq(rv, Spec.qty_sum(rs, ksku, Spec.Held{})), Nat.is_eq(sd, Spec.qty_sum(rs, ksku, Spec.Confirmed{})), i_a1(mkS(u, clk, ksku, tot, av, rv, sd, rs), h)))), cong_add_r(qty, cn(Spec.Res{id, sku, qty, Spec.Held{}, Nat.add(clk, ttl), 0n, 0n}, ksku, Spec.Held{}), Spec.qty_sum(rs, ksku, Spec.Held{}), symN(cn(Spec.Res{id, sku, qty, Spec.Held{}, Nat.add(clk, ttl), 0n, 0n}, ksku, Spec.Held{}), qty, cn_hit(Spec.Res{id, sku, qty, Spec.Held{}, Nat.add(clk, ttl), 0n, 0n}, ksku, Spec.Held{}, and_i(Nat.is_eq(sku, ksku), True{}, hk, {==}))))), qs_snoc(rs, ksku, Spec.Held{}, Spec.Res{id, sku, qty, Spec.Held{}, Nat.add(clk, ttl), 0n, 0n}))), eq_back(sd, Spec.qty_sum(snoc(rs, Spec.Res{id, sku, qty, Spec.Held{}, Nat.add(clk, ttl), 0n, 0n}), ksku, Spec.Confirmed{}), trN(sd, Spec.qty_sum(rs, ksku, Spec.Confirmed{}), Spec.qty_sum(snoc(rs, Spec.Res{id, sku, qty, Spec.Held{}, Nat.add(clk, ttl), 0n, 0n}), ksku, Spec.Confirmed{}), eq_prop(sd, Spec.qty_sum(rs, ksku, Spec.Confirmed{}), and_r(Nat.is_eq(rv, Spec.qty_sum(rs, ksku, Spec.Held{})), Nat.is_eq(sd, Spec.qty_sum(rs, ksku, Spec.Confirmed{})), i_a1(mkS(u, clk, ksku, tot, av, rv, sd, rs), h))), trN(Spec.qty_sum(rs, ksku, Spec.Confirmed{}), Nat.add(Spec.qty_sum(rs, ksku, Spec.Confirmed{}), cn(Spec.Res{id, sku, qty, Spec.Held{}, Nat.add(clk, ttl), 0n, 0n}, ksku, Spec.Confirmed{})), Spec.qty_sum(snoc(rs, Spec.Res{id, sku, qty, Spec.Held{}, Nat.add(clk, ttl), 0n, 0n}), ksku, Spec.Confirmed{}), trN(Spec.qty_sum(rs, ksku, Spec.Confirmed{}), Nat.add(Spec.qty_sum(rs, ksku, Spec.Confirmed{}), 0n), Nat.add(Spec.qty_sum(rs, ksku, Spec.Confirmed{}), cn(Spec.Res{id, sku, qty, Spec.Held{}, Nat.add(clk, ttl), 0n, 0n}, ksku, Spec.Confirmed{})), az(Spec.qty_sum(rs, ksku, Spec.Confirmed{})), cong_add_r(0n, cn(Spec.Res{id, sku, qty, Spec.Held{}, Nat.add(clk, ttl), 0n, 0n}, ksku, Spec.Confirmed{}), Spec.qty_sum(rs, ksku, Spec.Confirmed{}), symN(cn(Spec.Res{id, sku, qty, Spec.Held{}, Nat.add(clk, ttl), 0n, 0n}, ksku, Spec.Confirmed{}), 0n, cn_miss(Spec.Res{id, sku, qty, Spec.Held{}, Nat.add(clk, ttl), 0n, 0n}, ksku, Spec.Confirmed{}, and_f_r(Nat.is_eq(sku, ksku)))))), qs_snoc(rs, ksku, Spec.Confirmed{}, Spec.Res{id, sku, qty, Spec.Held{}, Nat.add(clk, ttl), 0n, 0n}))))), and_i(Spec.uniq(snoc(rs, Spec.Res{id, sku, qty, Spec.Held{}, Nat.add(clk, ttl), 0n, 0n})), Spec.all_rec(Spec.PSku{}, ksku, snoc(rs, Spec.Res{id, sku, qty, Spec.Held{}, Nat.add(clk, ttl), 0n, 0n})), uniq_snoc(rs, Spec.Res{id, sku, qty, Spec.Held{}, Nat.add(clk, ttl), 0n, 0n}, and_l(Spec.uniq(rs), Spec.all_rec(Spec.PSku{}, ksku, rs), i_a2(mkS(u, clk, ksku, tot, av, rv, sd, rs), h)), fn_hid(rs, id, hd)), all_snoc(Spec.PSku{}, ksku, rs, Spec.Res{id, sku, qty, Spec.Held{}, Nat.add(clk, ttl), 0n, 0n}, and_r(Spec.uniq(rs), Spec.all_rec(Spec.PSku{}, ksku, rs), i_a2(mkS(u, clk, ksku, tot, av, rv, sd, rs), h)), hk)))


def inv_c_acc(+u: Bool, +clk: Nat, +ksku: Nat, +tot: Nat, +av: Nat, +rv: Nat, +sd: Nat, +rs: +List<Spec.Res>, +id: Nat, +i: Nat, +sku: Nat, +qty: Nat, +exp: Nat, +cf: Nat, +ret: Nat, +r2: Nat, +h: {Spec.inv(mkS(u, clk, ksku, tot, av, rv, sd, rs)) == True{} : Bool}, +hr: {Nat.add(r2, qty) == rv : Nat}, +hf: {Spec.find_res(rs, id) == Spec.Got{Spec.Res{i, sku, qty, Spec.Held{}, exp, cf, ret}} : Spec.Look}, +hd: {Nat.is_le(exp, clk) == False{} : Bool}) -> {Spec.inv(Spec.st(confirm_mk(u, clk, ksku, tot, av, r2, sd, rs, id, sku, qty, exp, ret))) == True{} : Bool}:
  i_mk(Spec.st(confirm_mk(u, clk, ksku, tot, av, r2, sd, rs, id, sku, qty, exp, ret)), eq_back(Nat.add(Nat.add(av, r2), Nat.add(sd, qty)), tot, p2_conf(av, r2, qty, sd, tot, trN(Nat.add(Nat.add(av, Nat.add(r2, qty)), sd), Nat.add(Nat.add(av, rv), sd), tot, cong_add_l(Nat.add(av, Nat.add(r2, qty)), Nat.add(av, rv), sd, cong_add_r(Nat.add(r2, qty), rv, av, hr)), eq_prop(Nat.add(Nat.add(av, rv), sd), tot, i_p2(mkS(u, clk, ksku, tot, av, rv, sd, rs), h))))), all_put(Spec.PThree{}, ksku, rs, id, Spec.Res{id, sku, qty, Spec.Confirmed{}, exp, clk, ret}, i_p3(mkS(u, clk, ksku, tot, av, rv, sd, rs), h), all_find(Spec.PThree{}, ksku, rs, id, Spec.Res{i, sku, qty, Spec.Held{}, exp, cf, ret}, i_p3(mkS(u, clk, ksku, tot, av, rv, sd, rs), h), hf)), all_put(Spec.PFourA{}, ksku, rs, id, Spec.Res{id, sku, qty, Spec.Confirmed{}, exp, clk, ret}, i_p4a(mkS(u, clk, ksku, tot, av, rv, sd, rs), h), lt_of_not_le(exp, clk, hd)), and_i(Nat.is_eq(r2, Spec.qty_sum(Spec.put_res(rs, id, Spec.Res{id, sku, qty, Spec.Confirmed{}, exp, clk, ret}), ksku, Spec.Held{})), Nat.is_eq(Nat.add(sd, qty), Spec.qty_sum(Spec.put_res(rs, id, Spec.Res{id, sku, qty, Spec.Confirmed{}, exp, clk, ret}), ksku, Spec.Confirmed{})), held_put(rs, id, Spec.Res{id, sku, qty, Spec.Confirmed{}, exp, clk, ret}, Spec.Res{i, sku, qty, Spec.Held{}, exp, cf, ret}, ksku, qty, rv, r2, hf, hr, eq_prop(rv, Spec.qty_sum(rs, ksku, Spec.Held{}), and_l(Nat.is_eq(rv, Spec.qty_sum(rs, ksku, Spec.Held{})), Nat.is_eq(sd, Spec.qty_sum(rs, ksku, Spec.Confirmed{})), i_a1(mkS(u, clk, ksku, tot, av, rv, sd, rs), h))), cn_hit(Spec.Res{i, sku, qty, Spec.Held{}, exp, cf, ret}, ksku, Spec.Held{}, and_i(Nat.is_eq(sku, ksku), True{}, all_find(Spec.PSku{}, ksku, rs, id, Spec.Res{i, sku, qty, Spec.Held{}, exp, cf, ret}, and_r(Spec.uniq(rs), Spec.all_rec(Spec.PSku{}, ksku, rs), i_a2(mkS(u, clk, ksku, tot, av, rv, sd, rs), h)), hf), {==})), cn_miss(Spec.Res{id, sku, qty, Spec.Confirmed{}, exp, clk, ret}, ksku, Spec.Held{}, and_f_r(Nat.is_eq(sku, ksku)))), sold_put_c(rs, id, Spec.Res{id, sku, qty, Spec.Confirmed{}, exp, clk, ret}, Spec.Res{i, sku, qty, Spec.Held{}, exp, cf, ret}, ksku, qty, sd, hf, eq_prop(sd, Spec.qty_sum(rs, ksku, Spec.Confirmed{}), and_r(Nat.is_eq(rv, Spec.qty_sum(rs, ksku, Spec.Held{})), Nat.is_eq(sd, Spec.qty_sum(rs, ksku, Spec.Confirmed{})), i_a1(mkS(u, clk, ksku, tot, av, rv, sd, rs), h))), cn_miss(Spec.Res{i, sku, qty, Spec.Held{}, exp, cf, ret}, ksku, Spec.Confirmed{}, and_f_r(Nat.is_eq(sku, ksku))), cn_hit(Spec.Res{id, sku, qty, Spec.Confirmed{}, exp, clk, ret}, ksku, Spec.Confirmed{}, and_i(Nat.is_eq(sku, ksku), True{}, all_find(Spec.PSku{}, ksku, rs, id, Spec.Res{i, sku, qty, Spec.Held{}, exp, cf, ret}, and_r(Spec.uniq(rs), Spec.all_rec(Spec.PSku{}, ksku, rs), i_a2(mkS(u, clk, ksku, tot, av, rv, sd, rs), h)), hf), {==})))), and_i(Spec.uniq(Spec.put_res(rs, id, Spec.Res{id, sku, qty, Spec.Confirmed{}, exp, clk, ret})), Spec.all_rec(Spec.PSku{}, ksku, Spec.put_res(rs, id, Spec.Res{id, sku, qty, Spec.Confirmed{}, exp, clk, ret})), trB(Spec.uniq(Spec.put_res(rs, id, Spec.Res{id, sku, qty, Spec.Confirmed{}, exp, clk, ret})), Spec.uniq(rs), True{}, uniq_put(rs, id, Spec.Res{id, sku, qty, Spec.Confirmed{}, exp, clk, ret}, {==}), and_l(Spec.uniq(rs), Spec.all_rec(Spec.PSku{}, ksku, rs), i_a2(mkS(u, clk, ksku, tot, av, rv, sd, rs), h))), all_put(Spec.PSku{}, ksku, rs, id, Spec.Res{id, sku, qty, Spec.Confirmed{}, exp, clk, ret}, and_r(Spec.uniq(rs), Spec.all_rec(Spec.PSku{}, ksku, rs), i_a2(mkS(u, clk, ksku, tot, av, rv, sd, rs), h)), all_find(Spec.PSku{}, ksku, rs, id, Spec.Res{i, sku, qty, Spec.Held{}, exp, cf, ret}, and_r(Spec.uniq(rs), Spec.all_rec(Spec.PSku{}, ksku, rs), i_a2(mkS(u, clk, ksku, tot, av, rv, sd, rs), h)), hf))))


def inv_e_acc(+u: Bool, +clk: Nat, +ksku: Nat, +tot: Nat, +av: Nat, +rv: Nat, +sd: Nat, +rs: +List<Spec.Res>, +id: Nat, +i: Nat, +sku: Nat, +qty: Nat, +exp: Nat, +cf: Nat, +ret: Nat, +r2: Nat, +h: {Spec.inv(mkS(u, clk, ksku, tot, av, rv, sd, rs)) == True{} : Bool}, +hr: {Nat.add(r2, qty) == rv : Nat}, +hf: {Spec.find_res(rs, id) == Spec.Got{Spec.Res{i, sku, qty, Spec.Held{}, exp, cf, ret}} : Spec.Look}, +hd: {Nat.is_le(exp, clk) == True{} : Bool}) -> {Spec.inv(Spec.st(expire_mk(u, clk, ksku, tot, av, r2, sd, rs, id, sku, qty, exp, cf, ret))) == True{} : Bool}:
  i_mk(Spec.st(expire_mk(u, clk, ksku, tot, av, r2, sd, rs, id, sku, qty, exp, cf, ret)), eq_back(Nat.add(Nat.add(Nat.add(av, qty), r2), sd), tot, p2_exp(av, qty, r2, sd, tot, trN(Nat.add(Nat.add(av, Nat.add(r2, qty)), sd), Nat.add(Nat.add(av, rv), sd), tot, cong_add_l(Nat.add(av, Nat.add(r2, qty)), Nat.add(av, rv), sd, cong_add_r(Nat.add(r2, qty), rv, av, hr)), eq_prop(Nat.add(Nat.add(av, rv), sd), tot, i_p2(mkS(u, clk, ksku, tot, av, rv, sd, rs), h))))), all_put(Spec.PThree{}, ksku, rs, id, Spec.Res{id, sku, qty, Spec.Expired{}, exp, cf, Nat.add(ret, 1n)}, i_p3(mkS(u, clk, ksku, tot, av, rv, sd, rs), h), ret_one(ret, all_find(Spec.PThree{}, ksku, rs, id, Spec.Res{i, sku, qty, Spec.Held{}, exp, cf, ret}, i_p3(mkS(u, clk, ksku, tot, av, rv, sd, rs), h), hf))), all_put(Spec.PFourA{}, ksku, rs, id, Spec.Res{id, sku, qty, Spec.Expired{}, exp, cf, Nat.add(ret, 1n)}, i_p4a(mkS(u, clk, ksku, tot, av, rv, sd, rs), h), {==}), and_i(Nat.is_eq(r2, Spec.qty_sum(Spec.put_res(rs, id, Spec.Res{id, sku, qty, Spec.Expired{}, exp, cf, Nat.add(ret, 1n)}), ksku, Spec.Held{})), Nat.is_eq(sd, Spec.qty_sum(Spec.put_res(rs, id, Spec.Res{id, sku, qty, Spec.Expired{}, exp, cf, Nat.add(ret, 1n)}), ksku, Spec.Confirmed{})), held_put(rs, id, Spec.Res{id, sku, qty, Spec.Expired{}, exp, cf, Nat.add(ret, 1n)}, Spec.Res{i, sku, qty, Spec.Held{}, exp, cf, ret}, ksku, qty, rv, r2, hf, hr, eq_prop(rv, Spec.qty_sum(rs, ksku, Spec.Held{}), and_l(Nat.is_eq(rv, Spec.qty_sum(rs, ksku, Spec.Held{})), Nat.is_eq(sd, Spec.qty_sum(rs, ksku, Spec.Confirmed{})), i_a1(mkS(u, clk, ksku, tot, av, rv, sd, rs), h))), cn_hit(Spec.Res{i, sku, qty, Spec.Held{}, exp, cf, ret}, ksku, Spec.Held{}, and_i(Nat.is_eq(sku, ksku), True{}, all_find(Spec.PSku{}, ksku, rs, id, Spec.Res{i, sku, qty, Spec.Held{}, exp, cf, ret}, and_r(Spec.uniq(rs), Spec.all_rec(Spec.PSku{}, ksku, rs), i_a2(mkS(u, clk, ksku, tot, av, rv, sd, rs), h)), hf), {==})), cn_miss(Spec.Res{id, sku, qty, Spec.Expired{}, exp, cf, Nat.add(ret, 1n)}, ksku, Spec.Held{}, and_f_r(Nat.is_eq(sku, ksku)))), sold_put_e(rs, id, Spec.Res{id, sku, qty, Spec.Expired{}, exp, cf, Nat.add(ret, 1n)}, Spec.Res{i, sku, qty, Spec.Held{}, exp, cf, ret}, ksku, sd, hf, eq_prop(sd, Spec.qty_sum(rs, ksku, Spec.Confirmed{}), and_r(Nat.is_eq(rv, Spec.qty_sum(rs, ksku, Spec.Held{})), Nat.is_eq(sd, Spec.qty_sum(rs, ksku, Spec.Confirmed{})), i_a1(mkS(u, clk, ksku, tot, av, rv, sd, rs), h))), cn_miss(Spec.Res{i, sku, qty, Spec.Held{}, exp, cf, ret}, ksku, Spec.Confirmed{}, and_f_r(Nat.is_eq(sku, ksku))), cn_miss(Spec.Res{id, sku, qty, Spec.Expired{}, exp, cf, Nat.add(ret, 1n)}, ksku, Spec.Confirmed{}, and_f_r(Nat.is_eq(sku, ksku))))), and_i(Spec.uniq(Spec.put_res(rs, id, Spec.Res{id, sku, qty, Spec.Expired{}, exp, cf, Nat.add(ret, 1n)})), Spec.all_rec(Spec.PSku{}, ksku, Spec.put_res(rs, id, Spec.Res{id, sku, qty, Spec.Expired{}, exp, cf, Nat.add(ret, 1n)})), trB(Spec.uniq(Spec.put_res(rs, id, Spec.Res{id, sku, qty, Spec.Expired{}, exp, cf, Nat.add(ret, 1n)})), Spec.uniq(rs), True{}, uniq_put(rs, id, Spec.Res{id, sku, qty, Spec.Expired{}, exp, cf, Nat.add(ret, 1n)}, {==}), and_l(Spec.uniq(rs), Spec.all_rec(Spec.PSku{}, ksku, rs), i_a2(mkS(u, clk, ksku, tot, av, rv, sd, rs), h))), all_put(Spec.PSku{}, ksku, rs, id, Spec.Res{id, sku, qty, Spec.Expired{}, exp, cf, Nat.add(ret, 1n)}, and_r(Spec.uniq(rs), Spec.all_rec(Spec.PSku{}, ksku, rs), i_a2(mkS(u, clk, ksku, tot, av, rv, sd, rs), h)), all_find(Spec.PSku{}, ksku, rs, id, Spec.Res{i, sku, qty, Spec.Held{}, exp, cf, ret}, and_r(Spec.uniq(rs), Spec.all_rec(Spec.PSku{}, ksku, rs), i_a2(mkS(u, clk, ksku, tot, av, rv, sd, rs), h)), hf))))

def nle_zero(+c: Nat) -> {Nat.is_le(0n, c) == True{} : Bool}:
  match c:
    case 0n:
      {==}
    case 1n+p:
      {==}

def le_add_l(+a: Nat, +b: Nat) -> {Nat.is_le(b, Nat.add(a, b)) == True{} : Bool}:
  match b:
    case 0n:
      nle_zero(Nat.add(a, 0n))
    case 1n+q:
      %as_(a, q) : {Nat.is_le(1n+q, _) == True{} : Bool}
      le_add_l(a, q)

def le_via(+q: Nat, +x: Nat, +rv: Nat, +e: {Nat.add(x, q) == rv : Nat}) -> {Nat.is_le(q, rv) == True{} : Bool}:
  %e : {Nat.is_le(q, _) == True{} : Bool}
  le_add_l(x, q)


def held_split(+rs: +List<Spec.Res>, +id: Nat, +x: Spec.Res, +r: Spec.Res, +k: Nat, +q: Nat, +rv: Nat, +hf: {Spec.find_res(rs, id) == Spec.Got{r} : Spec.Look}, +eqrv: {rv == Spec.qty_sum(rs, k, Spec.Held{}) : Nat}, +cnR: {cn(r, k, Spec.Held{}) == q : Nat}, +cnX: {cn(x, k, Spec.Held{}) == 0n : Nat}) -> {Nat.add(Spec.qty_sum(Spec.put_res(rs, id, x), k, Spec.Held{}), q) == rv : Nat}:
  trN(Nat.add(Spec.qty_sum(Spec.put_res(rs, id, x), k, Spec.Held{}), q), Nat.add(Spec.qty_sum(Spec.put_res(rs, id, x), k, Spec.Held{}), cn(r, k, Spec.Held{})), rv, cong_add_r(q, cn(r, k, Spec.Held{}), Spec.qty_sum(Spec.put_res(rs, id, x), k, Spec.Held{}), symN(cn(r, k, Spec.Held{}), q, cnR)), trN(Nat.add(Spec.qty_sum(Spec.put_res(rs, id, x), k, Spec.Held{}), cn(r, k, Spec.Held{})), Nat.add(Spec.qty_sum(rs, k, Spec.Held{}), cn(x, k, Spec.Held{})), rv, qs_put(rs, id, x, r, k, Spec.Held{}, hf), trN(Nat.add(Spec.qty_sum(rs, k, Spec.Held{}), cn(x, k, Spec.Held{})), Spec.qty_sum(rs, k, Spec.Held{}), rv, trN(Nat.add(Spec.qty_sum(rs, k, Spec.Held{}), cn(x, k, Spec.Held{})), Nat.add(Spec.qty_sum(rs, k, Spec.Held{}), 0n), Spec.qty_sum(rs, k, Spec.Held{}), cong_add_r(cn(x, k, Spec.Held{}), 0n, Spec.qty_sum(rs, k, Spec.Held{}), cnX), symN(Spec.qty_sum(rs, k, Spec.Held{}), Nat.add(Spec.qty_sum(rs, k, Spec.Held{}), 0n), az(Spec.qty_sum(rs, k, Spec.Held{})))), symN(rv, Spec.qty_sum(rs, k, Spec.Held{}), eqrv))))


def inv_rsv(+g1: Bool, +g2: Bool, +g3: Spec.Look, +g4: Bool, +u: Bool, +clk: Nat, +ksku: Nat, +tot: Nat, +av: Nat, +rv: Nat, +sd: Nat, +rs: +List<Spec.Res>, +id: Nat, +sku: Nat, +qty: Nat, +ttl: Nat, +h: {Spec.inv(mkS(u, clk, ksku, tot, av, rv, sd, rs)) == True{} : Bool}, +e2: {Nat.is_eq(sku, ksku) == g2 : Bool}, +e3: {Spec.find_res(rs, id) == g3 : Spec.Look}, +e4: {Nat.is_le(qty, av) == g4 : Bool}) -> {Spec.inv(Spec.st(Code.rsv(g1, g2, g3, g4, mkS(u, clk, ksku, tot, av, rv, sd, rs), id, sku, qty, ttl))) == True{} : Bool}:
  match g1 g2 g3 g4:
    case False{} _ _ _:
      h
    case True{} False{} _ _:
      h
    case True{} True{} Spec.Got{_} _:
      h
    case True{} True{} Spec.NoRes{} False{}:
      h
    case True{} True{} Spec.NoRes{} True{}:
      inv_r_acc(u, clk, ksku, tot, av, rv, sd, rs, id, sku, qty, ttl, Nat.sub(av, qty), h, le_sub_add(qty, av, e4), e2, e3)

def inv_reserve(+u: Bool, +clk: Nat, +ksku: Nat, +tot: Nat, +av: Nat, +rv: Nat, +sd: Nat, +rs: +List<Spec.Res>, +id: Nat, +sku: Nat, +qty: Nat, +ttl: Nat, +h: {Spec.inv(mkS(u, clk, ksku, tot, av, rv, sd, rs)) == True{} : Bool}) -> {Spec.inv(Spec.st(Code.reserve(mkS(u, clk, ksku, tot, av, rv, sd, rs), id, sku, qty, ttl))) == True{} : Bool}:
  inv_rsv(Bool.and(Nat.is_lt(0n, qty), Nat.is_lt(0n, ttl)), Nat.is_eq(sku, ksku), Spec.find_res(rs, id), Nat.is_le(qty, av), u, clk, ksku, tot, av, rv, sd, rs, id, sku, qty, ttl, h, {==}, {==}, {==})


def inv_conf2(+x: Spec.Status, +due: Bool, +u: Bool, +clk: Nat, +ksku: Nat, +tot: Nat, +av: Nat, +rv: Nat, +sd: Nat, +rs: +List<Spec.Res>, +id: Nat, +i: Nat, +sku: Nat, +qty: Nat, +exp: Nat, +cf: Nat, +ret: Nat, +h: {Spec.inv(mkS(u, clk, ksku, tot, av, rv, sd, rs)) == True{} : Bool}, +hf: {Spec.find_res(rs, id) == Spec.Got{Spec.Res{i, sku, qty, x, exp, cf, ret}} : Spec.Look}, +ed: {Nat.is_le(exp, clk) == due : Bool}) -> {Spec.inv(Spec.st(Code.conf2(x, due, mkS(u, clk, ksku, tot, av, rv, sd, rs), id, sku, qty, exp, ret))) == True{} : Bool}:
  match x due:
    case Spec.Held{} False{}:
      inv_c_acc(u, clk, ksku, tot, av, rv, sd, rs, id, i, sku, qty, exp, cf, ret, Nat.sub(rv, qty), h, le_sub_add(qty, rv, le_via(qty, Spec.qty_sum(Spec.put_res(rs, id, Spec.Res{id, sku, qty, Spec.Confirmed{}, exp, clk, ret}), ksku, Spec.Held{}), rv, held_split(rs, id, Spec.Res{id, sku, qty, Spec.Confirmed{}, exp, clk, ret}, Spec.Res{i, sku, qty, Spec.Held{}, exp, cf, ret}, ksku, qty, rv, hf, eq_prop(rv, Spec.qty_sum(rs, ksku, Spec.Held{}), and_l(Nat.is_eq(rv, Spec.qty_sum(rs, ksku, Spec.Held{})), Nat.is_eq(sd, Spec.qty_sum(rs, ksku, Spec.Confirmed{})), i_a1(mkS(u, clk, ksku, tot, av, rv, sd, rs), h))), cn_hit(Spec.Res{i, sku, qty, Spec.Held{}, exp, cf, ret}, ksku, Spec.Held{}, and_i(Nat.is_eq(sku, ksku), True{}, all_find(Spec.PSku{}, ksku, rs, id, Spec.Res{i, sku, qty, Spec.Held{}, exp, cf, ret}, and_r(Spec.uniq(rs), Spec.all_rec(Spec.PSku{}, ksku, rs), i_a2(mkS(u, clk, ksku, tot, av, rv, sd, rs), h)), hf), {==})), cn_miss(Spec.Res{id, sku, qty, Spec.Confirmed{}, exp, clk, ret}, ksku, Spec.Held{}, and_f_r(Nat.is_eq(sku, ksku)))))), hf, ed)
    case Spec.Held{} True{}:
      h
    case Spec.Confirmed{} _:
      h
    case Spec.Expired{} _:
      h

def inv_conf1(+l: Spec.Look, +u: Bool, +clk: Nat, +ksku: Nat, +tot: Nat, +av: Nat, +rv: Nat, +sd: Nat, +rs: +List<Spec.Res>, +id: Nat, +h: {Spec.inv(mkS(u, clk, ksku, tot, av, rv, sd, rs)) == True{} : Bool}, +el: {Spec.find_res(rs, id) == l : Spec.Look}) -> {Spec.inv(Spec.st(Code.conf1(l, mkS(u, clk, ksku, tot, av, rv, sd, rs), id))) == True{} : Bool}:
  match l:
    case Spec.NoRes{}:
      h
    case Spec.Got{Spec.Res{i, sku, qty, x, exp, cf, ret}}:
      inv_conf2(x, Nat.is_le(exp, clk), u, clk, ksku, tot, av, rv, sd, rs, id, i, sku, qty, exp, cf, ret, h, el, {==})

def inv_confirm(+u: Bool, +clk: Nat, +ksku: Nat, +tot: Nat, +av: Nat, +rv: Nat, +sd: Nat, +rs: +List<Spec.Res>, +id: Nat, +h: {Spec.inv(mkS(u, clk, ksku, tot, av, rv, sd, rs)) == True{} : Bool}) -> {Spec.inv(Spec.st(Code.confirm(mkS(u, clk, ksku, tot, av, rv, sd, rs), id))) == True{} : Bool}:
  inv_conf1(Spec.find_res(rs, id), u, clk, ksku, tot, av, rv, sd, rs, id, h, {==})


def inv_exp2(+x: Spec.Status, +due: Bool, +u: Bool, +clk: Nat, +ksku: Nat, +tot: Nat, +av: Nat, +rv: Nat, +sd: Nat, +rs: +List<Spec.Res>, +id: Nat, +i: Nat, +sku: Nat, +qty: Nat, +exp: Nat, +cf: Nat, +ret: Nat, +h: {Spec.inv(mkS(u, clk, ksku, tot, av, rv, sd, rs)) == True{} : Bool}, +hf: {Spec.find_res(rs, id) == Spec.Got{Spec.Res{i, sku, qty, x, exp, cf, ret}} : Spec.Look}, +ed: {Nat.is_le(exp, clk) == due : Bool}) -> {Spec.inv(Spec.st(Code.exp2(x, due, mkS(u, clk, ksku, tot, av, rv, sd, rs), id, sku, qty, exp, cf, ret))) == True{} : Bool}:
  match x due:
    case Spec.Held{} True{}:
      inv_e_acc(u, clk, ksku, tot, av, rv, sd, rs, id, i, sku, qty, exp, cf, ret, Nat.sub(rv, qty), h, le_sub_add(qty, rv, le_via(qty, Spec.qty_sum(Spec.put_res(rs, id, Spec.Res{id, sku, qty, Spec.Expired{}, exp, cf, Nat.add(ret, 1n)}), ksku, Spec.Held{}), rv, held_split(rs, id, Spec.Res{id, sku, qty, Spec.Expired{}, exp, cf, Nat.add(ret, 1n)}, Spec.Res{i, sku, qty, Spec.Held{}, exp, cf, ret}, ksku, qty, rv, hf, eq_prop(rv, Spec.qty_sum(rs, ksku, Spec.Held{}), and_l(Nat.is_eq(rv, Spec.qty_sum(rs, ksku, Spec.Held{})), Nat.is_eq(sd, Spec.qty_sum(rs, ksku, Spec.Confirmed{})), i_a1(mkS(u, clk, ksku, tot, av, rv, sd, rs), h))), cn_hit(Spec.Res{i, sku, qty, Spec.Held{}, exp, cf, ret}, ksku, Spec.Held{}, and_i(Nat.is_eq(sku, ksku), True{}, all_find(Spec.PSku{}, ksku, rs, id, Spec.Res{i, sku, qty, Spec.Held{}, exp, cf, ret}, and_r(Spec.uniq(rs), Spec.all_rec(Spec.PSku{}, ksku, rs), i_a2(mkS(u, clk, ksku, tot, av, rv, sd, rs), h)), hf), {==})), cn_miss(Spec.Res{id, sku, qty, Spec.Expired{}, exp, cf, Nat.add(ret, 1n)}, ksku, Spec.Held{}, and_f_r(Nat.is_eq(sku, ksku)))))), hf, ed)
    case Spec.Held{} False{}:
      h
    case Spec.Confirmed{} _:
      h
    case Spec.Expired{} _:
      h

def inv_exp1(+l: Spec.Look, +u: Bool, +clk: Nat, +ksku: Nat, +tot: Nat, +av: Nat, +rv: Nat, +sd: Nat, +rs: +List<Spec.Res>, +id: Nat, +h: {Spec.inv(mkS(u, clk, ksku, tot, av, rv, sd, rs)) == True{} : Bool}, +el: {Spec.find_res(rs, id) == l : Spec.Look}) -> {Spec.inv(Spec.st(Code.exp1(l, mkS(u, clk, ksku, tot, av, rv, sd, rs), id))) == True{} : Bool}:
  match l:
    case Spec.NoRes{}:
      h
    case Spec.Got{Spec.Res{i, sku, qty, x, exp, cf, ret}}:
      inv_exp2(x, Nat.is_le(exp, clk), u, clk, ksku, tot, av, rv, sd, rs, id, i, sku, qty, exp, cf, ret, h, el, {==})

def inv_expire(+u: Bool, +clk: Nat, +ksku: Nat, +tot: Nat, +av: Nat, +rv: Nat, +sd: Nat, +rs: +List<Spec.Res>, +id: Nat, +h: {Spec.inv(mkS(u, clk, ksku, tot, av, rv, sd, rs)) == True{} : Bool}) -> {Spec.inv(Spec.st(Code.expire(mkS(u, clk, ksku, tot, av, rv, sd, rs), id))) == True{} : Bool}:
  inv_exp1(Spec.find_res(rs, id), u, clk, ksku, tot, av, rv, sd, rs, id, h, {==})


def init_inv_l(+sku: Nat, +t: Nat) -> {Spec.inv(Spec.init(sku, t)) == True{} : Bool}:
  i_mk(Spec.init(sku, t), eq_back(Nat.add(Nat.add(t, 0n), 0n), t, trN(Nat.add(Nat.add(t, 0n), 0n), Nat.add(t, 0n), t, symN(Nat.add(t, 0n), Nat.add(Nat.add(t, 0n), 0n), az(Nat.add(t, 0n))), symN(t, Nat.add(t, 0n), az(t)))), {==}, {==}, {==}, {==})

def Laws.init_inv(sku, t):
  init_inv_l(sku, t)


def inv_gr(+u: Bool, +clk: Nat, +ksku: Nat, +tot: Nat, +av: Nat, +rv: Nat, +sd: Nat, +rs: +List<Spec.Res>, +id: Nat, +sku: Nat, +qty: Nat, +ttl: Nat, +h: {Spec.inv(mkS(u, clk, ksku, tot, av, rv, sd, rs)) == True{} : Bool}) -> {Spec.inv(Spec.st(Code.step(mkS(u, clk, ksku, tot, av, rv, sd, rs), Spec.Reserve{id, sku, qty, ttl}))) == True{} : Bool}:
  match u:
    case False{}:
      h
    case True{}:
      inv_reserve(u, clk, ksku, tot, av, rv, sd, rs, id, sku, qty, ttl, h)

def inv_gc(+u: Bool, +clk: Nat, +ksku: Nat, +tot: Nat, +av: Nat, +rv: Nat, +sd: Nat, +rs: +List<Spec.Res>, +id: Nat, +h: {Spec.inv(mkS(u, clk, ksku, tot, av, rv, sd, rs)) == True{} : Bool}) -> {Spec.inv(Spec.st(Code.step(mkS(u, clk, ksku, tot, av, rv, sd, rs), Spec.Confirm{id}))) == True{} : Bool}:
  match u:
    case False{}:
      h
    case True{}:
      inv_confirm(u, clk, ksku, tot, av, rv, sd, rs, id, h)

def inv_ge(+u: Bool, +clk: Nat, +ksku: Nat, +tot: Nat, +av: Nat, +rv: Nat, +sd: Nat, +rs: +List<Spec.Res>, +id: Nat, +h: {Spec.inv(mkS(u, clk, ksku, tot, av, rv, sd, rs)) == True{} : Bool}) -> {Spec.inv(Spec.st(Code.step(mkS(u, clk, ksku, tot, av, rv, sd, rs), Spec.Expire{id}))) == True{} : Bool}:
  match u:
    case False{}:
      h
    case True{}:
      inv_expire(u, clk, ksku, tot, av, rv, sd, rs, id, h)

def Laws.inv_step(s, e, h):
  match s e:
    case Spec.State{u, clk, Spec.Stock{ksku, tot, av, rv, sd}, rs} Spec.Reserve{id, sku, qty, ttl}:
      inv_gr(u, clk, ksku, tot, av, rv, sd, rs, id, sku, qty, ttl, h)
    case Spec.State{u, clk, Spec.Stock{ksku, tot, av, rv, sd}, rs} Spec.Confirm{id}:
      inv_gc(u, clk, ksku, tot, av, rv, sd, rs, id, h)
    case Spec.State{u, clk, Spec.Stock{ksku, tot, av, rv, sd}, rs} Spec.Expire{id}:
      inv_ge(u, clk, ksku, tot, av, rv, sd, rs, id, h)
    case Spec.State{u, clk, Spec.Stock{ksku, tot, av, rv, sd}, rs} Spec.Tick{}:
      h
    case Spec.State{u, clk, Spec.Stock{ksku, tot, av, rv, sd}, rs} Spec.Crash{}:
      h
    case Spec.State{u, clk, Spec.Stock{ksku, tot, av, rv, sd}, rs} Spec.Restart{}:
      h
    case Spec.State{u, clk, Spec.Stock{ksku, tot, av, rv, sd}, rs} Spec.ReserveCheck{id, sku, qty, ttl}:
      h
    case Spec.State{u, clk, Spec.Stock{ksku, tot, av, rv, sd}, rs} Spec.ReserveCommit{id, sku, qty, ttl}:
      inv_gr(u, clk, ksku, tot, av, rv, sd, rs, id, sku, qty, ttl, h)

def Laws.inv_run(events, s, h):
  match events:
    case Nil{}:
      h
    case +e <> t:
      Laws.inv_run(t, Spec.st(Code.step(s, e)), Laws.inv_step(s, e, h))


def Laws.p2_conservation_step(s, e, h):
  i_p2(Spec.st(Code.step(s, e)), Laws.inv_step(s, e, h))

def Laws.p2_conservation_run(events, s, h):
  match events:
    case Nil{}:
      i_p2(s, h)
    case +e <> t:
      Laws.p2_conservation_run(t, Spec.st(Code.step(s, e)), Laws.inv_step(s, e, h))


def Laws.p3_once_step(s, e, h):
  i_p3(Spec.st(Code.step(s, e)), Laws.inv_step(s, e, h))

def Laws.p3_once_run(events, s, h):
  match events:
    case Nil{}:
      i_p3(s, h)
    case +e <> t:
      Laws.p3_once_run(t, Spec.st(Code.step(s, e)), Laws.inv_step(s, e, h))


def Laws.p4a_before_due_step(s, e, h):
  i_p4a(Spec.st(Code.step(s, e)), Laws.inv_step(s, e, h))

def Laws.p4a_before_due_run(events, s, h):
  match events:
    case Nil{}:
      i_p4a(s, h)
    case +e <> t:
      Laws.p4a_before_due_run(t, Spec.st(Code.step(s, e)), Laws.inv_step(s, e, h))


def Laws.a1_counters_step(s, e, h):
  i_a1(Spec.st(Code.step(s, e)), Laws.inv_step(s, e, h))

def Laws.a1_counters_run(events, s, h):
  match events:
    case Nil{}:
      i_a1(s, h)
    case +e <> t:
      Laws.a1_counters_run(t, Spec.st(Code.step(s, e)), Laws.inv_step(s, e, h))


def Laws.a2_unique_step(s, e, h):
  i_a2(Spec.st(Code.step(s, e)), Laws.inv_step(s, e, h))

def Laws.a2_unique_run(events, s, h):
  match events:
    case Nil{}:
      i_a2(s, h)
    case +e <> t:
      Laws.a2_unique_run(t, Spec.st(Code.step(s, e)), Laws.inv_step(s, e, h))

# ================================================================ pins
def trP(-a: Spec.State & List<Spec.Effect>, -b: Spec.State & List<Spec.Effect>, -c: Spec.State & List<Spec.Effect>, ab: {a == b : Spec.State & List<Spec.Effect>}, bc: {b == c : Spec.State & List<Spec.Effect>}) -> {a == c : Spec.State & List<Spec.Effect>}:
  Equal.trans(Spec.State & List<Spec.Effect>, a, b, c, ab, bc)

def gate_t(+up: Bool, +s: Spec.State, r: Spec.State & List<Spec.Effect>, +hu: {up == True{} : Bool}) -> {Code.gate(up, s, r) == r : Spec.State & List<Spec.Effect>}:
  match up:
    case False{}:
      ft_absurd({(s, Nil{}) == r : Spec.State & List<Spec.Effect>}, hu)
    case True{}:
      {==}

def gate_f(+up: Bool, +s: Spec.State, r: Spec.State & List<Spec.Effect>, +hu: {up == False{} : Bool}) -> {Code.gate(up, s, r) == (s, Nil{}) : Spec.State & List<Spec.Effect>}:
  match up:
    case False{}:
      {==}
    case True{}:
      tf_absurd({r == (s, Nil{}) : Spec.State & List<Spec.Effect>}, hu)

def contra(-G: Type, +a: Bool, +h1: {a == True{} : Bool}, +h2: {a == False{} : Bool}) -> G:
  match a:
    case False{}:
      ft_absurd(G, h1)
    case True{}:
      tf_absurd(G, h2)

def not_ft(+a: Bool, +h: {Bool.not(a) == False{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case False{}:
      tf_absurd({False{} == True{} : Bool}, h)
    case True{}:
      {==}

def pd_crash(+u: Bool, +clk: Nat, +ksku: Nat, +tot: Nat, +av: Nat, +rv: Nat, +sd: Nat, +rs: +List<Spec.Res>, +hu: {u == False{} : Bool}) -> {Code.step(mkS(u, clk, ksku, tot, av, rv, sd, rs), Spec.Crash{}) == (mkS(u, clk, ksku, tot, av, rv, sd, rs), Nil{}) : Spec.State & List<Spec.Effect>}:
  match u:
    case False{}:
      {==}
    case True{}:
      tf_absurd({Code.step(mkS(True{}, clk, ksku, tot, av, rv, sd, rs), Spec.Crash{}) == (mkS(True{}, clk, ksku, tot, av, rv, sd, rs), Nil{}) : Spec.State & List<Spec.Effect>}, hu)

def Laws.pin_tick(s, h):
  {==}

def Laws.pin_crash(s, h):
  {==}

def Laws.pin_restart(s, h):
  {==}


def Laws.pin_down(s, e, h, he, hu):
  match s e:
    case Spec.State{u, clk, Spec.Stock{ksku, tot, av, rv, sd}, rs} Spec.Reserve{id, sku, qty, ttl}:
      gate_f(u, mkS(u, clk, ksku, tot, av, rv, sd, rs), Code.reserve(mkS(u, clk, ksku, tot, av, rv, sd, rs), id, sku, qty, ttl), hu)
    case Spec.State{u, clk, Spec.Stock{ksku, tot, av, rv, sd}, rs} Spec.Confirm{id}:
      gate_f(u, mkS(u, clk, ksku, tot, av, rv, sd, rs), Code.confirm(mkS(u, clk, ksku, tot, av, rv, sd, rs), id), hu)
    case Spec.State{u, clk, Spec.Stock{ksku, tot, av, rv, sd}, rs} Spec.Expire{id}:
      gate_f(u, mkS(u, clk, ksku, tot, av, rv, sd, rs), Code.expire(mkS(u, clk, ksku, tot, av, rv, sd, rs), id), hu)
    case Spec.State{u, clk, Spec.Stock{ksku, tot, av, rv, sd}, rs} Spec.Tick{}:
      ft_absurd({Code.step(mkS(u, clk, ksku, tot, av, rv, sd, rs), Spec.Tick{}) == (mkS(u, clk, ksku, tot, av, rv, sd, rs), Nil{}) : Spec.State & List<Spec.Effect>}, he)
    case Spec.State{u, clk, Spec.Stock{ksku, tot, av, rv, sd}, rs} Spec.Crash{}:
      pd_crash(u, clk, ksku, tot, av, rv, sd, rs, hu)
    case Spec.State{u, clk, Spec.Stock{ksku, tot, av, rv, sd}, rs} Spec.Restart{}:
      ft_absurd({Code.step(mkS(u, clk, ksku, tot, av, rv, sd, rs), Spec.Restart{}) == (mkS(u, clk, ksku, tot, av, rv, sd, rs), Nil{}) : Spec.State & List<Spec.Effect>}, he)


def rsv_ok_full(+g1: Bool, +g2: Bool, +g3: Spec.Look, +g4: Bool, +hg1: {g1 == True{} : Bool}, +hg2: {g2 == True{} : Bool}, +hg3: {g3 == Spec.NoRes{} : Spec.Look}, +hg4: {g4 == True{} : Bool}, +u: Bool, +clk: Nat, +ksku: Nat, +tot: Nat, +av: Nat, +rv: Nat, +sd: Nat, +rs: +List<Spec.Res>, +id: Nat, +sku: Nat, +qty: Nat, +ttl: Nat, +a2: Nat, +ha: {Nat.add(a2, qty) == av : Nat}) -> {Code.rsv(g1, g2, g3, g4, mkS(u, clk, ksku, tot, av, rv, sd, rs), id, sku, qty, ttl) == reserve_mk(u, clk, ksku, tot, a2, rv, sd, rs, id, sku, qty, ttl) : Spec.State & List<Spec.Effect>}:
  match g1 g2 g3 g4:
    case False{} _ _ _:
      ft_absurd({Code.rsv(False{}, True{}, Spec.NoRes{}, True{}, mkS(u, clk, ksku, tot, av, rv, sd, rs), id, sku, qty, ttl) == reserve_mk(u, clk, ksku, tot, a2, rv, sd, rs, id, sku, qty, ttl) : Spec.State & List<Spec.Effect>}, hg1)
    case True{} False{} _ _:
      ft_absurd({Code.rsv(True{}, False{}, Spec.NoRes{}, True{}, mkS(u, clk, ksku, tot, av, rv, sd, rs), id, sku, qty, ttl) == reserve_mk(u, clk, ksku, tot, a2, rv, sd, rs, id, sku, qty, ttl) : Spec.State & List<Spec.Effect>}, hg2)
    case True{} True{} Spec.Got{r3} _:
      gt_absurd({Code.rsv(True{}, True{}, Spec.Got{r3}, True{}, mkS(u, clk, ksku, tot, av, rv, sd, rs), id, sku, qty, ttl) == reserve_mk(u, clk, ksku, tot, a2, rv, sd, rs, id, sku, qty, ttl) : Spec.State & List<Spec.Effect>}, r3, hg3)
    case True{} True{} Spec.NoRes{} False{}:
      ft_absurd({Code.rsv(True{}, True{}, Spec.NoRes{}, False{}, mkS(u, clk, ksku, tot, av, rv, sd, rs), id, sku, qty, ttl) == reserve_mk(u, clk, ksku, tot, a2, rv, sd, rs, id, sku, qty, ttl) : Spec.State & List<Spec.Effect>}, hg4)
    case True{} True{} Spec.NoRes{} True{}:
      %symN(Nat.sub(av, qty), a2, sub_wit(av, qty, a2, ha)) : {reserve_mk(u, clk, ksku, tot, _, rv, sd, rs, id, sku, qty, ttl) == reserve_mk(u, clk, ksku, tot, a2, rv, sd, rs, id, sku, qty, ttl) : Spec.State & List<Spec.Effect>}
      {==}

def step_rsv_ok(+u: Bool, +clk: Nat, +ksku: Nat, +tot: Nat, +av: Nat, +rv: Nat, +sd: Nat, +rs: +List<Spec.Res>, +id: Nat, +sku: Nat, +qty: Nat, +ttl: Nat, +a2: Nat, +hu: {u == True{} : Bool}, +hq: {Nat.is_lt(0n, qty) == True{} : Bool}, +ht: {Nat.is_lt(0n, ttl) == True{} : Bool}, +hk: {Nat.is_eq(sku, ksku) == True{} : Bool}, +hd: {Spec.find_res(rs, id) == Spec.NoRes{} : Spec.Look}, +hl: {Nat.is_le(qty, av) == True{} : Bool}, +ha: {Nat.add(a2, qty) == av : Nat}) -> {Code.step(mkS(u, clk, ksku, tot, av, rv, sd, rs), Spec.Reserve{id, sku, qty, ttl}) == reserve_mk(u, clk, ksku, tot, a2, rv, sd, rs, id, sku, qty, ttl) : Spec.State & List<Spec.Effect>}:
  trP(Code.step(mkS(u, clk, ksku, tot, av, rv, sd, rs), Spec.Reserve{id, sku, qty, ttl}), Code.reserve(mkS(u, clk, ksku, tot, av, rv, sd, rs), id, sku, qty, ttl), reserve_mk(u, clk, ksku, tot, a2, rv, sd, rs, id, sku, qty, ttl), gate_t(u, mkS(u, clk, ksku, tot, av, rv, sd, rs), Code.reserve(mkS(u, clk, ksku, tot, av, rv, sd, rs), id, sku, qty, ttl), hu), rsv_ok_full(Bool.and(Nat.is_lt(0n, qty), Nat.is_lt(0n, ttl)), Nat.is_eq(sku, ksku), Spec.find_res(rs, id), Nat.is_le(qty, av), and_i(Nat.is_lt(0n, qty), Nat.is_lt(0n, ttl), hq, ht), hk, hd, hl, u, clk, ksku, tot, av, rv, sd, rs, id, sku, qty, ttl, a2, ha))

def Laws.pin_reserve_ok(s, id, sku, qty, ttl, a2, h, hu, hq, ht, hk, hd, hl, ha):
  match s:
    case Spec.State{u, clk, Spec.Stock{ksku, tot, av, rv, sd}, rs}:
      step_rsv_ok(u, clk, ksku, tot, av, rv, sd, rs, id, sku, qty, ttl, a2, hu, hq, ht, hk, hd, hl, ha)


def rsv_rej_full(+g1: Bool, +g2: Bool, +g3: Spec.Look, +g4: Bool, +hrej: {Bool.and(g1, Bool.and(g2, Bool.and(Spec.look_none(g3), g4))) == False{} : Bool}, +u: Bool, +clk: Nat, +ksku: Nat, +tot: Nat, +av: Nat, +rv: Nat, +sd: Nat, +rs: +List<Spec.Res>, +id: Nat, +sku: Nat, +qty: Nat, +ttl: Nat) -> {Code.rsv(g1, g2, g3, g4, mkS(u, clk, ksku, tot, av, rv, sd, rs), id, sku, qty, ttl) == (mkS(u, clk, ksku, tot, av, rv, sd, rs), Spec.FxRejected{id, Spec.rsv_why(g1, g2, g3, g4)} <> Nil{}) : Spec.State & List<Spec.Effect>}:
  match g1 g2 g3 g4:
    case False{} _ _ _:
      {==}
    case True{} False{} _ _:
      {==}
    case True{} True{} Spec.Got{r3} _:
      {==}
    case True{} True{} Spec.NoRes{} False{}:
      {==}
    case True{} True{} Spec.NoRes{} True{}:
      tf_absurd({Code.rsv(True{}, True{}, Spec.NoRes{}, True{}, mkS(u, clk, ksku, tot, av, rv, sd, rs), id, sku, qty, ttl) == (mkS(u, clk, ksku, tot, av, rv, sd, rs), Spec.FxRejected{id, Spec.rsv_why(True{}, True{}, Spec.NoRes{}, True{})} <> Nil{}) : Spec.State & List<Spec.Effect>}, hrej)

def step_rsv_rej(+u: Bool, +clk: Nat, +ksku: Nat, +tot: Nat, +av: Nat, +rv: Nat, +sd: Nat, +rs: +List<Spec.Res>, +id: Nat, +sku: Nat, +qty: Nat, +ttl: Nat, +hu: {u == True{} : Bool}, +hn: {Spec.reserve_ok_g(mkS(u, clk, ksku, tot, av, rv, sd, rs), id, sku, qty, ttl) == False{} : Bool}) -> {Code.step(mkS(u, clk, ksku, tot, av, rv, sd, rs), Spec.Reserve{id, sku, qty, ttl}) == (mkS(u, clk, ksku, tot, av, rv, sd, rs), Spec.FxRejected{id, Spec.reserve_reason(mkS(u, clk, ksku, tot, av, rv, sd, rs), id, sku, qty, ttl)} <> Nil{}) : Spec.State & List<Spec.Effect>}:
  trP(Code.step(mkS(u, clk, ksku, tot, av, rv, sd, rs), Spec.Reserve{id, sku, qty, ttl}), Code.reserve(mkS(u, clk, ksku, tot, av, rv, sd, rs), id, sku, qty, ttl), (mkS(u, clk, ksku, tot, av, rv, sd, rs), Spec.FxRejected{id, Spec.reserve_reason(mkS(u, clk, ksku, tot, av, rv, sd, rs), id, sku, qty, ttl)} <> Nil{}), gate_t(u, mkS(u, clk, ksku, tot, av, rv, sd, rs), Code.reserve(mkS(u, clk, ksku, tot, av, rv, sd, rs), id, sku, qty, ttl), hu), rsv_rej_full(Bool.and(Nat.is_lt(0n, qty), Nat.is_lt(0n, ttl)), Nat.is_eq(sku, ksku), Spec.find_res(rs, id), Nat.is_le(qty, av), hn, u, clk, ksku, tot, av, rv, sd, rs, id, sku, qty, ttl))

def Laws.pin_reserve_rejected(s, id, sku, qty, ttl, h, hu, hn):
  match s:
    case Spec.State{u, clk, Spec.Stock{ksku, tot, av, rv, sd}, rs}:
      step_rsv_rej(u, clk, ksku, tot, av, rv, sd, rs, id, sku, qty, ttl, hu, hn)


def conf2_ok(+due: Bool, +hd: {due == False{} : Bool}, +u: Bool, +clk: Nat, +ksku: Nat, +tot: Nat, +av: Nat, +rv: Nat, +sd: Nat, +rs: +List<Spec.Res>, +id: Nat, +sku: Nat, +qty: Nat, +exp: Nat, +ret: Nat, +r2: Nat, +hr: {Nat.add(r2, qty) == rv : Nat}) -> {Code.conf2(Spec.Held{}, due, mkS(u, clk, ksku, tot, av, rv, sd, rs), id, sku, qty, exp, ret) == confirm_mk(u, clk, ksku, tot, av, r2, sd, rs, id, sku, qty, exp, ret) : Spec.State & List<Spec.Effect>}:
  match due:
    case False{}:
      %symN(Nat.sub(rv, qty), r2, sub_wit(rv, qty, r2, hr)) : {confirm_mk(u, clk, ksku, tot, av, _, sd, rs, id, sku, qty, exp, ret) == confirm_mk(u, clk, ksku, tot, av, r2, sd, rs, id, sku, qty, exp, ret) : Spec.State & List<Spec.Effect>}
      {==}
    case True{}:
      tf_absurd({Code.conf2(Spec.Held{}, True{}, mkS(u, clk, ksku, tot, av, rv, sd, rs), id, sku, qty, exp, ret) == confirm_mk(u, clk, ksku, tot, av, r2, sd, rs, id, sku, qty, exp, ret) : Spec.State & List<Spec.Effect>}, hd)

def step_conf_ok(+u: Bool, +clk: Nat, +ksku: Nat, +tot: Nat, +av: Nat, +rv: Nat, +sd: Nat, +rs: +List<Spec.Res>, +id: Nat, +sku: Nat, +qty: Nat, +exp: Nat, +cf: Nat, +ret: Nat, +r2: Nat, +hu: {u == True{} : Bool}, +hf: {Spec.find_res(rs, id) == Spec.Got{Spec.Res{id, sku, qty, Spec.Held{}, exp, cf, ret}} : Spec.Look}, +hd: {Nat.is_le(exp, clk) == False{} : Bool}, +hr: {Nat.add(r2, qty) == rv : Nat}) -> {Code.step(mkS(u, clk, ksku, tot, av, rv, sd, rs), Spec.Confirm{id}) == confirm_mk(u, clk, ksku, tot, av, r2, sd, rs, id, sku, qty, exp, ret) : Spec.State & List<Spec.Effect>}:
  trP(Code.step(mkS(u, clk, ksku, tot, av, rv, sd, rs), Spec.Confirm{id}), Code.conf1(Spec.Got{Spec.Res{id, sku, qty, Spec.Held{}, exp, cf, ret}}, mkS(u, clk, ksku, tot, av, rv, sd, rs), id), confirm_mk(u, clk, ksku, tot, av, r2, sd, rs, id, sku, qty, exp, ret), trP(Code.step(mkS(u, clk, ksku, tot, av, rv, sd, rs), Spec.Confirm{id}), Code.confirm(mkS(u, clk, ksku, tot, av, rv, sd, rs), id), Code.conf1(Spec.Got{Spec.Res{id, sku, qty, Spec.Held{}, exp, cf, ret}}, mkS(u, clk, ksku, tot, av, rv, sd, rs), id), gate_t(u, mkS(u, clk, ksku, tot, av, rv, sd, rs), Code.confirm(mkS(u, clk, ksku, tot, av, rv, sd, rs), id), hu), Equal.cong(Spec.Look, Spec.State & List<Spec.Effect>, l => Code.conf1(l, mkS(u, clk, ksku, tot, av, rv, sd, rs), id), Spec.find_res(rs, id), Spec.Got{Spec.Res{id, sku, qty, Spec.Held{}, exp, cf, ret}}, hf)), conf2_ok(Nat.is_le(exp, clk), hd, u, clk, ksku, tot, av, rv, sd, rs, id, sku, qty, exp, ret, r2, hr))

def Laws.pin_confirm_ok(s, id, sku, qty, exp, cf, ret, r2, h, hu, hf, hd, hr):
  match s:
    case Spec.State{u, clk, Spec.Stock{ksku, tot, av, rv, sd}, rs}:
      step_conf_ok(u, clk, ksku, tot, av, rv, sd, rs, id, sku, qty, exp, cf, ret, r2, hu, hf, hd, hr)

def exp2_ok(+due: Bool, +hd: {due == True{} : Bool}, +u: Bool, +clk: Nat, +ksku: Nat, +tot: Nat, +av: Nat, +rv: Nat, +sd: Nat, +rs: +List<Spec.Res>, +id: Nat, +sku: Nat, +qty: Nat, +exp: Nat, +cf: Nat, +ret: Nat, +r2: Nat, +hr: {Nat.add(r2, qty) == rv : Nat}) -> {Code.exp2(Spec.Held{}, due, mkS(u, clk, ksku, tot, av, rv, sd, rs), id, sku, qty, exp, cf, ret) == expire_mk(u, clk, ksku, tot, av, r2, sd, rs, id, sku, qty, exp, cf, ret) : Spec.State & List<Spec.Effect>}:
  match due:
    case True{}:
      %symN(Nat.sub(rv, qty), r2, sub_wit(rv, qty, r2, hr)) : {expire_mk(u, clk, ksku, tot, av, _, sd, rs, id, sku, qty, exp, cf, ret) == expire_mk(u, clk, ksku, tot, av, r2, sd, rs, id, sku, qty, exp, cf, ret) : Spec.State & List<Spec.Effect>}
      {==}
    case False{}:
      ft_absurd({Code.exp2(Spec.Held{}, False{}, mkS(u, clk, ksku, tot, av, rv, sd, rs), id, sku, qty, exp, cf, ret) == expire_mk(u, clk, ksku, tot, av, r2, sd, rs, id, sku, qty, exp, cf, ret) : Spec.State & List<Spec.Effect>}, hd)

def step_exp_ok(+u: Bool, +clk: Nat, +ksku: Nat, +tot: Nat, +av: Nat, +rv: Nat, +sd: Nat, +rs: +List<Spec.Res>, +id: Nat, +sku: Nat, +qty: Nat, +exp: Nat, +cf: Nat, +ret: Nat, +r2: Nat, +hu: {u == True{} : Bool}, +hf: {Spec.find_res(rs, id) == Spec.Got{Spec.Res{id, sku, qty, Spec.Held{}, exp, cf, ret}} : Spec.Look}, +hd: {Nat.is_le(exp, clk) == True{} : Bool}, +hr: {Nat.add(r2, qty) == rv : Nat}) -> {Code.step(mkS(u, clk, ksku, tot, av, rv, sd, rs), Spec.Expire{id}) == expire_mk(u, clk, ksku, tot, av, r2, sd, rs, id, sku, qty, exp, cf, ret) : Spec.State & List<Spec.Effect>}:
  trP(Code.step(mkS(u, clk, ksku, tot, av, rv, sd, rs), Spec.Expire{id}), Code.exp1(Spec.Got{Spec.Res{id, sku, qty, Spec.Held{}, exp, cf, ret}}, mkS(u, clk, ksku, tot, av, rv, sd, rs), id), expire_mk(u, clk, ksku, tot, av, r2, sd, rs, id, sku, qty, exp, cf, ret), trP(Code.step(mkS(u, clk, ksku, tot, av, rv, sd, rs), Spec.Expire{id}), Code.expire(mkS(u, clk, ksku, tot, av, rv, sd, rs), id), Code.exp1(Spec.Got{Spec.Res{id, sku, qty, Spec.Held{}, exp, cf, ret}}, mkS(u, clk, ksku, tot, av, rv, sd, rs), id), gate_t(u, mkS(u, clk, ksku, tot, av, rv, sd, rs), Code.expire(mkS(u, clk, ksku, tot, av, rv, sd, rs), id), hu), Equal.cong(Spec.Look, Spec.State & List<Spec.Effect>, l => Code.exp1(l, mkS(u, clk, ksku, tot, av, rv, sd, rs), id), Spec.find_res(rs, id), Spec.Got{Spec.Res{id, sku, qty, Spec.Held{}, exp, cf, ret}}, hf)), exp2_ok(Nat.is_le(exp, clk), hd, u, clk, ksku, tot, av, rv, sd, rs, id, sku, qty, exp, cf, ret, r2, hr))

def Laws.pin_expire_ok(s, id, sku, qty, exp, cf, ret, r2, h, hu, hf, hd, hr):
  match s:
    case Spec.State{u, clk, Spec.Stock{ksku, tot, av, rv, sd}, rs}:
      step_exp_ok(u, clk, ksku, tot, av, rv, sd, rs, id, sku, qty, exp, cf, ret, r2, hu, hf, hd, hr)


def conf2_rej(+x: Spec.Status, +due: Bool, +u: Bool, +clk: Nat, +ksku: Nat, +tot: Nat, +av: Nat, +rv: Nat, +sd: Nat, +rs: +List<Spec.Res>, +id: Nat, +i: Nat, +sku: Nat, +qty: Nat, +exp: Nat, +cf: Nat, +ret: Nat, +hn: {Spec.conf_acc(Spec.Got{Spec.Res{i, sku, qty, x, exp, cf, ret}}, clk) == False{} : Bool}, +ed: {Nat.is_le(exp, clk) == due : Bool}) -> {Code.conf2(x, due, mkS(u, clk, ksku, tot, av, rv, sd, rs), id, sku, qty, exp, ret) == (mkS(u, clk, ksku, tot, av, rv, sd, rs), Spec.FxRejected{id, Spec.conf_why(Spec.Got{Spec.Res{i, sku, qty, x, exp, cf, ret}}, clk)} <> Nil{}) : Spec.State & List<Spec.Effect>}:
  match x due:
    case Spec.Held{} False{}:
      contra({Code.conf2(Spec.Held{}, False{}, mkS(u, clk, ksku, tot, av, rv, sd, rs), id, sku, qty, exp, ret) == (mkS(u, clk, ksku, tot, av, rv, sd, rs), Spec.FxRejected{id, Spec.conf_why(Spec.Got{Spec.Res{i, sku, qty, Spec.Held{}, exp, cf, ret}}, clk)} <> Nil{}) : Spec.State & List<Spec.Effect>}, Nat.is_le(exp, clk), not_ft(Nat.is_le(exp, clk), hn), ed)
    case Spec.Held{} True{}:
      {==}
    case Spec.Confirmed{} _:
      {==}
    case Spec.Expired{} _:
      {==}

def conf1_rej(+l: Spec.Look, +u: Bool, +clk: Nat, +ksku: Nat, +tot: Nat, +av: Nat, +rv: Nat, +sd: Nat, +rs: +List<Spec.Res>, +id: Nat, +hn: {Spec.conf_acc(l, clk) == False{} : Bool}) -> {Code.conf1(l, mkS(u, clk, ksku, tot, av, rv, sd, rs), id) == (mkS(u, clk, ksku, tot, av, rv, sd, rs), Spec.FxRejected{id, Spec.conf_why(l, clk)} <> Nil{}) : Spec.State & List<Spec.Effect>}:
  match l:
    case Spec.NoRes{}:
      {==}
    case Spec.Got{Spec.Res{i, sku, qty, x, exp, cf, ret}}:
      conf2_rej(x, Nat.is_le(exp, clk), u, clk, ksku, tot, av, rv, sd, rs, id, i, sku, qty, exp, cf, ret, hn, {==})

def step_conf_rej(+u: Bool, +clk: Nat, +ksku: Nat, +tot: Nat, +av: Nat, +rv: Nat, +sd: Nat, +rs: +List<Spec.Res>, +id: Nat, +hu: {u == True{} : Bool}, +hn: {Spec.confirm_ok_g(mkS(u, clk, ksku, tot, av, rv, sd, rs), id) == False{} : Bool}) -> {Code.step(mkS(u, clk, ksku, tot, av, rv, sd, rs), Spec.Confirm{id}) == (mkS(u, clk, ksku, tot, av, rv, sd, rs), Spec.FxRejected{id, Spec.confirm_reason(mkS(u, clk, ksku, tot, av, rv, sd, rs), id)} <> Nil{}) : Spec.State & List<Spec.Effect>}:
  trP(Code.step(mkS(u, clk, ksku, tot, av, rv, sd, rs), Spec.Confirm{id}), Code.confirm(mkS(u, clk, ksku, tot, av, rv, sd, rs), id), (mkS(u, clk, ksku, tot, av, rv, sd, rs), Spec.FxRejected{id, Spec.confirm_reason(mkS(u, clk, ksku, tot, av, rv, sd, rs), id)} <> Nil{}), gate_t(u, mkS(u, clk, ksku, tot, av, rv, sd, rs), Code.confirm(mkS(u, clk, ksku, tot, av, rv, sd, rs), id), hu), conf1_rej(Spec.find_res(rs, id), u, clk, ksku, tot, av, rv, sd, rs, id, hn))

def Laws.pin_confirm_rejected(s, id, h, hu, hn):
  match s:
    case Spec.State{u, clk, Spec.Stock{ksku, tot, av, rv, sd}, rs}:
      step_conf_rej(u, clk, ksku, tot, av, rv, sd, rs, id, hu, hn)

def exp2_rej(+x: Spec.Status, +due: Bool, +u: Bool, +clk: Nat, +ksku: Nat, +tot: Nat, +av: Nat, +rv: Nat, +sd: Nat, +rs: +List<Spec.Res>, +id: Nat, +i: Nat, +sku: Nat, +qty: Nat, +exp: Nat, +cf: Nat, +ret: Nat, +hn: {Spec.exp_acc(Spec.Got{Spec.Res{i, sku, qty, x, exp, cf, ret}}, clk) == False{} : Bool}, +ed: {Nat.is_le(exp, clk) == due : Bool}) -> {Code.exp2(x, due, mkS(u, clk, ksku, tot, av, rv, sd, rs), id, sku, qty, exp, cf, ret) == (mkS(u, clk, ksku, tot, av, rv, sd, rs), Spec.FxRejected{id, Spec.exp_why(Spec.Got{Spec.Res{i, sku, qty, x, exp, cf, ret}}, clk)} <> Nil{}) : Spec.State & List<Spec.Effect>}:
  match x due:
    case Spec.Held{} True{}:
      contra({Code.exp2(Spec.Held{}, True{}, mkS(u, clk, ksku, tot, av, rv, sd, rs), id, sku, qty, exp, cf, ret) == (mkS(u, clk, ksku, tot, av, rv, sd, rs), Spec.FxRejected{id, Spec.exp_why(Spec.Got{Spec.Res{i, sku, qty, Spec.Held{}, exp, cf, ret}}, clk)} <> Nil{}) : Spec.State & List<Spec.Effect>}, Nat.is_le(exp, clk), ed, hn)
    case Spec.Held{} False{}:
      {==}
    case Spec.Confirmed{} _:
      {==}
    case Spec.Expired{} _:
      {==}

def exp1_rej(+l: Spec.Look, +u: Bool, +clk: Nat, +ksku: Nat, +tot: Nat, +av: Nat, +rv: Nat, +sd: Nat, +rs: +List<Spec.Res>, +id: Nat, +hn: {Spec.exp_acc(l, clk) == False{} : Bool}) -> {Code.exp1(l, mkS(u, clk, ksku, tot, av, rv, sd, rs), id) == (mkS(u, clk, ksku, tot, av, rv, sd, rs), Spec.FxRejected{id, Spec.exp_why(l, clk)} <> Nil{}) : Spec.State & List<Spec.Effect>}:
  match l:
    case Spec.NoRes{}:
      {==}
    case Spec.Got{Spec.Res{i, sku, qty, x, exp, cf, ret}}:
      exp2_rej(x, Nat.is_le(exp, clk), u, clk, ksku, tot, av, rv, sd, rs, id, i, sku, qty, exp, cf, ret, hn, {==})

def step_exp_rej(+u: Bool, +clk: Nat, +ksku: Nat, +tot: Nat, +av: Nat, +rv: Nat, +sd: Nat, +rs: +List<Spec.Res>, +id: Nat, +hu: {u == True{} : Bool}, +hn: {Spec.expire_ok_g(mkS(u, clk, ksku, tot, av, rv, sd, rs), id) == False{} : Bool}) -> {Code.step(mkS(u, clk, ksku, tot, av, rv, sd, rs), Spec.Expire{id}) == (mkS(u, clk, ksku, tot, av, rv, sd, rs), Spec.FxRejected{id, Spec.expire_reason(mkS(u, clk, ksku, tot, av, rv, sd, rs), id)} <> Nil{}) : Spec.State & List<Spec.Effect>}:
  trP(Code.step(mkS(u, clk, ksku, tot, av, rv, sd, rs), Spec.Expire{id}), Code.expire(mkS(u, clk, ksku, tot, av, rv, sd, rs), id), (mkS(u, clk, ksku, tot, av, rv, sd, rs), Spec.FxRejected{id, Spec.expire_reason(mkS(u, clk, ksku, tot, av, rv, sd, rs), id)} <> Nil{}), gate_t(u, mkS(u, clk, ksku, tot, av, rv, sd, rs), Code.expire(mkS(u, clk, ksku, tot, av, rv, sd, rs), id), hu), exp1_rej(Spec.find_res(rs, id), u, clk, ksku, tot, av, rv, sd, rs, id, hn))

def Laws.pin_expire_rejected(s, id, h, hu, hn):
  match s:
    case Spec.State{u, clk, Spec.Stock{ksku, tot, av, rv, sd}, rs}:
      step_exp_rej(u, clk, ksku, tot, av, rv, sd, rs, id, hu, hn)

# ================================================================ P1b
def lt_via(+x: Nat, +y: Nat, +e: {x == y : Nat}) -> {Nat.is_lt(x, y) == False{} : Bool}:
  %e : {Nat.is_lt(x, _) == False{} : Bool}
  lt_irrefl(x)

def eff_self(+i: Nat, +s: Nat, +q: Nat, +x: Nat) -> {Spec.eff_eq(Spec.FxReserved{i, s, q, x}, Spec.FxReserved{i, s, q, x}) == True{} : Bool}:
  and_i(Bool.and(Nat.is_eq(i, i), Nat.is_eq(s, s)), Bool.and(Nat.is_eq(q, q), Nat.is_eq(x, x)), and_i(Nat.is_eq(i, i), Nat.is_eq(s, s), eq_refl(i), eq_refl(s)), and_i(Nat.is_eq(q, q), Nat.is_eq(x, x), eq_refl(q), eq_refl(x)))


def p1b_rsv(+g1: Bool, +g2: Bool, +g3: Spec.Look, +g4: Bool, +u: Bool, +clk: Nat, +ksku: Nat, +tot: Nat, +av: Nat, +rv: Nat, +sd: Nat, +rs: +List<Spec.Res>, +id: Nat, +sku: Nat, +qty: Nat, +ttl: Nat, +e2: {Nat.is_eq(sku, ksku) == g2 : Bool}, +e4: {Nat.is_le(qty, av) == g4 : Bool}, +hl: {Nat.is_lt(Spec.k_avail(Spec.stock_of(Spec.st(Code.rsv(g1, g2, g3, g4, mkS(u, clk, ksku, tot, av, rv, sd, rs), id, sku, qty, ttl)))), av) == True{} : Bool}) -> {Spec.p1b(mkS(u, clk, ksku, tot, av, rv, sd, rs), Spec.Reserve{id, sku, qty, ttl}, Code.rsv(g1, g2, g3, g4, mkS(u, clk, ksku, tot, av, rv, sd, rs), id, sku, qty, ttl)) == True{} : Bool}:
  match g1 g2 g3 g4:
    case False{} _ _ _:
      contra({Spec.p1b(mkS(u, clk, ksku, tot, av, rv, sd, rs), Spec.Reserve{id, sku, qty, ttl}, Code.rsv(False{}, True{}, Spec.NoRes{}, True{}, mkS(u, clk, ksku, tot, av, rv, sd, rs), id, sku, qty, ttl)) == True{} : Bool}, Nat.is_lt(av, av), hl, lt_irrefl(av))
    case True{} False{} _ _:
      contra({Spec.p1b(mkS(u, clk, ksku, tot, av, rv, sd, rs), Spec.Reserve{id, sku, qty, ttl}, Code.rsv(True{}, False{}, Spec.NoRes{}, True{}, mkS(u, clk, ksku, tot, av, rv, sd, rs), id, sku, qty, ttl)) == True{} : Bool}, Nat.is_lt(av, av), hl, lt_irrefl(av))
    case True{} True{} Spec.Got{r3} _:
      contra({Spec.p1b(mkS(u, clk, ksku, tot, av, rv, sd, rs), Spec.Reserve{id, sku, qty, ttl}, Code.rsv(True{}, True{}, Spec.Got{r3}, True{}, mkS(u, clk, ksku, tot, av, rv, sd, rs), id, sku, qty, ttl)) == True{} : Bool}, Nat.is_lt(av, av), hl, lt_irrefl(av))
    case True{} True{} Spec.NoRes{} False{}:
      contra({Spec.p1b(mkS(u, clk, ksku, tot, av, rv, sd, rs), Spec.Reserve{id, sku, qty, ttl}, Code.rsv(True{}, True{}, Spec.NoRes{}, False{}, mkS(u, clk, ksku, tot, av, rv, sd, rs), id, sku, qty, ttl)) == True{} : Bool}, Nat.is_lt(av, av), hl, lt_irrefl(av))
    case True{} True{} Spec.NoRes{} True{}:
      and_i(Bool.and(Nat.is_eq(sku, ksku), Spec.fx_one(Spec.FxReserved{id, sku, qty, Nat.add(clk, ttl)} <> Nil{}, Spec.FxReserved{id, sku, qty, Nat.add(clk, ttl)})), Nat.is_eq(Nat.add(Nat.sub(av, qty), qty), av), and_i(Nat.is_eq(sku, ksku), Spec.fx_one(Spec.FxReserved{id, sku, qty, Nat.add(clk, ttl)} <> Nil{}, Spec.FxReserved{id, sku, qty, Nat.add(clk, ttl)}), e2, eff_self(id, sku, qty, Nat.add(clk, ttl))), eq_back(Nat.add(Nat.sub(av, qty), qty), av, le_sub_add(qty, av, e4)))

def p1b_gr(+u: Bool, +clk: Nat, +ksku: Nat, +tot: Nat, +av: Nat, +rv: Nat, +sd: Nat, +rs: +List<Spec.Res>, +id: Nat, +sku: Nat, +qty: Nat, +ttl: Nat, +hl: {Nat.is_lt(Spec.k_avail(Spec.stock_of(Spec.st(Code.step(mkS(u, clk, ksku, tot, av, rv, sd, rs), Spec.Reserve{id, sku, qty, ttl})))), av) == True{} : Bool}) -> {Spec.p1b(mkS(u, clk, ksku, tot, av, rv, sd, rs), Spec.Reserve{id, sku, qty, ttl}, Code.step(mkS(u, clk, ksku, tot, av, rv, sd, rs), Spec.Reserve{id, sku, qty, ttl})) == True{} : Bool}:
  match u:
    case False{}:
      contra({Spec.p1b(mkS(False{}, clk, ksku, tot, av, rv, sd, rs), Spec.Reserve{id, sku, qty, ttl}, Code.step(mkS(False{}, clk, ksku, tot, av, rv, sd, rs), Spec.Reserve{id, sku, qty, ttl})) == True{} : Bool}, Nat.is_lt(av, av), hl, lt_irrefl(av))
    case True{}:
      p1b_rsv(Bool.and(Nat.is_lt(0n, qty), Nat.is_lt(0n, ttl)), Nat.is_eq(sku, ksku), Spec.find_res(rs, id), Nat.is_le(qty, av), u, clk, ksku, tot, av, rv, sd, rs, id, sku, qty, ttl, {==}, {==}, hl)


def lt_conf2(+x: Spec.Status, +due: Bool, +u: Bool, +clk: Nat, +ksku: Nat, +tot: Nat, +av: Nat, +rv: Nat, +sd: Nat, +rs: +List<Spec.Res>, +id: Nat, +sku: Nat, +qty: Nat, +exp: Nat, +ret: Nat) -> {Nat.is_lt(Spec.k_avail(Spec.stock_of(Spec.st(Code.conf2(x, due, mkS(u, clk, ksku, tot, av, rv, sd, rs), id, sku, qty, exp, ret)))), av) == False{} : Bool}:
  match x due:
    case Spec.Held{} False{}:
      lt_irrefl(av)
    case Spec.Held{} True{}:
      lt_irrefl(av)
    case Spec.Confirmed{} _:
      lt_irrefl(av)
    case Spec.Expired{} _:
      lt_irrefl(av)

def lt_conf1(+l: Spec.Look, +u: Bool, +clk: Nat, +ksku: Nat, +tot: Nat, +av: Nat, +rv: Nat, +sd: Nat, +rs: +List<Spec.Res>, +id: Nat) -> {Nat.is_lt(Spec.k_avail(Spec.stock_of(Spec.st(Code.conf1(l, mkS(u, clk, ksku, tot, av, rv, sd, rs), id)))), av) == False{} : Bool}:
  match l:
    case Spec.NoRes{}:
      lt_irrefl(av)
    case Spec.Got{Spec.Res{i, sku, qty, x, exp, cf, ret}}:
      lt_conf2(x, Nat.is_le(exp, clk), u, clk, ksku, tot, av, rv, sd, rs, id, sku, qty, exp, ret)


def p1b_gc(+u: Bool, +clk: Nat, +ksku: Nat, +tot: Nat, +av: Nat, +rv: Nat, +sd: Nat, +rs: +List<Spec.Res>, +id: Nat, +hl: {Nat.is_lt(Spec.k_avail(Spec.stock_of(Spec.st(Code.step(mkS(u, clk, ksku, tot, av, rv, sd, rs), Spec.Confirm{id})))), av) == True{} : Bool}) -> {Spec.p1b(mkS(u, clk, ksku, tot, av, rv, sd, rs), Spec.Confirm{id}, Code.step(mkS(u, clk, ksku, tot, av, rv, sd, rs), Spec.Confirm{id})) == True{} : Bool}:
  match u:
    case False{}:
      contra({Spec.p1b(mkS(False{}, clk, ksku, tot, av, rv, sd, rs), Spec.Confirm{id}, Code.step(mkS(False{}, clk, ksku, tot, av, rv, sd, rs), Spec.Confirm{id})) == True{} : Bool}, Nat.is_lt(av, av), hl, lt_irrefl(av))
    case True{}:
      contra({Spec.p1b(mkS(True{}, clk, ksku, tot, av, rv, sd, rs), Spec.Confirm{id}, Code.step(mkS(True{}, clk, ksku, tot, av, rv, sd, rs), Spec.Confirm{id})) == True{} : Bool}, Nat.is_lt(Spec.k_avail(Spec.stock_of(Spec.st(Code.conf1(Spec.find_res(rs, id), mkS(True{}, clk, ksku, tot, av, rv, sd, rs), id)))), av), hl, lt_conf1(Spec.find_res(rs, id), u, clk, ksku, tot, av, rv, sd, rs, id))


def lt_exp2(+x: Spec.Status, +due: Bool, +u: Bool, +clk: Nat, +ksku: Nat, +tot: Nat, +av: Nat, +rv: Nat, +sd: Nat, +rs: +List<Spec.Res>, +id: Nat, +sku: Nat, +qty: Nat, +exp: Nat, +cf: Nat, +ret: Nat) -> {Nat.is_lt(Spec.k_avail(Spec.stock_of(Spec.st(Code.exp2(x, due, mkS(u, clk, ksku, tot, av, rv, sd, rs), id, sku, qty, exp, cf, ret)))), av) == False{} : Bool}:
  match x due:
    case Spec.Held{} True{}:
      lt_add_false(av, qty)
    case Spec.Held{} False{}:
      lt_irrefl(av)
    case Spec.Confirmed{} _:
      lt_irrefl(av)
    case Spec.Expired{} _:
      lt_irrefl(av)

def lt_exp1(+l: Spec.Look, +u: Bool, +clk: Nat, +ksku: Nat, +tot: Nat, +av: Nat, +rv: Nat, +sd: Nat, +rs: +List<Spec.Res>, +id: Nat) -> {Nat.is_lt(Spec.k_avail(Spec.stock_of(Spec.st(Code.exp1(l, mkS(u, clk, ksku, tot, av, rv, sd, rs), id)))), av) == False{} : Bool}:
  match l:
    case Spec.NoRes{}:
      lt_irrefl(av)
    case Spec.Got{Spec.Res{i, sku, qty, x, exp, cf, ret}}:
      lt_exp2(x, Nat.is_le(exp, clk), u, clk, ksku, tot, av, rv, sd, rs, id, sku, qty, exp, cf, ret)


def p1b_ge(+u: Bool, +clk: Nat, +ksku: Nat, +tot: Nat, +av: Nat, +rv: Nat, +sd: Nat, +rs: +List<Spec.Res>, +id: Nat, +hl: {Nat.is_lt(Spec.k_avail(Spec.stock_of(Spec.st(Code.step(mkS(u, clk, ksku, tot, av, rv, sd, rs), Spec.Expire{id})))), av) == True{} : Bool}) -> {Spec.p1b(mkS(u, clk, ksku, tot, av, rv, sd, rs), Spec.Expire{id}, Code.step(mkS(u, clk, ksku, tot, av, rv, sd, rs), Spec.Expire{id})) == True{} : Bool}:
  match u:
    case False{}:
      contra({Spec.p1b(mkS(False{}, clk, ksku, tot, av, rv, sd, rs), Spec.Expire{id}, Code.step(mkS(False{}, clk, ksku, tot, av, rv, sd, rs), Spec.Expire{id})) == True{} : Bool}, Nat.is_lt(av, av), hl, lt_irrefl(av))
    case True{}:
      contra({Spec.p1b(mkS(True{}, clk, ksku, tot, av, rv, sd, rs), Spec.Expire{id}, Code.step(mkS(True{}, clk, ksku, tot, av, rv, sd, rs), Spec.Expire{id})) == True{} : Bool}, Nat.is_lt(Spec.k_avail(Spec.stock_of(Spec.st(Code.exp1(Spec.find_res(rs, id), mkS(True{}, clk, ksku, tot, av, rv, sd, rs), id)))), av), hl, lt_exp1(Spec.find_res(rs, id), u, clk, ksku, tot, av, rv, sd, rs, id))


def Laws.p1b_take_step(s, e, h, hl):
  match s e:
    case Spec.State{u, clk, Spec.Stock{ksku, tot, av, rv, sd}, rs} Spec.Reserve{id, sku, qty, ttl}:
      p1b_gr(u, clk, ksku, tot, av, rv, sd, rs, id, sku, qty, ttl, hl)
    case Spec.State{u, clk, Spec.Stock{ksku, tot, av, rv, sd}, rs} Spec.Confirm{id}:
      p1b_gc(u, clk, ksku, tot, av, rv, sd, rs, id, hl)
    case Spec.State{u, clk, Spec.Stock{ksku, tot, av, rv, sd}, rs} Spec.Expire{id}:
      p1b_ge(u, clk, ksku, tot, av, rv, sd, rs, id, hl)
    case Spec.State{u, clk, Spec.Stock{ksku, tot, av, rv, sd}, rs} Spec.Tick{}:
      contra({Spec.p1b(mkS(u, clk, ksku, tot, av, rv, sd, rs), Spec.Tick{}, Code.step(mkS(u, clk, ksku, tot, av, rv, sd, rs), Spec.Tick{})) == True{} : Bool}, Nat.is_lt(av, av), hl, lt_irrefl(av))
    case Spec.State{u, clk, Spec.Stock{ksku, tot, av, rv, sd}, rs} Spec.Crash{}:
      contra({Spec.p1b(mkS(u, clk, ksku, tot, av, rv, sd, rs), Spec.Crash{}, Code.step(mkS(u, clk, ksku, tot, av, rv, sd, rs), Spec.Crash{})) == True{} : Bool}, Nat.is_lt(av, av), hl, lt_irrefl(av))
    case Spec.State{u, clk, Spec.Stock{ksku, tot, av, rv, sd}, rs} Spec.Restart{}:
      contra({Spec.p1b(mkS(u, clk, ksku, tot, av, rv, sd, rs), Spec.Restart{}, Code.step(mkS(u, clk, ksku, tot, av, rv, sd, rs), Spec.Restart{})) == True{} : Bool}, Nat.is_lt(av, av), hl, lt_irrefl(av))

# ================================================================ find lemmas
def trL(-a: Spec.Look, -b: Spec.Look, -c: Spec.Look, ab: {a == b : Spec.Look}, bc: {b == c : Spec.Look}) -> {a == c : Spec.Look}:
  Equal.trans(Spec.Look, a, b, c, ab, bc)

def symL(-a: Spec.Look, -b: Spec.Look, e: {a == b : Spec.Look}) -> {b == a : Spec.Look}:
  Equal.sym(Spec.Look, a, b, e)

def fpk_f(+g: Bool, +h: Spec.Res, +rest: Spec.Look, +hg: {g == False{} : Bool}) -> {Spec.find_pick(h, g, rest) == rest : Spec.Look}:
  match g:
    case False{}:
      {==}
    case True{}:
      tf_absurd({Spec.Got{h} == rest : Spec.Look}, hg)

def fpk_t(+g: Bool, +h: Spec.Res, +rest: Spec.Look, +hg: {g == True{} : Bool}) -> {Spec.find_pick(h, g, rest) == Spec.Got{h} : Spec.Look}:
  match g:
    case False{}:
      ft_absurd({rest == Spec.Got{h} : Spec.Look}, hg)
    case True{}:
      {==}

def eqf_via(+a: Nat, +b: Nat, +j: Nat, +e: {a == b : Nat}, +h: {Nat.is_eq(b, j) == False{} : Bool}) -> {Nat.is_eq(a, j) == False{} : Bool}:
  %symN(a, b, e) : {Nat.is_eq(_, j) == False{} : Bool}
  h

def bcase(+d: Bool, -Q: Type, th: {d == True{} : Bool} -> Q, fh: {d == False{} : Bool} -> Q) -> Q:
  match d:
    case False{}:
      fh({==})
    case True{}:
      th({==})

def fpn_pick(+g: Bool, +h: Spec.Res, +x: Spec.Res, +t: +List<Spec.Res>, +rest: +List<Spec.Res>, +id: Nat, +j: Nat, +hx: {Spec.r_id(x) == id : Nat}, +hg: {Nat.is_eq(Spec.r_id(h), id) == g : Bool}, +hne: {Nat.is_eq(j, id) == False{} : Bool}, +ih: {Spec.find_res(rest, j) == Spec.find_res(t, j) : Spec.Look}) -> {Spec.find_res(Spec.put_pick(g, h, x, t, rest), j) == Spec.find_res(h <> t, j) : Spec.Look}:
  match g:
    case True{}:
      trL(Spec.find_pick(x, Nat.is_eq(Spec.r_id(x), j), Spec.find_res(t, j)), Spec.find_res(t, j), Spec.find_pick(h, Nat.is_eq(Spec.r_id(h), j), Spec.find_res(t, j)), fpk_f(Nat.is_eq(Spec.r_id(x), j), x, Spec.find_res(t, j), eqf_via(Spec.r_id(x), id, j, hx, eq_f_sym(j, id, hne))), symL(Spec.find_pick(h, Nat.is_eq(Spec.r_id(h), j), Spec.find_res(t, j)), Spec.find_res(t, j), fpk_f(Nat.is_eq(Spec.r_id(h), j), h, Spec.find_res(t, j), eqf_via(Spec.r_id(h), id, j, eq_prop(Spec.r_id(h), id, hg), eq_f_sym(j, id, hne)))))
    case False{}:
      %ih : {Spec.find_pick(h, Nat.is_eq(Spec.r_id(h), j), Spec.find_res(rest, j)) == Spec.find_pick(h, Nat.is_eq(Spec.r_id(h), j), _) : Spec.Look}
      {==}

def find_put_ne(+rs: +List<Spec.Res>, +id: Nat, +x: Spec.Res, +j: Nat, +hx: {Spec.r_id(x) == id : Nat}, +hne: {Nat.is_eq(j, id) == False{} : Bool}) -> {Spec.find_res(Spec.put_res(rs, id, x), j) == Spec.find_res(rs, j) : Spec.Look}:
  match rs:
    case Nil{}:
      {==}
    case +h <> +t:
      fpn_pick(Nat.is_eq(Spec.r_id(h), id), h, x, t, Spec.put_res(t, id, x), id, j, hx, {==}, hne, find_put_ne(t, id, x, j, hx, hne))

def fpe_pick(+g: Bool, +h: Spec.Res, +x: Spec.Res, +t: +List<Spec.Res>, +rest: +List<Spec.Res>, +r: Spec.Res, +id: Nat, +hx: {Spec.r_id(x) == id : Nat}, +hg: {Nat.is_eq(Spec.r_id(h), id) == g : Bool}, +hf: {Spec.find_pick(h, g, Spec.find_res(t, id)) == Spec.Got{r} : Spec.Look}, ih: {Spec.find_res(t, id) == Spec.Got{r} : Spec.Look} -> {Spec.find_res(rest, id) == Spec.Got{x} : Spec.Look}) -> {Spec.find_res(Spec.put_pick(g, h, x, t, rest), id) == Spec.Got{x} : Spec.Look}:
  match g:
    case True{}:
      fpk_t(Nat.is_eq(Spec.r_id(x), id), x, Spec.find_res(t, id), eq_back(Spec.r_id(x), id, hx))
    case False{}:
      trL(Spec.find_pick(h, Nat.is_eq(Spec.r_id(h), id), Spec.find_res(rest, id)), Spec.find_res(rest, id), Spec.Got{x}, fpk_f(Nat.is_eq(Spec.r_id(h), id), h, Spec.find_res(rest, id), hg), ih(hf))

def find_put_eq(+rs: +List<Spec.Res>, +id: Nat, +x: Spec.Res, +r: Spec.Res, +hx: {Spec.r_id(x) == id : Nat}, +hf: {Spec.find_res(rs, id) == Spec.Got{r} : Spec.Look}) -> {Spec.find_res(Spec.put_res(rs, id, x), id) == Spec.Got{x} : Spec.Look}:
  match rs:
    case Nil{}:
      nr_absurd({Spec.NoRes{} == Spec.Got{x} : Spec.Look}, r, hf)
    case +h <> +t:
      fpe_pick(Nat.is_eq(Spec.r_id(h), id), h, x, t, Spec.put_res(t, id, x), r, id, hx, {==}, hf, hf2 => find_put_eq(t, id, x, r, hx, hf2))

def fs_pick(+g: Bool, +h: Spec.Res, +t: +List<Spec.Res>, +x: Spec.Res, +id: Nat, +r: Spec.Res, +hf: {Spec.find_pick(h, g, Spec.find_res(t, id)) == Spec.Got{r} : Spec.Look}, ih: {Spec.find_res(t, id) == Spec.Got{r} : Spec.Look} -> {Spec.find_res(snoc(t, x), id) == Spec.Got{r} : Spec.Look}) -> {Spec.find_pick(h, g, Spec.find_res(snoc(t, x), id)) == Spec.Got{r} : Spec.Look}:
  match g:
    case True{}:
      hf
    case False{}:
      ih(hf)

def find_snoc(+rs: +List<Spec.Res>, +x: Spec.Res, +id: Nat, +r: Spec.Res, +hf: {Spec.find_res(rs, id) == Spec.Got{r} : Spec.Look}) -> {Spec.find_res(snoc(rs, x), id) == Spec.Got{r} : Spec.Look}:
  match rs:
    case Nil{}:
      nr_absurd({Spec.find_res(snoc(Nil{}, x), id) == Spec.Got{r} : Spec.Look}, r, hf)
    case +h <> +t:
      fs_pick(Nat.is_eq(Spec.r_id(h), id), h, t, x, id, r, hf, hf2 => find_snoc(t, x, id, r, hf2))

def fsn_pick(+g: Bool, +h: Spec.Res, +t: +List<Spec.Res>, +x: Spec.Res, +hf: {Spec.find_pick(h, g, Spec.find_res(t, Spec.r_id(x))) == Spec.NoRes{} : Spec.Look}, ih: {Spec.find_res(t, Spec.r_id(x)) == Spec.NoRes{} : Spec.Look} -> {Spec.find_res(snoc(t, x), Spec.r_id(x)) == Spec.Got{x} : Spec.Look}) -> {Spec.find_pick(h, g, Spec.find_res(snoc(t, x), Spec.r_id(x))) == Spec.Got{x} : Spec.Look}:
  match g:
    case True{}:
      gt_absurd({Spec.Got{h} == Spec.Got{x} : Spec.Look}, h, hf)
    case False{}:
      ih(hf)

def find_snoc_new(+rs: +List<Spec.Res>, +x: Spec.Res, +hd: {Spec.find_res(rs, Spec.r_id(x)) == Spec.NoRes{} : Spec.Look}) -> {Spec.find_res(snoc(rs, x), Spec.r_id(x)) == Spec.Got{x} : Spec.Look}:
  match rs:
    case Nil{}:
      fpk_t(Nat.is_eq(Spec.r_id(x), Spec.r_id(x)), x, Spec.NoRes{}, eq_refl(Spec.r_id(x)))
    case +h <> +t:
      fsn_pick(Nat.is_eq(Spec.r_id(h), Spec.r_id(x)), h, t, x, hd, hf2 => find_snoc_new(t, x, hf2))

def sis_false(+L: +List<Spec.Res>, +j: Nat, +r: Spec.Res, +stt: Spec.Status, +hf: {Spec.find_res(L, j) == Spec.Got{r} : Spec.Look}, +hn: {Spec.st_eq(Spec.r_status(r), stt) == False{} : Bool}) -> {Spec.status_is(L, j, stt) == False{} : Bool}:
  %symL(Spec.find_res(L, j), Spec.Got{r}, hf) : {Spec.look_is(_, stt) == False{} : Bool}
  hn

def lis_false(+rs: +List<Spec.Res>, +j: Nat, +id: Nat, +r: Spec.Res, +stt: Spec.Status, +hj: {j == id : Nat}, +hf: {Spec.find_res(rs, id) == Spec.Got{r} : Spec.Look}, +hr: {Spec.st_eq(Spec.r_status(r), stt) == False{} : Bool}) -> {Spec.status_is(rs, j, stt) == False{} : Bool}:
  %symN(j, id, hj) : {Spec.status_is(rs, _, stt) == False{} : Bool}
  sis_false(rs, id, r, stt, hf, hr)

def si_pick(+g: Bool, +h: Spec.Res, +t: +List<Spec.Res>, +x: Spec.Res, +id: Nat, +stt: Spec.Status, +hy: {Spec.look_is(Spec.find_pick(h, g, Spec.find_res(t, id)), stt) == True{} : Bool}, ih: {Spec.status_is(t, id, stt) == True{} : Bool} -> {Spec.status_is(snoc(t, x), id, stt) == True{} : Bool}) -> {Spec.look_is(Spec.find_pick(h, g, Spec.find_res(snoc(t, x), id)), stt) == True{} : Bool}:
  match g:
    case True{}:
      hy
    case False{}:
      ih(hy)

def si_snoc(+rs: +List<Spec.Res>, +x: Spec.Res, +id: Nat, +stt: Spec.Status, +h: {Spec.status_is(rs, id, stt) == True{} : Bool}) -> {Spec.status_is(snoc(rs, x), id, stt) == True{} : Bool}:
  match rs:
    case Nil{}:
      ft_absurd({Spec.status_is(snoc(Nil{}, x), id, stt) == True{} : Bool}, h)
    case +h2 <> +t:
      si_pick(Nat.is_eq(Spec.r_id(h2), id), h2, t, x, id, stt, h, hh => si_snoc(t, x, id, stt, hh))

def si_put_f(+rs: +List<Spec.Res>, +id: Nat, +x: Spec.Res, +j: Nat, +stt: Spec.Status, +hx: {Spec.r_id(x) == id : Nat}, +hn: {Nat.is_eq(j, id) == False{} : Bool}, +h: {Spec.status_is(rs, j, stt) == True{} : Bool}) -> {Spec.status_is(Spec.put_res(rs, id, x), j, stt) == True{} : Bool}:
  %symL(Spec.find_res(Spec.put_res(rs, id, x), j), Spec.find_res(rs, j), find_put_ne(rs, id, x, j, hx, hn)) : {Spec.look_is(_, stt) == True{} : Bool}
  h

def si_put_t(+rs: +List<Spec.Res>, +id: Nat, +x: Spec.Res, +r: Spec.Res, +j: Nat, +stt: Spec.Status, +hf: {Spec.find_res(rs, id) == Spec.Got{r} : Spec.Look}, +hr: {Spec.st_eq(Spec.r_status(r), stt) == False{} : Bool}, +hj: {Nat.is_eq(j, id) == True{} : Bool}, +h: {Spec.status_is(rs, j, stt) == True{} : Bool}) -> {Spec.status_is(Spec.put_res(rs, id, x), j, stt) == True{} : Bool}:
  contra({Spec.status_is(Spec.put_res(rs, id, x), j, stt) == True{} : Bool}, Spec.status_is(rs, j, stt), h, lis_false(rs, j, id, r, stt, eq_prop(j, id, hj), hf, hr))

def si_put(+rs: +List<Spec.Res>, +id: Nat, +x: Spec.Res, +r: Spec.Res, +j: Nat, +stt: Spec.Status, +hx: {Spec.r_id(x) == id : Nat}, +hf: {Spec.find_res(rs, id) == Spec.Got{r} : Spec.Look}, +hr: {Spec.st_eq(Spec.r_status(r), stt) == False{} : Bool}, +h: {Spec.status_is(rs, j, stt) == True{} : Bool}) -> {Spec.status_is(Spec.put_res(rs, id, x), j, stt) == True{} : Bool}:
  bcase(Nat.is_eq(j, id), {Spec.status_is(Spec.put_res(rs, id, x), j, stt) == True{} : Bool}, hj => si_put_t(rs, id, x, r, j, stt, hf, hr, hj, h), hn => si_put_f(rs, id, x, j, stt, hx, hn, h))


def p4_rsv(+g1: Bool, +g2: Bool, +g3: Spec.Look, +g4: Bool, +u: Bool, +clk: Nat, +ksku: Nat, +tot: Nat, +av: Nat, +rv: Nat, +sd: Nat, +rs: +List<Spec.Res>, +id: Nat, +sku: Nat, +qty: Nat, +ttl: Nat, +j: Nat, +hx: {Spec.status_is(rs, j, Spec.Expired{}) == True{} : Bool}) -> {Spec.status_is(Spec.res_of(Spec.st(Code.rsv(g1, g2, g3, g4, mkS(u, clk, ksku, tot, av, rv, sd, rs), id, sku, qty, ttl))), j, Spec.Expired{}) == True{} : Bool}:
  match g1 g2 g3 g4:
    case False{} _ _ _:
      hx
    case True{} False{} _ _:
      hx
    case True{} True{} Spec.Got{_} _:
      hx
    case True{} True{} Spec.NoRes{} False{}:
      hx
    case True{} True{} Spec.NoRes{} True{}:
      si_snoc(rs, Spec.Res{id, sku, qty, Spec.Held{}, Nat.add(clk, ttl), 0n, 0n}, j, Spec.Expired{}, hx)

def p4_gr(+u: Bool, +clk: Nat, +ksku: Nat, +tot: Nat, +av: Nat, +rv: Nat, +sd: Nat, +rs: +List<Spec.Res>, +id: Nat, +sku: Nat, +qty: Nat, +ttl: Nat, +j: Nat, +hx: {Spec.status_is(rs, j, Spec.Expired{}) == True{} : Bool}) -> {Spec.status_is(Spec.res_of(Spec.st(Code.step(mkS(u, clk, ksku, tot, av, rv, sd, rs), Spec.Reserve{id, sku, qty, ttl}))), j, Spec.Expired{}) == True{} : Bool}:
  match u:
    case False{}:
      hx
    case True{}:
      p4_rsv(Bool.and(Nat.is_lt(0n, qty), Nat.is_lt(0n, ttl)), Nat.is_eq(sku, ksku), Spec.find_res(rs, id), Nat.is_le(qty, av), u, clk, ksku, tot, av, rv, sd, rs, id, sku, qty, ttl, j, hx)


def p4_conf2(+x: Spec.Status, +due: Bool, +u: Bool, +clk: Nat, +ksku: Nat, +tot: Nat, +av: Nat, +rv: Nat, +sd: Nat, +rs: +List<Spec.Res>, +id: Nat, +i: Nat, +sku: Nat, +qty: Nat, +exp: Nat, +cf: Nat, +ret: Nat, +j: Nat, +hx: {Spec.status_is(rs, j, Spec.Expired{}) == True{} : Bool}, +hf: {Spec.find_res(rs, id) == Spec.Got{Spec.Res{i, sku, qty, x, exp, cf, ret}} : Spec.Look}) -> {Spec.status_is(Spec.res_of(Spec.st(Code.conf2(x, due, mkS(u, clk, ksku, tot, av, rv, sd, rs), id, sku, qty, exp, ret))), j, Spec.Expired{}) == True{} : Bool}:
  match x due:
    case Spec.Held{} False{}:
      si_put(rs, id, Spec.Res{id, sku, qty, Spec.Confirmed{}, exp, clk, ret}, Spec.Res{i, sku, qty, Spec.Held{}, exp, cf, ret}, j, Spec.Expired{}, {==}, hf, {==}, hx)
    case Spec.Held{} True{}:
      hx
    case Spec.Confirmed{} _:
      hx
    case Spec.Expired{} _:
      hx

def p4_conf1(+l: Spec.Look, +u: Bool, +clk: Nat, +ksku: Nat, +tot: Nat, +av: Nat, +rv: Nat, +sd: Nat, +rs: +List<Spec.Res>, +id: Nat, +j: Nat, +hx: {Spec.status_is(rs, j, Spec.Expired{}) == True{} : Bool}, +el: {Spec.find_res(rs, id) == l : Spec.Look}) -> {Spec.status_is(Spec.res_of(Spec.st(Code.conf1(l, mkS(u, clk, ksku, tot, av, rv, sd, rs), id))), j, Spec.Expired{}) == True{} : Bool}:
  match l:
    case Spec.NoRes{}:
      hx
    case Spec.Got{Spec.Res{i, sku, qty, x, exp, cf, ret}}:
      p4_conf2(x, Nat.is_le(exp, clk), u, clk, ksku, tot, av, rv, sd, rs, id, i, sku, qty, exp, cf, ret, j, hx, el)

def p4_gc(+u: Bool, +clk: Nat, +ksku: Nat, +tot: Nat, +av: Nat, +rv: Nat, +sd: Nat, +rs: +List<Spec.Res>, +id: Nat, +j: Nat, +hx: {Spec.status_is(rs, j, Spec.Expired{}) == True{} : Bool}) -> {Spec.status_is(Spec.res_of(Spec.st(Code.step(mkS(u, clk, ksku, tot, av, rv, sd, rs), Spec.Confirm{id}))), j, Spec.Expired{}) == True{} : Bool}:
  match u:
    case False{}:
      hx
    case True{}:
      p4_conf1(Spec.find_res(rs, id), u, clk, ksku, tot, av, rv, sd, rs, id, j, hx, {==})


def p4_exp2(+x: Spec.Status, +due: Bool, +u: Bool, +clk: Nat, +ksku: Nat, +tot: Nat, +av: Nat, +rv: Nat, +sd: Nat, +rs: +List<Spec.Res>, +id: Nat, +i: Nat, +sku: Nat, +qty: Nat, +exp: Nat, +cf: Nat, +ret: Nat, +j: Nat, +hx: {Spec.status_is(rs, j, Spec.Expired{}) == True{} : Bool}, +hf: {Spec.find_res(rs, id) == Spec.Got{Spec.Res{i, sku, qty, x, exp, cf, ret}} : Spec.Look}) -> {Spec.status_is(Spec.res_of(Spec.st(Code.exp2(x, due, mkS(u, clk, ksku, tot, av, rv, sd, rs), id, sku, qty, exp, cf, ret))), j, Spec.Expired{}) == True{} : Bool}:
  match x due:
    case Spec.Held{} True{}:
      si_put(rs, id, Spec.Res{id, sku, qty, Spec.Expired{}, exp, cf, Nat.add(ret, 1n)}, Spec.Res{i, sku, qty, Spec.Held{}, exp, cf, ret}, j, Spec.Expired{}, {==}, hf, {==}, hx)
    case Spec.Held{} False{}:
      hx
    case Spec.Confirmed{} _:
      hx
    case Spec.Expired{} _:
      hx

def p4_exp1(+l: Spec.Look, +u: Bool, +clk: Nat, +ksku: Nat, +tot: Nat, +av: Nat, +rv: Nat, +sd: Nat, +rs: +List<Spec.Res>, +id: Nat, +j: Nat, +hx: {Spec.status_is(rs, j, Spec.Expired{}) == True{} : Bool}, +el: {Spec.find_res(rs, id) == l : Spec.Look}) -> {Spec.status_is(Spec.res_of(Spec.st(Code.exp1(l, mkS(u, clk, ksku, tot, av, rv, sd, rs), id))), j, Spec.Expired{}) == True{} : Bool}:
  match l:
    case Spec.NoRes{}:
      hx
    case Spec.Got{Spec.Res{i, sku, qty, x, exp, cf, ret}}:
      p4_exp2(x, Nat.is_le(exp, clk), u, clk, ksku, tot, av, rv, sd, rs, id, i, sku, qty, exp, cf, ret, j, hx, el)

def p4_ge(+u: Bool, +clk: Nat, +ksku: Nat, +tot: Nat, +av: Nat, +rv: Nat, +sd: Nat, +rs: +List<Spec.Res>, +id: Nat, +j: Nat, +hx: {Spec.status_is(rs, j, Spec.Expired{}) == True{} : Bool}) -> {Spec.status_is(Spec.res_of(Spec.st(Code.step(mkS(u, clk, ksku, tot, av, rv, sd, rs), Spec.Expire{id}))), j, Spec.Expired{}) == True{} : Bool}:
  match u:
    case False{}:
      hx
    case True{}:
      p4_exp1(Spec.find_res(rs, id), u, clk, ksku, tot, av, rv, sd, rs, id, j, hx, {==})


def Laws.p4_expired_stays_step(s, e, h, id, hx):
  match s e:
    case Spec.State{u, clk, Spec.Stock{ksku, tot, av, rv, sd}, rs} Spec.Reserve{eid, sku, qty, ttl}:
      p4_gr(u, clk, ksku, tot, av, rv, sd, rs, eid, sku, qty, ttl, id, hx)
    case Spec.State{u, clk, Spec.Stock{ksku, tot, av, rv, sd}, rs} Spec.Confirm{eid}:
      p4_gc(u, clk, ksku, tot, av, rv, sd, rs, eid, id, hx)
    case Spec.State{u, clk, Spec.Stock{ksku, tot, av, rv, sd}, rs} Spec.Expire{eid}:
      p4_ge(u, clk, ksku, tot, av, rv, sd, rs, eid, id, hx)
    case Spec.State{u, clk, Spec.Stock{ksku, tot, av, rv, sd}, rs} Spec.Tick{}:
      hx
    case Spec.State{u, clk, Spec.Stock{ksku, tot, av, rv, sd}, rs} Spec.Crash{}:
      hx
    case Spec.State{u, clk, Spec.Stock{ksku, tot, av, rv, sd}, rs} Spec.Restart{}:
      hx

# ================================================================ P4b
def p4b_rsv(+g1: Bool, +g2: Bool, +g3: Spec.Look, +g4: Bool, +u: Bool, +clk: Nat, +ksku: Nat, +tot: Nat, +av: Nat, +rv: Nat, +sd: Nat, +rs: +List<Spec.Res>, +id: Nat, +sku: Nat, +qty: Nat, +ttl: Nat, +j: Nat, +r: Spec.Res, +hf: {Spec.find_res(rs, j) == Spec.Got{r} : Spec.Look}, +hn: {Spec.st_eq(Spec.r_status(r), Spec.Confirmed{}) == False{} : Bool}, +hs: {Spec.status_is(Spec.res_of(Spec.st(Code.rsv(g1, g2, g3, g4, mkS(u, clk, ksku, tot, av, rv, sd, rs), id, sku, qty, ttl))), j, Spec.Confirmed{}) == True{} : Bool}) -> {(Spec.r_status(r), Nat.is_le(Spec.r_exp(r), clk)) == (Spec.Held{}, False{}) : Spec.Status & Bool}:
  match g1 g2 g3 g4:
    case False{} _ _ _:
      contra({(Spec.r_status(r), Nat.is_le(Spec.r_exp(r), clk)) == (Spec.Held{}, False{}) : Spec.Status & Bool}, Spec.status_is(rs, j, Spec.Confirmed{}), hs, sis_false(rs, j, r, Spec.Confirmed{}, hf, hn))
    case True{} False{} _ _:
      contra({(Spec.r_status(r), Nat.is_le(Spec.r_exp(r), clk)) == (Spec.Held{}, False{}) : Spec.Status & Bool}, Spec.status_is(rs, j, Spec.Confirmed{}), hs, sis_false(rs, j, r, Spec.Confirmed{}, hf, hn))
    case True{} True{} Spec.Got{_} _:
      contra({(Spec.r_status(r), Nat.is_le(Spec.r_exp(r), clk)) == (Spec.Held{}, False{}) : Spec.Status & Bool}, Spec.status_is(rs, j, Spec.Confirmed{}), hs, sis_false(rs, j, r, Spec.Confirmed{}, hf, hn))
    case True{} True{} Spec.NoRes{} False{}:
      contra({(Spec.r_status(r), Nat.is_le(Spec.r_exp(r), clk)) == (Spec.Held{}, False{}) : Spec.Status & Bool}, Spec.status_is(rs, j, Spec.Confirmed{}), hs, sis_false(rs, j, r, Spec.Confirmed{}, hf, hn))
    case True{} True{} Spec.NoRes{} True{}:
      contra({(Spec.r_status(r), Nat.is_le(Spec.r_exp(r), clk)) == (Spec.Held{}, False{}) : Spec.Status & Bool}, Spec.status_is(snoc(rs, Spec.Res{id, sku, qty, Spec.Held{}, Nat.add(clk, ttl), 0n, 0n}), j, Spec.Confirmed{}), hs, sis_false(snoc(rs, Spec.Res{id, sku, qty, Spec.Held{}, Nat.add(clk, ttl), 0n, 0n}), j, r, Spec.Confirmed{}, find_snoc(rs, Spec.Res{id, sku, qty, Spec.Held{}, Nat.add(clk, ttl), 0n, 0n}, j, r, hf), hn))

def p4b_gr(+u: Bool, +clk: Nat, +ksku: Nat, +tot: Nat, +av: Nat, +rv: Nat, +sd: Nat, +rs: +List<Spec.Res>, +id: Nat, +sku: Nat, +qty: Nat, +ttl: Nat, +j: Nat, +r: Spec.Res, +hf: {Spec.find_res(rs, j) == Spec.Got{r} : Spec.Look}, +hn: {Spec.st_eq(Spec.r_status(r), Spec.Confirmed{}) == False{} : Bool}, +hs: {Spec.status_is(Spec.res_of(Spec.st(Code.step(mkS(u, clk, ksku, tot, av, rv, sd, rs), Spec.Reserve{id, sku, qty, ttl}))), j, Spec.Confirmed{}) == True{} : Bool}) -> {(Spec.r_status(r), Nat.is_le(Spec.r_exp(r), clk)) == (Spec.Held{}, False{}) : Spec.Status & Bool}:
  match u:
    case False{}:
      contra({(Spec.r_status(r), Nat.is_le(Spec.r_exp(r), clk)) == (Spec.Held{}, False{}) : Spec.Status & Bool}, Spec.status_is(rs, j, Spec.Confirmed{}), hs, sis_false(rs, j, r, Spec.Confirmed{}, hf, hn))
    case True{}:
      p4b_rsv(Bool.and(Nat.is_lt(0n, qty), Nat.is_lt(0n, ttl)), Nat.is_eq(sku, ksku), Spec.find_res(rs, id), Nat.is_le(qty, av), u, clk, ksku, tot, av, rv, sd, rs, id, sku, qty, ttl, j, r, hf, hn, hs)

def p4b_put_ne(+rs: +List<Spec.Res>, +id: Nat, +x: Spec.Res, +j: Nat, +clk: Nat, +r: Spec.Res, +hx: {Spec.r_id(x) == id : Nat}, +hf: {Spec.find_res(rs, j) == Spec.Got{r} : Spec.Look}, +hn: {Spec.st_eq(Spec.r_status(r), Spec.Confirmed{}) == False{} : Bool}, +hs: {Spec.status_is(Spec.put_res(rs, id, x), j, Spec.Confirmed{}) == True{} : Bool}, +hne: {Nat.is_eq(j, id) == False{} : Bool}) -> {(Spec.r_status(r), Nat.is_le(Spec.r_exp(r), clk)) == (Spec.Held{}, False{}) : Spec.Status & Bool}:
  contra({(Spec.r_status(r), Nat.is_le(Spec.r_exp(r), clk)) == (Spec.Held{}, False{}) : Spec.Status & Bool}, Spec.status_is(Spec.put_res(rs, id, x), j, Spec.Confirmed{}), hs, sis_false(Spec.put_res(rs, id, x), j, r, Spec.Confirmed{}, trL(Spec.find_res(Spec.put_res(rs, id, x), j), Spec.find_res(rs, j), Spec.Got{r}, find_put_ne(rs, id, x, j, hx, hne), hf), hn))


def p4b_conf_t(+rs: +List<Spec.Res>, +id: Nat, +i: Nat, +sku: Nat, +qty: Nat, +exp: Nat, +cf: Nat, +ret: Nat, +j: Nat, +clk: Nat, +r: Spec.Res, +hj: {Nat.is_eq(j, id) == True{} : Bool}, +hf: {Spec.find_res(rs, j) == Spec.Got{r} : Spec.Look}, +el: {Spec.find_res(rs, id) == Spec.Got{Spec.Res{i, sku, qty, Spec.Held{}, exp, cf, ret}} : Spec.Look}, +ed: {Nat.is_le(exp, clk) == False{} : Bool}) -> {(Spec.r_status(r), Nat.is_le(Spec.r_exp(r), clk)) == (Spec.Held{}, False{}) : Spec.Status & Bool}:
  %got_inj(Spec.Res{i, sku, qty, Spec.Held{}, exp, cf, ret}, r, trL(Spec.Got{Spec.Res{i, sku, qty, Spec.Held{}, exp, cf, ret}}, Spec.find_res(rs, id), Spec.Got{r}, symL(Spec.find_res(rs, id), Spec.Got{Spec.Res{i, sku, qty, Spec.Held{}, exp, cf, ret}}, el), trL(Spec.find_res(rs, id), Spec.find_res(rs, j), Spec.Got{r}, Equal.cong(Nat, Spec.Look, y => Spec.find_res(rs, y), id, j, symN(j, id, eq_prop(j, id, hj))), hf))) : {(Spec.r_status(_), Nat.is_le(Spec.r_exp(_), clk)) == (Spec.Held{}, False{}) : Spec.Status & Bool}
  %ed : {(Spec.Held{}, Nat.is_le(exp, clk)) == (Spec.Held{}, _) : Spec.Status & Bool}
  {==}

def p4b_conf2(+x: Spec.Status, +due: Bool, +u: Bool, +clk: Nat, +ksku: Nat, +tot: Nat, +av: Nat, +rv: Nat, +sd: Nat, +rs: +List<Spec.Res>, +id: Nat, +i: Nat, +sku: Nat, +qty: Nat, +exp: Nat, +cf: Nat, +ret: Nat, +j: Nat, +r: Spec.Res, +hf: {Spec.find_res(rs, j) == Spec.Got{r} : Spec.Look}, +hn: {Spec.st_eq(Spec.r_status(r), Spec.Confirmed{}) == False{} : Bool}, +hs: {Spec.status_is(Spec.res_of(Spec.st(Code.conf2(x, due, mkS(u, clk, ksku, tot, av, rv, sd, rs), id, sku, qty, exp, ret))), j, Spec.Confirmed{}) == True{} : Bool}, +el: {Spec.find_res(rs, id) == Spec.Got{Spec.Res{i, sku, qty, x, exp, cf, ret}} : Spec.Look}, +ed: {Nat.is_le(exp, clk) == due : Bool}) -> {(Spec.r_status(r), Nat.is_le(Spec.r_exp(r), clk)) == (Spec.Held{}, False{}) : Spec.Status & Bool}:
  match x due:
    case Spec.Held{} False{}:
      bcase(Nat.is_eq(j, id), {(Spec.r_status(r), Nat.is_le(Spec.r_exp(r), clk)) == (Spec.Held{}, False{}) : Spec.Status & Bool}, hj => p4b_conf_t(rs, id, i, sku, qty, exp, cf, ret, j, clk, r, hj, hf, el, ed), hne => p4b_put_ne(rs, id, Spec.Res{id, sku, qty, Spec.Confirmed{}, exp, clk, ret}, j, clk, r, {==}, hf, hn, hs, hne))
    case Spec.Held{} True{}:
      contra({(Spec.r_status(r), Nat.is_le(Spec.r_exp(r), clk)) == (Spec.Held{}, False{}) : Spec.Status & Bool}, Spec.status_is(rs, j, Spec.Confirmed{}), hs, sis_false(rs, j, r, Spec.Confirmed{}, hf, hn))
    case Spec.Confirmed{} _:
      contra({(Spec.r_status(r), Nat.is_le(Spec.r_exp(r), clk)) == (Spec.Held{}, False{}) : Spec.Status & Bool}, Spec.status_is(rs, j, Spec.Confirmed{}), hs, sis_false(rs, j, r, Spec.Confirmed{}, hf, hn))
    case Spec.Expired{} _:
      contra({(Spec.r_status(r), Nat.is_le(Spec.r_exp(r), clk)) == (Spec.Held{}, False{}) : Spec.Status & Bool}, Spec.status_is(rs, j, Spec.Confirmed{}), hs, sis_false(rs, j, r, Spec.Confirmed{}, hf, hn))

def p4b_conf1(+l: Spec.Look, +u: Bool, +clk: Nat, +ksku: Nat, +tot: Nat, +av: Nat, +rv: Nat, +sd: Nat, +rs: +List<Spec.Res>, +id: Nat, +j: Nat, +r: Spec.Res, +hf: {Spec.find_res(rs, j) == Spec.Got{r} : Spec.Look}, +hn: {Spec.st_eq(Spec.r_status(r), Spec.Confirmed{}) == False{} : Bool}, +hs: {Spec.status_is(Spec.res_of(Spec.st(Code.conf1(l, mkS(u, clk, ksku, tot, av, rv, sd, rs), id))), j, Spec.Confirmed{}) == True{} : Bool}, +el: {Spec.find_res(rs, id) == l : Spec.Look}) -> {(Spec.r_status(r), Nat.is_le(Spec.r_exp(r), clk)) == (Spec.Held{}, False{}) : Spec.Status & Bool}:
  match l:
    case Spec.NoRes{}:
      contra({(Spec.r_status(r), Nat.is_le(Spec.r_exp(r), clk)) == (Spec.Held{}, False{}) : Spec.Status & Bool}, Spec.status_is(rs, j, Spec.Confirmed{}), hs, sis_false(rs, j, r, Spec.Confirmed{}, hf, hn))
    case Spec.Got{Spec.Res{i, sku, qty, x, exp, cf, ret}}:
      p4b_conf2(x, Nat.is_le(exp, clk), u, clk, ksku, tot, av, rv, sd, rs, id, i, sku, qty, exp, cf, ret, j, r, hf, hn, hs, el, {==})

def p4b_gc(+u: Bool, +clk: Nat, +ksku: Nat, +tot: Nat, +av: Nat, +rv: Nat, +sd: Nat, +rs: +List<Spec.Res>, +id: Nat, +j: Nat, +r: Spec.Res, +hf: {Spec.find_res(rs, j) == Spec.Got{r} : Spec.Look}, +hn: {Spec.st_eq(Spec.r_status(r), Spec.Confirmed{}) == False{} : Bool}, +hs: {Spec.status_is(Spec.res_of(Spec.st(Code.step(mkS(u, clk, ksku, tot, av, rv, sd, rs), Spec.Confirm{id}))), j, Spec.Confirmed{}) == True{} : Bool}) -> {(Spec.r_status(r), Nat.is_le(Spec.r_exp(r), clk)) == (Spec.Held{}, False{}) : Spec.Status & Bool}:
  match u:
    case False{}:
      contra({(Spec.r_status(r), Nat.is_le(Spec.r_exp(r), clk)) == (Spec.Held{}, False{}) : Spec.Status & Bool}, Spec.status_is(rs, j, Spec.Confirmed{}), hs, sis_false(rs, j, r, Spec.Confirmed{}, hf, hn))
    case True{}:
      p4b_conf1(Spec.find_res(rs, id), u, clk, ksku, tot, av, rv, sd, rs, id, j, r, hf, hn, hs, {==})


def p4b_exp_t(+rs: +List<Spec.Res>, +id: Nat, +i: Nat, +sku: Nat, +qty: Nat, +exp: Nat, +cf: Nat, +ret: Nat, +j: Nat, +clk: Nat, +r: Spec.Res, +hj: {Nat.is_eq(j, id) == True{} : Bool}, +hn: {Spec.st_eq(Spec.r_status(r), Spec.Confirmed{}) == False{} : Bool}, +hs: {Spec.status_is(Spec.put_res(rs, id, Spec.Res{id, sku, qty, Spec.Expired{}, exp, cf, Nat.add(ret, 1n)}), j, Spec.Confirmed{}) == True{} : Bool}, +el: {Spec.find_res(rs, id) == Spec.Got{Spec.Res{i, sku, qty, Spec.Held{}, exp, cf, ret}} : Spec.Look}) -> {(Spec.r_status(r), Nat.is_le(Spec.r_exp(r), clk)) == (Spec.Held{}, False{}) : Spec.Status & Bool}:
  contra({(Spec.r_status(r), Nat.is_le(Spec.r_exp(r), clk)) == (Spec.Held{}, False{}) : Spec.Status & Bool}, Spec.status_is(Spec.put_res(rs, id, Spec.Res{id, sku, qty, Spec.Expired{}, exp, cf, Nat.add(ret, 1n)}), j, Spec.Confirmed{}), hs, sis_false(Spec.put_res(rs, id, Spec.Res{id, sku, qty, Spec.Expired{}, exp, cf, Nat.add(ret, 1n)}), j, Spec.Res{id, sku, qty, Spec.Expired{}, exp, cf, Nat.add(ret, 1n)}, Spec.Confirmed{}, trL(Spec.find_res(Spec.put_res(rs, id, Spec.Res{id, sku, qty, Spec.Expired{}, exp, cf, Nat.add(ret, 1n)}), j), Spec.find_res(Spec.put_res(rs, id, Spec.Res{id, sku, qty, Spec.Expired{}, exp, cf, Nat.add(ret, 1n)}), id), Spec.Got{Spec.Res{id, sku, qty, Spec.Expired{}, exp, cf, Nat.add(ret, 1n)}}, symL(Spec.find_res(Spec.put_res(rs, id, Spec.Res{id, sku, qty, Spec.Expired{}, exp, cf, Nat.add(ret, 1n)}), id), Spec.find_res(Spec.put_res(rs, id, Spec.Res{id, sku, qty, Spec.Expired{}, exp, cf, Nat.add(ret, 1n)}), j), Equal.cong(Nat, Spec.Look, y => Spec.find_res(Spec.put_res(rs, id, Spec.Res{id, sku, qty, Spec.Expired{}, exp, cf, Nat.add(ret, 1n)}), y), id, j, symN(j, id, eq_prop(j, id, hj)))), find_put_eq(rs, id, Spec.Res{id, sku, qty, Spec.Expired{}, exp, cf, Nat.add(ret, 1n)}, Spec.Res{i, sku, qty, Spec.Held{}, exp, cf, ret}, {==}, el)), {==}))

def p4b_exp2(+x: Spec.Status, +due: Bool, +u: Bool, +clk: Nat, +ksku: Nat, +tot: Nat, +av: Nat, +rv: Nat, +sd: Nat, +rs: +List<Spec.Res>, +id: Nat, +i: Nat, +sku: Nat, +qty: Nat, +exp: Nat, +cf: Nat, +ret: Nat, +j: Nat, +r: Spec.Res, +hf: {Spec.find_res(rs, j) == Spec.Got{r} : Spec.Look}, +hn: {Spec.st_eq(Spec.r_status(r), Spec.Confirmed{}) == False{} : Bool}, +hs: {Spec.status_is(Spec.res_of(Spec.st(Code.exp2(x, due, mkS(u, clk, ksku, tot, av, rv, sd, rs), id, sku, qty, exp, cf, ret))), j, Spec.Confirmed{}) == True{} : Bool}, +el: {Spec.find_res(rs, id) == Spec.Got{Spec.Res{i, sku, qty, x, exp, cf, ret}} : Spec.Look}, +ed: {Nat.is_le(exp, clk) == due : Bool}) -> {(Spec.r_status(r), Nat.is_le(Spec.r_exp(r), clk)) == (Spec.Held{}, False{}) : Spec.Status & Bool}:
  match x due:
    case Spec.Held{} True{}:
      bcase(Nat.is_eq(j, id), {(Spec.r_status(r), Nat.is_le(Spec.r_exp(r), clk)) == (Spec.Held{}, False{}) : Spec.Status & Bool}, hj => p4b_exp_t(rs, id, i, sku, qty, exp, cf, ret, j, clk, r, hj, hn, hs, el), hne => p4b_put_ne(rs, id, Spec.Res{id, sku, qty, Spec.Expired{}, exp, cf, Nat.add(ret, 1n)}, j, clk, r, {==}, hf, hn, hs, hne))
    case Spec.Held{} False{}:
      contra({(Spec.r_status(r), Nat.is_le(Spec.r_exp(r), clk)) == (Spec.Held{}, False{}) : Spec.Status & Bool}, Spec.status_is(rs, j, Spec.Confirmed{}), hs, sis_false(rs, j, r, Spec.Confirmed{}, hf, hn))
    case Spec.Confirmed{} _:
      contra({(Spec.r_status(r), Nat.is_le(Spec.r_exp(r), clk)) == (Spec.Held{}, False{}) : Spec.Status & Bool}, Spec.status_is(rs, j, Spec.Confirmed{}), hs, sis_false(rs, j, r, Spec.Confirmed{}, hf, hn))
    case Spec.Expired{} _:
      contra({(Spec.r_status(r), Nat.is_le(Spec.r_exp(r), clk)) == (Spec.Held{}, False{}) : Spec.Status & Bool}, Spec.status_is(rs, j, Spec.Confirmed{}), hs, sis_false(rs, j, r, Spec.Confirmed{}, hf, hn))

def p4b_exp1(+l: Spec.Look, +u: Bool, +clk: Nat, +ksku: Nat, +tot: Nat, +av: Nat, +rv: Nat, +sd: Nat, +rs: +List<Spec.Res>, +id: Nat, +j: Nat, +r: Spec.Res, +hf: {Spec.find_res(rs, j) == Spec.Got{r} : Spec.Look}, +hn: {Spec.st_eq(Spec.r_status(r), Spec.Confirmed{}) == False{} : Bool}, +hs: {Spec.status_is(Spec.res_of(Spec.st(Code.exp1(l, mkS(u, clk, ksku, tot, av, rv, sd, rs), id))), j, Spec.Confirmed{}) == True{} : Bool}, +el: {Spec.find_res(rs, id) == l : Spec.Look}) -> {(Spec.r_status(r), Nat.is_le(Spec.r_exp(r), clk)) == (Spec.Held{}, False{}) : Spec.Status & Bool}:
  match l:
    case Spec.NoRes{}:
      contra({(Spec.r_status(r), Nat.is_le(Spec.r_exp(r), clk)) == (Spec.Held{}, False{}) : Spec.Status & Bool}, Spec.status_is(rs, j, Spec.Confirmed{}), hs, sis_false(rs, j, r, Spec.Confirmed{}, hf, hn))
    case Spec.Got{Spec.Res{i, sku, qty, x, exp, cf, ret}}:
      p4b_exp2(x, Nat.is_le(exp, clk), u, clk, ksku, tot, av, rv, sd, rs, id, i, sku, qty, exp, cf, ret, j, r, hf, hn, hs, el, {==})

def p4b_ge(+u: Bool, +clk: Nat, +ksku: Nat, +tot: Nat, +av: Nat, +rv: Nat, +sd: Nat, +rs: +List<Spec.Res>, +id: Nat, +j: Nat, +r: Spec.Res, +hf: {Spec.find_res(rs, j) == Spec.Got{r} : Spec.Look}, +hn: {Spec.st_eq(Spec.r_status(r), Spec.Confirmed{}) == False{} : Bool}, +hs: {Spec.status_is(Spec.res_of(Spec.st(Code.step(mkS(u, clk, ksku, tot, av, rv, sd, rs), Spec.Expire{id}))), j, Spec.Confirmed{}) == True{} : Bool}) -> {(Spec.r_status(r), Nat.is_le(Spec.r_exp(r), clk)) == (Spec.Held{}, False{}) : Spec.Status & Bool}:
  match u:
    case False{}:
      contra({(Spec.r_status(r), Nat.is_le(Spec.r_exp(r), clk)) == (Spec.Held{}, False{}) : Spec.Status & Bool}, Spec.status_is(rs, j, Spec.Confirmed{}), hs, sis_false(rs, j, r, Spec.Confirmed{}, hf, hn))
    case True{}:
      p4b_exp1(Spec.find_res(rs, id), u, clk, ksku, tot, av, rv, sd, rs, id, j, r, hf, hn, hs, {==})


def Laws.p4b_confirm_guard_step(s, e, h, id, r, hf, hn, hs):
  match s e:
    case Spec.State{u, clk, Spec.Stock{ksku, tot, av, rv, sd}, rs} Spec.Reserve{eid, sku, qty, ttl}:
      p4b_gr(u, clk, ksku, tot, av, rv, sd, rs, eid, sku, qty, ttl, id, r, hf, hn, hs)
    case Spec.State{u, clk, Spec.Stock{ksku, tot, av, rv, sd}, rs} Spec.Confirm{eid}:
      p4b_gc(u, clk, ksku, tot, av, rv, sd, rs, eid, id, r, hf, hn, hs)
    case Spec.State{u, clk, Spec.Stock{ksku, tot, av, rv, sd}, rs} Spec.Expire{eid}:
      p4b_ge(u, clk, ksku, tot, av, rv, sd, rs, eid, id, r, hf, hn, hs)
    case Spec.State{u, clk, Spec.Stock{ksku, tot, av, rv, sd}, rs} Spec.Tick{}:
      contra({(Spec.r_status(r), Nat.is_le(Spec.r_exp(r), clk)) == (Spec.Held{}, False{}) : Spec.Status & Bool}, Spec.status_is(rs, id, Spec.Confirmed{}), hs, sis_false(rs, id, r, Spec.Confirmed{}, hf, hn))
    case Spec.State{u, clk, Spec.Stock{ksku, tot, av, rv, sd}, rs} Spec.Crash{}:
      contra({(Spec.r_status(r), Nat.is_le(Spec.r_exp(r), clk)) == (Spec.Held{}, False{}) : Spec.Status & Bool}, Spec.status_is(rs, id, Spec.Confirmed{}), hs, sis_false(rs, id, r, Spec.Confirmed{}, hf, hn))
    case Spec.State{u, clk, Spec.Stock{ksku, tot, av, rv, sd}, rs} Spec.Restart{}:
      contra({(Spec.r_status(r), Nat.is_le(Spec.r_exp(r), clk)) == (Spec.Held{}, False{}) : Spec.Status & Bool}, Spec.status_is(rs, id, Spec.Confirmed{}), hs, sis_false(rs, id, r, Spec.Confirmed{}, hf, hn))

# ================================================================ S10 stable
def so_refl(+x: Spec.Status) -> {Spec.stat_ok(x, x) == True{} : Bool}:
  match x:
    case Spec.Held{}:
      {==}
    case Spec.Confirmed{}:
      {==}
    case Spec.Expired{}:
      {==}

def rec_refl(+r: Spec.Res) -> {Spec.rec_stable(r, r) == True{} : Bool}:
  match r:
    case Spec.Res{+i, +sku, +qty, +x, +exp, +cf, +ret}:
      and_i(Bool.and(Nat.is_eq(i, i), Nat.is_eq(sku, sku)), Bool.and(Bool.and(Nat.is_eq(qty, qty), Nat.is_eq(exp, exp)), Spec.stat_ok(x, x)), and_i(Nat.is_eq(i, i), Nat.is_eq(sku, sku), eq_refl(i), eq_refl(sku)), and_i(Bool.and(Nat.is_eq(qty, qty), Nat.is_eq(exp, exp)), Spec.stat_ok(x, x), and_i(Nat.is_eq(qty, qty), Nat.is_eq(exp, exp), eq_refl(qty), eq_refl(exp)), so_refl(x)))

def rs_refl(+rs: +List<Spec.Res>) -> {Spec.recs_stable(rs, rs) == True{} : Bool}:
  match rs:
    case Nil{}:
      {==}
    case +h <> +t:
      and_i(Spec.rec_stable(h, h), Spec.recs_stable(t, t), rec_refl(h), rs_refl(t))

def rs_snoc(+rs: +List<Spec.Res>, +x: Spec.Res) -> {Spec.recs_stable(rs, snoc(rs, x)) == True{} : Bool}:
  match rs:
    case Nil{}:
      {==}
    case +h <> +t:
      and_i(Spec.rec_stable(h, h), Spec.recs_stable(t, snoc(t, x)), rec_refl(h), rs_snoc(t, x))

def rp_pick(+g: Bool, +h: Spec.Res, +x: Spec.Res, +t: +List<Spec.Res>, +rest: +List<Spec.Res>, +r: Spec.Res, +id: Nat, +hf: {Spec.find_pick(h, g, Spec.find_res(t, id)) == Spec.Got{r} : Spec.Look}, +hrx: {Spec.rec_stable(r, x) == True{} : Bool}, ih: {Spec.find_res(t, id) == Spec.Got{r} : Spec.Look} -> {Spec.recs_stable(t, rest) == True{} : Bool}) -> {Spec.recs_stable(h <> t, Spec.put_pick(g, h, x, t, rest)) == True{} : Bool}:
  match g:
    case True{}:
      %Equal.sym(Spec.Res, h, r, got_inj(h, r, hf)) : {Bool.and(Spec.rec_stable(_, x), Spec.recs_stable(t, t)) == True{} : Bool}
      and_i(Spec.rec_stable(r, x), Spec.recs_stable(t, t), hrx, rs_refl(t))
    case False{}:
      and_i(Spec.rec_stable(h, h), Spec.recs_stable(t, rest), rec_refl(h), ih(hf))

def rs_put(+rs: +List<Spec.Res>, +id: Nat, +x: Spec.Res, +r: Spec.Res, +hf: {Spec.find_res(rs, id) == Spec.Got{r} : Spec.Look}, +hrx: {Spec.rec_stable(r, x) == True{} : Bool}) -> {Spec.recs_stable(rs, Spec.put_res(rs, id, x)) == True{} : Bool}:
  match rs:
    case Nil{}:
      nr_absurd({Spec.recs_stable(Nil{}, Nil{}) == True{} : Bool}, r, hf)
    case +h <> +t:
      rp_pick(Nat.is_eq(Spec.r_id(h), id), h, x, t, Spec.put_res(t, id, x), r, id, hf, hrx, hf2 => rs_put(t, id, x, r, hf2, hrx))

def fi_pick(+g: Bool, +h: Spec.Res, +t: +List<Spec.Res>, +id: Nat, +r: Spec.Res, +hg: {Nat.is_eq(Spec.r_id(h), id) == g : Bool}, +hf: {Spec.find_pick(h, g, Spec.find_res(t, id)) == Spec.Got{r} : Spec.Look}, ih: {Spec.find_res(t, id) == Spec.Got{r} : Spec.Look} -> {Nat.is_eq(Spec.r_id(r), id) == True{} : Bool}) -> {Nat.is_eq(Spec.r_id(r), id) == True{} : Bool}:
  match g:
    case True{}:
      %got_inj(h, r, hf) : {Nat.is_eq(Spec.r_id(_), id) == True{} : Bool}
      hg
    case False{}:
      ih(hf)

def find_id(+rs: +List<Spec.Res>, +id: Nat, +r: Spec.Res, +hf: {Spec.find_res(rs, id) == Spec.Got{r} : Spec.Look}) -> {Nat.is_eq(Spec.r_id(r), id) == True{} : Bool}:
  match rs:
    case Nil{}:
      nr_absurd({Nat.is_eq(Spec.r_id(r), id) == True{} : Bool}, r, hf)
    case +h <> +t:
      fi_pick(Nat.is_eq(Spec.r_id(h), id), h, t, id, r, {==}, hf, hf2 => find_id(t, id, r, hf2))

def stable_same(+u: Bool, +clk: Nat, +ksku: Nat, +tot: Nat, +av: Nat, +rv: Nat, +sd: Nat, +rs: +List<Spec.Res>) -> {Spec.stable(mkS(u, clk, ksku, tot, av, rv, sd, rs), mkS(u, clk, ksku, tot, av, rv, sd, rs)) == True{} : Bool}:
  and_i(Nat.is_eq(tot, tot), Spec.recs_stable(rs, rs), eq_refl(tot), rs_refl(rs))

def rstab(+x: Spec.Res, +r: Spec.Res, +hid: {Nat.is_eq(Spec.r_id(r), Spec.r_id(x)) == True{} : Bool}, +hs: {Spec.stat_ok(Spec.r_status(r), Spec.r_status(x)) == True{} : Bool}, +hsku: {Nat.is_eq(Spec.r_sku(r), Spec.r_sku(x)) == True{} : Bool}, +hq: {Nat.is_eq(Spec.r_qty(r), Spec.r_qty(x)) == True{} : Bool}, +he: {Nat.is_eq(Spec.r_exp(r), Spec.r_exp(x)) == True{} : Bool}) -> {Spec.rec_stable(r, x) == True{} : Bool}:
  match x r:
    case Spec.Res{+i2, +s2, +q2, +x2, +e2, +c2, +r2} Spec.Res{+i1, +s1, +q1, +x1, +e1, +c1, +r1}:
      and_i(Bool.and(Nat.is_eq(i1, i2), Nat.is_eq(s1, s2)), Bool.and(Bool.and(Nat.is_eq(q1, q2), Nat.is_eq(e1, e2)), Spec.stat_ok(x1, x2)), and_i(Nat.is_eq(i1, i2), Nat.is_eq(s1, s2), hid, hsku), and_i(Bool.and(Nat.is_eq(q1, q2), Nat.is_eq(e1, e2)), Spec.stat_ok(x1, x2), and_i(Nat.is_eq(q1, q2), Nat.is_eq(e1, e2), hq, he), hs))


def stable_rsv(+g1: Bool, +g2: Bool, +g3: Spec.Look, +g4: Bool, +u: Bool, +clk: Nat, +ksku: Nat, +tot: Nat, +av: Nat, +rv: Nat, +sd: Nat, +rs: +List<Spec.Res>, +id: Nat, +sku: Nat, +qty: Nat, +ttl: Nat) -> {Spec.stable(mkS(u, clk, ksku, tot, av, rv, sd, rs), Spec.st(Code.rsv(g1, g2, g3, g4, mkS(u, clk, ksku, tot, av, rv, sd, rs), id, sku, qty, ttl))) == True{} : Bool}:
  match g1 g2 g3 g4:
    case False{} _ _ _:
      stable_same(u, clk, ksku, tot, av, rv, sd, rs)
    case True{} False{} _ _:
      stable_same(u, clk, ksku, tot, av, rv, sd, rs)
    case True{} True{} Spec.Got{_} _:
      stable_same(u, clk, ksku, tot, av, rv, sd, rs)
    case True{} True{} Spec.NoRes{} False{}:
      stable_same(u, clk, ksku, tot, av, rv, sd, rs)
    case True{} True{} Spec.NoRes{} True{}:
      and_i(Nat.is_eq(tot, tot), Spec.recs_stable(rs, snoc(rs, Spec.Res{id, sku, qty, Spec.Held{}, Nat.add(clk, ttl), 0n, 0n})), eq_refl(tot), rs_snoc(rs, Spec.Res{id, sku, qty, Spec.Held{}, Nat.add(clk, ttl), 0n, 0n}))

def stable_gr(+u: Bool, +clk: Nat, +ksku: Nat, +tot: Nat, +av: Nat, +rv: Nat, +sd: Nat, +rs: +List<Spec.Res>, +id: Nat, +sku: Nat, +qty: Nat, +ttl: Nat) -> {Spec.stable(mkS(u, clk, ksku, tot, av, rv, sd, rs), Spec.st(Code.step(mkS(u, clk, ksku, tot, av, rv, sd, rs), Spec.Reserve{id, sku, qty, ttl}))) == True{} : Bool}:
  match u:
    case False{}:
      stable_same(u, clk, ksku, tot, av, rv, sd, rs)
    case True{}:
      stable_rsv(Bool.and(Nat.is_lt(0n, qty), Nat.is_lt(0n, ttl)), Nat.is_eq(sku, ksku), Spec.find_res(rs, id), Nat.is_le(qty, av), u, clk, ksku, tot, av, rv, sd, rs, id, sku, qty, ttl)


def stable_conf2(+x: Spec.Status, +due: Bool, +u: Bool, +clk: Nat, +ksku: Nat, +tot: Nat, +av: Nat, +rv: Nat, +sd: Nat, +rs: +List<Spec.Res>, +id: Nat, +i: Nat, +sku: Nat, +qty: Nat, +exp: Nat, +cf: Nat, +ret: Nat, +hf: {Spec.find_res(rs, id) == Spec.Got{Spec.Res{i, sku, qty, x, exp, cf, ret}} : Spec.Look}) -> {Spec.stable(mkS(u, clk, ksku, tot, av, rv, sd, rs), Spec.st(Code.conf2(x, due, mkS(u, clk, ksku, tot, av, rv, sd, rs), id, sku, qty, exp, ret))) == True{} : Bool}:
  match x due:
    case Spec.Held{} False{}:
      and_i(Nat.is_eq(tot, tot), Spec.recs_stable(rs, Spec.put_res(rs, id, Spec.Res{id, sku, qty, Spec.Confirmed{}, exp, clk, ret})), eq_refl(tot), rs_put(rs, id, Spec.Res{id, sku, qty, Spec.Confirmed{}, exp, clk, ret}, Spec.Res{i, sku, qty, Spec.Held{}, exp, cf, ret}, hf, rstab(Spec.Res{id, sku, qty, Spec.Confirmed{}, exp, clk, ret}, Spec.Res{i, sku, qty, Spec.Held{}, exp, cf, ret}, find_id(rs, id, Spec.Res{i, sku, qty, Spec.Held{}, exp, cf, ret}, hf), {==}, eq_refl(sku), eq_refl(qty), eq_refl(exp))))
    case Spec.Held{} True{}:
      stable_same(u, clk, ksku, tot, av, rv, sd, rs)
    case Spec.Confirmed{} _:
      stable_same(u, clk, ksku, tot, av, rv, sd, rs)
    case Spec.Expired{} _:
      stable_same(u, clk, ksku, tot, av, rv, sd, rs)

def stable_conf1(+l: Spec.Look, +u: Bool, +clk: Nat, +ksku: Nat, +tot: Nat, +av: Nat, +rv: Nat, +sd: Nat, +rs: +List<Spec.Res>, +id: Nat, +el: {Spec.find_res(rs, id) == l : Spec.Look}) -> {Spec.stable(mkS(u, clk, ksku, tot, av, rv, sd, rs), Spec.st(Code.conf1(l, mkS(u, clk, ksku, tot, av, rv, sd, rs), id))) == True{} : Bool}:
  match l:
    case Spec.NoRes{}:
      stable_same(u, clk, ksku, tot, av, rv, sd, rs)
    case Spec.Got{Spec.Res{i, sku, qty, x, exp, cf, ret}}:
      stable_conf2(x, Nat.is_le(exp, clk), u, clk, ksku, tot, av, rv, sd, rs, id, i, sku, qty, exp, cf, ret, el)

def stable_gc(+u: Bool, +clk: Nat, +ksku: Nat, +tot: Nat, +av: Nat, +rv: Nat, +sd: Nat, +rs: +List<Spec.Res>, +id: Nat) -> {Spec.stable(mkS(u, clk, ksku, tot, av, rv, sd, rs), Spec.st(Code.step(mkS(u, clk, ksku, tot, av, rv, sd, rs), Spec.Confirm{id}))) == True{} : Bool}:
  match u:
    case False{}:
      stable_same(u, clk, ksku, tot, av, rv, sd, rs)
    case True{}:
      stable_conf1(Spec.find_res(rs, id), u, clk, ksku, tot, av, rv, sd, rs, id, {==})


def stable_exp2(+x: Spec.Status, +due: Bool, +u: Bool, +clk: Nat, +ksku: Nat, +tot: Nat, +av: Nat, +rv: Nat, +sd: Nat, +rs: +List<Spec.Res>, +id: Nat, +i: Nat, +sku: Nat, +qty: Nat, +exp: Nat, +cf: Nat, +ret: Nat, +hf: {Spec.find_res(rs, id) == Spec.Got{Spec.Res{i, sku, qty, x, exp, cf, ret}} : Spec.Look}) -> {Spec.stable(mkS(u, clk, ksku, tot, av, rv, sd, rs), Spec.st(Code.exp2(x, due, mkS(u, clk, ksku, tot, av, rv, sd, rs), id, sku, qty, exp, cf, ret))) == True{} : Bool}:
  match x due:
    case Spec.Held{} True{}:
      and_i(Nat.is_eq(tot, tot), Spec.recs_stable(rs, Spec.put_res(rs, id, Spec.Res{id, sku, qty, Spec.Expired{}, exp, cf, Nat.add(ret, 1n)})), eq_refl(tot), rs_put(rs, id, Spec.Res{id, sku, qty, Spec.Expired{}, exp, cf, Nat.add(ret, 1n)}, Spec.Res{i, sku, qty, Spec.Held{}, exp, cf, ret}, hf, rstab(Spec.Res{id, sku, qty, Spec.Expired{}, exp, cf, Nat.add(ret, 1n)}, Spec.Res{i, sku, qty, Spec.Held{}, exp, cf, ret}, find_id(rs, id, Spec.Res{i, sku, qty, Spec.Held{}, exp, cf, ret}, hf), {==}, eq_refl(sku), eq_refl(qty), eq_refl(exp))))
    case Spec.Held{} False{}:
      stable_same(u, clk, ksku, tot, av, rv, sd, rs)
    case Spec.Confirmed{} _:
      stable_same(u, clk, ksku, tot, av, rv, sd, rs)
    case Spec.Expired{} _:
      stable_same(u, clk, ksku, tot, av, rv, sd, rs)

def stable_exp1(+l: Spec.Look, +u: Bool, +clk: Nat, +ksku: Nat, +tot: Nat, +av: Nat, +rv: Nat, +sd: Nat, +rs: +List<Spec.Res>, +id: Nat, +el: {Spec.find_res(rs, id) == l : Spec.Look}) -> {Spec.stable(mkS(u, clk, ksku, tot, av, rv, sd, rs), Spec.st(Code.exp1(l, mkS(u, clk, ksku, tot, av, rv, sd, rs), id))) == True{} : Bool}:
  match l:
    case Spec.NoRes{}:
      stable_same(u, clk, ksku, tot, av, rv, sd, rs)
    case Spec.Got{Spec.Res{i, sku, qty, x, exp, cf, ret}}:
      stable_exp2(x, Nat.is_le(exp, clk), u, clk, ksku, tot, av, rv, sd, rs, id, i, sku, qty, exp, cf, ret, el)

def stable_ge(+u: Bool, +clk: Nat, +ksku: Nat, +tot: Nat, +av: Nat, +rv: Nat, +sd: Nat, +rs: +List<Spec.Res>, +id: Nat) -> {Spec.stable(mkS(u, clk, ksku, tot, av, rv, sd, rs), Spec.st(Code.step(mkS(u, clk, ksku, tot, av, rv, sd, rs), Spec.Expire{id}))) == True{} : Bool}:
  match u:
    case False{}:
      stable_same(u, clk, ksku, tot, av, rv, sd, rs)
    case True{}:
      stable_exp1(Spec.find_res(rs, id), u, clk, ksku, tot, av, rv, sd, rs, id, {==})


def Laws.pin_stable(s, e, h):
  match s e:
    case Spec.State{u, clk, Spec.Stock{ksku, tot, av, rv, sd}, rs} Spec.Reserve{eid, sku, qty, ttl}:
      stable_gr(u, clk, ksku, tot, av, rv, sd, rs, eid, sku, qty, ttl)
    case Spec.State{u, clk, Spec.Stock{ksku, tot, av, rv, sd}, rs} Spec.Confirm{eid}:
      stable_gc(u, clk, ksku, tot, av, rv, sd, rs, eid)
    case Spec.State{u, clk, Spec.Stock{ksku, tot, av, rv, sd}, rs} Spec.Expire{eid}:
      stable_ge(u, clk, ksku, tot, av, rv, sd, rs, eid)
    case Spec.State{u, clk, Spec.Stock{ksku, tot, av, rv, sd}, rs} Spec.Tick{}:
      stable_same(u, clk, ksku, tot, av, rv, sd, rs)
    case Spec.State{u, clk, Spec.Stock{ksku, tot, av, rv, sd}, rs} Spec.Crash{}:
      stable_same(u, clk, ksku, tot, av, rv, sd, rs)
    case Spec.State{u, clk, Spec.Stock{ksku, tot, av, rv, sd}, rs} Spec.Restart{}:
      stable_same(u, clk, ksku, tot, av, rv, sd, rs)

# ================================================================ S11 duplicate delivery
def and_fl(+a: Bool, +b: Bool, +ha: {a == False{} : Bool}) -> {Bool.and(a, b) == False{} : Bool}:
  match a:
    case False{}:
      {==}
    case True{}:
      tf_absurd({Bool.and(True{}, b) == False{} : Bool}, ha)

def and_fr(+a: Bool, +b: Bool, +hb: {b == False{} : Bool}) -> {Bool.and(a, b) == False{} : Bool}:
  match a:
    case False{}:
      {==}
    case True{}:
      hb

def look_none_f(+l: Spec.Look, +r: Spec.Res, +hl: {l == Spec.Got{r} : Spec.Look}) -> {Spec.look_none(l) == False{} : Bool}:
  %symL(l, Spec.Got{r}, hl) : {Spec.look_none(_) == False{} : Bool}
  {==}

def dup_rej(-F: List<Spec.Effect>, +S: Spec.State, +ev: Spec.Ev, +e1: {Code.step(S, ev) == (S, F) : Spec.State & List<Spec.Effect>}) -> {Spec.st(Code.step(Spec.st(Code.step(S, ev)), ev)) == Spec.st(Code.step(S, ev)) : Spec.State}:
  %Equal.sym(Spec.State & List<Spec.Effect>, Code.step(S, ev), (S, F), e1) : {Spec.st(Code.step(Spec.st(_), ev)) == Spec.st(_) : Spec.State}
  %Equal.sym(Spec.State & List<Spec.Effect>, Code.step(S, ev), (S, F), e1) : {Spec.st(_) == S : Spec.State}
  {==}

def dup_acc(-F1: List<Spec.Effect>, -F2: List<Spec.Effect>, +S: Spec.State, +S2: Spec.State, +ev: Spec.Ev, +e1: {Code.step(S, ev) == (S2, F1) : Spec.State & List<Spec.Effect>}, +e2: {Code.step(S2, ev) == (S2, F2) : Spec.State & List<Spec.Effect>}) -> {Spec.st(Code.step(Spec.st(Code.step(S, ev)), ev)) == Spec.st(Code.step(S, ev)) : Spec.State}:
  %Equal.sym(Spec.State & List<Spec.Effect>, Code.step(S, ev), (S2, F1), e1) : {Spec.st(Code.step(Spec.st(_), ev)) == Spec.st(_) : Spec.State}
  %Equal.sym(Spec.State & List<Spec.Effect>, Code.step(S2, ev), (S2, F2), e2) : {Spec.st(_) == S2 : Spec.State}
  {==}


def dup_rsv_acc(+u: Bool, +clk: Nat, +ksku: Nat, +tot: Nat, +av: Nat, +rv: Nat, +sd: Nat, +rs: +List<Spec.Res>, +id: Nat, +sku: Nat, +qty: Nat, +ttl: Nat, +hu: {u == True{} : Bool}, +hD: {Spec.reserve_ok_g(mkS(u, clk, ksku, tot, av, rv, sd, rs), id, sku, qty, ttl) == True{} : Bool}) -> {Spec.st(Code.step(Spec.st(Code.step(mkS(u, clk, ksku, tot, av, rv, sd, rs), Spec.Reserve{id, sku, qty, ttl})), Spec.Reserve{id, sku, qty, ttl})) == Spec.st(Code.step(mkS(u, clk, ksku, tot, av, rv, sd, rs), Spec.Reserve{id, sku, qty, ttl})) : Spec.State}:
  dup_acc(Spec.FxReserved{id, sku, qty, Nat.add(clk, ttl)} <> Nil{}, Spec.FxRejected{id, Spec.reserve_reason(mkS(u, clk, ksku, tot, Nat.sub(av, qty), Nat.add(rv, qty), sd, snoc(rs, Spec.Res{id, sku, qty, Spec.Held{}, Nat.add(clk, ttl), 0n, 0n})), id, sku, qty, ttl)} <> Nil{}, mkS(u, clk, ksku, tot, av, rv, sd, rs), mkS(u, clk, ksku, tot, Nat.sub(av, qty), Nat.add(rv, qty), sd, snoc(rs, Spec.Res{id, sku, qty, Spec.Held{}, Nat.add(clk, ttl), 0n, 0n})), Spec.Reserve{id, sku, qty, ttl}, step_rsv_ok(u, clk, ksku, tot, av, rv, sd, rs, id, sku, qty, ttl, Nat.sub(av, qty), hu, and_l(Nat.is_lt(0n, qty), Nat.is_lt(0n, ttl), and_l(Bool.and(Nat.is_lt(0n, qty), Nat.is_lt(0n, ttl)), Bool.and(Nat.is_eq(sku, ksku), Bool.and(Spec.look_none(Spec.find_res(rs, id)), Nat.is_le(qty, av))), hD)), and_r(Nat.is_lt(0n, qty), Nat.is_lt(0n, ttl), and_l(Bool.and(Nat.is_lt(0n, qty), Nat.is_lt(0n, ttl)), Bool.and(Nat.is_eq(sku, ksku), Bool.and(Spec.look_none(Spec.find_res(rs, id)), Nat.is_le(qty, av))), hD)), and_l(Nat.is_eq(sku, ksku), Bool.and(Spec.look_none(Spec.find_res(rs, id)), Nat.is_le(qty, av)), and_r(Bool.and(Nat.is_lt(0n, qty), Nat.is_lt(0n, ttl)), Bool.and(Nat.is_eq(sku, ksku), Bool.and(Spec.look_none(Spec.find_res(rs, id)), Nat.is_le(qty, av))), hD)), look_none_t(Spec.find_res(rs, id), and_l(Spec.look_none(Spec.find_res(rs, id)), Nat.is_le(qty, av), and_r(Nat.is_eq(sku, ksku), Bool.and(Spec.look_none(Spec.find_res(rs, id)), Nat.is_le(qty, av)), and_r(Bool.and(Nat.is_lt(0n, qty), Nat.is_lt(0n, ttl)), Bool.and(Nat.is_eq(sku, ksku), Bool.and(Spec.look_none(Spec.find_res(rs, id)), Nat.is_le(qty, av))), hD)))), and_r(Spec.look_none(Spec.find_res(rs, id)), Nat.is_le(qty, av), and_r(Nat.is_eq(sku, ksku), Bool.and(Spec.look_none(Spec.find_res(rs, id)), Nat.is_le(qty, av)), and_r(Bool.and(Nat.is_lt(0n, qty), Nat.is_lt(0n, ttl)), Bool.and(Nat.is_eq(sku, ksku), Bool.and(Spec.look_none(Spec.find_res(rs, id)), Nat.is_le(qty, av))), hD))), le_sub_add(qty, av, and_r(Spec.look_none(Spec.find_res(rs, id)), Nat.is_le(qty, av), and_r(Nat.is_eq(sku, ksku), Bool.and(Spec.look_none(Spec.find_res(rs, id)), Nat.is_le(qty, av)), and_r(Bool.and(Nat.is_lt(0n, qty), Nat.is_lt(0n, ttl)), Bool.and(Nat.is_eq(sku, ksku), Bool.and(Spec.look_none(Spec.find_res(rs, id)), Nat.is_le(qty, av))), hD))))), step_rsv_rej(u, clk, ksku, tot, Nat.sub(av, qty), Nat.add(rv, qty), sd, snoc(rs, Spec.Res{id, sku, qty, Spec.Held{}, Nat.add(clk, ttl), 0n, 0n}), id, sku, qty, ttl, hu, and_fr(Bool.and(Nat.is_lt(0n, qty), Nat.is_lt(0n, ttl)), Bool.and(Nat.is_eq(sku, ksku), Bool.and(Spec.look_none(Spec.find_res(snoc(rs, Spec.Res{id, sku, qty, Spec.Held{}, Nat.add(clk, ttl), 0n, 0n}), id)), Nat.is_le(qty, Nat.sub(av, qty)))), and_fr(Nat.is_eq(sku, ksku), Bool.and(Spec.look_none(Spec.find_res(snoc(rs, Spec.Res{id, sku, qty, Spec.Held{}, Nat.add(clk, ttl), 0n, 0n}), id)), Nat.is_le(qty, Nat.sub(av, qty))), and_fl(Spec.look_none(Spec.find_res(snoc(rs, Spec.Res{id, sku, qty, Spec.Held{}, Nat.add(clk, ttl), 0n, 0n}), id)), Nat.is_le(qty, Nat.sub(av, qty)), look_none_f(Spec.find_res(snoc(rs, Spec.Res{id, sku, qty, Spec.Held{}, Nat.add(clk, ttl), 0n, 0n}), id), Spec.Res{id, sku, qty, Spec.Held{}, Nat.add(clk, ttl), 0n, 0n}, find_snoc_new(rs, Spec.Res{id, sku, qty, Spec.Held{}, Nat.add(clk, ttl), 0n, 0n}, look_none_t(Spec.find_res(rs, id), and_l(Spec.look_none(Spec.find_res(rs, id)), Nat.is_le(qty, av), and_r(Nat.is_eq(sku, ksku), Bool.and(Spec.look_none(Spec.find_res(rs, id)), Nat.is_le(qty, av)), and_r(Bool.and(Nat.is_lt(0n, qty), Nat.is_lt(0n, ttl)), Bool.and(Nat.is_eq(sku, ksku), Bool.and(Spec.look_none(Spec.find_res(rs, id)), Nat.is_le(qty, av))), hD)))))))))))

def dup_rsv(+u: Bool, +clk: Nat, +ksku: Nat, +tot: Nat, +av: Nat, +rv: Nat, +sd: Nat, +rs: +List<Spec.Res>, +id: Nat, +sku: Nat, +qty: Nat, +ttl: Nat, +hu: {u == True{} : Bool}) -> {Spec.st(Code.step(Spec.st(Code.step(mkS(u, clk, ksku, tot, av, rv, sd, rs), Spec.Reserve{id, sku, qty, ttl})), Spec.Reserve{id, sku, qty, ttl})) == Spec.st(Code.step(mkS(u, clk, ksku, tot, av, rv, sd, rs), Spec.Reserve{id, sku, qty, ttl})) : Spec.State}:
  bcase(Spec.reserve_ok_g(mkS(u, clk, ksku, tot, av, rv, sd, rs), id, sku, qty, ttl), {Spec.st(Code.step(Spec.st(Code.step(mkS(u, clk, ksku, tot, av, rv, sd, rs), Spec.Reserve{id, sku, qty, ttl})), Spec.Reserve{id, sku, qty, ttl})) == Spec.st(Code.step(mkS(u, clk, ksku, tot, av, rv, sd, rs), Spec.Reserve{id, sku, qty, ttl})) : Spec.State}, hD => dup_rsv_acc(u, clk, ksku, tot, av, rv, sd, rs, id, sku, qty, ttl, hu, hD), hD => dup_rej(Spec.FxRejected{id, Spec.reserve_reason(mkS(u, clk, ksku, tot, av, rv, sd, rs), id, sku, qty, ttl)} <> Nil{}, mkS(u, clk, ksku, tot, av, rv, sd, rs), Spec.Reserve{id, sku, qty, ttl}, step_rsv_rej(u, clk, ksku, tot, av, rv, sd, rs, id, sku, qty, ttl, hu, hD)))

def dup_gr(+u: Bool, +clk: Nat, +ksku: Nat, +tot: Nat, +av: Nat, +rv: Nat, +sd: Nat, +rs: +List<Spec.Res>, +id: Nat, +sku: Nat, +qty: Nat, +ttl: Nat) -> {Spec.st(Code.step(Spec.st(Code.step(mkS(u, clk, ksku, tot, av, rv, sd, rs), Spec.Reserve{id, sku, qty, ttl})), Spec.Reserve{id, sku, qty, ttl})) == Spec.st(Code.step(mkS(u, clk, ksku, tot, av, rv, sd, rs), Spec.Reserve{id, sku, qty, ttl})) : Spec.State}:
  match u:
    case False{}:
      {==}
    case True{}:
      dup_rsv(u, clk, ksku, tot, av, rv, sd, rs, id, sku, qty, ttl, {==})


def el_id(+rs: +List<Spec.Res>, +id: Nat, +i: Nat, +sku: Nat, +qty: Nat, +x: Spec.Status, +exp: Nat, +cf: Nat, +ret: Nat, +el: {Spec.find_res(rs, id) == Spec.Got{Spec.Res{i, sku, qty, x, exp, cf, ret}} : Spec.Look}) -> {Spec.find_res(rs, id) == Spec.Got{Spec.Res{id, sku, qty, x, exp, cf, ret}} : Spec.Look}:
  %eq_prop(i, id, find_id(rs, id, Spec.Res{i, sku, qty, x, exp, cf, ret}, el)) : {Spec.find_res(rs, id) == Spec.Got{Spec.Res{_, sku, qty, x, exp, cf, ret}} : Spec.Look}
  el

def ca_conf(+l: Spec.Look, +clk: Nat, +id: Nat, +sku: Nat, +qty: Nat, +exp: Nat, +ret: Nat, +hl: {l == Spec.Got{Spec.Res{id, sku, qty, Spec.Confirmed{}, exp, clk, ret}} : Spec.Look}) -> {Spec.conf_acc(l, clk) == False{} : Bool}:
  %symL(l, Spec.Got{Spec.Res{id, sku, qty, Spec.Confirmed{}, exp, clk, ret}}, hl) : {Spec.conf_acc(_, clk) == False{} : Bool}
  {==}

def ea_exp(+l: Spec.Look, +clk: Nat, +id: Nat, +sku: Nat, +qty: Nat, +exp: Nat, +cf: Nat, +ret: Nat, +hl: {l == Spec.Got{Spec.Res{id, sku, qty, Spec.Expired{}, exp, cf, Nat.add(ret, 1n)}} : Spec.Look}) -> {Spec.exp_acc(l, clk) == False{} : Bool}:
  %symL(l, Spec.Got{Spec.Res{id, sku, qty, Spec.Expired{}, exp, cf, Nat.add(ret, 1n)}}, hl) : {Spec.exp_acc(_, clk) == False{} : Bool}
  {==}


def dup_conf2(+x: Spec.Status, +u: Bool, +clk: Nat, +ksku: Nat, +tot: Nat, +av: Nat, +rv: Nat, +sd: Nat, +rs: +List<Spec.Res>, +id: Nat, +i: Nat, +sku: Nat, +qty: Nat, +exp: Nat, +cf: Nat, +ret: Nat, +h: {Spec.inv(mkS(u, clk, ksku, tot, av, rv, sd, rs)) == True{} : Bool}, +hu: {u == True{} : Bool}, +hD: {Spec.conf_acc(Spec.Got{Spec.Res{i, sku, qty, x, exp, cf, ret}}, clk) == True{} : Bool}, +el: {Spec.find_res(rs, id) == Spec.Got{Spec.Res{i, sku, qty, x, exp, cf, ret}} : Spec.Look}) -> {Spec.st(Code.step(Spec.st(Code.step(mkS(u, clk, ksku, tot, av, rv, sd, rs), Spec.Confirm{id})), Spec.Confirm{id})) == Spec.st(Code.step(mkS(u, clk, ksku, tot, av, rv, sd, rs), Spec.Confirm{id})) : Spec.State}:
  match x:
    case Spec.Held{}:
      dup_acc(Spec.FxConfirmed{id} <> Nil{}, Spec.FxRejected{id, Spec.confirm_reason(mkS(u, clk, ksku, tot, av, Nat.sub(rv, qty), Nat.add(sd, qty), Spec.put_res(rs, id, Spec.Res{id, sku, qty, Spec.Confirmed{}, exp, clk, ret})), id)} <> Nil{}, mkS(u, clk, ksku, tot, av, rv, sd, rs), mkS(u, clk, ksku, tot, av, Nat.sub(rv, qty), Nat.add(sd, qty), Spec.put_res(rs, id, Spec.Res{id, sku, qty, Spec.Confirmed{}, exp, clk, ret})), Spec.Confirm{id}, step_conf_ok(u, clk, ksku, tot, av, rv, sd, rs, id, sku, qty, exp, cf, ret, Nat.sub(rv, qty), hu, el_id(rs, id, i, sku, qty, Spec.Held{}, exp, cf, ret, el), not_t(Nat.is_le(exp, clk), hD), le_sub_add(qty, rv, le_via(qty, Spec.qty_sum(Spec.put_res(rs, id, Spec.Res{id, sku, qty, Spec.Confirmed{}, exp, clk, ret}), ksku, Spec.Held{}), rv, held_split(rs, id, Spec.Res{id, sku, qty, Spec.Confirmed{}, exp, clk, ret}, Spec.Res{i, sku, qty, Spec.Held{}, exp, cf, ret}, ksku, qty, rv, el, eq_prop(rv, Spec.qty_sum(rs, ksku, Spec.Held{}), and_l(Nat.is_eq(rv, Spec.qty_sum(rs, ksku, Spec.Held{})), Nat.is_eq(sd, Spec.qty_sum(rs, ksku, Spec.Confirmed{})), i_a1(mkS(u, clk, ksku, tot, av, rv, sd, rs), h))), cn_hit(Spec.Res{i, sku, qty, Spec.Held{}, exp, cf, ret}, ksku, Spec.Held{}, and_i(Nat.is_eq(sku, ksku), True{}, all_find(Spec.PSku{}, ksku, rs, id, Spec.Res{i, sku, qty, Spec.Held{}, exp, cf, ret}, and_r(Spec.uniq(rs), Spec.all_rec(Spec.PSku{}, ksku, rs), i_a2(mkS(u, clk, ksku, tot, av, rv, sd, rs), h)), el), {==})), cn_miss(Spec.Res{id, sku, qty, Spec.Confirmed{}, exp, clk, ret}, ksku, Spec.Held{}, and_f_r(Nat.is_eq(sku, ksku))))))), step_conf_rej(u, clk, ksku, tot, av, Nat.sub(rv, qty), Nat.add(sd, qty), Spec.put_res(rs, id, Spec.Res{id, sku, qty, Spec.Confirmed{}, exp, clk, ret}), id, hu, ca_conf(Spec.find_res(Spec.put_res(rs, id, Spec.Res{id, sku, qty, Spec.Confirmed{}, exp, clk, ret}), id), clk, id, sku, qty, exp, ret, find_put_eq(rs, id, Spec.Res{id, sku, qty, Spec.Confirmed{}, exp, clk, ret}, Spec.Res{i, sku, qty, Spec.Held{}, exp, cf, ret}, {==}, el))))
    case Spec.Confirmed{}:
      ft_absurd({Spec.st(Code.step(Spec.st(Code.step(mkS(u, clk, ksku, tot, av, rv, sd, rs), Spec.Confirm{id})), Spec.Confirm{id})) == Spec.st(Code.step(mkS(u, clk, ksku, tot, av, rv, sd, rs), Spec.Confirm{id})) : Spec.State}, hD)
    case Spec.Expired{}:
      ft_absurd({Spec.st(Code.step(Spec.st(Code.step(mkS(u, clk, ksku, tot, av, rv, sd, rs), Spec.Confirm{id})), Spec.Confirm{id})) == Spec.st(Code.step(mkS(u, clk, ksku, tot, av, rv, sd, rs), Spec.Confirm{id})) : Spec.State}, hD)

def dup_conf1(+l: Spec.Look, +u: Bool, +clk: Nat, +ksku: Nat, +tot: Nat, +av: Nat, +rv: Nat, +sd: Nat, +rs: +List<Spec.Res>, +id: Nat, +h: {Spec.inv(mkS(u, clk, ksku, tot, av, rv, sd, rs)) == True{} : Bool}, +hu: {u == True{} : Bool}, +hD: {Spec.conf_acc(l, clk) == True{} : Bool}, +el: {Spec.find_res(rs, id) == l : Spec.Look}) -> {Spec.st(Code.step(Spec.st(Code.step(mkS(u, clk, ksku, tot, av, rv, sd, rs), Spec.Confirm{id})), Spec.Confirm{id})) == Spec.st(Code.step(mkS(u, clk, ksku, tot, av, rv, sd, rs), Spec.Confirm{id})) : Spec.State}:
  match l:
    case Spec.NoRes{}:
      ft_absurd({Spec.st(Code.step(Spec.st(Code.step(mkS(u, clk, ksku, tot, av, rv, sd, rs), Spec.Confirm{id})), Spec.Confirm{id})) == Spec.st(Code.step(mkS(u, clk, ksku, tot, av, rv, sd, rs), Spec.Confirm{id})) : Spec.State}, hD)
    case Spec.Got{Spec.Res{i, sku, qty, x, exp, cf, ret}}:
      dup_conf2(x, u, clk, ksku, tot, av, rv, sd, rs, id, i, sku, qty, exp, cf, ret, h, hu, hD, el)

def dup_conf(+u: Bool, +clk: Nat, +ksku: Nat, +tot: Nat, +av: Nat, +rv: Nat, +sd: Nat, +rs: +List<Spec.Res>, +id: Nat, +h: {Spec.inv(mkS(u, clk, ksku, tot, av, rv, sd, rs)) == True{} : Bool}, +hu: {u == True{} : Bool}) -> {Spec.st(Code.step(Spec.st(Code.step(mkS(u, clk, ksku, tot, av, rv, sd, rs), Spec.Confirm{id})), Spec.Confirm{id})) == Spec.st(Code.step(mkS(u, clk, ksku, tot, av, rv, sd, rs), Spec.Confirm{id})) : Spec.State}:
  bcase(Spec.confirm_ok_g(mkS(u, clk, ksku, tot, av, rv, sd, rs), id), {Spec.st(Code.step(Spec.st(Code.step(mkS(u, clk, ksku, tot, av, rv, sd, rs), Spec.Confirm{id})), Spec.Confirm{id})) == Spec.st(Code.step(mkS(u, clk, ksku, tot, av, rv, sd, rs), Spec.Confirm{id})) : Spec.State}, hD => dup_conf1(Spec.find_res(rs, id), u, clk, ksku, tot, av, rv, sd, rs, id, h, hu, hD, {==}), hD => dup_rej(Spec.FxRejected{id, Spec.confirm_reason(mkS(u, clk, ksku, tot, av, rv, sd, rs), id)} <> Nil{}, mkS(u, clk, ksku, tot, av, rv, sd, rs), Spec.Confirm{id}, step_conf_rej(u, clk, ksku, tot, av, rv, sd, rs, id, hu, hD)))

def dup_gc(+u: Bool, +clk: Nat, +ksku: Nat, +tot: Nat, +av: Nat, +rv: Nat, +sd: Nat, +rs: +List<Spec.Res>, +id: Nat, +h: {Spec.inv(mkS(u, clk, ksku, tot, av, rv, sd, rs)) == True{} : Bool}) -> {Spec.st(Code.step(Spec.st(Code.step(mkS(u, clk, ksku, tot, av, rv, sd, rs), Spec.Confirm{id})), Spec.Confirm{id})) == Spec.st(Code.step(mkS(u, clk, ksku, tot, av, rv, sd, rs), Spec.Confirm{id})) : Spec.State}:
  match u:
    case False{}:
      {==}
    case True{}:
      dup_conf(u, clk, ksku, tot, av, rv, sd, rs, id, h, {==})


def dup_exp2(+x: Spec.Status, +u: Bool, +clk: Nat, +ksku: Nat, +tot: Nat, +av: Nat, +rv: Nat, +sd: Nat, +rs: +List<Spec.Res>, +id: Nat, +i: Nat, +sku: Nat, +qty: Nat, +exp: Nat, +cf: Nat, +ret: Nat, +h: {Spec.inv(mkS(u, clk, ksku, tot, av, rv, sd, rs)) == True{} : Bool}, +hu: {u == True{} : Bool}, +hD: {Spec.exp_acc(Spec.Got{Spec.Res{i, sku, qty, x, exp, cf, ret}}, clk) == True{} : Bool}, +el: {Spec.find_res(rs, id) == Spec.Got{Spec.Res{i, sku, qty, x, exp, cf, ret}} : Spec.Look}) -> {Spec.st(Code.step(Spec.st(Code.step(mkS(u, clk, ksku, tot, av, rv, sd, rs), Spec.Expire{id})), Spec.Expire{id})) == Spec.st(Code.step(mkS(u, clk, ksku, tot, av, rv, sd, rs), Spec.Expire{id})) : Spec.State}:
  match x:
    case Spec.Held{}:
      dup_acc(Spec.FxReleased{id, qty} <> Nil{}, Spec.FxRejected{id, Spec.expire_reason(mkS(u, clk, ksku, tot, Nat.add(av, qty), Nat.sub(rv, qty), sd, Spec.put_res(rs, id, Spec.Res{id, sku, qty, Spec.Expired{}, exp, cf, Nat.add(ret, 1n)})), id)} <> Nil{}, mkS(u, clk, ksku, tot, av, rv, sd, rs), mkS(u, clk, ksku, tot, Nat.add(av, qty), Nat.sub(rv, qty), sd, Spec.put_res(rs, id, Spec.Res{id, sku, qty, Spec.Expired{}, exp, cf, Nat.add(ret, 1n)})), Spec.Expire{id}, step_exp_ok(u, clk, ksku, tot, av, rv, sd, rs, id, sku, qty, exp, cf, ret, Nat.sub(rv, qty), hu, el_id(rs, id, i, sku, qty, Spec.Held{}, exp, cf, ret, el), hD, le_sub_add(qty, rv, le_via(qty, Spec.qty_sum(Spec.put_res(rs, id, Spec.Res{id, sku, qty, Spec.Expired{}, exp, cf, Nat.add(ret, 1n)}), ksku, Spec.Held{}), rv, held_split(rs, id, Spec.Res{id, sku, qty, Spec.Expired{}, exp, cf, Nat.add(ret, 1n)}, Spec.Res{i, sku, qty, Spec.Held{}, exp, cf, ret}, ksku, qty, rv, el, eq_prop(rv, Spec.qty_sum(rs, ksku, Spec.Held{}), and_l(Nat.is_eq(rv, Spec.qty_sum(rs, ksku, Spec.Held{})), Nat.is_eq(sd, Spec.qty_sum(rs, ksku, Spec.Confirmed{})), i_a1(mkS(u, clk, ksku, tot, av, rv, sd, rs), h))), cn_hit(Spec.Res{i, sku, qty, Spec.Held{}, exp, cf, ret}, ksku, Spec.Held{}, and_i(Nat.is_eq(sku, ksku), True{}, all_find(Spec.PSku{}, ksku, rs, id, Spec.Res{i, sku, qty, Spec.Held{}, exp, cf, ret}, and_r(Spec.uniq(rs), Spec.all_rec(Spec.PSku{}, ksku, rs), i_a2(mkS(u, clk, ksku, tot, av, rv, sd, rs), h)), el), {==})), cn_miss(Spec.Res{id, sku, qty, Spec.Expired{}, exp, cf, Nat.add(ret, 1n)}, ksku, Spec.Held{}, and_f_r(Nat.is_eq(sku, ksku))))))), step_exp_rej(u, clk, ksku, tot, Nat.add(av, qty), Nat.sub(rv, qty), sd, Spec.put_res(rs, id, Spec.Res{id, sku, qty, Spec.Expired{}, exp, cf, Nat.add(ret, 1n)}), id, hu, ea_exp(Spec.find_res(Spec.put_res(rs, id, Spec.Res{id, sku, qty, Spec.Expired{}, exp, cf, Nat.add(ret, 1n)}), id), clk, id, sku, qty, exp, cf, ret, find_put_eq(rs, id, Spec.Res{id, sku, qty, Spec.Expired{}, exp, cf, Nat.add(ret, 1n)}, Spec.Res{i, sku, qty, Spec.Held{}, exp, cf, ret}, {==}, el))))
    case Spec.Confirmed{}:
      ft_absurd({Spec.st(Code.step(Spec.st(Code.step(mkS(u, clk, ksku, tot, av, rv, sd, rs), Spec.Expire{id})), Spec.Expire{id})) == Spec.st(Code.step(mkS(u, clk, ksku, tot, av, rv, sd, rs), Spec.Expire{id})) : Spec.State}, hD)
    case Spec.Expired{}:
      ft_absurd({Spec.st(Code.step(Spec.st(Code.step(mkS(u, clk, ksku, tot, av, rv, sd, rs), Spec.Expire{id})), Spec.Expire{id})) == Spec.st(Code.step(mkS(u, clk, ksku, tot, av, rv, sd, rs), Spec.Expire{id})) : Spec.State}, hD)

def dup_exp1(+l: Spec.Look, +u: Bool, +clk: Nat, +ksku: Nat, +tot: Nat, +av: Nat, +rv: Nat, +sd: Nat, +rs: +List<Spec.Res>, +id: Nat, +h: {Spec.inv(mkS(u, clk, ksku, tot, av, rv, sd, rs)) == True{} : Bool}, +hu: {u == True{} : Bool}, +hD: {Spec.exp_acc(l, clk) == True{} : Bool}, +el: {Spec.find_res(rs, id) == l : Spec.Look}) -> {Spec.st(Code.step(Spec.st(Code.step(mkS(u, clk, ksku, tot, av, rv, sd, rs), Spec.Expire{id})), Spec.Expire{id})) == Spec.st(Code.step(mkS(u, clk, ksku, tot, av, rv, sd, rs), Spec.Expire{id})) : Spec.State}:
  match l:
    case Spec.NoRes{}:
      ft_absurd({Spec.st(Code.step(Spec.st(Code.step(mkS(u, clk, ksku, tot, av, rv, sd, rs), Spec.Expire{id})), Spec.Expire{id})) == Spec.st(Code.step(mkS(u, clk, ksku, tot, av, rv, sd, rs), Spec.Expire{id})) : Spec.State}, hD)
    case Spec.Got{Spec.Res{i, sku, qty, x, exp, cf, ret}}:
      dup_exp2(x, u, clk, ksku, tot, av, rv, sd, rs, id, i, sku, qty, exp, cf, ret, h, hu, hD, el)

def dup_exp(+u: Bool, +clk: Nat, +ksku: Nat, +tot: Nat, +av: Nat, +rv: Nat, +sd: Nat, +rs: +List<Spec.Res>, +id: Nat, +h: {Spec.inv(mkS(u, clk, ksku, tot, av, rv, sd, rs)) == True{} : Bool}, +hu: {u == True{} : Bool}) -> {Spec.st(Code.step(Spec.st(Code.step(mkS(u, clk, ksku, tot, av, rv, sd, rs), Spec.Expire{id})), Spec.Expire{id})) == Spec.st(Code.step(mkS(u, clk, ksku, tot, av, rv, sd, rs), Spec.Expire{id})) : Spec.State}:
  bcase(Spec.expire_ok_g(mkS(u, clk, ksku, tot, av, rv, sd, rs), id), {Spec.st(Code.step(Spec.st(Code.step(mkS(u, clk, ksku, tot, av, rv, sd, rs), Spec.Expire{id})), Spec.Expire{id})) == Spec.st(Code.step(mkS(u, clk, ksku, tot, av, rv, sd, rs), Spec.Expire{id})) : Spec.State}, hD => dup_exp1(Spec.find_res(rs, id), u, clk, ksku, tot, av, rv, sd, rs, id, h, hu, hD, {==}), hD => dup_rej(Spec.FxRejected{id, Spec.expire_reason(mkS(u, clk, ksku, tot, av, rv, sd, rs), id)} <> Nil{}, mkS(u, clk, ksku, tot, av, rv, sd, rs), Spec.Expire{id}, step_exp_rej(u, clk, ksku, tot, av, rv, sd, rs, id, hu, hD)))

def dup_ge(+u: Bool, +clk: Nat, +ksku: Nat, +tot: Nat, +av: Nat, +rv: Nat, +sd: Nat, +rs: +List<Spec.Res>, +id: Nat, +h: {Spec.inv(mkS(u, clk, ksku, tot, av, rv, sd, rs)) == True{} : Bool}) -> {Spec.st(Code.step(Spec.st(Code.step(mkS(u, clk, ksku, tot, av, rv, sd, rs), Spec.Expire{id})), Spec.Expire{id})) == Spec.st(Code.step(mkS(u, clk, ksku, tot, av, rv, sd, rs), Spec.Expire{id})) : Spec.State}:
  match u:
    case False{}:
      {==}
    case True{}:
      dup_exp(u, clk, ksku, tot, av, rv, sd, rs, id, h, {==})


def Laws.pin_dup_idempotent(s, e, h, hd):
  match s e:
    case Spec.State{u, clk, Spec.Stock{ksku, tot, av, rv, sd}, rs} Spec.Reserve{id, sku, qty, ttl}:
      dup_gr(u, clk, ksku, tot, av, rv, sd, rs, id, sku, qty, ttl)
    case Spec.State{u, clk, Spec.Stock{ksku, tot, av, rv, sd}, rs} Spec.Confirm{id}:
      dup_gc(u, clk, ksku, tot, av, rv, sd, rs, id, h)
    case Spec.State{u, clk, Spec.Stock{ksku, tot, av, rv, sd}, rs} Spec.Expire{id}:
      dup_ge(u, clk, ksku, tot, av, rv, sd, rs, id, h)
    case Spec.State{u, clk, Spec.Stock{ksku, tot, av, rv, sd}, rs} Spec.Tick{}:
      ft_absurd({Spec.st(Code.step(Spec.st(Code.step(mkS(u, clk, ksku, tot, av, rv, sd, rs), Spec.Tick{})), Spec.Tick{})) == Spec.st(Code.step(mkS(u, clk, ksku, tot, av, rv, sd, rs), Spec.Tick{})) : Spec.State}, hd)
    case Spec.State{u, clk, Spec.Stock{ksku, tot, av, rv, sd}, rs} Spec.Crash{}:
      ft_absurd({Spec.st(Code.step(Spec.st(Code.step(mkS(u, clk, ksku, tot, av, rv, sd, rs), Spec.Crash{})), Spec.Crash{})) == Spec.st(Code.step(mkS(u, clk, ksku, tot, av, rv, sd, rs), Spec.Crash{})) : Spec.State}, hd)
    case Spec.State{u, clk, Spec.Stock{ksku, tot, av, rv, sd}, rs} Spec.Restart{}:
      ft_absurd({Spec.st(Code.step(Spec.st(Code.step(mkS(u, clk, ksku, tot, av, rv, sd, rs), Spec.Restart{})), Spec.Restart{})) == Spec.st(Code.step(mkS(u, clk, ksku, tot, av, rv, sd, rs), Spec.Restart{})) : Spec.State}, hd)

# ================================================================ P3b (accumulated effects)
def sne(acc: +List<Spec.Effect>, x: Spec.Effect) -> +List<Spec.Effect>:
  List.append(&2, Spec.Effect, acc, x <> Nil{})

def and_t_r(+a: Bool) -> {a == Bool.and(a, True{}) : Bool}:
  match a:
    case False{}:
      {==}
    case True{}:
      {==}

def and_assoc(+a: Bool, +b: Bool, +c: Bool) -> {Bool.and(Bool.and(a, b), c) == Bool.and(a, Bool.and(b, c)) : Bool}:
  match a:
    case False{}:
      {==}
    case True{}:
      {==}

def rcp2(+g: Bool, +A: Nat, +B: Nat, +c: Nat, +ih: {Nat.add(B, c) == A : Nat}) -> {Nat.add(Spec.rc_hit(g, B), c) == Spec.rc_hit(g, A) : Nat}:
  match g:
    case True{}:
      %ih : {1n+Nat.add(B, c) == 1n+_ : Nat}
      {==}
    case False{}:
      ih

def rcp_comb(+h: Spec.Effect, +i: Nat, +A: Nat, +B: Nat, +c: Nat, +ih: {Nat.add(B, c) == A : Nat}) -> {Nat.add(Spec.rc_pick(h, i, B), c) == Spec.rc_pick(h, i, A) : Nat}:
  match h:
    case Spec.FxReleased{j, q}:
      rcp2(Nat.is_eq(j, i), A, B, c, ih)
    case Spec.FxReserved{a, b, c2, d}:
      ih
    case Spec.FxConfirmed{a}:
      ih
    case Spec.FxRejected{a, b}:
      ih

def rc_sne(+acc: +List<Spec.Effect>, +x: Spec.Effect, +i: Nat) -> {Nat.add(Spec.released_count(acc, i), Spec.rc_pick(x, i, 0n)) == Spec.released_count(sne(acc, x), i) : Nat}:
  match acc:
    case Nil{}:
      {==}
    case +h <> +t:
      rcp_comb(h, i, Spec.released_count(sne(t, x), i), Spec.released_count(t, i), Spec.rc_pick(x, i, 0n), rc_sne(t, x, i))

def qok_sne(+acc: +List<Spec.Effect>, +x: Spec.Effect, +i: Nat, +q: Nat) -> {Bool.and(Spec.released_qty_ok(acc, i, q), Spec.rq_pick(x, i, q)) == Spec.released_qty_ok(sne(acc, x), i, q) : Bool}:
  match acc:
    case Nil{}:
      and_t_r(Spec.rq_pick(x, i, q))
    case +h <> +t:
      %qok_sne(t, x, i, q) : {Bool.and(Bool.and(Spec.rq_pick(h, i, q), Spec.released_qty_ok(t, i, q)), Spec.rq_pick(x, i, q)) == Bool.and(Spec.rq_pick(h, i, q), _) : Bool}
      and_assoc(Spec.rq_pick(h, i, q), Spec.released_qty_ok(t, i, q), Spec.rq_pick(x, i, q))

def look_q(+l: Spec.Look, +q: Nat) -> Bool:
  match l:
    case Spec.NoRes{}:
      False{}
    case Spec.Got{r}:
      Nat.is_eq(Spec.r_qty(r), q)

def w_one(+rs: +List<Spec.Res>, +x: Spec.Effect) -> Bool:
  match x:
    case Spec.FxReleased{i, q}:
      look_q(Spec.find_res(rs, i), q)
    case _:
      True{}

def w_ok(+rs: +List<Spec.Res>, +acc: +List<Spec.Effect>) -> Bool:
  match acc:
    case Nil{}:
      True{}
    case +x <> +t:
      Bool.and(w_one(rs, x), w_ok(rs, t))

def w_sne(+rs: +List<Spec.Res>, +acc: +List<Spec.Effect>, +x: Spec.Effect) -> {Bool.and(w_ok(rs, acc), w_one(rs, x)) == w_ok(rs, sne(acc, x)) : Bool}:
  match acc:
    case Nil{}:
      and_t_r(w_one(rs, x))
    case +y <> +t:
      %w_sne(rs, t, x) : {Bool.and(Bool.and(w_one(rs, y), w_ok(rs, t)), w_one(rs, x)) == Bool.and(w_one(rs, y), _) : Bool}
      and_assoc(w_one(rs, y), w_ok(rs, t), w_one(rs, x))

def symB(-a: Bool, -b: Bool, e: {a == b : Bool}) -> {b == a : Bool}:
  Equal.sym(Bool, a, b, e)

def nonrel(x: Spec.Effect) -> Bool:
  match x:
    case Spec.FxReleased{_, _}:
      False{}
    case _:
      True{}

def rcp_nr(+x: Spec.Effect, +i: Nat, +h: {nonrel(x) == True{} : Bool}) -> {Spec.rc_pick(x, i, 0n) == 0n : Nat}:
  match x:
    case Spec.FxReleased{j, q}:
      ft_absurd({Spec.rc_hit(Nat.is_eq(j, i), 0n) == 0n : Nat}, h)
    case Spec.FxReserved{a, b, c, d}:
      {==}
    case Spec.FxConfirmed{a}:
      {==}
    case Spec.FxRejected{a, b}:
      {==}

def rqp_nr(+x: Spec.Effect, +i: Nat, +q: Nat, +h: {nonrel(x) == True{} : Bool}) -> {Spec.rq_pick(x, i, q) == True{} : Bool}:
  match x:
    case Spec.FxReleased{j, q2}:
      ft_absurd({Spec.rq_hit(Nat.is_eq(j, i), Nat.is_eq(q2, q)) == True{} : Bool}, h)
    case Spec.FxReserved{a, b, c, d}:
      {==}
    case Spec.FxConfirmed{a}:
      {==}
    case Spec.FxRejected{a, b}:
      {==}

def w1_nr(+rs: +List<Spec.Res>, +x: Spec.Effect, +h: {nonrel(x) == True{} : Bool}) -> {w_one(rs, x) == True{} : Bool}:
  match x:
    case Spec.FxReleased{j, q}:
      ft_absurd({look_q(Spec.find_res(rs, j), q) == True{} : Bool}, h)
    case Spec.FxReserved{a, b, c, d}:
      {==}
    case Spec.FxConfirmed{a}:
      {==}
    case Spec.FxRejected{a, b}:
      {==}

def recok(+acc: +List<Spec.Effect>, +r: Spec.Res) -> Bool:
  Bool.and(Nat.is_eq(Spec.released_count(acc, Spec.r_id(r)), Spec.r_ret(r)), Spec.released_qty_ok(acc, Spec.r_id(r), Spec.r_qty(r)))

def rc_sne_nr(+acc: +List<Spec.Effect>, +x: Spec.Effect, +i: Nat, +hnr: {nonrel(x) == True{} : Bool}) -> {Spec.released_count(sne(acc, x), i) == Spec.released_count(acc, i) : Nat}:
  trN(Spec.released_count(sne(acc, x), i), Nat.add(Spec.released_count(acc, i), Spec.rc_pick(x, i, 0n)), Spec.released_count(acc, i), symN(Nat.add(Spec.released_count(acc, i), Spec.rc_pick(x, i, 0n)), Spec.released_count(sne(acc, x), i), rc_sne(acc, x, i)), trN(Nat.add(Spec.released_count(acc, i), Spec.rc_pick(x, i, 0n)), Nat.add(Spec.released_count(acc, i), 0n), Spec.released_count(acc, i), cong_add_r(Spec.rc_pick(x, i, 0n), 0n, Spec.released_count(acc, i), rcp_nr(x, i, hnr)), symN(Spec.released_count(acc, i), Nat.add(Spec.released_count(acc, i), 0n), az(Spec.released_count(acc, i)))))

def qok_sne_nr(+acc: +List<Spec.Effect>, +x: Spec.Effect, +i: Nat, +q: Nat, +hnr: {nonrel(x) == True{} : Bool}) -> {Spec.released_qty_ok(sne(acc, x), i, q) == Spec.released_qty_ok(acc, i, q) : Bool}:
  %qok_sne(acc, x, i, q) : {_ == Spec.released_qty_ok(acc, i, q) : Bool}
  %symB(Spec.rq_pick(x, i, q), True{}, rqp_nr(x, i, q, hnr)) : {Bool.and(Spec.released_qty_ok(acc, i, q), _) == Spec.released_qty_ok(acc, i, q) : Bool}
  %and_t_r(Spec.released_qty_ok(acc, i, q)) : {_ == Spec.released_qty_ok(acc, i, q) : Bool}
  {==}

def recok_nr(+acc: +List<Spec.Effect>, +x: Spec.Effect, +r: Spec.Res, +hnr: {nonrel(x) == True{} : Bool}, +h: {recok(acc, r) == True{} : Bool}) -> {recok(sne(acc, x), r) == True{} : Bool}:
  %symN(Spec.released_count(sne(acc, x), Spec.r_id(r)), Spec.released_count(acc, Spec.r_id(r)), rc_sne_nr(acc, x, Spec.r_id(r), hnr)) : {Bool.and(Nat.is_eq(_, Spec.r_ret(r)), Spec.released_qty_ok(sne(acc, x), Spec.r_id(r), Spec.r_qty(r))) == True{} : Bool}
  %symB(Spec.released_qty_ok(sne(acc, x), Spec.r_id(r), Spec.r_qty(r)), Spec.released_qty_ok(acc, Spec.r_id(r), Spec.r_qty(r)), qok_sne_nr(acc, x, Spec.r_id(r), Spec.r_qty(r), hnr)) : {Bool.and(Nat.is_eq(Spec.released_count(acc, Spec.r_id(r)), Spec.r_ret(r)), _) == True{} : Bool}
  h

def ro_nr(+rs: +List<Spec.Res>, +acc: +List<Spec.Effect>, +x: Spec.Effect, +hnr: {nonrel(x) == True{} : Bool}, +h: {Spec.released_ok2(rs, acc) == True{} : Bool}) -> {Spec.released_ok2(rs, sne(acc, x)) == True{} : Bool}:
  match rs:
    case Nil{}:
      {==}
    case +r <> +t:
      and_i(recok(sne(acc, x), r), Spec.released_ok2(t, sne(acc, x)), recok_nr(acc, x, r, hnr, and_l(recok(acc, r), Spec.released_ok2(t, acc), h)), ro_nr(t, acc, x, hnr, and_r(recok(acc, r), Spec.released_ok2(t, acc), h)))

def ro_snoc(+rs: +List<Spec.Res>, +acc: +List<Spec.Effect>, +x: Spec.Res, +h1: {Spec.released_ok2(rs, acc) == True{} : Bool}, +h2: {recok(acc, x) == True{} : Bool}) -> {Spec.released_ok2(snoc(rs, x), acc) == True{} : Bool}:
  match rs:
    case Nil{}:
      and_i(recok(acc, x), True{}, h2, {==})
    case +r <> +t:
      and_i(recok(acc, r), Spec.released_ok2(snoc(t, x), acc), and_l(recok(acc, r), Spec.released_ok2(t, acc), h1), ro_snoc(t, acc, x, and_r(recok(acc, r), Spec.released_ok2(t, acc), h1), h2))

def lq_none(+rs: +List<Spec.Res>, +j: Nat, +id: Nat, +q: Nat, +hj: {j == id : Nat}, +hn: {Spec.find_res(rs, id) == Spec.NoRes{} : Spec.Look}) -> {look_q(Spec.find_res(rs, j), q) == False{} : Bool}:
  %symN(j, id, hj) : {look_q(Spec.find_res(rs, _), q) == False{} : Bool}
  %symL(Spec.find_res(rs, id), Spec.NoRes{}, hn) : {look_q(_, q) == False{} : Bool}
  {==}

def c0_hit(+g: Bool, +j: Nat, +id: Nat, +q: Nat, +rs: +List<Spec.Res>, +B: Nat, +hg: {Nat.is_eq(j, id) == g : Bool}, +hW: {look_q(Spec.find_res(rs, j), q) == True{} : Bool}, +hn: {Spec.find_res(rs, id) == Spec.NoRes{} : Spec.Look}, +ih: {B == 0n : Nat}) -> {Spec.rc_hit(g, B) == 0n : Nat}:
  match g:
    case True{}:
      contra({Spec.rc_hit(True{}, B) == 0n : Nat}, look_q(Spec.find_res(rs, j), q), hW, lq_none(rs, j, id, q, eq_prop(j, id, hg), hn))
    case False{}:
      ih

def c0_pick(+y: Spec.Effect, +rs: +List<Spec.Res>, +id: Nat, +t: +List<Spec.Effect>, +hy: {w_one(rs, y) == True{} : Bool}, +hn: {Spec.find_res(rs, id) == Spec.NoRes{} : Spec.Look}, +ih: {Spec.released_count(t, id) == 0n : Nat}) -> {Spec.rc_pick(y, id, Spec.released_count(t, id)) == 0n : Nat}:
  match y:
    case Spec.FxReleased{j, q}:
      c0_hit(Nat.is_eq(j, id), j, id, q, rs, Spec.released_count(t, id), {==}, hy, hn, ih)
    case Spec.FxReserved{a, b, c, d}:
      ih
    case Spec.FxConfirmed{a}:
      ih
    case Spec.FxRejected{a, b}:
      ih

def count0(+acc: +List<Spec.Effect>, +rs: +List<Spec.Res>, +id: Nat, +hW: {w_ok(rs, acc) == True{} : Bool}, +hn: {Spec.find_res(rs, id) == Spec.NoRes{} : Spec.Look}) -> {Spec.released_count(acc, id) == 0n : Nat}:
  match acc:
    case Nil{}:
      {==}
    case +y <> +t:
      c0_pick(y, rs, id, t, and_l(w_one(rs, y), w_ok(rs, t), hW), hn, count0(t, rs, id, and_r(w_one(rs, y), w_ok(rs, t), hW), hn))

def q0_hit(+g: Bool, +j: Nat, +id: Nat, +q2: Nat, +q: Nat, +rs: +List<Spec.Res>, +R: Bool, +hg: {Nat.is_eq(j, id) == g : Bool}, +hW: {look_q(Spec.find_res(rs, j), q2) == True{} : Bool}, +hn: {Spec.find_res(rs, id) == Spec.NoRes{} : Spec.Look}, +ih: {R == True{} : Bool}) -> {Bool.and(Spec.rq_hit(g, Nat.is_eq(q2, q)), R) == True{} : Bool}:
  match g:
    case True{}:
      contra({Bool.and(Spec.rq_hit(True{}, Nat.is_eq(q2, q)), R) == True{} : Bool}, look_q(Spec.find_res(rs, j), q2), hW, lq_none(rs, j, id, q2, eq_prop(j, id, hg), hn))
    case False{}:
      ih

def q0_pick(+y: Spec.Effect, +rs: +List<Spec.Res>, +id: Nat, +q: Nat, +t: +List<Spec.Effect>, +hy: {w_one(rs, y) == True{} : Bool}, +hn: {Spec.find_res(rs, id) == Spec.NoRes{} : Spec.Look}, +ih: {Spec.released_qty_ok(t, id, q) == True{} : Bool}) -> {Bool.and(Spec.rq_pick(y, id, q), Spec.released_qty_ok(t, id, q)) == True{} : Bool}:
  match y:
    case Spec.FxReleased{j, q2}:
      q0_hit(Nat.is_eq(j, id), j, id, q2, q, rs, Spec.released_qty_ok(t, id, q), {==}, hy, hn, ih)
    case Spec.FxReserved{a, b, c, d}:
      ih
    case Spec.FxConfirmed{a}:
      ih
    case Spec.FxRejected{a, b}:
      ih

def qok0(+acc: +List<Spec.Effect>, +rs: +List<Spec.Res>, +id: Nat, +q: Nat, +hW: {w_ok(rs, acc) == True{} : Bool}, +hn: {Spec.find_res(rs, id) == Spec.NoRes{} : Spec.Look}) -> {Spec.released_qty_ok(acc, id, q) == True{} : Bool}:
  match acc:
    case Nil{}:
      {==}
    case +y <> +t:
      q0_pick(y, rs, id, q, t, and_l(w_one(rs, y), w_ok(rs, t), hW), hn, qok0(t, rs, id, q, and_r(w_one(rs, y), w_ok(rs, t), hW), hn))

def lq_snoc1(+l: Spec.Look, +rs: +List<Spec.Res>, +x: Spec.Res, +i: Nat, +q: Nat, +el: {Spec.find_res(rs, i) == l : Spec.Look}, +h: {look_q(l, q) == True{} : Bool}) -> {look_q(Spec.find_res(snoc(rs, x), i), q) == True{} : Bool}:
  match l:
    case Spec.NoRes{}:
      ft_absurd({look_q(Spec.find_res(snoc(rs, x), i), q) == True{} : Bool}, h)
    case Spec.Got{r}:
      %symL(Spec.find_res(snoc(rs, x), i), Spec.Got{r}, find_snoc(rs, x, i, r, el)) : {look_q(_, q) == True{} : Bool}
      h

def w1_snoc(+rs: +List<Spec.Res>, +x: Spec.Res, +y: Spec.Effect, +h: {w_one(rs, y) == True{} : Bool}) -> {w_one(snoc(rs, x), y) == True{} : Bool}:
  match y:
    case Spec.FxReleased{i, q}:
      lq_snoc1(Spec.find_res(rs, i), rs, x, i, q, {==}, h)
    case Spec.FxReserved{a, b, c, d}:
      {==}
    case Spec.FxConfirmed{a}:
      {==}
    case Spec.FxRejected{a, b}:
      {==}

def w_snoc_rs(+acc: +List<Spec.Effect>, +rs: +List<Spec.Res>, +x: Spec.Res, +h: {w_ok(rs, acc) == True{} : Bool}) -> {w_ok(snoc(rs, x), acc) == True{} : Bool}:
  match acc:
    case Nil{}:
      {==}
    case +y <> +t:
      and_i(w_one(snoc(rs, x), y), w_ok(snoc(rs, x), t), w1_snoc(rs, x, y, and_l(w_one(rs, y), w_ok(rs, t), h)), w_snoc_rs(t, rs, x, and_r(w_one(rs, y), w_ok(rs, t), h)))

def app2(a: +List<Spec.Effect>, b: +List<Spec.Effect>) -> +List<Spec.Effect>:
  List.append(&2, Spec.Effect, a, b)

def app2_nil(+acc: +List<Spec.Effect>) -> {acc == app2(acc, Nil{}) : +List<Spec.Effect>}:
  match acc:
    case Nil{}:
      {==}
    case +h <> +t:
      %app2_nil(t) : {h <> t == h <> _ : +List<Spec.Effect>}
      {==}

def pq(+rs: +List<Spec.Res>, +acc: +List<Spec.Effect>) -> Bool:
  Bool.and(w_ok(rs, acc), Spec.released_ok2(rs, acc))

def pq_down(+rs: +List<Spec.Res>, +acc: +List<Spec.Effect>, +hW: {w_ok(rs, acc) == True{} : Bool}, +hR: {Spec.released_ok2(rs, acc) == True{} : Bool}) -> {pq(rs, app2(acc, Nil{})) == True{} : Bool}:
  %app2_nil(acc) : {pq(rs, _) == True{} : Bool}
  and_i(w_ok(rs, acc), Spec.released_ok2(rs, acc), hW, hR)

def w_nr(+rs: +List<Spec.Res>, +acc: +List<Spec.Effect>, +x: Spec.Effect, +hnr: {nonrel(x) == True{} : Bool}, +hW: {w_ok(rs, acc) == True{} : Bool}) -> {w_ok(rs, sne(acc, x)) == True{} : Bool}:
  %w_sne(rs, acc, x) : {_ == True{} : Bool}
  and_i(w_ok(rs, acc), w_one(rs, x), hW, w1_nr(rs, x, hnr))

def pq_nr(+rs: +List<Spec.Res>, +acc: +List<Spec.Effect>, +x: Spec.Effect, +hnr: {nonrel(x) == True{} : Bool}, +hW: {w_ok(rs, acc) == True{} : Bool}, +hR: {Spec.released_ok2(rs, acc) == True{} : Bool}) -> {pq(rs, sne(acc, x)) == True{} : Bool}:
  and_i(w_ok(rs, sne(acc, x)), Spec.released_ok2(rs, sne(acc, x)), w_nr(rs, acc, x, hnr, hW), ro_nr(rs, acc, x, hnr, hR))


def wsn(+rs: +List<Spec.Res>, +acc: +List<Spec.Effect>, +x: Spec.Res, +f: Spec.Effect, +hnr: {nonrel(f) == True{} : Bool}, +hW: {w_ok(rs, acc) == True{} : Bool}) -> {w_ok(snoc(rs, x), sne(acc, f)) == True{} : Bool}:
  w_nr(snoc(rs, x), acc, f, hnr, w_snoc_rs(acc, rs, x, hW))

def pq_rsv_acc(+u: Bool, +clk: Nat, +ksku: Nat, +tot: Nat, +av: Nat, +rv: Nat, +sd: Nat, +rs: +List<Spec.Res>, +id: Nat, +sku: Nat, +qty: Nat, +ttl: Nat, +acc: +List<Spec.Effect>, +hW: {w_ok(rs, acc) == True{} : Bool}, +hR: {Spec.released_ok2(rs, acc) == True{} : Bool}, +hn: {Spec.find_res(rs, id) == Spec.NoRes{} : Spec.Look}) -> {pq(snoc(rs, Spec.Res{id, sku, qty, Spec.Held{}, Nat.add(clk, ttl), 0n, 0n}), sne(acc, Spec.FxReserved{id, sku, qty, Nat.add(clk, ttl)})) == True{} : Bool}:
  and_i(w_ok(snoc(rs, Spec.Res{id, sku, qty, Spec.Held{}, Nat.add(clk, ttl), 0n, 0n}), sne(acc, Spec.FxReserved{id, sku, qty, Nat.add(clk, ttl)})), Spec.released_ok2(snoc(rs, Spec.Res{id, sku, qty, Spec.Held{}, Nat.add(clk, ttl), 0n, 0n}), sne(acc, Spec.FxReserved{id, sku, qty, Nat.add(clk, ttl)})), wsn(rs, acc, Spec.Res{id, sku, qty, Spec.Held{}, Nat.add(clk, ttl), 0n, 0n}, Spec.FxReserved{id, sku, qty, Nat.add(clk, ttl)}, {==}, hW), ro_snoc(rs, sne(acc, Spec.FxReserved{id, sku, qty, Nat.add(clk, ttl)}), Spec.Res{id, sku, qty, Spec.Held{}, Nat.add(clk, ttl), 0n, 0n}, ro_nr(rs, acc, Spec.FxReserved{id, sku, qty, Nat.add(clk, ttl)}, {==}, hR), and_i(Nat.is_eq(Spec.released_count(sne(acc, Spec.FxReserved{id, sku, qty, Nat.add(clk, ttl)}), id), 0n), Spec.released_qty_ok(sne(acc, Spec.FxReserved{id, sku, qty, Nat.add(clk, ttl)}), id, qty), eq_back(Spec.released_count(sne(acc, Spec.FxReserved{id, sku, qty, Nat.add(clk, ttl)}), id), 0n, count0(sne(acc, Spec.FxReserved{id, sku, qty, Nat.add(clk, ttl)}), rs, id, w_nr(rs, acc, Spec.FxReserved{id, sku, qty, Nat.add(clk, ttl)}, {==}, hW), hn)), qok0(sne(acc, Spec.FxReserved{id, sku, qty, Nat.add(clk, ttl)}), rs, id, qty, w_nr(rs, acc, Spec.FxReserved{id, sku, qty, Nat.add(clk, ttl)}, {==}, hW), hn))))



def rf_pick(+g: Bool, +h: Spec.Res, +acc: +List<Spec.Effect>, +r: Spec.Res, +rest: Spec.Look, +hh: {recok(acc, h) == True{} : Bool}, +hf: {Spec.find_pick(h, g, rest) == Spec.Got{r} : Spec.Look}, ih: {rest == Spec.Got{r} : Spec.Look} -> {recok(acc, r) == True{} : Bool}) -> {recok(acc, r) == True{} : Bool}:
  match g:
    case True{}:
      %got_inj(h, r, hf) : {recok(acc, _) == True{} : Bool}
      hh
    case False{}:
      ih(hf)

def ro_find(+rs: +List<Spec.Res>, +acc: +List<Spec.Effect>, +id: Nat, +r: Spec.Res, +h: {Spec.released_ok2(rs, acc) == True{} : Bool}, +hf: {Spec.find_res(rs, id) == Spec.Got{r} : Spec.Look}) -> {recok(acc, r) == True{} : Bool}:
  match rs:
    case Nil{}:
      nr_absurd({recok(acc, r) == True{} : Bool}, r, hf)
    case +h2 <> +t:
      rf_pick(Nat.is_eq(Spec.r_id(h2), id), h2, acc, r, Spec.find_res(t, id), and_l(recok(acc, h2), Spec.released_ok2(t, acc), h), hf, hf2 => ro_find(t, acc, id, r, and_r(recok(acc, h2), Spec.released_ok2(t, acc), h), hf2))

def recok_id(+acc: +List<Spec.Effect>, +i: Nat, +id: Nat, +sku: Nat, +qty: Nat, +x1: Spec.Status, +x2: Spec.Status, +exp: Nat, +cf1: Nat, +cf2: Nat, +ret: Nat, +hi: {i == id : Nat}, +h: {recok(acc, Spec.Res{i, sku, qty, x1, exp, cf1, ret}) == True{} : Bool}) -> {recok(acc, Spec.Res{id, sku, qty, x2, exp, cf2, ret}) == True{} : Bool}:
  %hi : {recok(acc, Spec.Res{_, sku, qty, x2, exp, cf2, ret}) == True{} : Bool}
  h

def rop_pp(+g: Bool, +h: Spec.Res, +x: Spec.Res, +t: +List<Spec.Res>, +rest: +List<Spec.Res>, +acc: +List<Spec.Effect>, +hh: {recok(acc, h) == True{} : Bool}, +ht: {Spec.released_ok2(t, acc) == True{} : Bool}, +hx: {recok(acc, x) == True{} : Bool}, +hr: {Spec.released_ok2(rest, acc) == True{} : Bool}) -> {Spec.released_ok2(Spec.put_pick(g, h, x, t, rest), acc) == True{} : Bool}:
  match g:
    case True{}:
      and_i(recok(acc, x), Spec.released_ok2(t, acc), hx, ht)
    case False{}:
      and_i(recok(acc, h), Spec.released_ok2(rest, acc), hh, hr)

def ro_put_gen(+rs: +List<Spec.Res>, +acc: +List<Spec.Effect>, +id: Nat, +x: Spec.Res, +h1: {Spec.released_ok2(rs, acc) == True{} : Bool}, +h2: {recok(acc, x) == True{} : Bool}) -> {Spec.released_ok2(Spec.put_res(rs, id, x), acc) == True{} : Bool}:
  match rs:
    case Nil{}:
      {==}
    case +h <> +t:
      rop_pp(Nat.is_eq(Spec.r_id(h), id), h, x, t, Spec.put_res(t, id, x), acc, and_l(recok(acc, h), Spec.released_ok2(t, acc), h1), and_r(recok(acc, h), Spec.released_ok2(t, acc), h1), h2, ro_put_gen(t, acc, id, x, and_r(recok(acc, h), Spec.released_ok2(t, acc), h1), h2))

def lq_put_f(+rs: +List<Spec.Res>, +id: Nat, +x: Spec.Res, +i: Nat, +q: Nat, +hx: {Spec.r_id(x) == id : Nat}, +hn: {Nat.is_eq(i, id) == False{} : Bool}, +h: {look_q(Spec.find_res(rs, i), q) == True{} : Bool}) -> {look_q(Spec.find_res(Spec.put_res(rs, id, x), i), q) == True{} : Bool}:
  %symL(Spec.find_res(Spec.put_res(rs, id, x), i), Spec.find_res(rs, i), find_put_ne(rs, id, x, i, hx, hn)) : {look_q(_, q) == True{} : Bool}
  h

def lq_put_t(+rs: +List<Spec.Res>, +id: Nat, +x: Spec.Res, +r0: Spec.Res, +i: Nat, +q: Nat, +hx: {Spec.r_id(x) == id : Nat}, +hq: {Spec.r_qty(x) == Spec.r_qty(r0) : Nat}, +hf: {Spec.find_res(rs, id) == Spec.Got{r0} : Spec.Look}, +hj: {Nat.is_eq(i, id) == True{} : Bool}, +h: {look_q(Spec.find_res(rs, i), q) == True{} : Bool}) -> {look_q(Spec.find_res(Spec.put_res(rs, id, x), i), q) == True{} : Bool}:
  %symL(Spec.find_res(Spec.put_res(rs, id, x), i), Spec.Got{x}, trL(Spec.find_res(Spec.put_res(rs, id, x), i), Spec.find_res(Spec.put_res(rs, id, x), id), Spec.Got{x}, symL(Spec.find_res(Spec.put_res(rs, id, x), id), Spec.find_res(Spec.put_res(rs, id, x), i), Equal.cong(Nat, Spec.Look, y => Spec.find_res(Spec.put_res(rs, id, x), y), id, i, symN(i, id, eq_prop(i, id, hj)))), find_put_eq(rs, id, x, r0, hx, hf))) : {look_q(_, q) == True{} : Bool}
  %symN(Spec.r_qty(x), Spec.r_qty(r0), hq) : {Nat.is_eq(_, q) == True{} : Bool}
  %trL(Spec.find_res(rs, i), Spec.find_res(rs, id), Spec.Got{r0}, symL(Spec.find_res(rs, id), Spec.find_res(rs, i), Equal.cong(Nat, Spec.Look, y => Spec.find_res(rs, y), id, i, symN(i, id, eq_prop(i, id, hj)))), hf) : {look_q(_, q) == True{} : Bool}
  h

def lq_put(+rs: +List<Spec.Res>, +id: Nat, +x: Spec.Res, +r0: Spec.Res, +i: Nat, +q: Nat, +hx: {Spec.r_id(x) == id : Nat}, +hq: {Spec.r_qty(x) == Spec.r_qty(r0) : Nat}, +hf: {Spec.find_res(rs, id) == Spec.Got{r0} : Spec.Look}, +h: {look_q(Spec.find_res(rs, i), q) == True{} : Bool}) -> {look_q(Spec.find_res(Spec.put_res(rs, id, x), i), q) == True{} : Bool}:
  bcase(Nat.is_eq(i, id), {look_q(Spec.find_res(Spec.put_res(rs, id, x), i), q) == True{} : Bool}, hj => lq_put_t(rs, id, x, r0, i, q, hx, hq, hf, hj, h), hn => lq_put_f(rs, id, x, i, q, hx, hn, h))

def w1_put(+rs: +List<Spec.Res>, +id: Nat, +x: Spec.Res, +r0: Spec.Res, +y: Spec.Effect, +hx: {Spec.r_id(x) == id : Nat}, +hq: {Spec.r_qty(x) == Spec.r_qty(r0) : Nat}, +hf: {Spec.find_res(rs, id) == Spec.Got{r0} : Spec.Look}, +h: {w_one(rs, y) == True{} : Bool}) -> {w_one(Spec.put_res(rs, id, x), y) == True{} : Bool}:
  match y:
    case Spec.FxReleased{i, q}:
      lq_put(rs, id, x, r0, i, q, hx, hq, hf, h)
    case Spec.FxReserved{a, b, c, d}:
      {==}
    case Spec.FxConfirmed{a}:
      {==}
    case Spec.FxRejected{a, b}:
      {==}

def w_put(+acc: +List<Spec.Effect>, +rs: +List<Spec.Res>, +id: Nat, +x: Spec.Res, +r0: Spec.Res, +hx: {Spec.r_id(x) == id : Nat}, +hq: {Spec.r_qty(x) == Spec.r_qty(r0) : Nat}, +hf: {Spec.find_res(rs, id) == Spec.Got{r0} : Spec.Look}, +h: {w_ok(rs, acc) == True{} : Bool}) -> {w_ok(Spec.put_res(rs, id, x), acc) == True{} : Bool}:
  match acc:
    case Nil{}:
      {==}
    case +y <> +t:
      and_i(w_one(Spec.put_res(rs, id, x), y), w_ok(Spec.put_res(rs, id, x), t), w1_put(rs, id, x, r0, y, hx, hq, hf, and_l(w_one(rs, y), w_ok(rs, t), h)), w_put(t, rs, id, x, r0, hx, hq, hf, and_r(w_one(rs, y), w_ok(rs, t), h)))


def pq_conf_acc(+u: Bool, +clk: Nat, +ksku: Nat, +tot: Nat, +av: Nat, +rv: Nat, +sd: Nat, +rs: +List<Spec.Res>, +id: Nat, +i: Nat, +sku: Nat, +qty: Nat, +exp: Nat, +cf: Nat, +ret: Nat, +acc: +List<Spec.Effect>, +hW: {w_ok(rs, acc) == True{} : Bool}, +hR: {Spec.released_ok2(rs, acc) == True{} : Bool}, +hf: {Spec.find_res(rs, id) == Spec.Got{Spec.Res{i, sku, qty, Spec.Held{}, exp, cf, ret}} : Spec.Look}) -> {pq(Spec.put_res(rs, id, Spec.Res{id, sku, qty, Spec.Confirmed{}, exp, clk, ret}), sne(acc, Spec.FxConfirmed{id})) == True{} : Bool}:
  and_i(w_ok(Spec.put_res(rs, id, Spec.Res{id, sku, qty, Spec.Confirmed{}, exp, clk, ret}), sne(acc, Spec.FxConfirmed{id})), Spec.released_ok2(Spec.put_res(rs, id, Spec.Res{id, sku, qty, Spec.Confirmed{}, exp, clk, ret}), sne(acc, Spec.FxConfirmed{id})), w_nr(Spec.put_res(rs, id, Spec.Res{id, sku, qty, Spec.Confirmed{}, exp, clk, ret}), acc, Spec.FxConfirmed{id}, {==}, w_put(acc, rs, id, Spec.Res{id, sku, qty, Spec.Confirmed{}, exp, clk, ret}, Spec.Res{i, sku, qty, Spec.Held{}, exp, cf, ret}, {==}, {==}, hf, hW)), ro_put_gen(rs, sne(acc, Spec.FxConfirmed{id}), id, Spec.Res{id, sku, qty, Spec.Confirmed{}, exp, clk, ret}, ro_nr(rs, acc, Spec.FxConfirmed{id}, {==}, hR), recok_id(sne(acc, Spec.FxConfirmed{id}), i, id, sku, qty, Spec.Held{}, Spec.Confirmed{}, exp, cf, clk, ret, eq_prop(i, id, find_id(rs, id, Spec.Res{i, sku, qty, Spec.Held{}, exp, cf, ret}, hf)), ro_find(rs, sne(acc, Spec.FxConfirmed{id}), id, Spec.Res{i, sku, qty, Spec.Held{}, exp, cf, ret}, ro_nr(rs, acc, Spec.FxConfirmed{id}, {==}, hR), hf))))


def pq_conf2(+x: Spec.Status, +due: Bool, +u: Bool, +clk: Nat, +ksku: Nat, +tot: Nat, +av: Nat, +rv: Nat, +sd: Nat, +rs: +List<Spec.Res>, +id: Nat, +i: Nat, +sku: Nat, +qty: Nat, +exp: Nat, +cf: Nat, +ret: Nat, +acc: +List<Spec.Effect>, +hW: {w_ok(rs, acc) == True{} : Bool}, +hR: {Spec.released_ok2(rs, acc) == True{} : Bool}, +hf: {Spec.find_res(rs, id) == Spec.Got{Spec.Res{i, sku, qty, x, exp, cf, ret}} : Spec.Look}) -> {pq(Spec.res_of(Spec.st(Code.conf2(x, due, mkS(u, clk, ksku, tot, av, rv, sd, rs), id, sku, qty, exp, ret))), app2(acc, Spec.fx_data(Spec.fx(Code.conf2(x, due, mkS(u, clk, ksku, tot, av, rv, sd, rs), id, sku, qty, exp, ret))))) == True{} : Bool}:
  match x due:
    case Spec.Held{} False{}:
      pq_conf_acc(u, clk, ksku, tot, av, rv, sd, rs, id, i, sku, qty, exp, cf, ret, acc, hW, hR, hf)
    case Spec.Held{} True{}:
      pq_nr(rs, acc, Spec.FxRejected{id, Spec.TooLate{}}, {==}, hW, hR)
    case Spec.Confirmed{} _:
      pq_nr(rs, acc, Spec.FxRejected{id, Spec.NotHeld{}}, {==}, hW, hR)
    case Spec.Expired{} _:
      pq_nr(rs, acc, Spec.FxRejected{id, Spec.NotHeld{}}, {==}, hW, hR)

def pq_conf1(+l: Spec.Look, +u: Bool, +clk: Nat, +ksku: Nat, +tot: Nat, +av: Nat, +rv: Nat, +sd: Nat, +rs: +List<Spec.Res>, +id: Nat, +acc: +List<Spec.Effect>, +hW: {w_ok(rs, acc) == True{} : Bool}, +hR: {Spec.released_ok2(rs, acc) == True{} : Bool}, +el: {Spec.find_res(rs, id) == l : Spec.Look}) -> {pq(Spec.res_of(Spec.st(Code.conf1(l, mkS(u, clk, ksku, tot, av, rv, sd, rs), id))), app2(acc, Spec.fx_data(Spec.fx(Code.conf1(l, mkS(u, clk, ksku, tot, av, rv, sd, rs), id))))) == True{} : Bool}:
  match l:
    case Spec.NoRes{}:
      pq_nr(rs, acc, Spec.FxRejected{id, Spec.UnknownReservation{}}, {==}, hW, hR)
    case Spec.Got{Spec.Res{i, sku, qty, x, exp, cf, ret}}:
      pq_conf2(x, Nat.is_le(exp, clk), u, clk, ksku, tot, av, rv, sd, rs, id, i, sku, qty, exp, cf, ret, acc, hW, hR, el)

def pq_gc(+u: Bool, +clk: Nat, +ksku: Nat, +tot: Nat, +av: Nat, +rv: Nat, +sd: Nat, +rs: +List<Spec.Res>, +id: Nat, +acc: +List<Spec.Effect>, +hW: {w_ok(rs, acc) == True{} : Bool}, +hR: {Spec.released_ok2(rs, acc) == True{} : Bool}) -> {pq(Spec.res_of(Spec.st(Code.step(mkS(u, clk, ksku, tot, av, rv, sd, rs), Spec.Confirm{id}))), app2(acc, Spec.fx_data(Spec.fx(Code.step(mkS(u, clk, ksku, tot, av, rv, sd, rs), Spec.Confirm{id}))))) == True{} : Bool}:
  match u:
    case False{}:
      pq_down(rs, acc, hW, hR)
    case True{}:
      pq_conf1(Spec.find_res(rs, id), u, clk, ksku, tot, av, rv, sd, rs, id, acc, hW, hR, {==})

def rc_self(+id: Nat, +q: Nat) -> {Spec.rc_pick(Spec.FxReleased{id, q}, id, 0n) == 1n : Nat}:
  %symB(Nat.is_eq(id, id), True{}, eq_refl(id)) : {Spec.rc_hit(_, 0n) == 1n : Nat}
  {==}

def rq_self(+id: Nat, +q: Nat) -> {Spec.rq_pick(Spec.FxReleased{id, q}, id, q) == True{} : Bool}:
  %symB(Nat.is_eq(id, id), True{}, eq_refl(id)) : {Spec.rq_hit(_, Nat.is_eq(q, q)) == True{} : Bool}
  eq_refl(q)

def rcp_miss(+f0: Nat, +q0: Nat, +i: Nat, +hne: {Nat.is_eq(f0, i) == False{} : Bool}) -> {Spec.rc_pick(Spec.FxReleased{f0, q0}, i, 0n) == 0n : Nat}:
  %symB(Nat.is_eq(f0, i), False{}, hne) : {Spec.rc_hit(_, 0n) == 0n : Nat}
  {==}

def rqp_miss(+f0: Nat, +q0: Nat, +i: Nat, +q: Nat, +hne: {Nat.is_eq(f0, i) == False{} : Bool}) -> {Spec.rq_pick(Spec.FxReleased{f0, q0}, i, q) == True{} : Bool}:
  %symB(Nat.is_eq(f0, i), False{}, hne) : {Spec.rq_hit(_, Nat.is_eq(q0, q)) == True{} : Bool}
  {==}

def rc_sne0(+acc: +List<Spec.Effect>, +x: Spec.Effect, +i: Nat, +hc: {Spec.rc_pick(x, i, 0n) == 0n : Nat}) -> {Spec.released_count(sne(acc, x), i) == Spec.released_count(acc, i) : Nat}:
  trN(Spec.released_count(sne(acc, x), i), Nat.add(Spec.released_count(acc, i), Spec.rc_pick(x, i, 0n)), Spec.released_count(acc, i), symN(Nat.add(Spec.released_count(acc, i), Spec.rc_pick(x, i, 0n)), Spec.released_count(sne(acc, x), i), rc_sne(acc, x, i)), trN(Nat.add(Spec.released_count(acc, i), Spec.rc_pick(x, i, 0n)), Nat.add(Spec.released_count(acc, i), 0n), Spec.released_count(acc, i), cong_add_r(Spec.rc_pick(x, i, 0n), 0n, Spec.released_count(acc, i), hc), symN(Spec.released_count(acc, i), Nat.add(Spec.released_count(acc, i), 0n), az(Spec.released_count(acc, i)))))

def qok_sne0(+acc: +List<Spec.Effect>, +x: Spec.Effect, +i: Nat, +q: Nat, +hq: {Spec.rq_pick(x, i, q) == True{} : Bool}) -> {Spec.released_qty_ok(sne(acc, x), i, q) == Spec.released_qty_ok(acc, i, q) : Bool}:
  %qok_sne(acc, x, i, q) : {_ == Spec.released_qty_ok(acc, i, q) : Bool}
  %symB(Spec.rq_pick(x, i, q), True{}, hq) : {Bool.and(Spec.released_qty_ok(acc, i, q), _) == Spec.released_qty_ok(acc, i, q) : Bool}
  %and_t_r(Spec.released_qty_ok(acc, i, q)) : {_ == Spec.released_qty_ok(acc, i, q) : Bool}
  {==}

def recok_gen(+acc: +List<Spec.Effect>, +x: Spec.Effect, +r: Spec.Res, +hc: {Spec.rc_pick(x, Spec.r_id(r), 0n) == 0n : Nat}, +hq: {Spec.rq_pick(x, Spec.r_id(r), Spec.r_qty(r)) == True{} : Bool}, +h: {recok(acc, r) == True{} : Bool}) -> {recok(sne(acc, x), r) == True{} : Bool}:
  %symN(Spec.released_count(sne(acc, x), Spec.r_id(r)), Spec.released_count(acc, Spec.r_id(r)), rc_sne0(acc, x, Spec.r_id(r), hc)) : {Bool.and(Nat.is_eq(_, Spec.r_ret(r)), Spec.released_qty_ok(sne(acc, x), Spec.r_id(r), Spec.r_qty(r))) == True{} : Bool}
  %symB(Spec.released_qty_ok(sne(acc, x), Spec.r_id(r), Spec.r_qty(r)), Spec.released_qty_ok(acc, Spec.r_id(r), Spec.r_qty(r)), qok_sne0(acc, x, Spec.r_id(r), Spec.r_qty(r), hq)) : {Bool.and(Nat.is_eq(Spec.released_count(acc, Spec.r_id(r)), Spec.r_ret(r)), _) == True{} : Bool}
  h

def recok_keep(+acc: +List<Spec.Effect>, +f0: Nat, +q0: Nat, +j: Spec.Res, +hne: {Nat.is_eq(f0, Spec.r_id(j)) == False{} : Bool}, +h: {recok(acc, j) == True{} : Bool}) -> {recok(sne(acc, Spec.FxReleased{f0, q0}), j) == True{} : Bool}:
  recok_gen(acc, Spec.FxReleased{f0, q0}, j, rcp_miss(f0, q0, Spec.r_id(j), hne), rqp_miss(f0, q0, Spec.r_id(j), Spec.r_qty(j), hne), h)

def ro_keep(+rs: +List<Spec.Res>, +acc: +List<Spec.Effect>, +f0: Nat, +q0: Nat, +hno: {Spec.has_id(rs, f0) == False{} : Bool}, +h: {Spec.released_ok2(rs, acc) == True{} : Bool}) -> {Spec.released_ok2(rs, sne(acc, Spec.FxReleased{f0, q0})) == True{} : Bool}:
  match rs:
    case Nil{}:
      {==}
    case +r <> +t:
      and_i(recok(sne(acc, Spec.FxReleased{f0, q0}), r), Spec.released_ok2(t, sne(acc, Spec.FxReleased{f0, q0})), recok_keep(acc, f0, q0, r, eq_f_sym(Spec.r_id(r), f0, or_f_l(Nat.is_eq(Spec.r_id(r), f0), Spec.has_id(t, f0), hno)), and_l(recok(acc, r), Spec.released_ok2(t, acc), h)), ro_keep(t, acc, f0, q0, or_f_r(Nat.is_eq(Spec.r_id(r), f0), Spec.has_id(t, f0), hno), and_r(recok(acc, r), Spec.released_ok2(t, acc), h)))

def hid_via(+t: +List<Spec.Res>, +a: Nat, +b: Nat, +e: {a == b : Nat}, +h: {Spec.has_id(t, a) == False{} : Bool}) -> {Spec.has_id(t, b) == False{} : Bool}:
  %e : {Spec.has_id(t, _) == False{} : Bool}
  h



def rex_pick(+g: Bool, +h: Spec.Res, +x: Spec.Res, +t: +List<Spec.Res>, +rest: +List<Spec.Res>, +acc: +List<Spec.Effect>, +id: Nat, +q0: Nat, +r0: Spec.Res, +hg: {Nat.is_eq(Spec.r_id(h), id) == g : Bool}, +hxk: {recok(sne(acc, Spec.FxReleased{id, q0}), x) == True{} : Bool}, +hu: {Spec.uniq(h <> t) == True{} : Bool}, +hR: {Spec.released_ok2(h <> t, acc) == True{} : Bool}, +hf: {Spec.find_pick(h, g, Spec.find_res(t, id)) == Spec.Got{r0} : Spec.Look}, ih: {Spec.find_res(t, id) == Spec.Got{r0} : Spec.Look} -> {Spec.released_ok2(rest, sne(acc, Spec.FxReleased{id, q0})) == True{} : Bool}) -> {Spec.released_ok2(Spec.put_pick(g, h, x, t, rest), sne(acc, Spec.FxReleased{id, q0})) == True{} : Bool}:
  match g:
    case True{}:
      and_i(recok(sne(acc, Spec.FxReleased{id, q0}), x), Spec.released_ok2(t, sne(acc, Spec.FxReleased{id, q0})), hxk, ro_keep(t, acc, id, q0, hid_via(t, Spec.r_id(h), id, eq_prop(Spec.r_id(h), id, hg), not_t(Spec.has_id(t, Spec.r_id(h)), and_l(Bool.not(Spec.has_id(t, Spec.r_id(h))), Spec.uniq(t), hu))), and_r(recok(acc, h), Spec.released_ok2(t, acc), hR)))
    case False{}:
      and_i(recok(sne(acc, Spec.FxReleased{id, q0}), h), Spec.released_ok2(rest, sne(acc, Spec.FxReleased{id, q0})), recok_keep(acc, id, q0, h, eq_f_sym(Spec.r_id(h), id, hg), and_l(recok(acc, h), Spec.released_ok2(t, acc), hR)), ih(hf))

def ro_exp(+rs: +List<Spec.Res>, +acc: +List<Spec.Effect>, +id: Nat, +q0: Nat, +x: Spec.Res, +r0: Spec.Res, +hxk: {recok(sne(acc, Spec.FxReleased{id, q0}), x) == True{} : Bool}, +hu: {Spec.uniq(rs) == True{} : Bool}, +hf: {Spec.find_res(rs, id) == Spec.Got{r0} : Spec.Look}, +h: {Spec.released_ok2(rs, acc) == True{} : Bool}) -> {Spec.released_ok2(Spec.put_res(rs, id, x), sne(acc, Spec.FxReleased{id, q0})) == True{} : Bool}:
  match rs:
    case Nil{}:
      {==}
    case +r <> +t:
      rex_pick(Nat.is_eq(Spec.r_id(r), id), r, x, t, Spec.put_res(t, id, x), acc, id, q0, r0, {==}, hxk, hu, h, hf, hf2 => ro_exp(t, acc, id, q0, x, r0, hxk, and_r(Bool.not(Spec.has_id(t, Spec.r_id(r))), Spec.uniq(t), hu), hf2, and_r(recok(acc, r), Spec.released_ok2(t, acc), h)))

def w1_exp(+rs: +List<Spec.Res>, +id: Nat, +qty: Nat, +x: Spec.Res, +r0: Spec.Res, +hx: {Spec.r_id(x) == id : Nat}, +hq: {Spec.r_qty(x) == qty : Nat}, +hf: {Spec.find_res(rs, id) == Spec.Got{r0} : Spec.Look}) -> {w_one(Spec.put_res(rs, id, x), Spec.FxReleased{id, qty}) == True{} : Bool}:
  %symL(Spec.find_res(Spec.put_res(rs, id, x), id), Spec.Got{x}, find_put_eq(rs, id, x, r0, hx, hf)) : {look_q(_, qty) == True{} : Bool}
  eq_back(Spec.r_qty(x), qty, hq)

def qk_exp(+acc: +List<Spec.Effect>, +id: Nat, +qty: Nat, +hq: {Spec.released_qty_ok(acc, id, qty) == True{} : Bool}) -> {Spec.released_qty_ok(sne(acc, Spec.FxReleased{id, qty}), id, qty) == True{} : Bool}:
  %qok_sne(acc, Spec.FxReleased{id, qty}, id, qty) : {_ == True{} : Bool}
  %symB(Spec.rq_pick(Spec.FxReleased{id, qty}, id, qty), True{}, rq_self(id, qty)) : {Bool.and(Spec.released_qty_ok(acc, id, qty), _) == True{} : Bool}
  and_i(Spec.released_qty_ok(acc, id, qty), True{}, hq, {==})

def hxk_exp(+acc: +List<Spec.Effect>, +id: Nat, +qty: Nat, +ret: Nat, +hc: {Spec.released_count(acc, id) == ret : Nat}, +hq: {Spec.released_qty_ok(acc, id, qty) == True{} : Bool}) -> {Bool.and(Nat.is_eq(Spec.released_count(sne(acc, Spec.FxReleased{id, qty}), id), Nat.add(ret, 1n)), Spec.released_qty_ok(sne(acc, Spec.FxReleased{id, qty}), id, qty)) == True{} : Bool}:
  and_i(Nat.is_eq(Spec.released_count(sne(acc, Spec.FxReleased{id, qty}), id), Nat.add(ret, 1n)), Spec.released_qty_ok(sne(acc, Spec.FxReleased{id, qty}), id, qty), eq_back(Spec.released_count(sne(acc, Spec.FxReleased{id, qty}), id), Nat.add(ret, 1n), trN(Spec.released_count(sne(acc, Spec.FxReleased{id, qty}), id), Nat.add(Spec.released_count(acc, id), 1n), Nat.add(ret, 1n), trN(Spec.released_count(sne(acc, Spec.FxReleased{id, qty}), id), Nat.add(Spec.released_count(acc, id), Spec.rc_pick(Spec.FxReleased{id, qty}, id, 0n)), Nat.add(Spec.released_count(acc, id), 1n), symN(Nat.add(Spec.released_count(acc, id), Spec.rc_pick(Spec.FxReleased{id, qty}, id, 0n)), Spec.released_count(sne(acc, Spec.FxReleased{id, qty}), id), rc_sne(acc, Spec.FxReleased{id, qty}, id)), cong_add_r(Spec.rc_pick(Spec.FxReleased{id, qty}, id, 0n), 1n, Spec.released_count(acc, id), rc_self(id, qty))), cong_add_l(Spec.released_count(acc, id), ret, 1n, hc))), qk_exp(acc, id, qty, hq))

def w_exp(+rs: +List<Spec.Res>, +acc: +List<Spec.Effect>, +id: Nat, +i: Nat, +sku: Nat, +qty: Nat, +exp: Nat, +cf: Nat, +ret: Nat, +hW: {w_ok(rs, acc) == True{} : Bool}, +hf: {Spec.find_res(rs, id) == Spec.Got{Spec.Res{i, sku, qty, Spec.Held{}, exp, cf, ret}} : Spec.Look}) -> {w_ok(Spec.put_res(rs, id, Spec.Res{id, sku, qty, Spec.Expired{}, exp, cf, Nat.add(ret, 1n)}), sne(acc, Spec.FxReleased{id, qty})) == True{} : Bool}:
  %w_sne(Spec.put_res(rs, id, Spec.Res{id, sku, qty, Spec.Expired{}, exp, cf, Nat.add(ret, 1n)}), acc, Spec.FxReleased{id, qty}) : {_ == True{} : Bool}
  and_i(w_ok(Spec.put_res(rs, id, Spec.Res{id, sku, qty, Spec.Expired{}, exp, cf, Nat.add(ret, 1n)}), acc), w_one(Spec.put_res(rs, id, Spec.Res{id, sku, qty, Spec.Expired{}, exp, cf, Nat.add(ret, 1n)}), Spec.FxReleased{id, qty}), w_put(acc, rs, id, Spec.Res{id, sku, qty, Spec.Expired{}, exp, cf, Nat.add(ret, 1n)}, Spec.Res{i, sku, qty, Spec.Held{}, exp, cf, ret}, {==}, {==}, hf, hW), w1_exp(rs, id, qty, Spec.Res{id, sku, qty, Spec.Expired{}, exp, cf, Nat.add(ret, 1n)}, Spec.Res{i, sku, qty, Spec.Held{}, exp, cf, ret}, {==}, {==}, hf))

def pq_exp_acc(+u: Bool, +clk: Nat, +ksku: Nat, +tot: Nat, +av: Nat, +rv: Nat, +sd: Nat, +rs: +List<Spec.Res>, +id: Nat, +i: Nat, +sku: Nat, +qty: Nat, +exp: Nat, +cf: Nat, +ret: Nat, +acc: +List<Spec.Effect>, +hW: {w_ok(rs, acc) == True{} : Bool}, +hR: {Spec.released_ok2(rs, acc) == True{} : Bool}, +hu: {Spec.uniq(rs) == True{} : Bool}, +hf: {Spec.find_res(rs, id) == Spec.Got{Spec.Res{i, sku, qty, Spec.Held{}, exp, cf, ret}} : Spec.Look}) -> {pq(Spec.put_res(rs, id, Spec.Res{id, sku, qty, Spec.Expired{}, exp, cf, Nat.add(ret, 1n)}), sne(acc, Spec.FxReleased{id, qty})) == True{} : Bool}:
  and_i(w_ok(Spec.put_res(rs, id, Spec.Res{id, sku, qty, Spec.Expired{}, exp, cf, Nat.add(ret, 1n)}), sne(acc, Spec.FxReleased{id, qty})), Spec.released_ok2(Spec.put_res(rs, id, Spec.Res{id, sku, qty, Spec.Expired{}, exp, cf, Nat.add(ret, 1n)}), sne(acc, Spec.FxReleased{id, qty})), w_exp(rs, acc, id, i, sku, qty, exp, cf, ret, hW, hf), ro_exp(rs, acc, id, qty, Spec.Res{id, sku, qty, Spec.Expired{}, exp, cf, Nat.add(ret, 1n)}, Spec.Res{i, sku, qty, Spec.Held{}, exp, cf, ret}, hxk_exp(acc, id, qty, ret, eq_prop(Spec.released_count(acc, id), ret, and_l(Nat.is_eq(Spec.released_count(acc, id), ret), Spec.released_qty_ok(acc, id, qty), recok_id(acc, i, id, sku, qty, Spec.Held{}, Spec.Held{}, exp, cf, cf, ret, eq_prop(i, id, find_id(rs, id, Spec.Res{i, sku, qty, Spec.Held{}, exp, cf, ret}, hf)), ro_find(rs, acc, id, Spec.Res{i, sku, qty, Spec.Held{}, exp, cf, ret}, hR, hf)))), and_r(Nat.is_eq(Spec.released_count(acc, id), ret), Spec.released_qty_ok(acc, id, qty), recok_id(acc, i, id, sku, qty, Spec.Held{}, Spec.Held{}, exp, cf, cf, ret, eq_prop(i, id, find_id(rs, id, Spec.Res{i, sku, qty, Spec.Held{}, exp, cf, ret}, hf)), ro_find(rs, acc, id, Spec.Res{i, sku, qty, Spec.Held{}, exp, cf, ret}, hR, hf)))), hu, hf, hR))


def pq_exp2(+x: Spec.Status, +due: Bool, +u: Bool, +clk: Nat, +ksku: Nat, +tot: Nat, +av: Nat, +rv: Nat, +sd: Nat, +rs: +List<Spec.Res>, +id: Nat, +i: Nat, +sku: Nat, +qty: Nat, +exp: Nat, +cf: Nat, +ret: Nat, +acc: +List<Spec.Effect>, +hi: {Spec.inv(mkS(u, clk, ksku, tot, av, rv, sd, rs)) == True{} : Bool}, +hW: {w_ok(rs, acc) == True{} : Bool}, +hR: {Spec.released_ok2(rs, acc) == True{} : Bool}, +hf: {Spec.find_res(rs, id) == Spec.Got{Spec.Res{i, sku, qty, x, exp, cf, ret}} : Spec.Look}) -> {pq(Spec.res_of(Spec.st(Code.exp2(x, due, mkS(u, clk, ksku, tot, av, rv, sd, rs), id, sku, qty, exp, cf, ret))), app2(acc, Spec.fx_data(Spec.fx(Code.exp2(x, due, mkS(u, clk, ksku, tot, av, rv, sd, rs), id, sku, qty, exp, cf, ret))))) == True{} : Bool}:
  match x due:
    case Spec.Held{} True{}:
      pq_exp_acc(u, clk, ksku, tot, av, rv, sd, rs, id, i, sku, qty, exp, cf, ret, acc, hW, hR, and_l(Spec.uniq(rs), Spec.all_rec(Spec.PSku{}, ksku, rs), i_a2(mkS(u, clk, ksku, tot, av, rv, sd, rs), hi)), hf)
    case Spec.Held{} False{}:
      pq_nr(rs, acc, Spec.FxRejected{id, Spec.NotYet{}}, {==}, hW, hR)
    case Spec.Confirmed{} _:
      pq_nr(rs, acc, Spec.FxRejected{id, Spec.NotHeld{}}, {==}, hW, hR)
    case Spec.Expired{} _:
      pq_nr(rs, acc, Spec.FxRejected{id, Spec.NotHeld{}}, {==}, hW, hR)

def pq_exp1(+l: Spec.Look, +u: Bool, +clk: Nat, +ksku: Nat, +tot: Nat, +av: Nat, +rv: Nat, +sd: Nat, +rs: +List<Spec.Res>, +id: Nat, +acc: +List<Spec.Effect>, +hi: {Spec.inv(mkS(u, clk, ksku, tot, av, rv, sd, rs)) == True{} : Bool}, +hW: {w_ok(rs, acc) == True{} : Bool}, +hR: {Spec.released_ok2(rs, acc) == True{} : Bool}, +el: {Spec.find_res(rs, id) == l : Spec.Look}) -> {pq(Spec.res_of(Spec.st(Code.exp1(l, mkS(u, clk, ksku, tot, av, rv, sd, rs), id))), app2(acc, Spec.fx_data(Spec.fx(Code.exp1(l, mkS(u, clk, ksku, tot, av, rv, sd, rs), id))))) == True{} : Bool}:
  match l:
    case Spec.NoRes{}:
      pq_nr(rs, acc, Spec.FxRejected{id, Spec.UnknownReservation{}}, {==}, hW, hR)
    case Spec.Got{Spec.Res{i, sku, qty, x, exp, cf, ret}}:
      pq_exp2(x, Nat.is_le(exp, clk), u, clk, ksku, tot, av, rv, sd, rs, id, i, sku, qty, exp, cf, ret, acc, hi, hW, hR, el)

def pq_ge(+u: Bool, +clk: Nat, +ksku: Nat, +tot: Nat, +av: Nat, +rv: Nat, +sd: Nat, +rs: +List<Spec.Res>, +id: Nat, +acc: +List<Spec.Effect>, +hi: {Spec.inv(mkS(u, clk, ksku, tot, av, rv, sd, rs)) == True{} : Bool}, +hW: {w_ok(rs, acc) == True{} : Bool}, +hR: {Spec.released_ok2(rs, acc) == True{} : Bool}) -> {pq(Spec.res_of(Spec.st(Code.step(mkS(u, clk, ksku, tot, av, rv, sd, rs), Spec.Expire{id}))), app2(acc, Spec.fx_data(Spec.fx(Code.step(mkS(u, clk, ksku, tot, av, rv, sd, rs), Spec.Expire{id}))))) == True{} : Bool}:
  match u:
    case False{}:
      pq_down(rs, acc, hW, hR)
    case True{}:
      pq_exp1(Spec.find_res(rs, id), u, clk, ksku, tot, av, rv, sd, rs, id, acc, hi, hW, hR, {==})


def pq_rsv(+g1: Bool, +g2: Bool, +g3: Spec.Look, +g4: Bool, +u: Bool, +clk: Nat, +ksku: Nat, +tot: Nat, +av: Nat, +rv: Nat, +sd: Nat, +rs: +List<Spec.Res>, +id: Nat, +sku: Nat, +qty: Nat, +ttl: Nat, +acc: +List<Spec.Effect>, +hW: {w_ok(rs, acc) == True{} : Bool}, +hR: {Spec.released_ok2(rs, acc) == True{} : Bool}, +e3: {Spec.find_res(rs, id) == g3 : Spec.Look}) -> {pq(Spec.res_of(Spec.st(Code.rsv(g1, g2, g3, g4, mkS(u, clk, ksku, tot, av, rv, sd, rs), id, sku, qty, ttl))), app2(acc, Spec.fx_data(Spec.fx(Code.rsv(g1, g2, g3, g4, mkS(u, clk, ksku, tot, av, rv, sd, rs), id, sku, qty, ttl))))) == True{} : Bool}:
  match g1 g2 g3 g4:
    case False{} _ _ _:
      pq_nr(rs, acc, Spec.FxRejected{id, Spec.BadRequest{}}, {==}, hW, hR)
    case True{} False{} _ _:
      pq_nr(rs, acc, Spec.FxRejected{id, Spec.UnknownSku{}}, {==}, hW, hR)
    case True{} True{} Spec.Got{_} _:
      pq_nr(rs, acc, Spec.FxRejected{id, Spec.DuplicateId{}}, {==}, hW, hR)
    case True{} True{} Spec.NoRes{} False{}:
      pq_nr(rs, acc, Spec.FxRejected{id, Spec.InsufficientStock{}}, {==}, hW, hR)
    case True{} True{} Spec.NoRes{} True{}:
      pq_rsv_acc(u, clk, ksku, tot, av, rv, sd, rs, id, sku, qty, ttl, acc, hW, hR, e3)

def pq_gr(+u: Bool, +clk: Nat, +ksku: Nat, +tot: Nat, +av: Nat, +rv: Nat, +sd: Nat, +rs: +List<Spec.Res>, +id: Nat, +sku: Nat, +qty: Nat, +ttl: Nat, +acc: +List<Spec.Effect>, +hW: {w_ok(rs, acc) == True{} : Bool}, +hR: {Spec.released_ok2(rs, acc) == True{} : Bool}) -> {pq(Spec.res_of(Spec.st(Code.step(mkS(u, clk, ksku, tot, av, rv, sd, rs), Spec.Reserve{id, sku, qty, ttl}))), app2(acc, Spec.fx_data(Spec.fx(Code.step(mkS(u, clk, ksku, tot, av, rv, sd, rs), Spec.Reserve{id, sku, qty, ttl}))))) == True{} : Bool}:
  match u:
    case False{}:
      pq_down(rs, acc, hW, hR)
    case True{}:
      pq_rsv(Bool.and(Nat.is_lt(0n, qty), Nat.is_lt(0n, ttl)), Nat.is_eq(sku, ksku), Spec.find_res(rs, id), Nat.is_le(qty, av), u, clk, ksku, tot, av, rv, sd, rs, id, sku, qty, ttl, acc, hW, hR, {==})


def pq_step(+s: Spec.State, +e: Spec.Ev, +acc: +List<Spec.Effect>, +hi: {Spec.inv(s) == True{} : Bool}, +hW: {w_ok(Spec.res_of(s), acc) == True{} : Bool}, +hR: {Spec.released_ok2(Spec.res_of(s), acc) == True{} : Bool}) -> {pq(Spec.res_of(Spec.st(Code.step(s, e))), app2(acc, Spec.fx_data(Spec.fx(Code.step(s, e))))) == True{} : Bool}:
  match s e:
    case Spec.State{u, clk, Spec.Stock{ksku, tot, av, rv, sd}, rs} Spec.Reserve{id, sku, qty, ttl}:
      pq_gr(u, clk, ksku, tot, av, rv, sd, rs, id, sku, qty, ttl, acc, hW, hR)
    case Spec.State{u, clk, Spec.Stock{ksku, tot, av, rv, sd}, rs} Spec.Confirm{id}:
      pq_gc(u, clk, ksku, tot, av, rv, sd, rs, id, acc, hW, hR)
    case Spec.State{u, clk, Spec.Stock{ksku, tot, av, rv, sd}, rs} Spec.Expire{id}:
      pq_ge(u, clk, ksku, tot, av, rv, sd, rs, id, acc, hi, hW, hR)
    case Spec.State{u, clk, Spec.Stock{ksku, tot, av, rv, sd}, rs} Spec.Tick{}:
      pq_down(rs, acc, hW, hR)
    case Spec.State{u, clk, Spec.Stock{ksku, tot, av, rv, sd}, rs} Spec.Crash{}:
      pq_down(rs, acc, hW, hR)
    case Spec.State{u, clk, Spec.Stock{ksku, tot, av, rv, sd}, rs} Spec.Restart{}:
      pq_down(rs, acc, hW, hR)

def trE(-a: List<&2, Spec.Effect>, -b: List<&2, Spec.Effect>, -c: List<&2, Spec.Effect>, ab: {a == b : List<&2, Spec.Effect>}, bc: {b == c : List<&2, Spec.Effect>}) -> {a == c : List<&2, Spec.Effect>}:
  Equal.trans(List<&2, Spec.Effect>, a, b, c, ab, bc)

def symE(-a: List<&2, Spec.Effect>, -b: List<&2, Spec.Effect>, e: {a == b : List<&2, Spec.Effect>}) -> {b == a : List<&2, Spec.Effect>}:
  Equal.sym(List<&2, Spec.Effect>, a, b, e)

def fxd_app(f1: List<Spec.Effect>, -R: List<Spec.Effect>) -> {Spec.fx_data(List.append(&1, Spec.Effect, f1, R)) == app2(Spec.fx_data(f1), Spec.fx_data(R)) : List<&2, Spec.Effect>}:
  match f1:
    case Nil{}:
      {==}
    case +h <> t:
      %fxd_app(t, R) : {h <> Spec.fx_data(List.append(&1, Spec.Effect, t, R)) == h <> _ : List<&2, Spec.Effect>}
      {==}

def app2_assoc(+a: +List<Spec.Effect>, -b: +List<Spec.Effect>, -c: +List<Spec.Effect>) -> {app2(a, app2(b, c)) == app2(app2(a, b), c) : List<&2, Spec.Effect>}:
  match a:
    case Nil{}:
      {==}
    case +h <> +t:
      %app2_assoc(t, b, c) : {h <> app2(t, app2(b, c)) == h <> _ : List<&2, Spec.Effect>}
      {==}


def gen2(events: List<Spec.Ev>, +s: Spec.State, +acc: +List<Spec.Effect>, +hi: {Spec.inv(s) == True{} : Bool}, +hW: {w_ok(Spec.res_of(s), acc) == True{} : Bool}, +hR: {Spec.released_ok2(Spec.res_of(s), acc) == True{} : Bool}) -> {Spec.released_ok2(Spec.res_of(Code.run(events, s)), app2(acc, Spec.fx_data(Code.run_fx(events, s)))) == True{} : Bool}:
  match events:
    case Nil{}:
      and_r(w_ok(Spec.res_of(s), app2(acc, Nil{})), Spec.released_ok2(Spec.res_of(s), app2(acc, Nil{})), pq_down(Spec.res_of(s), acc, hW, hR))
    case +e <> t:
      %trE(app2(app2(acc, Spec.fx_data(Spec.fx(Code.step(s, e)))), Spec.fx_data(Code.run_fx(t, Spec.st(Code.step(s, e))))), app2(acc, app2(Spec.fx_data(Spec.fx(Code.step(s, e))), Spec.fx_data(Code.run_fx(t, Spec.st(Code.step(s, e)))))), app2(acc, Spec.fx_data(List.append(&1, Spec.Effect, Spec.fx(Code.step(s, e)), Code.run_fx(t, Spec.st(Code.step(s, e)))))), symE(app2(acc, app2(Spec.fx_data(Spec.fx(Code.step(s, e))), Spec.fx_data(Code.run_fx(t, Spec.st(Code.step(s, e)))))), app2(app2(acc, Spec.fx_data(Spec.fx(Code.step(s, e)))), Spec.fx_data(Code.run_fx(t, Spec.st(Code.step(s, e))))), app2_assoc(acc, Spec.fx_data(Spec.fx(Code.step(s, e))), Spec.fx_data(Code.run_fx(t, Spec.st(Code.step(s, e)))))), Equal.cong(List<&2, Spec.Effect>, List<&2, Spec.Effect>, y => app2(acc, y), app2(Spec.fx_data(Spec.fx(Code.step(s, e))), Spec.fx_data(Code.run_fx(t, Spec.st(Code.step(s, e))))), Spec.fx_data(List.append(&1, Spec.Effect, Spec.fx(Code.step(s, e)), Code.run_fx(t, Spec.st(Code.step(s, e))))), symE(Spec.fx_data(List.append(&1, Spec.Effect, Spec.fx(Code.step(s, e)), Code.run_fx(t, Spec.st(Code.step(s, e))))), app2(Spec.fx_data(Spec.fx(Code.step(s, e))), Spec.fx_data(Code.run_fx(t, Spec.st(Code.step(s, e))))), fxd_app(Spec.fx(Code.step(s, e)), Code.run_fx(t, Spec.st(Code.step(s, e))))))) : {Spec.released_ok2(Spec.res_of(Code.run(t, Spec.st(Code.step(s, e)))), _) == True{} : Bool}
      gen2(t, Spec.st(Code.step(s, e)), app2(acc, Spec.fx_data(Spec.fx(Code.step(s, e)))), Laws.inv_step(s, e, hi), and_l(w_ok(Spec.res_of(Spec.st(Code.step(s, e))), app2(acc, Spec.fx_data(Spec.fx(Code.step(s, e))))), Spec.released_ok2(Spec.res_of(Spec.st(Code.step(s, e))), app2(acc, Spec.fx_data(Spec.fx(Code.step(s, e))))), pq_step(s, e, acc, hi, hW, hR)), and_r(w_ok(Spec.res_of(Spec.st(Code.step(s, e))), app2(acc, Spec.fx_data(Spec.fx(Code.step(s, e))))), Spec.released_ok2(Spec.res_of(Spec.st(Code.step(s, e))), app2(acc, Spec.fx_data(Spec.fx(Code.step(s, e))))), pq_step(s, e, acc, hi, hW, hR)))

def Laws.p3b_released_count_run(events, sku, t):
  gen2(events, Spec.init(sku, t), Nil{}, init_inv_l(sku, t), {==}, {==})
