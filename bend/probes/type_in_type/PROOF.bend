import Base
import ./LAWS.bend as Laws

# V : Type holds a field A : Type (Type : Type). Bend accepts the declaration.
type V is Type:
  Sup{A: Type, f: A -> V}

# a is a member of b
def In(a: V, b: V) -> Type:
  match b:
    case Sup{A, f}:
      &x: A -> {a == f(x) : V}

# The Russell set: all v that are not members of themselves.
def NotSelf() -> Type:
  &v: V -> (In(v, v) -> Empty)

def Rus.proj(p: NotSelf()) -> V:
  (v, h) = p
  v

def Rus() -> V:
  Sup{NotSelf(), p => Rus.proj(p)}

# Transport a membership proof along Rus == v.
def cast(-v: V, eq: {Rus() == v : V}, i: In(Rus(), Rus())) -> In(v, v):
  %eq : In(_, _)
  i

# Rus in Rus implies Empty.
# Route 1: rebuild the membership proof from its own pieces (copies nh, v, eq).
def lem1(i: In(Rus(), Rus())) -> Empty:
  (x, eq) = i
  (v, nh) = x
  nh(cast(v, eq, ((v, nh), eq)))

# Rus is not a member of itself, so it is: contradiction.
def Laws.type_in_type():
  Empty.absurd({1n == 0n : Nat}, lem1(((Rus(), lem1), {==})))
