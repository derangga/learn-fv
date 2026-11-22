import Base

# A saturating counter: state is a Nat, events are Inc and Reset.
type Ev is Data:
  Inc{}
  Reset{}

def step(s: Nat, e: Ev) -> Nat:
  match e:
    case Inc{}:
      Nat.min(1n+s, 3n)
    case Reset{}:
      0n

# events come first: the checker wants the shrinking argument leftmost.
def run(events: List<Ev>, s: Nat) -> Nat:
  match events:
    case Nil{}:
      s
    case e <> t:
      run(t, step(s, e))
