import Base
import ./LAWS.bend as Laws

# Not strictly positive: Bad occurs on the left of an arrow.
type Bad is Type:
  MkBad{f: Bad -> Empty}

def app(b: Bad, x: Bad) -> Empty:
  match b:
    case MkBad{f}:
      f(x)

# omega = app(b, b) needs b twice.
def omega(b: Bad) -> Empty:
  app(b, b)

def russell() -> Empty:
  omega(MkBad{x => omega(x)})

def Laws.negative_type():
  Empty.absurd({1n == 0n : Nat}, russell())
