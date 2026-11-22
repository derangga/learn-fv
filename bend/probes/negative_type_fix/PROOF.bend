import Base
import ./LAWS.bend as Laws

# Not strictly positive: Bad occurs on the left of an arrow. The type is accepted.
type Bad is Type:
  MkBad{f: Bad -> Empty}

def app(b: Bad, x: Bad) -> Empty:
  match b:
    case MkBad{f}:
      f(x)

# Duplication-free self-application: a top-level def may be called any number of
# times, so mk() builds a fresh Bad each time and the closure never copies x.
# This is the fixpoint (Y combinator) route round the affine check; it needs mk
# to call itself with no smaller argument.
def mk() -> Bad:
  MkBad{x => app(x, mk())}

def Laws.negative_type_fix():
  Empty.absurd({1n == 0n : Nat}, app(mk(), mk()))
