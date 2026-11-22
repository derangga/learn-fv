import Base
import ./LAWS.bend as Laws

type Bad is Type:
  MkBad{f: Bad -> Empty}

def app(b: Bad, x: Bad) -> Empty:
  match b:
    case MkBad{f}:
      f(x)

# Dead mode accepts the Russell term below as an erased argument (a closure is
# copied there). Attempt: return an erased Empty as live Empty, then use it.
def leak(-e: Empty) -> Empty:
  e

def Laws.dead_mode_leak():
  Empty.absurd({1n == 0n : Nat}, leak(app(MkBad{x => app(x, x)}, MkBad{x => app(x, x)})))
