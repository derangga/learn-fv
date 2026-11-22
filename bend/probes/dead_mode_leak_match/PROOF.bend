import Base
import ./LAWS.bend as Laws

type Bad is Type:
  MkBad{f: Bad -> Empty}

def app(b: Bad, x: Bad) -> Empty:
  match b:
    case MkBad{f}:
      f(x)

# Attempt: eliminate an erased Empty by a live match (no cases), producing the
# false equation. The dead Empty comes from the paradox term at the call site.
def leak(-e: Empty) -> {1n == 0n : Nat}:
  match e:

def Laws.dead_mode_leak_match():
  leak(app(MkBad{x => app(x, x)}, MkBad{x => app(x, x)}))
