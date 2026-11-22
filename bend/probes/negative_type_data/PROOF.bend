import Base
import ./LAWS.bend as Laws

# Attempt: declare Bad as Data so a Bad value may be copied (the missing piece
# of the Russell paradox). A closure field is Type, not Data.
type Bad is Data:
  MkBad{f: Bad -> Empty}

def omega(+b: Bad) -> Empty:
  match b:
    case MkBad{f}:
      f(b)

def Laws.negative_type_data():
  Empty.absurd({1n == 0n : Nat}, omega(MkBad{x => omega(x)}))
