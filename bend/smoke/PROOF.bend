import Base
import ./code.bend as Code
import ./LAWS.bend as Laws

def Laws.reset_zero(s):
  {==}

def Laws.step_preserves(s, e, h):
  match s e:
    case _ Code.Reset{}:
      {==}
    case 0n Code.Inc{}:
      {==}
    case 1n+0n Code.Inc{}:
      {==}
    case 1n+1n+0n Code.Inc{}:
      {==}
    case 1n+1n+1n+r Code.Inc{}:
      {==}

def Laws.run_preserves(events, s, h):
  match events:
    case Nil{}:
      h
    case +e <> t:
      Laws.run_preserves(t, Code.step(s, e), Laws.step_preserves(s, e, h))
