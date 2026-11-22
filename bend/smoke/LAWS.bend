import Base
import ./code.bend as Code

# Trivial: Reset always gives 0.
law reset_zero:
  for s: Nat
  {Code.step(s, Code.Reset{}) == 0n : Nat}

# One event keeps the counter within the cap of 3.
law step_preserves:
  for s: Nat
  for e: Code.Ev
  for h: {Nat.is_le(s, 3n) == True{} : Bool}
  {Nat.is_le(Code.step(s, e), 3n) == True{} : Bool}

# Any list of events keeps the counter within the cap of 3.
law run_preserves:
  for events: List<Code.Ev>
  for +s: Nat
  for h: {Nat.is_le(s, 3n) == True{} : Bool}
  {Nat.is_le(Code.run(events, s), 3n) == True{} : Bool}
