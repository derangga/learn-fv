import Base
import ./LAWS.bend as Laws

# Regression: @unsafe skips the termination check, so a loop "proves" anything.
# bend runs it, but the gate must say SOME PROOFS FAIL.
@unsafe
def Laws.unsafe_false():
  Laws.unsafe_false()
