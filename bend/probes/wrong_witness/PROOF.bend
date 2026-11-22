import Base
import ./LAWS.bend as Laws

# Attempt: witness 0n with reflexivity. 1n+0n computes to 1n, not 0n.
def Laws.wrong_witness():
  (0n, {==})
