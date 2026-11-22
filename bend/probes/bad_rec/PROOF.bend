import Base
import ./LAWS.bend as Laws

# Attempt: "induction" whose recursive call is on the same n, not a smaller part.
# If the termination check let this through, the law would be "proved" by a loop.
def Laws.bad_rec(n):
  match n:
    case 0n:
      Laws.bad_rec(0n)
    case 1n+p:
      Laws.bad_rec(1n+p)
