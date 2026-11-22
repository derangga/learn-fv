import Base
import ./LAWS.bend as Laws

# Attempt: induction on n. Base case 1n == 0n cannot hold, step case is rewriting.
def Laws.succ_eq(n):
  match n:
    case 0n:
      {==}
    case 1n+p:
      %Laws.succ_eq(p) : {1n+1n+p == 1n+_ : Nat}
      {==}
