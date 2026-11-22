import Base

# FALSE: n + 1 is never equal to n.
law bad_rec:
  for n: Nat
  {1n+n == n : Nat}
