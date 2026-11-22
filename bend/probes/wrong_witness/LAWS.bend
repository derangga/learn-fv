import Base

# FALSE: no natural y satisfies 1 + y == 0.
law wrong_witness:
  exs y: Nat
  {1n+y == 0n : Nat}
