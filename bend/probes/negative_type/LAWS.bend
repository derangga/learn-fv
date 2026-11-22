import Base

# FALSE: 1 does not equal 0. The only way to prove it here is to build an
# Empty value from a non-positive datatype (the Curry/Russell paradox).
law negative_type:
  {1n == 0n : Nat}
