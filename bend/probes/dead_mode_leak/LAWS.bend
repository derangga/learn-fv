import Base

# FALSE: 1 does not equal 0. The attempt smuggles an Empty value built in dead
# (erased) mode into live evidence.
law dead_mode_leak:
  {1n == 0n : Nat}
