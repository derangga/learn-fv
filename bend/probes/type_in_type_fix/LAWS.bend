import Base

# FALSE: 1 does not equal 0. The attempt is Russell's paradox over a
# Type-indexed tree type V : Type whose constructor stores a field A : Type
# (so it relies on Type : Type).
law type_in_type_fix:
  {1n == 0n : Nat}
