---- MODULE Smoke ----
\* Phase 0 toolchain smoke test: a bounded counter. Not a use case.
EXTENDS Naturals

CONSTANT N
ASSUME N \in Nat

VARIABLE count

Init == count = 0

Inc == count < N /\ count' = count + 1
\* Explicit stutter at the bound so TLC does not report a deadlock.
Done == count = N /\ UNCHANGED count

Next == Inc \/ Done

Spec == Init /\ [][Next]_count

TypeOK == count \in 0..N
Bounded == count <= N
====
