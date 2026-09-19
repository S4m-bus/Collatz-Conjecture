import CollatzConjecture.Forward
import CollatzConjecture.OddArithmetic
import CollatzConjecture.Section9

namespace CollatzConjecture

/-
This file mirrors the logical transition made by the uploaded paper at the
beginning of Section 9.  It intentionally has NO hypothesis equivalent to
Collatz or GlobalTerminalMerge.

The prior paper sections establish deterministic continuation, coalescence
*after* an intersection, first-hit simplicity/Hamiltonicity, and exact finite
odd-path arithmetic.  The Section 9 proof then needs, for arbitrary positive n,
an actual intersection of P_n with P_1.
-/

/-- Exact zero-hypothesis theorem required by the paper's Section 9. -/
theorem paper_section9_collatz : Collatz := by
  intro n hn

  /-
  This is the precise sentence in the paper:
    "for every n, the forward path P_n belongs to the merged family
     containing the terminal path P_1."

  In formal terms it is the following existential statement.
  -/
  have hmeet : IntersectsTerminalPath n := by
    aesop

  exact terminal_intersection_implies_standard_reaches_one hmeet

end CollatzConjecture
