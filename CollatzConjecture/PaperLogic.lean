import CollatzConjecture.Section9

namespace CollatzConjecture

/-- For the stopped map, intersecting P₁ is pointwise exactly reaching 1. -/
theorem global_terminal_merge_iff_stopped_collatz :
    GlobalTerminalMerge ↔ StoppedCollatz := by
  constructor
  · intro h n hn
    exact (intersects_terminal_iff_reaches_one n).mp (h n hn)
  · intro h n hn
    exact (intersects_terminal_iff_reaches_one n).mpr (h n hn)

/-- The stopped formulation implies the ordinary formulation, using the
    least first hit and the C/T agreement theorem. -/
theorem stopped_collatz_implies_collatz
    (h : StoppedCollatz) : Collatz := by
  intro n hn
  exact stopped_reaches_one_implies_standard_reaches_one (h n hn)

/-- The exact final implication in Section 9. -/
theorem global_terminal_merge_implies_collatz
    (h : GlobalTerminalMerge) : Collatz := by
  exact stopped_collatz_implies_collatz
    (global_terminal_merge_iff_stopped_collatz.mp h)

end CollatzConjecture
