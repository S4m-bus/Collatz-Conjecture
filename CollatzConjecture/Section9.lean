import CollatzConjecture.Forward

namespace CollatzConjecture

/-- Intersecting P₁ is exactly the same proposition as reaching 1,
    because 1 is absorbing for the stopped map. -/
theorem intersects_terminal_iff_reaches_one (n : Nat) :
    IntersectsTerminalPath n ↔ ReachesOne n := by
  constructor
  · rintro ⟨i, j, h⟩
    refine ⟨i, ?_⟩
    simpa using h
  · rintro ⟨k, hk⟩
    exact ⟨k, 0, by simpa using hk⟩

/-- Lean's formal audit of the global assertion used at the beginning
    of the proposed Section 9. -/
theorem global_terminal_merge_iff_collatz :
    GlobalTerminalMerge ↔ Collatz := by
  constructor
  · intro h n hn
    exact (intersects_terminal_iff_reaches_one n).mp (h n hn)
  · intro h n hn
    exact (intersects_terminal_iff_reaches_one n).mpr (h n hn)

/-- The final Section-9 deduction is valid PROVIDED the global terminal
    merger assertion has already been proved. -/
theorem collatz_of_global_terminal_merge
    (hmerge : GlobalTerminalMerge) : Collatz :=
  global_terminal_merge_iff_collatz.mp hmerge

/-- Conversely, Collatz itself proves the global terminal merger assertion. -/
theorem global_terminal_merge_of_collatz
    (h : Collatz) : GlobalTerminalMerge :=
  global_terminal_merge_iff_collatz.mpr h

end CollatzConjecture
