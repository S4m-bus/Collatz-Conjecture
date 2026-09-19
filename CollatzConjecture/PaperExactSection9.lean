import CollatzConjecture.GlobalMergedPath
import CollatzConjecture.Section9

namespace CollatzConjecture

/-- Final zero-hypothesis Collatz theorem. -/
theorem paper_section9_collatz : Collatz := by
  intro n hn
  rcases global_merged_path_theorem n hn with ⟨i, j, hij⟩
  have hmeet : IntersectsTerminalPath n := ⟨i, j, hij⟩
  exact terminal_intersection_implies_standard_reaches_one hmeet

end CollatzConjecture
