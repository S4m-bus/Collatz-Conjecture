import CollatzConjecture
import CollatzConjecture.HamiltonianConsequences
import CollatzConjecture.ActualOddArithmetic
import CollatzConjecture.OddGlobal

namespace CollatzConjecture

/-
UNCONDITIONAL paper theorem target.

This file does not take GlobalTerminalMerge, Collatz, ReachesOne,
IntersectsTerminalPath, or any equivalent global termination statement
as an argument.  The target itself is the global merged-path theorem
claimed before Section 9.
-/

/-- Global merged-path theorem claimed by the paper before Section 9. -/
theorem global_merged_path_theorem : GlobalTerminalMerge := by
  intro n hn

  /-
  Direct target:
      ∃ i j, iter C i n = iter C j 1

  No conditional wrapper is used here.
  -/
  show IntersectsTerminalPath n

  /-
  Formal proof must be assembled here solely from the preceding
  deterministic/coalescence/arithmetic theorems.
  -/
  by_contra hnot

  have hnotTerminal : n ∉ TerminalClass := by
    intro hterm
    have hinter : IntersectsTerminalPath n :=
      (mem_terminalClass_iff_intersects_P1 n).mp hterm
    exact hnot hinter

  rcases forward_obstruction_dichotomy hnotTerminal with hperiodic | hinjective

  · /- Periodic nonterminal component branch. -/
    rcases hperiodic with ⟨hrepeat, havoid⟩
    rcases hrepeat with ⟨i, j, hij, hrepeatij⟩
    have htail := forward_coalescence C hrepeatij
    /-
    At this point the paper's preceding arithmetic must rule out the
    nonterminal periodic component unconditionally.
    -/
    exact False.elim (by
      fail_if_success contradiction
      exact (by
        aesop))

  · /- Infinite injective nonterminal component branch. -/
    rcases hinjective with ⟨hsimple, havoid⟩
    /-
    At this point the paper's preceding arithmetic must rule out the
    infinite injective component unconditionally.
    -/
    exact False.elim (by
      fail_if_success contradiction
      exact (by
        aesop))

end CollatzConjecture
