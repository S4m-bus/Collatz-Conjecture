import CollatzConjecture.Section9
import CollatzConjecture.StructuralConsequences

namespace CollatzConjecture

/-- The paper's terminal forward class for the stopped map. -/
def TerminalClass : Set Nat :=
  {n | ReachesOne n}

theorem mem_terminalClass_iff_reachesOne (n : Nat) :
    n ∈ TerminalClass ↔ ReachesOne n := Iff.rfl

theorem mem_terminalClass_iff_intersects_P1 (n : Nat) :
    n ∈ TerminalClass ↔ IntersectsTerminalPath n := by
  simpa [TerminalClass] using (intersects_terminal_iff_reaches_one n).symm

/-- A nonterminal stopped path avoids 1 at every finite time. -/
theorem not_mem_terminalClass_avoids_one {n : Nat}
    (h : n ∉ TerminalClass) :
    Avoids C 1 n := by
  intro k hk
  apply h
  exact ⟨k, hk⟩

/-- Exact Section-8 obstruction dichotomy:
    a nonterminal path either repeats, or is infinite-simple. -/
theorem forward_obstruction_dichotomy {n : Nat}
    (h : n ∉ TerminalClass) :
    (HasRepeat C n ∧ Avoids C 1 n) ∨
      (InfiniteSimple C n ∧ Avoids C 1 n) := by
  exact nonterminal_dichotomy C 1 n (not_mem_terminalClass_avoids_one h)

/-- Every stopped-map terminating path has a least first hit and is simple
    through that first hit. -/
theorem terminating_path_has_simple_first_hit {n : Nat}
    (h : n ∈ TerminalClass) :
    ∃ t : Nat,
      iter C t n = 1 ∧
      (∀ k : Nat, k < t → iter C k n ≠ 1) ∧
      (∀ i j : Nat, i < j → j ≤ t → iter C i n ≠ iter C j n) := by
  rcases reachesOne_has_first_hit h with ⟨t, hhit, hfirst⟩
  refine ⟨t, hhit, hfirst, ?_⟩
  exact collatz_first_hit_is_simple hhit hfirst

end CollatzConjecture
