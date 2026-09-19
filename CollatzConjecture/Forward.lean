import CollatzConjecture.Basic

namespace CollatzConjecture

/-- Determinism: once two forward paths meet, all later states coincide. -/
theorem forward_coalescence {α : Type*} (f : α → α)
    {a b : α} {i j : Nat}
    (h : iter f i a = iter f j b) :
    ∀ r : Nat, iter f (i + r) a = iter f (j + r) b := by
  intro r
  rw [iter_add, iter_add, h]

/-- A self-intersection forces a periodic suffix. -/
theorem repeated_vertex_periodic {α : Type*} (f : α → α)
    {x : α} {i j : Nat} (hij : i < j)
    (h : iter f i x = iter f j x) :
    ∀ r : Nat, iter f (i + r) x = iter f (j + r) x :=
  forward_coalescence f h

/-- If t is the first time a deterministic path reaches a terminal vertex,
    then no two vertices up to time t can repeat.  This is the exact
    trajectory-Hamiltonian implication used in Section 8. -/
theorem first_hit_is_simple {α : Type*} (f : α → α)
    {x terminal : α} {t : Nat}
    (hhit : iter f t x = terminal)
    (hfirst : ∀ k : Nat, k < t → iter f k x ≠ terminal) :
    ∀ i j : Nat, i < j → j ≤ t → iter f i x ≠ iter f j x := by
  intro i j hij hjt heq
  let r := t - j
  have hcoal := forward_coalescence f heq r
  have hjr : j + r = t := by
    dsimp [r]
    omega
  have hir : i + r < t := by
    dsimp [r]
    omega
  have hjterm : iter f (j + r) x = terminal := by
    rw [hjr, hhit]
  have hiterm : iter f (i + r) x = terminal := by
    exact hcoal.trans hjterm
  exact hfirst (i + r) hir hiterm

/-- Specialization of first-hit simplicity to the stopped Collatz map. -/
theorem collatz_first_hit_is_simple {n t : Nat}
    (hhit : iter C t n = 1)
    (hfirst : ∀ k : Nat, k < t → iter C k n ≠ 1) :
    ∀ i j : Nat, i < j → j ≤ t → iter C i n ≠ iter C j n :=
  first_hit_is_simple C hhit hfirst

end CollatzConjecture
