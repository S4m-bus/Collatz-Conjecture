import CollatzConjecture.OddCompressed
import CollatzConjecture.GlobalCoalescence
import CollatzConjecture.StructuralConsequences

namespace CollatzConjecture

/-- Eventual forward coalescence for the odd-compressed map. -/
def UCoalesces (a b : Nat) : Prop :=
  Coalesces U a b

theorem UCoalesces_refl (a : Nat) : UCoalesces a a :=
  coalesces_refl U a

theorem UCoalesces_symm {a b : Nat} (h : UCoalesces a b) :
    UCoalesces b a :=
  coalesces_symm U h

theorem UCoalesces_trans {a b c : Nat}
    (hab : UCoalesces a b) (hbc : UCoalesces b c) :
    UCoalesces a c :=
  coalesces_trans U hab hbc

theorem UCoalesces_equivalence :
    Equivalence UCoalesces where
  refl := UCoalesces_refl
  symm := @UCoalesces_symm
  trans := @UCoalesces_trans

/-- Coalescing with 1 is exactly hitting 1, since U fixes 1. -/
theorem UCoalesces_one_iff_hits_one (a : Nat) :
    UCoalesces a 1 ↔ ∃ m : Nat, iter U m a = 1 := by
  constructor
  · rintro ⟨i, j, hij⟩
    refine ⟨i, ?_⟩
    calc
      iter U i a = iter U j 1 := hij
      _ = 1 := by
        induction j with
        | zero => rfl
        | succ j ih =>
            simp [iter, ih, U_one]
  · rintro ⟨m, hm⟩
    exact ⟨m, 0, by simpa using hm⟩

/-- The exact deterministic obstruction dichotomy for an odd-compressed orbit. -/
theorem U_repeat_or_infinite_simple (a : Nat) :
    HasRepeat U a ∨ InfiniteSimple U a :=
  repeat_or_infiniteSimple U a

/-- If an odd-compressed orbit repeats, the repeated segment propagates forever. -/
theorem U_repeat_gives_periodic_tail {a : Nat}
    (h : HasRepeat U a) :
    ∃ i j : Nat, i < j ∧
      ∀ t : Nat, iter U (i + t) a = iter U (j + t) a := by
  rcases h with ⟨i, j, hij, heq⟩
  exact ⟨i, j, hij, forward_coalescence U heq⟩

/-- Forward hitting sets for U are laminar whenever they intersect. -/
theorem U_hittingSet_laminar {x y : Nat}
    (hne : (HittingSet U x ∩ HittingSet U y).Nonempty) :
    HittingSet U x ⊆ HittingSet U y ∨
      HittingSet U y ⊆ HittingSet U x :=
  hittingSet_laminar U hne

end CollatzConjecture
