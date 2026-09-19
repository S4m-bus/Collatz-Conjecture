import CollatzConjecture.Forward

namespace CollatzConjecture

/-- Intersecting the stopped terminal path P₁ is exactly the same as
    reaching 1 under C, because C fixes 1. -/
theorem intersects_terminal_iff_reaches_one (n : Nat) :
    IntersectsTerminalPath n ↔ ReachesOne n := by
  constructor
  · rintro ⟨i, j, h⟩
    refine ⟨i, ?_⟩
    calc
      iter C i n = iter C j 1 := h
      _ = 1 := iter_C_one j
  · rintro ⟨k, hk⟩
    exact ⟨k, 0, by simpa using hk⟩

/-- Every stopped-map hit has a least hit time. -/
theorem reachesOne_has_first_hit {n : Nat} (h : ReachesOne n) :
    ∃ t : Nat,
      iter C t n = 1 ∧
      ∀ k : Nat, k < t → iter C k n ≠ 1 := by
  classical
  let t := Nat.find h
  refine ⟨t, Nat.find_spec h, ?_⟩
  intro k hk hhit
  have hmin : t ≤ k := Nat.find_min' h hhit
  omega

/-- Before and including the first stopped-map hit of 1, C and T generate
    exactly the same trajectory. -/
theorem stopped_standard_agree_through_first_hit
    {n t : Nat}
    (hhit : iter C t n = 1)
    (hfirst : ∀ k : Nat, k < t → iter C k n ≠ 1) :
    ∀ k : Nat, k ≤ t → iter C k n = iter T k n := by
  intro k hk
  induction k with
  | zero =>
      simp
  | succ k ih =>
      have hkt : k < t := by omega
      have hk_le : k ≤ t := by omega
      have hih := ih hk_le
      have hne : iter C k n ≠ 1 := hfirst k hkt
      calc
        iter C (k + 1) n = C (iter C k n) := by
          simp [iter]
        _ = T (iter C k n) := C_eq_T_of_ne_one hne
        _ = T (iter T k n) := by rw [hih]
        _ = iter T (k + 1) n := by
          simp [iter]

/-- Every ordinary-map hit has a least hit time. -/
theorem standardReachesOne_has_first_hit {n : Nat}
    (h : StandardReachesOne n) :
    ∃ t : Nat,
      iter T t n = 1 ∧
      ∀ k : Nat, k < t → iter T k n ≠ 1 := by
  classical
  let t := Nat.find h
  refine ⟨t, Nat.find_spec h, ?_⟩
  intro k hk hhit
  have hmin : t ≤ k := Nat.find_min' h hhit
  omega

/-- Before and including the first ordinary-map hit of 1, C and T agree. -/
theorem stopped_standard_agree_through_standard_first_hit
    {n t : Nat}
    (hhit : iter T t n = 1)
    (hfirst : ∀ k : Nat, k < t → iter T k n ≠ 1) :
    ∀ k : Nat, k ≤ t → iter C k n = iter T k n := by
  intro k hk
  induction k with
  | zero =>
      simp
  | succ k ih =>
      have hkt : k < t := by omega
      have hk_le : k ≤ t := by omega
      have hih := ih hk_le
      have hne : iter T k n ≠ 1 := hfirst k hkt
      calc
        iter C (k + 1) n = C (iter C k n) := by simp [iter]
        _ = C (iter T k n) := by rw [hih]
        _ = T (iter T k n) := C_eq_T_of_ne_one hne
        _ = iter T (k + 1) n := by simp [iter]

/-- An ordinary-map hit yields a stopped-map hit. -/
theorem standard_reaches_one_implies_stopped_reaches_one
    {n : Nat} (h : StandardReachesOne n) :
    ReachesOne n := by
  rcases standardReachesOne_has_first_hit h with ⟨t, hhit, hfirst⟩
  refine ⟨t, ?_⟩
  have hagree :=
    stopped_standard_agree_through_standard_first_hit
      hhit hfirst t (Nat.le_refl t)
  calc
    iter C t n = iter T t n := hagree
    _ = 1 := hhit

/-- A stopped-map proof of reaching 1 yields an ordinary Collatz proof.
    The witness is the least stopped-map hitting time, not an arbitrary
    later stopped-map time. -/
theorem stopped_reaches_one_implies_standard_reaches_one
    {n : Nat} (h : ReachesOne n) :
    StandardReachesOne n := by
  rcases reachesOne_has_first_hit h with ⟨t, hhit, hfirst⟩
  refine ⟨t, ?_⟩
  have hagree :=
    stopped_standard_agree_through_first_hit hhit hfirst t (Nat.le_refl t)
  exact hagree ▸ hhit

/-- Exact equivalence of the stopped and ordinary first-hit formulations. -/
theorem reachesOne_iff_standardReachesOne (n : Nat) :
    ReachesOne n ↔ StandardReachesOne n := by
  constructor
  · exact stopped_reaches_one_implies_standard_reaches_one
  · exact standard_reaches_one_implies_stopped_reaches_one

/-- Section 9's pointwise closing step:
    a forward intersection with P₁ yields a genuine ordinary-Collatz hit of 1. -/
theorem terminal_intersection_implies_standard_reaches_one
    {n : Nat} (h : IntersectsTerminalPath n) :
    StandardReachesOne n := by
  exact stopped_reaches_one_implies_standard_reaches_one
    ((intersects_terminal_iff_reaches_one n).mp h)

/-- Once the preceding sections have produced the global merged-path theorem,
    this lemma is the exact Section-9 closure from that theorem to the ordinary
    Collatz statement.  This is intentionally a helper lemma; the final
    whole-paper theorem must instantiate it with the actually proved global
    theorem from the preceding module. -/
theorem section9_closure_from_global_merge
    (hglobal : GlobalTerminalMerge) :
    Collatz := by
  intro n hn
  exact terminal_intersection_implies_standard_reaches_one (hglobal n hn)

end CollatzConjecture
