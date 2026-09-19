import CollatzConjecture.OddCompressed
import CollatzConjecture.OddPathArithmetic

namespace CollatzConjecture

/-- The actual odd-compressed forward orbit. -/
def oddOrbit (a : Nat) (k : Nat) : Nat :=
  iter U k a

/-- The exact 2-adic exponent attached to the k-th actual odd-compressed state. -/
def rho (a : Nat) (k : Nat) : Nat :=
  v2 (oddOrbit a k)

/-- The actual U-orbit satisfies the exact odd recurrence used by the paper. -/
theorem actual_U_follows_odd_word (a : Nat) :
    FollowsOddWord (oddOrbit a) (rho a) := by
  intro k
  simpa [rho, oddOrbit, iter, Nat.mul_comm] using
    (U_factorization (oddOrbit a k))

/-- Cumulative valuation along the actual U orbit. -/
def R (a : Nat) (m : Nat) : Nat :=
  cumExp (rho a) m

/-- Additive finite-prefix term along the actual U orbit. -/
def S (a : Nat) (m : Nat) : Nat :=
  addTerm (rho a) m

/-- Exact master identity for every actual finite odd-compressed prefix. -/
theorem actual_finite_odd_path_expansion (a : Nat) (m : Nat) :
    2 ^ R a m * oddOrbit a m =
      3 ^ m * a + S a m := by
  simpa [R, S, oddOrbit] using
    (finite_odd_path_expansion (actual_U_follows_odd_word a) m)

/-- Endpoint recovery for an actual U prefix, in multiplication form. -/
theorem actual_prefix_endpoint_eq (a : Nat) (m : Nat) :
    3 ^ m * a + S a m =
      2 ^ R a m * iter U m a := by
  simpa [oddOrbit] using (actual_finite_odd_path_expansion a m).symm

/-- Exact merged-prefix cross identity for two actual U-orbits. -/
theorem actual_merged_prefix_cross_identity
    {a b : Nat} {m n : Nat}
    (hmeet : iter U m a = iter U n b) :
    2 ^ R b n * (3 ^ m * a + S a m) =
      2 ^ R a m * (3 ^ n * b + S b n) := by
  have hA := actual_prefix_endpoint_eq a m
  have hB := actual_prefix_endpoint_eq b n
  calc
    2 ^ R b n * (3 ^ m * a + S a m)
        = 2 ^ R b n * (2 ^ R a m * iter U m a) := by rw [hA]
    _ = 2 ^ R a m * (2 ^ R b n * iter U n b) := by
          rw [hmeet]
          ring
    _ = 2 ^ R a m * (3 ^ n * b + S b n) := by rw [← hB]

/-- Equal finite valuation words give equal cumulative exponents and additive terms. -/
theorem equal_word_equal_prefix_data
    {a b : Nat} {m : Nat}
    (hword : ∀ k : Nat, k < m → rho a k = rho b k) :
    R a m = R b m ∧ S a m = S b m := by
  induction m with
  | zero =>
      simp [R, S, cumExp, addTerm]
  | succ m ih =>
      have hpref : ∀ k : Nat, k < m → rho a k = rho b k := by
        intro k hk
        exact hword k (Nat.lt_trans hk (Nat.lt_succ_self m))
      rcases ih hpref with ⟨hR, hS⟩
      have hr : rho a m = rho b m :=
        hword m (Nat.lt_succ_self m)
      have hcum : cumExp (rho a) m = cumExp (rho b) m := by
        simpa [R] using hR
      have hadd : addTerm (rho a) m = addTerm (rho b) m := by
        simpa [S] using hS
      constructor
      · change
          cumExp (rho a) (m + 1) =
            cumExp (rho b) (m + 1)
        simp only [cumExp_succ]
        rw [hcum, hr]
      · change
          addTerm (rho a) (m + 1) =
            addTerm (rho b) (m + 1)
        simp only [addTerm_succ]
        rw [hadd, hcum]

/-- Exact common-word affine separation for actual U-orbits, in
    subtraction-free natural-number form. -/
theorem actual_common_word_affine_separation
    {a b : Nat} {m : Nat}
    (hword : ∀ k : Nat, k < m → rho a k = rho b k) :
    2 ^ R a m * iter U m a + 3 ^ m * b =
      2 ^ R a m * iter U m b + 3 ^ m * a := by
  rcases equal_word_equal_prefix_data hword with ⟨hR, hS⟩
  have hA := actual_finite_odd_path_expansion a m
  have hB := actual_finite_odd_path_expansion b m
  rw [← hR, ← hS] at hB
  change
    2 ^ R a m * oddOrbit a m + 3 ^ m * b =
      2 ^ R a m * oddOrbit b m + 3 ^ m * a
  omega

/-- Distinct actual starts cannot merge synchronously after carrying the
    same complete finite valuation word. -/
theorem actual_no_common_word_synchronous_merger
    {a b : Nat} {m : Nat}
    (hword : ∀ k : Nat, k < m → rho a k = rho b k)
    (hendpoint : iter U m a = iter U m b) :
    a = b := by
  have hsep := actual_common_word_affine_separation hword
  rw [hendpoint] at hsep
  have hmul : 3 ^ m * b = 3 ^ m * a := by
    exact Nat.add_left_cancel hsep
  exact (mul_left_cancel_iff_of_pos (show 0 < 3 ^ m by positivity)).mp hmul.symm

end CollatzConjecture
