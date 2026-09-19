import Collatz.Basic

namespace Collatz

/-- Cumulative exponent along a prescribed exponent word. -/
def cumExp (rho : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | m + 1 => cumExp rho m + rho m

/-- Additive term in the exact finite odd-path expansion, in recursive form. -/
def addTerm (rho : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | m + 1 => 3 * addTerm rho m + 2 ^ cumExp rho m

/-- A sequence satisfies the exact compressed Collatz transition equations
    for a prescribed exponent word.  Exactness of the valuation is a stronger
    property; the algebraic expansion below only needs these equations. -/
def FollowsOddWord (a : ℕ → ℕ) (rho : ℕ → ℕ) : Prop :=
  ∀ k : ℕ, 2 ^ rho k * a (k + 1) = 3 * a k + 1

@[simp] theorem cumExp_zero (rho : ℕ → ℕ) : cumExp rho 0 = 0 := rfl
@[simp] theorem cumExp_succ (rho : ℕ → ℕ) (m : ℕ) :
    cumExp rho (m + 1) = cumExp rho m + rho m := rfl
@[simp] theorem addTerm_zero (rho : ℕ → ℕ) : addTerm rho 0 = 0 := rfl
@[simp] theorem addTerm_succ (rho : ℕ → ℕ) (m : ℕ) :
    addTerm rho (m + 1) = 3 * addTerm rho m + 2 ^ cumExp rho m := rfl

/-- Section 5 finite odd-path expansion, proved over the natural numbers
    directly from the exact forward transition equations. -/
theorem finite_odd_path_expansion
    {a : ℕ → ℕ} {rho : ℕ → ℕ}
    (hstep : FollowsOddWord a rho) :
    ∀ m : ℕ,
      2 ^ cumExp rho m * a m =
        3 ^ m * a 0 + addTerm rho m := by
  intro m
  induction m with
  | zero =>
      simp [cumExp, addTerm]
  | succ m ih =>
      have hs := hstep m
      rw [cumExp_succ, addTerm_succ, pow_add]
      calc
        2 ^ cumExp rho m * 2 ^ rho m * a (m + 1)
            = 2 ^ cumExp rho m * (2 ^ rho m * a (m + 1)) := by
                ac_rfl
        _ = 2 ^ cumExp rho m * (3 * a m + 1) := by rw [hs]
        _ = 3 * (2 ^ cumExp rho m * a m) + 2 ^ cumExp rho m := by ring
        _ = 3 * (3 ^ m * a 0 + addTerm rho m) + 2 ^ cumExp rho m := by rw [ih]
        _ = 3 ^ (m + 1) * a 0 +
              (3 * addTerm rho m + 2 ^ cumExp rho m) := by
                rw [pow_succ]
                ring

/-- Exact cyclic closure in subtraction-free form. -/
theorem cyclic_closure_eq
    {a : ℕ → ℕ} {rho : ℕ → ℕ}
    (hstep : FollowsOddWord a rho) {q : ℕ}
    (hcycle : a q = a 0) :
    2 ^ cumExp rho q * a 0 =
      3 ^ q * a 0 + addTerm rho q := by
  simpa [hcycle] using finite_odd_path_expansion hstep q

/-- Two forward paths carrying the same complete exponent word obey an exact
    affine separation identity.  This is the subtraction-free form of
    2^R (a_m-b_m) = 3^m (a_0-b_0). -/
theorem common_word_affine_separation
    {a b : ℕ → ℕ} {rho : ℕ → ℕ}
    (ha : FollowsOddWord a rho)
    (hb : FollowsOddWord b rho)
    (m : ℕ) :
    2 ^ cumExp rho m * a m + 3 ^ m * b 0 =
      2 ^ cumExp rho m * b m + 3 ^ m * a 0 := by
  have hA := finite_odd_path_expansion ha m
  have hB := finite_odd_path_expansion hb m
  omega

/-- Synchronous merger under an identical exponent word forces
    identical starting values. -/
theorem no_distinct_synchronous_merger_same_word
    {a b : ℕ → ℕ} {rho : ℕ → ℕ}
    (ha : FollowsOddWord a rho)
    (hb : FollowsOddWord b rho)
    {m : ℕ}
    (hend : a m = b m) :
    a 0 = b 0 := by
  have hsep := common_word_affine_separation ha hb m
  rw [hend] at hsep
  have hmul : 3 ^ m * b 0 = 3 ^ m * a 0 := by
    exact Nat.add_left_cancel hsep
  exact (mul_left_cancel_iff_of_pos (show 0 < 3 ^ m by positivity)).mp hmul


end Collatz
