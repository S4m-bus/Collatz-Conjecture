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
  have hfac := U_factorization (oddOrbit a k)
  calc
    2 ^ rho a k * oddOrbit a (k + 1)
        = 2 ^ v2 (oddOrbit a k) * U (oddOrbit a k) := by
            simp [rho, oddOrbit, iter]
            ring
    _ = U (oddOrbit a k) * 2 ^ v2 (oddOrbit a k) := by ring
    _ = 3 * oddOrbit a k + 1 := hfac

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

end CollatzConjecture
