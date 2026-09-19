import CollatzConjecture.OddPathArithmetic

namespace CollatzConjecture

/-- Exact endpoint equation for a finite odd prefix. -/
theorem prefix_endpoint_eq
    {a : Nat → Nat} {rho : Nat → Nat}
    (hstep : FollowsOddWord a rho) (m : Nat) :
    3 ^ m * a 0 + addTerm rho m =
      2 ^ cumExp rho m * a m := by
  simpa [eq_comm] using (finite_odd_path_expansion hstep m).symm

/-- Exact cross-compatibility equation for two finite prefixes that end
    at the same odd state.  This is the paper's merged-prefix identity. -/
theorem merged_prefix_cross_identity
    {a b : Nat → Nat} {rho sigma : Nat → Nat}
    (ha : FollowsOddWord a rho)
    (hb : FollowsOddWord b sigma)
    {m n : Nat}
    (hend : a m = b n) :
    2 ^ cumExp sigma n * (3 ^ m * a 0 + addTerm rho m) =
      2 ^ cumExp rho m * (3 ^ n * b 0 + addTerm sigma n) := by
  have hA := finite_odd_path_expansion ha m
  have hB := finite_odd_path_expansion hb n
  calc
    2 ^ cumExp sigma n * (3 ^ m * a 0 + addTerm rho m)
        = 2 ^ cumExp sigma n * (2 ^ cumExp rho m * a m) := by rw [← hA]
    _ = 2 ^ cumExp rho m * (2 ^ cumExp sigma n * b n) := by
          rw [hend]
          ring
    _ = 2 ^ cumExp rho m * (3 ^ n * b 0 + addTerm sigma n) := by rw [hB]

/-- Finite multi-prefix compatibility, pairwise form. -/
theorem multipath_pairwise_compatibility
    {a b : Nat → Nat} {rho sigma : Nat → Nat}
    (ha : FollowsOddWord a rho)
    (hb : FollowsOddWord b sigma)
    {m n : Nat}
    (hcommon : a m = b n) :
    2 ^ cumExp sigma n * (3 ^ m * a 0 + addTerm rho m) =
      2 ^ cumExp rho m * (3 ^ n * b 0 + addTerm sigma n) :=
  merged_prefix_cross_identity ha hb hcommon

/-- Equal endpoints under an identical complete exponent word force
    identical starting values. -/
theorem common_word_endpoint_injective
    {a b : Nat → Nat} {rho : Nat → Nat}
    (ha : FollowsOddWord a rho)
    (hb : FollowsOddWord b rho)
    {m : Nat}
    (hendpoint : a m = b m) :
    a 0 = b 0 :=
  no_distinct_synchronous_merger_same_word ha hb hendpoint

/-- A repeated endpoint closes the finite odd recurrence exactly. -/
theorem self_merger_closure
    {a : Nat → Nat} {rho : Nat → Nat}
    (hstep : FollowsOddWord a rho)
    {q : Nat}
    (hreturn : a q = a 0) :
    2 ^ cumExp rho q * a 0 =
      3 ^ q * a 0 + addTerm rho q :=
  cyclic_closure_eq hstep hreturn

end CollatzConjecture
