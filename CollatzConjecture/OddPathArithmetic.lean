import CollatzConjecture.Basic

namespace CollatzConjecture

def cumExp (rho : Nat → Nat) : Nat → Nat
  | 0 => 0
  | m + 1 => cumExp rho m + rho m

def addTerm (rho : Nat → Nat) : Nat → Nat
  | 0 => 0
  | m + 1 => 3 * addTerm rho m + 2 ^ cumExp rho m

def FollowsOddWord (a : Nat → Nat) (rho : Nat → Nat) : Prop :=
  ∀ k : Nat, 2 ^ rho k * a (k + 1) = 3 * a k + 1

@[simp] theorem cumExp_zero (rho : Nat → Nat) : cumExp rho 0 = 0 := rfl
@[simp] theorem cumExp_succ (rho : Nat → Nat) (m : Nat) :
    cumExp rho (m + 1) = cumExp rho m + rho m := rfl
@[simp] theorem addTerm_zero (rho : Nat → Nat) : addTerm rho 0 = 0 := rfl
@[simp] theorem addTerm_succ (rho : Nat → Nat) (m : Nat) :
    addTerm rho (m + 1) = 3 * addTerm rho m + 2 ^ cumExp rho m := rfl

theorem finite_odd_path_expansion
    {a : Nat → Nat} {rho : Nat → Nat}
    (hstep : FollowsOddWord a rho) :
    ∀ m : Nat,
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
            = 2 ^ cumExp rho m * (2 ^ rho m * a (m + 1)) := by ac_rfl
        _ = 2 ^ cumExp rho m * (3 * a m + 1) := by rw [hs]
        _ = 3 * (2 ^ cumExp rho m * a m) + 2 ^ cumExp rho m := by ring
        _ = 3 * (3 ^ m * a 0 + addTerm rho m) + 2 ^ cumExp rho m := by rw [ih]
        _ = 3 ^ (m + 1) * a 0 +
              (3 * addTerm rho m + 2 ^ cumExp rho m) := by
                rw [pow_succ]
                ring

theorem cyclic_closure_eq
    {a : Nat → Nat} {rho : Nat → Nat}
    (hstep : FollowsOddWord a rho) {q : Nat}
    (hcycle : a q = a 0) :
    2 ^ cumExp rho q * a 0 =
      3 ^ q * a 0 + addTerm rho q := by
  simpa [hcycle] using finite_odd_path_expansion hstep q

theorem common_word_affine_separation
    {a b : Nat → Nat} {rho : Nat → Nat}
    (ha : FollowsOddWord a rho)
    (hb : FollowsOddWord b rho)
    (m : Nat) :
    2 ^ cumExp rho m * a m + 3 ^ m * b 0 =
      2 ^ cumExp rho m * b m + 3 ^ m * a 0 := by
  have hA := finite_odd_path_expansion ha m
  have hB := finite_odd_path_expansion hb m
  omega

theorem no_distinct_synchronous_merger_same_word
    {a b : Nat → Nat} {rho : Nat → Nat}
    (ha : FollowsOddWord a rho)
    (hb : FollowsOddWord b rho)
    {m : Nat}
    (hend : a m = b m) :
    a 0 = b 0 := by
  have hsep := common_word_affine_separation ha hb m
  rw [hend] at hsep
  have hmul : 3 ^ m * b 0 = 3 ^ m * a 0 := by
    exact Nat.add_left_cancel hsep
  exact (mul_left_cancel_iff_of_pos (show 0 < 3 ^ m by positivity)).mp hmul.symm

end CollatzConjecture
