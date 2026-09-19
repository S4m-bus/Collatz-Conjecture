import Mathlib

namespace CollatzConjecture

/-- Cumulative exponent of a finite valuation word. -/
def rsum (r : Nat → Nat) : Nat → Nat
  | 0 => 0
  | m + 1 => rsum r m + r m

@[simp] theorem rsum_zero (r : Nat → Nat) : rsum r 0 = 0 := rfl

@[simp] theorem rsum_succ (r : Nat → Nat) (m : Nat) :
    rsum r (m + 1) = rsum r m + r m := rfl

/-- Abstract exact odd-step recurrence used by Sections 5--7:
    2^(r_k) a_{k+1} = 3 a_k + 1.  We work over integers here so
    path differences can be subtracted without truncation. -/
def OddRecurrence (a : Nat → Int) (r : Nat → Nat) : Prop :=
  ∀ k : Nat, (2 : Int) ^ (r k) * a (k + 1) = 3 * a k + 1

/-- If two forward prefixes carry the same exponent at one step,
    their difference obeys the exact affine-separation identity. -/
theorem one_step_common_word_separation
    {a b : Nat → Int} {r : Nat → Nat}
    (ha : OddRecurrence a r) (hb : OddRecurrence b r) (k : Nat) :
    (2 : Int) ^ (r k) * (a (k + 1) - b (k + 1))
      = 3 * (a k - b k) := by
  calc
    (2 : Int) ^ (r k) * (a (k + 1) - b (k + 1))
        = (2 : Int) ^ (r k) * a (k + 1)
          - (2 : Int) ^ (r k) * b (k + 1) := by ring
    _ = (3 * a k + 1) - (3 * b k + 1) := by
          rw [ha k, hb k]
    _ = 3 * (a k - b k) := by ring

/-- Exact finite common-word separation:
    2^(sum r) (a_m-b_m) = 3^m (a_0-b_0).
    This formalizes the finite identity used in Section 7, with no
    density, averaging, probability, or asymptotics. -/
theorem common_word_prefix_separation
    {a b : Nat → Int} {r : Nat → Nat}
    (ha : OddRecurrence a r) (hb : OddRecurrence b r) :
    ∀ m : Nat,
      (2 : Int) ^ (rsum r m) * (a m - b m)
        = (3 : Int) ^ m * (a 0 - b 0) := by
  intro m
  induction m with
  | zero =>
      simp
  | succ m ih =>
      calc
        (2 : Int) ^ (rsum r (m + 1)) * (a (m + 1) - b (m + 1))
            = (2 : Int) ^ (rsum r m) *
                ((2 : Int) ^ (r m) * (a (m + 1) - b (m + 1))) := by
                  rw [rsum_succ, pow_add]
                  ring
        _ = (2 : Int) ^ (rsum r m) * (3 * (a m - b m)) := by
              rw [one_step_common_word_separation ha hb m]
        _ = 3 * ((2 : Int) ^ (rsum r m) * (a m - b m)) := by ring
        _ = 3 * ((3 : Int) ^ m * (a 0 - b 0)) := by rw [ih]
        _ = (3 : Int) ^ (m + 1) * (a 0 - b 0) := by
              rw [pow_succ]
              ring

/-- Consequence used by the paper: under a shared finite exponent word,
    equality of endpoints forces equality of starts. -/
theorem common_word_no_synchronous_merger
    {a b : Nat → Int} {r : Nat → Nat}
    (ha : OddRecurrence a r) (hb : OddRecurrence b r)
    {m : Nat} (hend : a m = b m) :
    a 0 = b 0 := by
  have h := common_word_prefix_separation ha hb m
  rw [hend, sub_self, mul_zero] at h
  have hpow : (3 : Int) ^ m ≠ 0 := pow_ne_zero _ (by norm_num)
  have hzero : (3 : Int) ^ m * (a 0 - b 0) = 0 := h.symm
  apply sub_eq_zero.mp
  exact (mul_eq_zero.mp hzero).resolve_left hpow

end CollatzConjecture
