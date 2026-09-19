import Mathlib
import CollatzConjecture.Basic
import CollatzConjecture.Forward

namespace CollatzConjecture

/-- Exact exponent of 2 removed from 3a+1. -/
def v2 (a : Nat) : Nat := padicValNat 2 (3 * a + 1)

/-- Odd-compressed Collatz map: the odd part of 3a+1. -/
def U (a : Nat) : Nat := Nat.divMaxPow (3 * a + 1) 2

theorem U_factorization (a : Nat) :
    U a * 2 ^ v2 a = 3 * a + 1 := by
  simpa [U, v2] using Nat.divMaxPow_mul_pow_padicValNat 2 (3 * a + 1)

theorem U_pos (a : Nat) : 0 < U a := by
  have hfac := U_factorization a
  by_contra h
  have hz : U a = 0 := Nat.eq_zero_of_not_pos h
  rw [hz, zero_mul] at hfac
  omega

theorem U_odd (a : Nat) : Odd (U a) := by
  rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
  exact Nat.not_dvd_divMaxPow (by omega) (by omega)

@[simp] theorem U_one : U 1 = 1 := by
  native_decide

@[simp] theorem v2_one : v2 1 = 2 := by
  native_decide

theorem U_forward_coalescence {a b : Nat} {i j : Nat}
    (h : iter U i a = iter U j b) :
    ∀ t : Nat, iter U (i + t) a = iter U (j + t) b :=
  forward_coalescence U h

end CollatzConjecture
