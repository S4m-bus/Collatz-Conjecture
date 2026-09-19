import Mathlib
import Collatz.Basic

namespace Collatz

/-- Exact exponent of 2 removed from 3a+1. -/
def v2 (a : ℕ) : ℕ := padicValNat 2 (3 * a + 1)

/-- Odd-compressed Collatz map, defined as the odd part of 3a+1. -/
def U (a : ℕ) : ℕ := Nat.divMaxPow (3 * a + 1) 2

/-- Exact odd decomposition: this is the algebraic definition behind the paper's U. -/
theorem U_factorization (a : ℕ) :
    U a * 2 ^ v2 a = 3 * a + 1 := by
  simpa [U, v2] using Nat.divMaxPow_mul_pow_padicValNat 2 (3 * a + 1)

/-- The odd part is always positive. -/
theorem U_pos (a : ℕ) : 0 < U a := by
  have hfac := U_factorization a
  by_contra h
  have hz : U a = 0 := Nat.eq_zero_of_not_pos h
  rw [hz, zero_mul] at hfac
  omega

/-- The compressed image is odd. -/
theorem U_odd (a : ℕ) : Odd (U a) := by
  rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
  exact Nat.not_dvd_divMaxPow (by omega) (by omega)

/-- The terminal odd state is fixed. -/
@[simp] theorem U_one : U 1 = 1 := by
  native_decide

/-- Its exact 2-adic exponent is 2. -/
@[simp] theorem v2_one : v2 1 = 2 := by
  native_decide

/-- Odd-compressed forward coalescence is just determinism of U. -/
theorem U_forward_coalescence {a b : ℕ} {i j : ℕ}
    (h : iter U i a = iter U j b) (t : ℕ) :
    iter U (i + t) a = iter U (j + t) b :=
  forward_coalescence U h t

end Collatz
