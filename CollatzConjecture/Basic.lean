import Mathlib

namespace CollatzConjecture

/-- Pure recursive iteration, used so the forward-path proofs do not depend on
    any external dynamical-systems API. -/
def iter {α : Type*} (f : α → α) : Nat → α → α
  | 0, x => x
  | k + 1, x => f (iter f k x)

@[simp] theorem iter_zero {α : Type*} (f : α → α) (x : α) :
    iter f 0 x = x := rfl

@[simp] theorem iter_succ {α : Type*} (f : α → α) (k : Nat) (x : α) :
    iter f (k + 1) x = f (iter f k x) := rfl

theorem iter_add {α : Type*} (f : α → α) (m n : Nat) (x : α) :
    iter f (m + n) x = iter f n (iter f m x) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Nat.add_succ, iter_succ, iter_succ, ih]

/-- The ordinary Collatz map. -/
def T (n : Nat) : Nat :=
  if n % 2 = 0 then n / 2 else 3 * n + 1

/-- The paper's stopped-at-1 Collatz map. -/
def C (n : Nat) : Nat :=
  if n = 1 then 1 else T n

@[simp] theorem C_one : C 1 = 1 := by
  simp [C]

theorem C_eq_T_of_ne_one {n : Nat} (h : n ≠ 1) :
    C n = T n := by
  simp [C, h]

@[simp] theorem iter_C_one (k : Nat) : iter C k 1 = 1 := by
  induction k with
  | zero => rfl
  | succ k ih => simp [iter, ih]

/-- The exact stopped-map Collatz statement on positive naturals. -/
def ReachesOne (n : Nat) : Prop :=
  ∃ k : Nat, iter C k n = 1

/-- A path intersects the stopped terminal path P₁. -/
def IntersectsTerminalPath (n : Nat) : Prop :=
  ∃ i j : Nat, iter C i n = iter C j 1

/-- The global assertion used in Section 9: every positive path intersects P₁. -/
def GlobalTerminalMerge : Prop :=
  ∀ n : Nat, 0 < n → IntersectsTerminalPath n

/-- The stopped-map Collatz statement. -/
def StoppedCollatz : Prop :=
  ∀ n : Nat, 0 < n → ReachesOne n

/-- Reaching 1 under the ordinary Collatz map. -/
def StandardReachesOne (n : Nat) : Prop :=
  ∃ k : Nat, iter T k n = 1

/-- The ordinary Collatz conjecture. -/
def Collatz : Prop :=
  ∀ n : Nat, 0 < n → StandardReachesOne n

end CollatzConjecture
