import Mathlib

namespace Collatz

/-- Standard Collatz map, extended to 0 for convenience. All paper-level statements
    quantify over positive naturals. -/
def T (n : ℕ) : ℕ :=
  if n % 2 = 0 then n / 2 else 3 * n + 1

/-- Stopped Collatz map: 1 is absorbing. -/
def C (n : ℕ) : ℕ :=
  if n = 1 then 1 else T n

/-- Explicit finite iteration, used so the formalization does not depend on notation
    for `Function.iterate`. -/
def iter {α : Type*} (f : α → α) : ℕ → α → α
  | 0, x => x
  | k + 1, x => iter f k (f x)

@[simp] theorem iter_zero {α : Type*} (f : α → α) (x : α) :
    iter f 0 x = x := rfl

@[simp] theorem iter_succ {α : Type*} (f : α → α) (k : ℕ) (x : α) :
    iter f (k + 1) x = iter f k (f x) := rfl

theorem iter_add {α : Type*} (f : α → α) (m n : ℕ) (x : α) :
    iter f (m + n) x = iter f n (iter f m x) := by
  induction m generalizing x with
  | zero => simp
  | succ m ih =>
      simp [Nat.succ_add, ih]

theorem iter_succ_right {α : Type*} (f : α → α) (k : ℕ) (x : α) :
    iter f (k + 1) x = f (iter f k x) := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
      simp only [iter_succ]
      rw [ih (f x), ih x]

@[simp] theorem C_one : C 1 = 1 := by
  simp [C]

@[simp] theorem iter_C_one (k : ℕ) : iter C k 1 = 1 := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simp [iter_succ, C_one, ih]

theorem C_eq_T_of_ne_one {n : ℕ} (h : n ≠ 1) : C n = T n := by
  simp [C, h]

/-- A target is hit by forward iteration. -/
def Hits {α : Type*} (f : α → α) (x z : α) : Prop :=
  ∃ k : ℕ, iter f k x = z

/-- Two starting points eventually coalesce, allowing different forward times. -/
def Coalesces {α : Type*} (f : α → α) (a b : α) : Prop :=
  ∃ i j : ℕ, iter f i a = iter f j b

/-- Exact first hitting statement at a specified time. -/
def FirstHit {α : Type*} (f : α → α) (terminal x : α) (k : ℕ) : Prop :=
  iter f k x = terminal ∧ ∀ i < k, iter f i x ≠ terminal

/-- Simplicity of a finite forward prefix through time k. -/
def SimplePrefix {α : Type*} (f : α → α) (x : α) (k : ℕ) : Prop :=
  ∀ ⦃i j : ℕ⦄, i < j → j ≤ k → iter f i x ≠ iter f j x

/-- Forward coalescence: after a meeting, all subsequent states coincide. -/
theorem forward_coalescence {α : Type*} (f : α → α) {a b : α} {i j : ℕ}
    (h : iter f i a = iter f j b) (t : ℕ) :
    iter f (i + t) a = iter f (j + t) b := by
  rw [iter_add, iter_add, h]

/-- Repetition forces a periodic tail. -/
theorem repeat_forces_periodic_tail {α : Type*} (f : α → α) {x : α} {i j : ℕ}
    (h : iter f i x = iter f j x) :
    ∀ t : ℕ, iter f (i + t) x = iter f (j + t) x :=
  fun t => forward_coalescence f h t

/-- A first-hit finite path cannot repeat a state before its terminal hit. -/
theorem firstHit_simple {α : Type*} (f : α → α) {terminal x : α} {k : ℕ}
    (hfirst : FirstHit f terminal x k) :
    SimplePrefix f x k := by
  intro i j hij hjk heq
  rcases hfirst with ⟨hk, hmin⟩
  have htail := forward_coalescence f heq (k - j)
  have hj : j + (k - j) = k := by omega
  have hi : i + (k - j) < k := by omega
  have hearly : iter f (i + (k - j)) x = terminal := by
    calc
      iter f (i + (k - j)) x = iter f (j + (k - j)) x := htail
      _ = iter f k x := by rw [hj]
      _ = terminal := hk
  exact (hmin (i + (k - j)) hi) hearly

/-- Eventual forward coalescence is reflexive. -/
theorem coalesces_refl {α : Type*} (f : α → α) (a : α) :
    Coalesces f a a := by
  exact ⟨0, 0, rfl⟩

theorem coalesces_symm {α : Type*} (f : α → α) {a b : α}
    (h : Coalesces f a b) : Coalesces f b a := by
  rcases h with ⟨i, j, hij⟩
  exact ⟨j, i, hij.symm⟩

theorem coalesces_trans {α : Type*} (f : α → α) {a b c : α}
    (hab : Coalesces f a b) (hbc : Coalesces f b c) :
    Coalesces f a c := by
  rcases hab with ⟨i, j, hij⟩
  rcases hbc with ⟨p, q, hpq⟩
  refine ⟨i + p, q + j, ?_⟩
  calc
    iter f (i + p) a = iter f p (iter f i a) := iter_add f i p a
    _ = iter f p (iter f j b) := congrArg (iter f p) hij
    _ = iter f (j + p) b := (iter_add f j p b).symm
    _ = iter f (p + j) b := by rw [Nat.add_comm]
    _ = iter f j (iter f p b) := iter_add f p j b
    _ = iter f j (iter f q c) := congrArg (iter f j) hpq
    _ = iter f (q + j) c := (iter_add f q j c).symm

theorem coalesces_equivalence {α : Type*} (f : α → α) :
    Equivalence (Coalesces f) where
  refl := coalesces_refl f
  symm := coalesces_symm f
  trans := coalesces_trans f

/-- Forward hitting set. -/
def HittingSet {α : Type*} (f : α → α) (z : α) : Set α :=
  {x | Hits f x z}

/-- Hitting sets of a deterministic map are laminar whenever they intersect. -/
theorem hittingSet_laminar {α : Type*} (f : α → α) {x y : α}
    (hne : (HittingSet f x ∩ HittingSet f y).Nonempty) :
    HittingSet f x ⊆ HittingSet f y ∨ HittingSet f y ⊆ HittingSet f x := by
  rcases hne with ⟨a, ⟨⟨i, hix⟩, ⟨j, hjy⟩⟩⟩
  rcases le_total i j with hij | hji
  · left
    intro c hc
    rcases hc with ⟨m, hmc⟩
    have hstep : iter f (j - i) x = y := by
      calc
        iter f (j - i) x = iter f (j - i) (iter f i a) := by rw [hix]
        _ = iter f (i + (j - i)) a := (iter_add f i (j - i) a).symm
        _ = iter f j a := by congr 1 <;> omega
        _ = y := hjy
    refine ⟨m + (j - i), ?_⟩
    calc
      iter f (m + (j - i)) c = iter f (j - i) (iter f m c) := iter_add f m (j - i) c
      _ = iter f (j - i) x := by rw [hmc]
      _ = y := hstep
  · right
    intro c hc
    rcases hc with ⟨m, hmc⟩
    have hstep : iter f (i - j) y = x := by
      calc
        iter f (i - j) y = iter f (i - j) (iter f j a) := by rw [hjy]
        _ = iter f (j + (i - j)) a := (iter_add f j (i - j) a).symm
        _ = iter f i a := by congr 1 <;> omega
        _ = x := hix
    refine ⟨m + (i - j), ?_⟩
    calc
      iter f (m + (i - j)) c = iter f (i - j) (iter f m c) := iter_add f m (i - j) c
      _ = iter f (i - j) y := by rw [hmc]
      _ = x := hstep

end Collatz
