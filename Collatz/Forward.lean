import Std
import Lean.Elab.Tactic.Omega

/-!
The deterministic forward Collatz map. No inverse map or probabilistic model
is used. The raw map is unchanged at 1; the path relation stops at its first 1.
-/

namespace Collatz

/-- The original Collatz rule, including its ordinary value at 1. -/
def step (n : Nat) : Nat :=
  if n % 2 = 0 then n / 2 else 3 * n + 1

/-- Exactly k applications of the original forward rule. -/
def orbit (n : Nat) : Nat → Nat
  | 0 => n
  | k + 1 => step (orbit n k)

@[simp] theorem orbit_zero (n : Nat) : orbit n 0 = n := rfl

@[simp] theorem orbit_succ (n k : Nat) :
    orbit n (k + 1) = step (orbit n k) := rfl

theorem step_pos {n : Nat} (hn : 0 < n) : 0 < step n := by
  unfold step
  split <;> omega

theorem orbit_pos {n : Nat} (hn : 0 < n) (k : Nat) :
    0 < orbit n k := by
  induction k with
  | zero => exact hn
  | succ k ih => exact step_pos ih

theorem orbit_add (n i j : Nat) :
    orbit n (i + j) = orbit (orbit n i) j := by
  induction j with
  | zero => rfl
  | succ j ih => simp only [Nat.add_succ, orbit_succ, ih]

/-- Meeting forward trajectories have the same subsequent values. -/
theorem equal_future {n m i j : Nat}
    (h : orbit n i = orbit m j) (r : Nat) :
    orbit n (i + r) = orbit m (j + r) := by
  rw [orbit_add, orbit_add, h]

/-- An edge of the positive-integer forward graph, with 1 terminal. -/
def ForwardEdge (a b : Nat) : Prop :=
  0 < a ∧ a ≠ 1 ∧ b = step a

/-- Completeness means there is no required next edge at the last vertex.
It does not mean merely that there is no unused next vertex. -/
def CompleteAt (n k : Nat) : Prop :=
  ∀ b, ¬ ForwardEdge (orbit n k) b

theorem complete_iff_one {n k : Nat} (hn : 0 < n) :
    CompleteAt n k ↔ orbit n k = 1 := by
  constructor
  · intro h
    by_cases heq : orbit n k = 1
    · exact heq
    · exact False.elim (h (step (orbit n k)) ⟨orbit_pos hn k, heq, rfl⟩)
  · intro heq b hedge
    exact hedge.2.1 heq

/-- The path's actual forward vertices at indices 0 through k are distinct. -/
def NoRepeatedVertex (n k : Nat) : Prop :=
  ∀ i j, i ≤ k → j ≤ k → orbit n i = orbit n j → i = j

/-- A finite path, Hamiltonian on its own visited vertices, that is complete
under the forward rule. Its endpoint is derived to be 1 below, not assumed
as a field. No assertion about existence for arbitrary n is built in. -/
structure ForwardHamiltonianPath (n : Nat) where
  length : Nat
  positive_start : 0 < n
  distinct_vertices : NoRepeatedVertex n length
  complete : CompleteAt n length

def HasForwardHamiltonianPath (n : Nat) : Prop :=
  Nonempty (ForwardHamiltonianPath n)

def ReachesOne (n : Nat) : Prop :=
  ∃ k, orbit n k = 1

def FirstHit (n k : Nat) : Prop :=
  orbit n k = 1 ∧ ∀ j, j < k → orbit n j ≠ 1

theorem ForwardHamiltonianPath.ends_at_one {n : Nat}
    (p : ForwardHamiltonianPath n) : orbit n p.length = 1 :=
  (complete_iff_one p.positive_start).mp p.complete

theorem ForwardHamiltonianPath.first_hit {n : Nat}
    (p : ForwardHamiltonianPath n) : FirstHit n p.length := by
  refine ⟨p.ends_at_one, ?_⟩
  intro j hj hOne
  have heq : orbit n j = orbit n p.length := hOne.trans p.ends_at_one.symm
  have hij := p.distinct_vertices j p.length (by omega) (by omega) heq
  omega

/-- Every edge in the finite object is an actual permitted forward edge. -/
theorem ForwardHamiltonianPath.edge_at {n : Nat}
    (p : ForwardHamiltonianPath n) {i : Nat} (hi : i < p.length) :
    ForwardEdge (orbit n i) (orbit n (i + 1)) :=
  ⟨orbit_pos p.positive_start i, p.first_hit.2 i hi, rfl⟩

theorem path_implies_reaches_one {n : Nat} (h : HasForwardHamiltonianPath n) :
    ReachesOne n := by
  obtain ⟨p⟩ := h
  exact ⟨p.length, p.ends_at_one⟩

/-- Every finite witness of reaching 1 has a least first hit. -/
theorem first_hit_exists (n k : Nat) (h : orbit n k = 1) :
    ∃ r, r ≤ k ∧ FirstHit n r := by
  classical
  induction k using Nat.strongRecOn with
  | ind k ih =>
    by_cases earlier : ∃ j, j < k ∧ orbit n j = 1
    · obtain ⟨j, hj, hOne⟩ := earlier
      obtain ⟨r, hr, hFirst⟩ := ih j hj hOne
      exact ⟨r, by omega, hFirst⟩
    · refine ⟨k, Nat.le_refl k, h, ?_⟩
      intro j hj hOne
      exact earlier ⟨j, hj, hOne⟩

/-- Determinism proves nonrepetition up to the first hit of 1. -/
theorem first_hit_no_repeated_vertex {n k : Nat} (h : FirstHit n k) :
    NoRepeatedVertex n k := by
  have no_lt : ∀ i j, i ≤ k → j ≤ k →
      orbit n i = orbit n j → ¬ i < j := by
    intro i j _ hj heq hij
    have hFuture := equal_future heq (k - j)
    have hEnd : j + (k - j) = k := Nat.add_sub_of_le hj
    rw [hEnd, h.1] at hFuture
    exact h.2 (i + (k - j)) (by omega) hFuture
  intro i j hi hj heq
  have hNotLt := no_lt i j hi hj heq
  have hNotGt := no_lt j i hj hi heq.symm
  omega

theorem reaches_one_implies_path {n : Nat} (hn : 0 < n)
    (h : ReachesOne n) : HasForwardHamiltonianPath n := by
  obtain ⟨k, hOne⟩ := h
  obtain ⟨r, _, hFirst⟩ := first_hit_exists n k hOne
  exact ⟨{
    length := r
    positive_start := hn
    distinct_vertices := first_hit_no_repeated_vertex hFirst
    complete := (complete_iff_one hn).mpr hFirst.1
  }⟩

theorem path_iff_reaches_one {n : Nat} (hn : 0 < n) :
    HasForwardHamiltonianPath n ↔ ReachesOne n :=
  ⟨path_implies_reaches_one, reaches_one_implies_path hn⟩

/-- The user's general forward-path claim. This is a proposition, not an axiom
or a theorem asserting that the proposition holds. -/
def ForwardHamiltonianClaim : Prop :=
  ∀ n, 0 < n → HasForwardHamiltonianPath n

def CollatzConjecture : Prop :=
  ∀ n, 0 < n → ReachesOne n

/-- A proof of the complete forward-path claim would prove Collatz. -/
theorem forward_hamiltonian_implies_collatz
    (h : ForwardHamiltonianClaim) : CollatzConjecture := by
  intro n hn
  exact path_implies_reaches_one (h n hn)

theorem forward_hamiltonian_iff_collatz :
    ForwardHamiltonianClaim ↔ CollatzConjecture := by
  constructor
  · exact forward_hamiltonian_implies_collatz
  · intro h n hn
    exact reaches_one_implies_path hn (h n hn)

end Collatz
