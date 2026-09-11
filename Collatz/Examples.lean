import Collatz.Forward

set_option maxRecDepth 4096

namespace Collatz

/-- These are exact kernel-checked witnesses for individual starting values.
They are not used to infer a statement about every positive integer. -/
theorem reaches_one_1 : ReachesOne 1 := ⟨0, by decide⟩
theorem reaches_one_3 : ReachesOne 3 := ⟨7, by decide⟩
theorem reaches_one_6 : ReachesOne 6 := ⟨8, by decide⟩
theorem reaches_one_7 : ReachesOne 7 := ⟨16, by decide⟩
theorem reaches_one_15 : ReachesOne 15 := ⟨17, by decide⟩
theorem reaches_one_27 : ReachesOne 27 := ⟨111, by decide⟩
theorem reaches_one_31 : ReachesOne 31 := ⟨106, by decide⟩

theorem forward_hamiltonian_27 : HasForwardHamiltonianPath 27 :=
  reaches_one_implies_path (by decide) reaches_one_27

theorem path_27_no_repetition :
    ∃ k, FirstHit 27 k ∧ NoRepeatedVertex 27 k := by
  obtain ⟨p⟩ := forward_hamiltonian_27
  exact ⟨p.length, p.first_hit, p.distinct_vertices⟩

/-- An exact, symbolic forward identity for every natural q. -/
theorem even_step (q : Nat) : step (2 * q) = q := by
  unfold step
  split <;> omega

theorem one_mod_four_forward (q : Nat) :
    orbit (4 * q + 1) 3 = 3 * q + 1 := by
  have h1 : step (4 * q + 1) = 12 * q + 4 := by
    unfold step
    split <;> omega
  have h2 : step (12 * q + 4) = 6 * q + 2 := by
    unfold step
    split <;> omega
  have h3 : step (6 * q + 2) = 3 * q + 1 := by
    unfold step
    split <;> omega
  change step (step (step (4 * q + 1))) = 3 * q + 1
  rw [h1, h2, h3]

end Collatz
