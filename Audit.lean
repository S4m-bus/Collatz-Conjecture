import Collatz
import Lean.Util.CollectAxioms

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut checked := 0
  for (name, _) in env.constants.toList do
    if (`Collatz).isPrefixOf name then
      let axioms ← collectAxioms name
      for ax in axioms do
        unless allowed.contains ax do
          throwError "Disallowed axiom {ax} in {name}"
      checked := checked + 1
  logInfo m!"Axiom audit passed for {checked} Collatz declarations."

#print axioms Collatz.first_hit_no_repeated_vertex
#print axioms Collatz.forward_hamiltonian_implies_collatz
#print axioms Collatz.forward_hamiltonian_iff_collatz
#print axioms Collatz.forward_hamiltonian_27
#check Collatz.ForwardHamiltonianClaim
