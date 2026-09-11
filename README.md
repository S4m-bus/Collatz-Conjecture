# Collatz Conjecture: forward paths

Lean 4 formalization of Muhammad Samuel Qudus's proposed forward-path formulation: every positive starting integer generates a complete finite path, Hamiltonian on its own visited vertices.

**Status: the general path-existence claim is not proved.** The project formalizes the forward objects, proves that the proposed complete-path claim implies Collatz, proves the converse, and provides exact finite examples. A successful build verifies those statements; it does not assert the general claim.

## The forward objects

`Collatz.step` is the original rule: even `n` goes to `n / 2`, and odd `n` goes to `3 * n + 1`. Its value at 1 is still 4. `Collatz.orbit n k` applies this rule exactly `k` times.

The path graph treats 1 as terminal: `ForwardEdge a b` requires `a > 0`, `a != 1`, and `b = step a`. This is the stop-at-first-1 convention, not an alteration of the arithmetic map.

`ForwardHamiltonianPath n` consists of:

- A finite last index `length`, giving vertices `orbit n 0` through `orbit n length`.
- A positive starting integer.
- No repeated vertex within those indices.
- Completeness: no required forward edge leaves the final vertex.

The endpoint is **not** assumed to equal 1 as a structure field; `ends_at_one` derives it. `edge_at` verifies the interior edges follow the permitted forward rule. Hamiltonian refers to the graph of this path's visited vertices, not to one path visiting every positive integer.

Completeness is stronger than being unable to append an *unvisited* vertex. The definition checks that there is no required next edge at all. No existence assumption for arbitrary starting integers is built into these definitions.

## Theorems and their exact scope

| Declaration | Statement |
| --- | --- |
| `equal_future` | Forward trajectories that meet have identical subsequent values. |
| `first_hit_exists` | A supplied finite witness of reaching 1 has a first hit. |
| `first_hit_no_repeated_vertex` | No value repeats up to a supplied first hit of 1. |
| `path_implies_reaches_one` | A complete finite forward Hamiltonian path reaches 1. |
| `reaches_one_implies_path` | A positive starting value that reaches 1 has such a path. |
| `forward_hamiltonian_implies_collatz` | **Given a proof of** `ForwardHamiltonianClaim`, obtain a proof of `CollatzConjecture`. |
| `forward_hamiltonian_iff_collatz` | The complete forward-path claim is equivalent to Collatz. |
| `forward_hamiltonian_27` | An exact path-existence proof for the starting integer 27. |

`ForwardHamiltonianClaim` is the proposition

```lean
∀ n, 0 < n → HasForwardHamiltonianPath n
```

There is currently no theorem establishing this proposition without that hypothesis. The remaining mathematical task is to construct the complete finite path for arbitrary positive `n`. Defining the proposition and proving its consequences does not supply that construction.

The individual witnesses for 1, 3, 6, 7, 15, 27, and 31 use ordinary `decide`, checked by Lean's kernel. `even_step` and `one_mod_four_forward` are symbolic forward identities for every natural parameter `q`. The project uses no backward Collatz map, no probabilistic model, no Mathlib dependency, and no external Collatz argument.

## Reproduce the verification

Install Lean via elan, then run:

```sh
lake build
lake env lean Audit.lean
```

The toolchain is pinned in `lean-toolchain`. GitHub Actions runs both commands.

`Audit.lean` examines the transitive axiom dependencies of declarations in the `Collatz` namespace. Its only permitted foundational axioms are Lean's `propext`, `Classical.choice`, and `Quot.sound`. It rejects dependencies on unfinished proof placeholders, native-decider trust axioms, or additional custom axioms. It also prints dependencies of the central theorems. A conditional theorem can pass this audit while still requiring its explicit hypothesis; the theorem statements above make that distinction visible.
