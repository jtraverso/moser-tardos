# The Moser–Tardos theorem in Lean 4

Author and maintainer: **Juan Pablo Traverso Gianini**. Licence: Apache-2.0 (see `LICENSE`).

R. A. Moser and G. Tardos, *A constructive proof of the general Lovász Local Lemma*, J. ACM 57
(2010), Article 11, [doi:10.1145/1667053.1667060](https://doi.org/10.1145/1667053.1667060).

**Variable setting.** Finitely many independent random variables indexed by `ι`, with values in a
finite type `α` and laws `P i`. There are `n` bad events; event `j` is determined by the variables
in `vbl j`, and its neighbours are the other events sharing a variable with it. The algorithm samples
all variables and, while some event holds, resamples the variables of the first violated one. It is
run on a *resampling table*: variable `i` takes the table entries `T i 0, T i 1, …` in turn.

Under the condition of the Lovász Local Lemma, `P(A_j) ≤ x_j ∏_{k ∈ Γ(j)} (1 - x_k)` with
`0 ≤ x_j < 1`, and for a random table of depth `t` (independent entries with the laws `P i`):

| Lean (namespace `MoserTardosTheorem`) | Statement |
|---|---|
| `expected_count_le` | Among the first `t` steps, event `j` is resampled at most `x_j / (1 - x_j)` times in expectation (Moser–Tardos, Theorem 1.2). |
| `expected_totalCount_le` | The expected total number of resamplings among the first `t` steps is at most `∑_j x_j / (1 - x_j)`. |
| `pProb_running_le` | The probability that the algorithm has not stopped after `t` steps is at most `(∑_j x_j / (1 - x_j)) / t`. |
| `exists_avoiding` | Some assignment avoids all the events (the Lovász Local Lemma in the variable setting). |

## Files

- [`Challenge.lean`](Challenge.lean): the definitions and the statements; it imports only Mathlib.
- [`Solution.lean`](Solution.lean) and [`MoserTardos/`](MoserTardos): the proofs.
- [`PseudorandomLib/FiniteProb.lean`](PseudorandomLib/FiniteProb.lean): finite product spaces,
  byte-identical to the registered entry
  [jtraverso/pseudorandom-hypergraph-matchings](https://github.com/jtraverso/pseudorandom-hypergraph-matchings)
  (PALOMAR-2026-10-17-000004).
- [`comparator.json`](comparator.json), [`MATHLIB_DEFINITIONS.md`](MATHLIB_DEFINITIONS.md),
  [`formalization.yaml`](formalization.yaml).

## How the proof goes

- `Defs.lean`: instances, the algorithm on a table, its log and counts.
- `GaltonWatson.lean`: proper witness trees as a finite type `Tr d j` (children indexed by the
  neighbours of the label, at most one each). Their total weight `∑ ∏ p(labels)` satisfies the
  Galton–Watson recursion and is at most `x_j / (1 - x_j)` under the LLL condition.
- `Indep.lean`: independence of events determined by disjoint sets of coordinates, and the law of
  coordinates read along an injective map.
- `WitnessTree.lean`: the `τ`-check reads, at each vertex `v`, the table entry of index "number of
  deeper vertices whose event shares the variable". For a *good* tree (distinct vertices, and no
  two vertices at the same depth with equal or neighbouring events), the entries read are
  distinct, so it passes with probability at most the weight of the tree.
- `LogTree.lean`: the witness tree of a step, built from the log by going back in time and
  attaching each earlier step as deep as possible (depth by recursion as a supremum in
  `WithBot ℕ`, then parent and descendants). It is good, and it passes the `τ`-check on the
  table that drove the run: the variable `i` of a vertex has been resampled once per deeper vertex
  involving `i`. Distinct steps resampling `j` give distinct trees, since the number of vertices
  labelled `j` grows.
- `Main.lean`: hence `E[count j] ≤ ∑_τ P(τ-check) ≤ ∑_τ weight ≤ x_j / (1 - x_j)`, then the total,
  Markov's inequality for termination, and the existence corollary.
- `Sanity.lean`: a fair coin with one event satisfies the condition with `x = 1/2`, giving at most
  one expected resampling and an avoiding assignment. An event that always holds cannot satisfy
  the condition.

## Provenance and checks

The theorem was chosen by the author; the formalization was written with Claude (Claude Code).
Lean `v4.35.0-rc3`, Mathlib `c55e6e786f49471c72fbddbec5415808896aec1e`: `lake build`; no `sorry`;
`#print axioms` gives only `propext`, `Classical.choice`, `Quot.sound`; the elaborated statements
and definitions of the Challenge and the Solution are identical (`pp.all`).
