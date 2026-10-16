# The 3-Decomposition Conjecture in Lean 4

[![Lean Action CI](https://github.com/mjc191812/The-3-Decomposition-Conjecture/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/mjc191812/The-3-Decomposition-Conjecture/actions/workflows/lean_action_ci.yml)
[![Comparator](https://github.com/mjc191812/The-3-Decomposition-Conjecture/actions/workflows/comparator.yml/badge.svg)](https://github.com/mjc191812/The-3-Decomposition-Conjecture/actions/workflows/comparator.yml)
[![arXiv](https://img.shields.io/badge/arXiv-2608.25385-b31b1b)](https://arxiv.org/abs/2608.25385)
[![Lean v4.34.1](https://img.shields.io/badge/Lean-v4.34.1-6f42c1)](https://github.com/leanprover/lean4/tree/v4.34.1)
[![Mathlib v4.34.1](https://img.shields.io/badge/Mathlib-v4.34.1-0969da)](https://github.com/leanprover-community/mathlib4/tree/v4.34.1)
[![License: Apache 2.0](https://img.shields.io/badge/License-Apache%202.0-yellow)](LICENSE)

A complete Lean 4 / Mathlib formalization of

> Jicheng Ma, *Matching complements in subcubic graphs and a proof of the 3-Decomposition
> Conjecture*, [arXiv:2608.25385](https://arxiv.org/abs/2608.25385).

The main results of the paper are formalized: Theorem 1.2, Theorem 1.3, Theorem 1.4,
Corollary 1.5, Theorem 2.2 and Corollary 4.1. The only assumption beyond Lean's standard
axioms is
Schönberger's theorem on perfect matchings through a prescribed edge, the external result
the paper itself relies on. The four statements are checked by
[Comparator](https://github.com/leanprover/comparator) in CI.

## The theorem

> [!NOTE]
> **3-Decomposition Conjecture** (Hoffmann-Ostenhof, 2011). Every finite connected cubic
> loopless multigraph has an edge partition into a spanning tree, a 2-regular subgraph and a
> matching.

In [`ThreeDecomposition/Statement.lean`](ThreeDecomposition/Statement.lean):

```lean
def ThreeDecompositionConjecture : Prop :=
  ∀ (V : Type u) (E : Type v) [Fintype V] [Fintype E] (G : LooplessMultigraph V E),
    G.Connected → (∀ x, G.degree x = 3) →
      ∃ T C M : Set E, G.IsSpanningTree T ∧ G.IsTwoRegular C ∧ G.IsMatching M ∧
        Disjoint T C ∧ Disjoint T M ∧ Disjoint C M ∧ T ∪ C ∪ M = Set.univ
```

and in [`ThreeDecomposition/MainResults.lean`](ThreeDecomposition/MainResults.lean):

```lean
theorem threeDecompositionConjecture : ThreeDecompositionConjecture.{u, v}
```

## Main results

| Paper | Statement (`Statement.lean`) | Proof |
|---|---|---|
| Theorem 1.2 (3-Decomposition Conjecture) | `ThreeDecompositionConjecture` | `threeDecompositionConjecture` |
| Theorem 1.3 | `TerminalSelectionTheorem` | `terminalSelectionTheorem` |
| Theorem 1.4 | `FragileDecompositionTheorem` | `fragileDecompositionTheorem` |
| Corollary 1.5 | — | `multigraphFragileDecomposition` |
| Theorem 2.2 (Borse–Waphare) | `ProtectedCycleTheorem` (`Interfaces.lean`) | `protectedCycleTheorem` |
| Corollary 4.1 (2-Decomposition Conjecture) | `TwoDecompositionConjecture` | `twoDecompositionConjecture` |

## What has to be trusted

**Statements.** [`ThreeDecomposition/Statement.lean`](ThreeDecomposition/Statement.lean)
depends only on Mathlib and three definition files:

- [`Basic/Definitions.lean`](ThreeDecomposition/Basic/Definitions.lean): `{2,3}`-graphs,
  terminals, bridgelessness, cyclomatic number, the tree-plus-cycles conclusion of
  Theorem 1.3;
- [`Basic/Fragile.lean`](ThreeDecomposition/Basic/Fragile.lean): fragile and subcubic simple
  graphs, tree–matching decompositions;
- [`Multigraph/Defs.lean`](ThreeDecomposition/Multigraph/Defs.lean): loopless multigraphs
  (an edge type with an unordered pair of distinct ends), spanning trees, matchings,
  2-regular subgraphs, cycles and fragility. Mathlib's `Graph` has no connectivity theory
  yet, so this small structure is used instead; connectivity goes through `SimpleGraph`.

**Axiom.** [`External/SpecifiedEdgeMatching.lean`](ThreeDecomposition/External/SpecifiedEdgeMatching.lean)
states Schönberger's theorem (Theorem 2.1 of the paper) for finite simple graphs:

```lean
axiom exists_perfect_matching_containing_edge
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hconn : G.Connected) (hbridge : IsBridgeless G)
    (hcubic : ∀ v : V, (G.neighborSet v).ncard = 3)
    {u v : V} (huv : G.Adj u v) :
    ∃ M : G.Subgraph, M.IsPerfectMatching ∧ M.Adj u v
```

`#print axioms ThreeDecomposition.threeDecompositionConjecture` reports

```text
[propext, Classical.choice, Quot.sound, ThreeDecomposition.exists_perfect_matching_containing_edge]
```

and the same holds for the other three main results.

## Verification

- `lake build` compiles [`ThreeDecomposition/AxiomAudit.lean`](ThreeDecomposition/AxiomAudit.lean),
  which fails if any axiom is declared in the project besides Schönberger's theorem, or if
  an audited theorem depends on an axiom outside its allowed list (in particular on
  `sorryAx`).
- CI rejects any `sorry` or `admit` in the library.
- [`Comparator/Challenge.lean`](Comparator/Challenge.lean) restates the four main results with
  `sorry`, and [`Comparator/Solution.lean`](Comparator/Solution.lean) proves them.
  [Comparator](https://github.com/leanprover/comparator) checks, inside a landrun sandbox,
  that the solution proves exactly the challenge statements, that the permitted axioms
  (`propext`, `Quot.sound`, `Classical.choice` and Schönberger's theorem) have the same
  declarations in both, and that the proofs replay in the Lean kernel. The four `sorry`s in
  `Challenge.lean` are the only ones in the repository.

## Building

Install Lean with [elan](https://leanprover-community.github.io/get_started.html), then

```text
lake exe cache get
lake build
```

To run Comparator locally (Linux, with [landrun](https://github.com/Zouuup/landrun) on
`PATH`), build [comparator](https://github.com/leanprover/comparator) and its `lean4export`
dependency at tag `v4.34.0` with this project's `lean-toolchain`, then

```text
lake build Challenge Solution
COMPARATOR_LEAN4EXPORT=/path/to/lean4export lake env /path/to/comparator Comparator/config.json
```

[`.github/workflows/comparator.yml`](.github/workflows/comparator.yml) does exactly this.

## Repository structure

```text
ThreeDecomposition/
  Statement.lean          the four main statements
  MainResults.lean        their proofs
  AxiomAudit.lean         build-time axiom checks
  Basic.lean              basic-graph public interface
  Basic/
    Definitions.lean      statement-level definitions
    Fragile.lean          fragile subcubic graph definitions
    Lemmas.lean           counting, bridgelessness and examples
  MatchingComplement/     Lemmas 3.1–3.2 and Theorem 1.3
  Reduction.lean          Lemma 3.4: suppression and triangle replacement
  FirstEntry.lean         Lemma 3.3
  Extension.lean          base case and Lemma 3.5
  Lift.lean               lifts through the two reductions
  Restore.lean            restoration after suppressing a terminal
  Induction.lean          induction proving Theorem 1.3
  ProtectedCycle.lean     Theorem 2.2
  Fragile.lean            Theorem 1.4
  Multigraph/
    Defs.lean             loopless-multigraph definitions
    Theory.lean           Corollary 1.5, 2DC and 3DC
  External/               Schönberger's theorem (the only axiom)
  Audit/                  reusable axiom-audit command
Comparator/             Comparator challenge, solution and configuration
Blueprint/              proof plan, module map and status
```

## Relation to the paper

The four statements in `Statement.lean` match the corresponding paper statements exactly.
The formal proofs are sometimes organized differently for Lean;
[`Blueprint/README.md`](Blueprint/README.md) summarizes the main differences.

- Theorem 1.3 is proved by strong induction on `k` and `|V|` instead of a minimum
  counterexample, and Lemma 3.3 by exchanging one matching edge at a time (strong induction
  on `|N \ M|`) instead of flipping an alternating-path prefix.
- Reduction 1 (adjacent terminals) is implemented as the suppression of one terminal rather
  than contraction of the shared edge.
- The comparison graph of Section 3.3 attaches the terminals to a cycle of new vertices
  instead of a cubic tree.

## Citation

```bibtex
@misc{Ma2026ThreeDecomposition,
  author        = {Jicheng Ma},
  title         = {Matching complements in subcubic graphs and a proof of the
                   3-Decomposition Conjecture},
  year          = {2026},
  eprint        = {2608.25385},
  archivePrefix = {arXiv}
}
```

## License

[Apache 2.0](LICENSE).
