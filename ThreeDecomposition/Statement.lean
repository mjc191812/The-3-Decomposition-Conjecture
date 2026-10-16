import ThreeDecomposition.Basic.Definitions
import ThreeDecomposition.Basic.Fragile
import ThreeDecomposition.Multigraph.Defs

/-!
# Statements of the main results

This file fixes the formal statements that the project proves.  It depends only on Mathlib,
`ThreeDecomposition/Basic/Definitions.lean`, `ThreeDecomposition/Basic/Fragile.lean` and
`ThreeDecomposition/Multigraph/Defs.lean`; reviewing those files is enough to check that the
statements match the paper.  Changes to any of them change what is proved and need explicit
review.

* Theorem 1.3 (`TerminalSelectionTheorem`).  Let `H` be a finite connected bridgeless simple
  graph, every vertex of which has degree two or three.  If `S` is the set of degree-two
  vertices and `|S| ≥ 2`, then `H` has a matching `M` of size `|E(H)| - |V(H)| + 1` such that
  `H - M` is the disjoint union of one tree containing `S` and zero or more cycles.
* Theorem 1.4 (`FragileDecompositionTheorem`).  Every finite connected simple fragile
  subcubic graph admits an edge partition into a spanning tree and a matching.
* 2-Decomposition Conjecture (`TwoDecompositionConjecture`).  Every finite connected
  loopless multigraph with all degrees two or three in which every cycle is separating has
  an edge partition into a spanning tree and a nonempty matching.
* 3-Decomposition Conjecture (`ThreeDecompositionConjecture`).  Every finite connected cubic
  loopless multigraph has an edge partition into a spanning tree, a `2`-regular subgraph,
  and a matching.
-/

namespace ThreeDecomposition

open SimpleGraph

universe u v

def TerminalSelectionTheorem : Prop :=
  ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    G.Connected → IsBridgeless G → Is23Graph G → 2 ≤ (terminals G).ncard →
      TerminalSelectionStatement G (terminals G)

def FragileDecompositionTheorem : Prop :=
  ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    G.Connected → IsFragile G → IsSubcubic G → HasTreeMatchingDecomposition G

def TwoDecompositionConjecture : Prop :=
  ∀ (V : Type u) (E : Type v) [Fintype V] [Fintype E] (G : LooplessMultigraph V E),
    G.Connected → (∀ x, G.degree x = 2 ∨ G.degree x = 3) → G.IsFragile →
      ∃ T M : Set E, G.IsSpanningTree T ∧ G.IsMatching M ∧ M.Nonempty ∧
        Disjoint T M ∧ T ∪ M = Set.univ

def ThreeDecompositionConjecture : Prop :=
  ∀ (V : Type u) (E : Type v) [Fintype V] [Fintype E] (G : LooplessMultigraph V E),
    G.Connected → (∀ x, G.degree x = 3) →
      ∃ T C M : Set E, G.IsSpanningTree T ∧ G.IsTwoRegular C ∧ G.IsMatching M ∧
        Disjoint T C ∧ Disjoint T M ∧ Disjoint C M ∧ T ∪ C ∪ M = Set.univ

end ThreeDecomposition
