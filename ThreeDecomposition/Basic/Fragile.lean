import ThreeDecomposition.Basic.Definitions

/-!
# Fragile graphs and tree–matching decompositions (simple graphs)

Definitions used in the statement of Theorem 1.4.
-/

namespace ThreeDecomposition

open SimpleGraph

variable {V : Type*}

/-- Every cycle of `G` is separating: deleting the edges of any cycle disconnects `G`. -/
def IsFragile (G : SimpleGraph V) : Prop :=
  ∀ ⦃u : V⦄ (p : G.Walk u u), p.IsCycle → ¬(G.deleteEdges {e | e ∈ p.edges}).Connected

/-- Every vertex has degree at most three. -/
def IsSubcubic [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  ∀ v, G.degree v ≤ 3

/-- `E(G) = E(T) ⊔ E(M)` for a spanning tree `T` of `G` and a matching `M` of `G`. -/
def HasTreeMatchingDecomposition (G : SimpleGraph V) : Prop :=
  ∃ (T : SimpleGraph V) (M : G.Subgraph), T ≤ G ∧ T.IsTree ∧ M.IsMatching ∧
    Disjoint T.edgeSet M.edgeSet ∧ T.edgeSet ∪ M.edgeSet = G.edgeSet

end ThreeDecomposition
