import ThreeDecomposition.Basic.Fragile

/-!
# Interfaces between workstreams

Intermediate results that one part of the development proves and another part uses.  They
are stated as propositions so that the consumer can be written before the producer is
finished; the final theorems instantiate them with proofs.
-/

namespace ThreeDecomposition

open SimpleGraph

universe u

/-- Theorem 2.2 (Borse–Waphare).  Let `G` be a connected simple graph and `Q` a connected
subgraph.  If `G` has a cycle edge-disjoint from `Q` and every vertex outside `Q` has degree
at least three, then `G` has a cycle `C` edge-disjoint from `Q` such that `G - E(C)` is
connected. -/
def ProtectedCycleTheorem : Prop :=
  ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (Q : G.Subgraph),
    G.Connected → Q.Connected →
    (∃ (x : V) (p : G.Walk x x), p.IsCycle ∧ ∀ e ∈ p.edges, e ∉ Q.edgeSet) →
    (∀ x, x ∉ Q.verts → 3 ≤ G.degree x) →
    ∃ (x : V) (p : G.Walk x x), p.IsCycle ∧ (∀ e ∈ p.edges, e ∉ Q.edgeSet) ∧
      (G.deleteEdges {e | e ∈ p.edges}).Connected

end ThreeDecomposition
