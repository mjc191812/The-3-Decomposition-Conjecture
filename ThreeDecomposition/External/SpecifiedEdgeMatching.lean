import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import ThreeDecomposition.Basic

/-!
# External interface: specified-edge perfect matchings

This file declares Schönberger's theorem (Theorem 2.1 of the paper): every
finite connected bridgeless cubic simple graph has a perfect matching
containing any prescribed edge.  It is the only non-standard axiom used in the
project, as verified by `ThreeDecomposition/AxiomAudit.lean`.
-/

namespace ThreeDecomposition

open SimpleGraph

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- Schönberger's theorem (Theorem 2.1): every finite connected bridgeless
cubic simple graph has a perfect matching containing any prescribed edge. -/
axiom exists_perfect_matching_containing_edge
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hconn : G.Connected)
    (hbridge : IsBridgeless G)
    (hcubic : ∀ v : V, (G.neighborSet v).ncard = 3)
    {u v : V} (huv : G.Adj u v) :
    ∃ M : G.Subgraph, M.IsPerfectMatching ∧ M.Adj u v

end ThreeDecomposition
