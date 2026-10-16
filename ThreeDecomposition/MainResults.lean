import ThreeDecomposition.MatchingComplement.Main
import ThreeDecomposition.ProtectedCycle
import ThreeDecomposition.Fragile
import ThreeDecomposition.Multigraph.Theory

/-!
# Main results

The four statements of `ThreeDecomposition/Statement.lean`, proved.  Their only non-standard
axiom is `exists_perfect_matching_containing_edge` (Schönberger's theorem), as checked in
`ThreeDecomposition/AxiomAudit.lean`.
-/

namespace ThreeDecomposition

universe u v

/-- **Theorem 1.4.** -/
theorem fragileDecompositionTheorem : FragileDecompositionTheorem.{u} :=
  fragileDecompositionTheorem_of_protectedCycle protectedCycleTheorem

/-- **Corollary 1.5.** Every finite connected fragile subcubic loopless multigraph admits an
edge partition into a spanning tree and a matching. -/
theorem multigraphFragileDecomposition
    (V : Type u) (E : Type v) [Finite V] [Finite E] (G : LooplessMultigraph V E)
    (hconn : G.Connected) (hfrag : G.IsFragile) (hdeg : ∀ x, G.degree x ≤ 3) :
    ∃ T M : Set E, G.IsSpanningTree T ∧ G.IsMatching M ∧
      Disjoint T M ∧ T ∪ M = Set.univ := by
  exact LooplessMultigraph.exists_isSpanningTree_isMatching
    fragileDecompositionTheorem G Set.univ hconn
      (fun x => by rw [← G.degree_eq]; exact hdeg x)
      ((G.isFragileOn_univ_iff).2 hfrag)

/-- **The 2-Decomposition Conjecture** holds. -/
theorem twoDecompositionConjecture : TwoDecompositionConjecture.{u, v} :=
  twoDecompositionConjecture_of_fragileDecomposition fragileDecompositionTheorem

/-- **The 3-Decomposition Conjecture** holds (Theorem 1.2 of the paper). -/
theorem threeDecompositionConjecture : ThreeDecompositionConjecture.{u, v} :=
  threeDecompositionConjecture_of_fragileDecomposition fragileDecompositionTheorem

end ThreeDecomposition
