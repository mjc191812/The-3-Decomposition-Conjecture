import ThreeDecomposition.Basic.Definitions
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import ThreeDecomposition.Basic.Lemmas

/-!
# Degree and exposure counting in matching complements

This module establishes the residual-degree formulas at covered and exposed vertices, the
global degree-defect identity `∑ (d(v) - 2) = 2ρ - 2`, and equation (3.1) of the paper
(`n - 2q = k - 2` exposed vertices for a matching of size `q = ρ(G)`).

## Local residual degrees
-/

namespace ThreeDecomposition

open SimpleGraph

variable {V : Type*} [Fintype V]

lemma neighborFinset_deletedMatching_eq_erase [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (M : G.Subgraph)
    [∀ v, Fintype ((deletedMatching G M).neighborSet v)]
    (hM : M.IsMatching) {v : V} (hv : v ∈ M.verts) :
    ∃ w : V, M.Adj v w ∧
      (deletedMatching G M).neighborFinset v = (G.neighborFinset v).erase w := by
  classical
  obtain ⟨w, hw, huniq⟩ := hM hv
  refine ⟨w, hw, ?_⟩
  ext u
  rw [SimpleGraph.mem_neighborFinset]
  change (G.deleteEdges M.edgeSet).Adj v u ↔
    u ∈ (G.neighborFinset v).erase w
  rw [Finset.mem_erase]
  rw [SimpleGraph.mem_neighborFinset]
  rw [SimpleGraph.deleteEdges_adj]
  constructor
  · rintro ⟨hGu, hnot⟩
    refine ⟨?_, hGu⟩
    intro huw
    apply hnot
    exact SimpleGraph.Subgraph.mem_edgeSet.mpr (by simpa [huw] using hw)
  · rintro ⟨huw, hGu⟩
    refine ⟨hGu, ?_⟩
    intro hMvu
    have hMu : M.Adj v u := SimpleGraph.Subgraph.mem_edgeSet.mp hMvu
    exact huw (huniq u hMu)

lemma deletedMatching_degree_eq_sub_one_of_mem
    (G : SimpleGraph V) [DecidableRel G.Adj] (M : G.Subgraph)
    [∀ v, Fintype ((deletedMatching G M).neighborSet v)]
    (hM : M.IsMatching) {v : V} (hv : v ∈ M.verts) :
    (deletedMatching G M).degree v = G.degree v - 1 := by
  classical
  obtain ⟨w, hw, hEq⟩ := neighborFinset_deletedMatching_eq_erase G M hM hv
  rw [← SimpleGraph.card_neighborFinset_eq_degree,
    ← SimpleGraph.card_neighborFinset_eq_degree G v, hEq,
    Finset.card_erase_of_mem]
  simpa using hw.adj_sub

lemma deletedMatching_degree_eq_of_not_mem
    (G : SimpleGraph V) [DecidableRel G.Adj] (M : G.Subgraph)
    [∀ v, Fintype ((deletedMatching G M).neighborSet v)]
    {v : V} (hv : v ∉ M.verts) :
    (deletedMatching G M).degree v = G.degree v := by
  have hno : ∀ u : V, ¬ M.Adj v u := by
    intro u huv
    exact hv (M.edge_vert huv)
  have hEq : (deletedMatching G M).neighborFinset v = G.neighborFinset v := by
    ext u
    rw [SimpleGraph.mem_neighborFinset]
    change (G.deleteEdges M.edgeSet).Adj v u ↔ u ∈ G.neighborFinset v
    rw [SimpleGraph.mem_neighborFinset, SimpleGraph.deleteEdges_adj]
    constructor
    · exact fun h => h.1
    · intro hGu
      refine ⟨hGu, ?_⟩
      intro hMvu
      exact hno u (SimpleGraph.Subgraph.mem_edgeSet.mp hMvu)
  rw [← SimpleGraph.card_neighborFinset_eq_degree,
    ← SimpleGraph.card_neighborFinset_eq_degree G v, hEq]

lemma deletedMatching_degree_eq_one_of_terminal_mem
    (G : SimpleGraph V) [DecidableRel G.Adj] (M : G.Subgraph)
    [∀ v, Fintype ((deletedMatching G M).neighborSet v)]
    (hM : M.IsMatching) {v : V}
    (hv : v ∈ terminals G) (hvM : v ∈ M.verts) :
    (deletedMatching G M).degree v = 1 := by
  have hdeg : G.degree v = 2 := hv
  rw [deletedMatching_degree_eq_sub_one_of_mem G M hM hvM, hdeg]

lemma deletedMatching_degree_eq_two_of_cubic_mem
    (G : SimpleGraph V) [DecidableRel G.Adj] (M : G.Subgraph)
    [∀ v, Fintype ((deletedMatching G M).neighborSet v)]
    (hM : M.IsMatching) {v : V}
    (hv : v ∈ cubicVertices G) (hvM : v ∈ M.verts) :
    (deletedMatching G M).degree v = 2 := by
  have hdeg : G.degree v = 3 := hv
  rw [deletedMatching_degree_eq_sub_one_of_mem G M hM hvM, hdeg]

lemma deletedMatching_degree_eq_two_of_terminal_not_mem
    (G : SimpleGraph V) [DecidableRel G.Adj] (M : G.Subgraph)
    [∀ v, Fintype ((deletedMatching G M).neighborSet v)]
    {v : V} (hv : v ∈ terminals G) (hvM : v ∉ M.verts) :
    (deletedMatching G M).degree v = 2 := by
  have hdeg : G.degree v = 2 := hv
  rw [deletedMatching_degree_eq_of_not_mem G M hvM, hdeg]

lemma deletedMatching_degree_eq_three_of_cubic_not_mem
    (G : SimpleGraph V) [DecidableRel G.Adj] (M : G.Subgraph)
    [∀ v, Fintype ((deletedMatching G M).neighborSet v)]
    {v : V} (hv : v ∈ cubicVertices G) (hvM : v ∉ M.verts) :
    (deletedMatching G M).degree v = 3 := by
  have hdeg : G.degree v = 3 := hv
  rw [deletedMatching_degree_eq_of_not_mem G M hvM, hdeg]

/- The four local cases in the component-identity proof can be compressed into
one integer-valued defect formula.  The first indicator records a terminal,
and the second records an exposed vertex (a vertex outside the matching
support). -/
lemma deletedMatching_degree_sub_two_eq_terminal_exposure
    (G : SimpleGraph V) [DecidableRel G.Adj] (M : G.Subgraph)
    [∀ v, Fintype ((deletedMatching G M).neighborSet v)]
    [DecidablePred (fun v : V => v ∈ M.verts)]
    (hM : M.IsMatching) (h23 : Is23Graph G) {v : V} :
    ((deletedMatching G M).degree v : ℤ) - 2 =
      (if v ∈ terminals G then (-1 : ℤ) else 0) +
        (if v ∉ M.verts then (1 : ℤ) else 0) := by
  classical
  by_cases hvT : v ∈ terminals G
  · by_cases hvM : v ∈ M.verts
    · have hdeg := deletedMatching_degree_eq_one_of_terminal_mem G M hM hvT hvM
      simp [hvT, hvM, hdeg]
    · have hdeg := deletedMatching_degree_eq_two_of_terminal_not_mem G M hvT hvM
      simp [hvT, hvM, hdeg]
  · have hv3 : v ∈ cubicVertices G := by
      have hcases := h23 v
      rcases hcases with h2 | h3
      · exact False.elim (hvT h2)
      · exact h3
    by_cases hvM : v ∈ M.verts
    · have hdeg := deletedMatching_degree_eq_two_of_cubic_mem G M hM hv3 hvM
      simp [hvT, hvM, hdeg]
    · have hdeg := deletedMatching_degree_eq_three_of_cubic_not_mem G M hv3 hvM
      simp [hvT, hvM, hdeg]


end ThreeDecomposition

/-!
## Degree-defect sum
-/

namespace ThreeDecomposition

open SimpleGraph

universe u

variable {V : Type u} [Fintype V]

/--
The degree defect (the sum of `2 - degree`) is twice the Euler defect
`|V| - |E|`.  This is a direct integer-valued reformulation of Mathlib's
`SimpleGraph.sum_degrees_eq_twice_card_edges`; no second proof of the
handshaking lemma is introduced here.
-/
lemma degree_defect_sum (H : SimpleGraph V) [DecidableRel H.Adj] :
    (∑ v : V, ((2 : ℤ) - (H.degree v : ℤ))) =
      2 * (Fintype.card V : ℤ) - 2 * (H.edgeFinset.card : ℤ) := by
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← Nat.cast_sum]
  rw [H.sum_degrees_eq_twice_card_edges]
  norm_num
  ring

lemma degree_defect_eq_cyclomatic_sub_two (H : SimpleGraph V) [DecidableRel H.Adj] :
    (∑ v : V, ((H.degree v : ℤ) - 2)) =
      2 * cyclomaticNumber H - 2 := by
  have hcast : (∑ v : V, (H.degree v : ℤ)) =
      2 * (H.edgeFinset.card : ℤ) := by
    rw [← Nat.cast_sum, H.sum_degrees_eq_twice_card_edges]
    norm_num
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [hcast]
  unfold cyclomaticNumber
  ring

lemma component_identity_terminal_consequence
    {k z rho : ℤ}
    (hz : z ≤ k - 2) (hrho : 0 ≤ rho)
    (hident : z - k = 2 * rho - 2) :
    z = k - 2 ∧ rho = 0 := by
  omega

lemma component_identity_terminal_free_consequence
    {z rho : ℤ} (hz : z = 0)
    (hident : z = 2 * rho - 2) :
    rho = 1 := by
  omega

end ThreeDecomposition

/-!
## Cardinality of a matching and its exposed vertices (equation (3.1))

A matching covers twice as many vertices as it has edges (`ncard_verts_eq_two_mul_ncard_edgeSet`).
For a matching of size `cyclomaticNumber G` in a `{2,3}`-graph, this gives equation (3.1) of the
paper: `k - 2` vertices are exposed (`ncard_compl_verts_eq_ncard_terminals_sub_two`).
-/

namespace ThreeDecomposition

open SimpleGraph

section Generic

variable {V : Type*} {G : SimpleGraph V} {M : G.Subgraph}

/-- A matching on a finite vertex type covers exactly twice as many vertices as it has
edges. -/
theorem ncard_verts_eq_two_mul_ncard_edgeSet [Finite V] (hM : M.IsMatching) :
    M.verts.ncard = 2 * M.edgeSet.ncard := by
  classical
  have := Fintype.ofFinite V
  have hedge : M.edgeSet.ncard = M.coe.edgeFinset.card := by
    rw [← M.image_coe_edgeSet_coe,
      Set.ncard_image_of_injective _ (Sym2.map.injective Subtype.val_injective),
      ← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset]
  rw [hedge, ← M.coe.sum_degrees_eq_twice_card_edges]
  calc M.verts.ncard = ∑ _v : M.verts, 1 := by
        simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one]
        exact Set.ncard_eq_toFinset_card' _ |>.trans (Set.toFinset_card _)
    _ = _ := Finset.sum_congr rfl fun v _ => by
        rw [Subgraph.coe_degree]
        convert ((Subgraph.isMatching_iff_forall_degree.mp hM) v v.2).symm

/-- Exposed vertices and covered vertices of a matching partition the vertex type. -/
theorem ncard_compl_verts_add_two_mul_ncard_edgeSet [Finite V] (hM : M.IsMatching) :
    M.vertsᶜ.ncard + 2 * M.edgeSet.ncard = Nat.card V := by
  rw [← ncard_verts_eq_two_mul_ncard_edgeSet hM, add_comm, Set.ncard_add_ncard_compl]

/-- A perfect matching on a finite vertex type has exactly half as many edges as there are
vertices. -/
theorem two_mul_ncard_edgeSet_of_isPerfectMatching [Finite V] (hM : M.IsPerfectMatching) :
    2 * M.edgeSet.ncard = Nat.card V := by
  rw [← ncard_verts_eq_two_mul_ncard_edgeSet hM.1, hM.2.verts_eq_univ, Set.ncard_univ]

end Generic

variable {V : Type*} [Fintype V]

/-- Equation (3.1): a matching of the target size in a `{2,3}`-graph with `k` terminals
exposes exactly `k - 2` vertices. -/
theorem ncard_compl_verts_eq_ncard_terminals_sub_two (G : SimpleGraph V) [DecidableRel G.Adj]
    (h23 : Is23Graph G) {M : G.Subgraph} (hM : M.IsMatching)
    (hsize : (M.edgeSet.ncard : ℤ) = cyclomaticNumber G) :
    (M.vertsᶜ.ncard : ℤ) = (terminals G).ncard - 2 := by
  classical
  have hcount := ncard_compl_verts_add_two_mul_ncard_edgeSet hM
  have htarget := twice_targetMatchingSize G h23
  rw [Nat.card_eq_fintype_card] at hcount
  rw [Set.ncard_eq_toFinset_card' (terminals G), terminals_eq_terminalFinset]
  unfold targetMatchingSize at htarget
  omega

/-- A perfect matching of a `{2,3}`-graph with exactly two terminals has the target size. -/
theorem ncard_edgeSet_eq_cyclomaticNumber_of_isPerfectMatching (G : SimpleGraph V)
    [DecidableRel G.Adj] (h23 : Is23Graph G) (hk : (terminals G).ncard = 2) {M : G.Subgraph}
    (hM : M.IsPerfectMatching) :
    (M.edgeSet.ncard : ℤ) = cyclomaticNumber G := by
  classical
  have hcount := two_mul_ncard_edgeSet_of_isPerfectMatching hM
  have htarget := twice_targetMatchingSize G h23
  rw [Nat.card_eq_fintype_card] at hcount
  rw [Set.ncard_eq_toFinset_card', terminals_eq_terminalFinset] at hk
  unfold targetMatchingSize at htarget
  omega

end ThreeDecomposition
