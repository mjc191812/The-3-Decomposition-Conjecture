import ThreeDecomposition.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Matching
import ThreeDecomposition.MatchingComplement.Counting

/-!
# Residual components and the component identity (Lemma 3.1)

This module wraps Mathlib's connected components for a matching complement `H - M`, defines the
component-local terminal count `t(L)` and exposure count `z(L)`, and proves Lemma 3.1 of the
paper (`component_identity`): `z(L) - t(L) = 2ρ(L) - 2`.

## Connected-component wrappers
-/

namespace ThreeDecomposition

open SimpleGraph

universe u

variable {V : Type u}

/- `SimpleGraph.degree` is defined through a `neighborFinset`, so its
   elaborated term carries the chosen `Fintype` instance as a parameter.
   The finset itself is extensionally determined by adjacency; this helper
   lets later component sums move between such instances without introducing
   a spurious type mismatch. -/
lemma degree_independent_fintype
    (H : SimpleGraph V) (v : V)
    (f₁ f₂ : Fintype (H.neighborSet v)) :
    @SimpleGraph.degree V H v f₁ = @SimpleGraph.degree V H v f₂ := by
  have hfin : @SimpleGraph.neighborFinset V H v f₁ =
      @SimpleGraph.neighborFinset V H v f₂ := by
    ext w
    simp only [SimpleGraph.mem_neighborFinset]
  unfold SimpleGraph.degree
  rw [hfin]

/-- The graph carried by a connected component, using Mathlib's induced graph. -/
abbrev componentGraph (H : SimpleGraph V) (c : H.ConnectedComponent) : SimpleGraph c :=
  c.toSimpleGraph

lemma componentGraph_connected (H : SimpleGraph V) (c : H.ConnectedComponent) :
    (componentGraph H c).Connected := by
  exact c.connected_toSimpleGraph

lemma componentGraph_tree_of_acyclic (H : SimpleGraph V) (c : H.ConnectedComponent)
    (hacyc : H.IsAcyclic) :
    (componentGraph H c).IsTree := by
  exact hacyc.isTree_connectedComponent c

lemma componentGraph_cycles_spanningCoe (H : SimpleGraph V) (c : H.ConnectedComponent)
    (hcycles : H.IsCycles) :
    (componentGraph H c).spanningCoe.IsCycles := by
  exact hcycles.toSimpleGraph c

lemma isCycles_of_degree_eq_two (H : SimpleGraph V)
    [∀ v, Fintype (H.neighborSet v)]
    (hdeg : ∀ v : V, H.degree v = 2) :
    H.IsCycles := by
  intro v hv
  rw [← Set.fintypeCard_eq_ncard, H.card_neighborSet_eq_degree]
  exact hdeg v

lemma component_spanningCoe_degree_eq (H : SimpleGraph V)
    (c : H.ConnectedComponent)
    [∀ v, Fintype ((componentGraph H c).spanningCoe.neighborSet v)]
    [∀ v, Fintype (H.neighborSet v)]
    {v : V} (hv : v ∈ c.supp) :
    (componentGraph H c).spanningCoe.degree v = H.degree v := by
  classical
  have hneighbor :
      (componentGraph H c).spanningCoe.neighborFinset v = H.neighborFinset v := by
    ext w
    simp only [SimpleGraph.mem_neighborFinset,
      ConnectedComponent.adj_spanningCoe_toSimpleGraph]
    constructor
    · intro h
      exact h.2
    · intro h
      exact ⟨hv, h⟩
  rw [← (componentGraph H c).spanningCoe.card_neighborFinset_eq_degree,
    ← H.card_neighborFinset_eq_degree, hneighbor]

lemma component_spanningCoe_isCycles_of_degree_eq_two
    (H : SimpleGraph V)
    (c : H.ConnectedComponent)
    [∀ v, Fintype (H.neighborSet v)]
    (hdeg : ∀ v : V, H.degree v = 2) :
    (componentGraph H c).spanningCoe.IsCycles := by
  intro v hv
  obtain ⟨w, hw⟩ := hv
  have hw' : (componentGraph H c).spanningCoe.Adj v w := by
    rw [SimpleGraph.mem_neighborSet] at hw
    exact hw
  have hv' : v ∈ c.supp := by
    rw [ConnectedComponent.adj_spanningCoe_toSimpleGraph] at hw'
    exact hw'.1
  have hneighbor :
      (componentGraph H c).spanningCoe.neighborSet v = H.neighborSet v := by
    ext u
    simp only [SimpleGraph.mem_neighborSet,
      ConnectedComponent.adj_spanningCoe_toSimpleGraph]
    exact and_iff_right hv'
  rw [hneighbor, ← Set.fintypeCard_eq_ncard, H.card_neighborSet_eq_degree, hdeg v]

end ThreeDecomposition

/-!
## Component-local counts `t(L)` and `z(L)`
-/

namespace ThreeDecomposition

open SimpleGraph

universe u

variable {V : Type u}

section Counts

variable [Fintype V]

/-! ## Local degree classification -/

lemma residual_degree_eq_one_iff_terminal_covered
    (G : SimpleGraph V) [DecidableRel G.Adj] (M : G.Subgraph)
    [∀ v, Fintype ((deletedMatching G M).neighborSet v)]
    (hM : M.IsMatching) (h23 : Is23Graph G) {v : V} :
    (deletedMatching G M).degree v = 1 ↔
      v ∈ terminals G ∧ v ∈ M.verts := by
  constructor
  · intro hdeg
    rcases h23 v with hterm | hcubic
    · have hcov : v ∈ M.verts := by
        by_contra hnot
        have hsame := deletedMatching_degree_eq_of_not_mem G M hnot
        rw [hsame, hterm] at hdeg
        omega
      exact ⟨hterm, hcov⟩
    · have hcov : v ∈ M.verts := by
        by_contra hnot
        have hsame := deletedMatching_degree_eq_of_not_mem G M hnot
        rw [hsame, hcubic] at hdeg
        omega
      have htwo := deletedMatching_degree_eq_two_of_cubic_mem G M hM hcubic hcov
      omega
  · rintro ⟨hterm, hcov⟩
    exact deletedMatching_degree_eq_one_of_terminal_mem G M hM hterm hcov

lemma residual_degree_eq_three_iff_cubic_uncovered
    (G : SimpleGraph V) [DecidableRel G.Adj] (M : G.Subgraph)
    [∀ v, Fintype ((deletedMatching G M).neighborSet v)]
    (hM : M.IsMatching) (h23 : Is23Graph G) {v : V} :
    (deletedMatching G M).degree v = 3 ↔
      v ∈ cubicVertices G ∧ v ∉ M.verts := by
  constructor
  · intro hdeg
    rcases h23 v with hterm | hcubic
    · have hcov : v ∈ M.verts := by
        by_contra hnot
        have hsame := deletedMatching_degree_eq_of_not_mem G M hnot
        rw [hsame, hterm] at hdeg
        omega
      have hone := deletedMatching_degree_eq_one_of_terminal_mem G M hM hterm hcov
      omega
    · have huncovered : v ∉ M.verts := by
        intro hcov
        have htwo := deletedMatching_degree_eq_two_of_cubic_mem G M hM hcubic hcov
        omega
      exact ⟨hcubic, huncovered⟩
  · rintro ⟨hcubic, huncovered⟩
    exact deletedMatching_degree_eq_three_of_cubic_not_mem G M hcubic huncovered

lemma residual_degree_eq_two_iff_terminal_uncovered_or_cubic_covered
    (G : SimpleGraph V) [DecidableRel G.Adj] (M : G.Subgraph)
    [∀ v, Fintype ((deletedMatching G M).neighborSet v)]
    (hM : M.IsMatching) (h23 : Is23Graph G) {v : V} :
    (deletedMatching G M).degree v = 2 ↔
      (v ∈ terminals G ∧ v ∉ M.verts) ∨
      (v ∈ cubicVertices G ∧ v ∈ M.verts) := by
  constructor
  · intro hdeg
    rcases h23 v with hterm | hcubic
    · by_cases hcov : v ∈ M.verts
      · have hone := deletedMatching_degree_eq_one_of_terminal_mem G M hM hterm hcov
        omega
      · exact Or.inl ⟨hterm, hcov⟩
    · by_cases hcov : v ∈ M.verts
      · exact Or.inr ⟨hcubic, hcov⟩
      · have hthree := deletedMatching_degree_eq_three_of_cubic_not_mem G M hcubic hcov
        omega
  · rintro (⟨hterm, huncovered⟩ | ⟨hcubic, hcov⟩)
    · exact deletedMatching_degree_eq_two_of_terminal_not_mem G M hterm huncovered
    · exact deletedMatching_degree_eq_two_of_cubic_mem G M hM hcubic hcov

/-! ## Component-local forms of the classification -/

lemma component_residual_degree_eq_one_iff_terminal_covered
    (G : SimpleGraph V) [DecidableRel G.Adj] (M : G.Subgraph)
    (c : (deletedMatching G M).ConnectedComponent)
    [∀ v, Fintype ((componentGraph (deletedMatching G M) c).spanningCoe.neighborSet v)]
    (hM : M.IsMatching) (h23 : Is23Graph G) {v : V}
    (hv : v ∈ c.supp) :
    (componentGraph (deletedMatching G M) c).spanningCoe.degree v = 1 ↔
      v ∈ terminals G ∧ v ∈ M.verts := by
  classical
  rw [component_spanningCoe_degree_eq (deletedMatching G M) c hv]
  exact residual_degree_eq_one_iff_terminal_covered G M hM h23

lemma component_residual_degree_eq_two_iff_terminal_uncovered_or_cubic_covered
    (G : SimpleGraph V) [DecidableRel G.Adj] (M : G.Subgraph)
    (c : (deletedMatching G M).ConnectedComponent)
    [∀ v, Fintype ((componentGraph (deletedMatching G M) c).spanningCoe.neighborSet v)]
    (hM : M.IsMatching) (h23 : Is23Graph G) {v : V}
    (hv : v ∈ c.supp) :
    (componentGraph (deletedMatching G M) c).spanningCoe.degree v = 2 ↔
      (v ∈ terminals G ∧ v ∉ M.verts) ∨
      (v ∈ cubicVertices G ∧ v ∈ M.verts) := by
  classical
  rw [component_spanningCoe_degree_eq (deletedMatching G M) c hv]
  exact residual_degree_eq_two_iff_terminal_uncovered_or_cubic_covered G M hM h23

lemma component_residual_degree_eq_three_iff_cubic_uncovered
    (G : SimpleGraph V) [DecidableRel G.Adj] (M : G.Subgraph)
    (c : (deletedMatching G M).ConnectedComponent)
    [∀ v, Fintype ((componentGraph (deletedMatching G M) c).spanningCoe.neighborSet v)]
    (hM : M.IsMatching) (h23 : Is23Graph G) {v : V}
    (hv : v ∈ c.supp) :
    (componentGraph (deletedMatching G M) c).spanningCoe.degree v = 3 ↔
      v ∈ cubicVertices G ∧ v ∉ M.verts := by
  classical
  rw [component_spanningCoe_degree_eq (deletedMatching G M) c hv]
  exact residual_degree_eq_three_iff_cubic_uncovered G M hM h23

lemma component_degree_sub_two_eq_terminal_exposure
    (G : SimpleGraph V) [DecidableRel G.Adj] (M : G.Subgraph)
    (c : (deletedMatching G M).ConnectedComponent)
    [∀ v, Fintype ((componentGraph (deletedMatching G M) c).spanningCoe.neighborSet v)]
    [DecidablePred (fun v : V => v ∈ M.verts)]
    (hM : M.IsMatching) (h23 : Is23Graph G) {v : V}
    (hv : v ∈ c.supp) :
    ((componentGraph (deletedMatching G M) c).spanningCoe.degree v : ℤ) - 2 =
      (if v ∈ terminals G then (-1 : ℤ) else 0) +
        (if v ∉ M.verts then (1 : ℤ) else 0) := by
  classical
  rw [component_spanningCoe_degree_eq (deletedMatching G M) c hv]
  exact deletedMatching_degree_sub_two_eq_terminal_exposure G M hM h23

/-! ## Component-local defect counting -/

/-- Number of terminals represented in a residual component. -/
def componentTerminalCount
    (G : SimpleGraph V) [DecidableRel G.Adj] (M : G.Subgraph)
    (c : (deletedMatching G M).ConnectedComponent) [Fintype c] : ℤ :=
  ∑ v : c, if (v : V) ∈ terminals G then (1 : ℤ) else 0

/-- Number of exposed (matching-uncovered) vertices represented in a residual
component. -/
def componentExposureCount
    (G : SimpleGraph V) [DecidableRel G.Adj] (M : G.Subgraph)
    (c : (deletedMatching G M).ConnectedComponent) [Fintype c]
    [DecidablePred (fun v : V => v ∈ M.verts)] : ℤ :=
  ∑ v : c, if (v : V) ∉ M.verts then (1 : ℤ) else 0

omit [Fintype V] in
lemma componentGraph_degree_eq_ambient_degree
    (H : SimpleGraph V)
    (c : H.ConnectedComponent) {v : V} (hv : v ∈ c.supp)
    [Fintype ((componentGraph H c).neighborSet ⟨v, hv⟩)]
    [Fintype (H.neighborSet v)] :
    (componentGraph H c).degree ⟨v, hv⟩ = H.degree v := by
  let e : ((componentGraph H c).neighborSet ⟨v, hv⟩) ≃ H.neighborSet v :=
    { toFun := fun w =>
        ⟨(w : V), by
          exact (ConnectedComponent.toSimpleGraph_adj c hv w.1.property).mp w.2⟩
      invFun := fun w =>
        ⟨⟨(w : V), c.mem_supp_of_adj_mem_supp hv w.2⟩, by
          exact (ConnectedComponent.toSimpleGraph_adj c hv _).mpr w.2⟩
      left_inv := by intro w; rfl
      right_inv := by intro w; rfl }
  rw [← (componentGraph H c).card_neighborSet_eq_degree,
    ← H.card_neighborSet_eq_degree]
  exact Fintype.card_congr e

lemma component_defect_sum_eq_exposure_sub_terminal_of_degree_bridge
    (G : SimpleGraph V) [DecidableRel G.Adj] (M : G.Subgraph)
    (c : (deletedMatching G M).ConnectedComponent)
    [Fintype c]
    [∀ v, Fintype ((componentGraph (deletedMatching G M) c).neighborSet v)]
    [∀ v, Fintype ((componentGraph (deletedMatching G M) c).spanningCoe.neighborSet v)]
    [DecidablePred (fun v : V => v ∈ M.verts)]
    (hM : M.IsMatching) (h23 : Is23Graph G)
    (hbridge : ∀ v : c,
      (componentGraph (deletedMatching G M) c).degree v =
        (componentGraph (deletedMatching G M) c).spanningCoe.degree (v : V)) :
    (∑ v : c, (((componentGraph (deletedMatching G M) c).degree v : ℤ) - 2)) =
      componentExposureCount G M c - componentTerminalCount G M c := by
  classical
  unfold componentExposureCount componentTerminalCount
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro v hv
  have hlocal := component_degree_sub_two_eq_terminal_exposure G M c hM h23 v.property
  rw [hbridge v]
  by_cases ht : (v : V) ∈ terminals G <;>
    by_cases hm : (v : V) ∈ M.verts <;>
      simp [ht, hm] at hlocal ⊢ <;> omega

lemma component_exposure_sub_terminal_eq_cyclomatic_sub_two_of_component_identity
    (G : SimpleGraph V) [DecidableRel G.Adj] (M : G.Subgraph)
    (c : (deletedMatching G M).ConnectedComponent)
    [Fintype c]
    [∀ v, Fintype ((componentGraph (deletedMatching G M) c).neighborSet v)]
    [∀ v, Fintype ((componentGraph (deletedMatching G M) c).spanningCoe.neighborSet v)]
    [DecidableRel (componentGraph (deletedMatching G M) c).Adj]
    [DecidablePred (fun v : V => v ∈ M.verts)]
    (hM : M.IsMatching) (h23 : Is23Graph G)
    (hbridge : ∀ v : c,
      (componentGraph (deletedMatching G M) c).degree v =
        (componentGraph (deletedMatching G M) c).spanningCoe.degree (v : V))
    (hidentity :
      (∑ v : c, (((componentGraph (deletedMatching G M) c).degree v : ℤ) - 2)) =
        2 * cyclomaticNumber (componentGraph (deletedMatching G M) c) - 2) :
    componentExposureCount G M c - componentTerminalCount G M c =
      2 * cyclomaticNumber (componentGraph (deletedMatching G M) c) - 2 := by
  classical
  rw [← component_defect_sum_eq_exposure_sub_terminal_of_degree_bridge
    G M c hM h23 hbridge]
  exact hidentity

end Counts

/-! ## Explicit tree/cycle component data -/

/-- A residual component is the tree part of a terminal decomposition. -/
def IsResidualTreeComponent (H : SimpleGraph V)
    (c : H.ConnectedComponent) : Prop :=
  (componentGraph H c).IsTree

/-- A residual component is a genuine cycle component.  The nonempty-neighbor
condition rules out the isolated-vertex case allowed by `IsCycles`. -/
def IsResidualCycleComponent (H : SimpleGraph V)
    (c : H.ConnectedComponent) : Prop :=
  (componentGraph H c).IsCycles ∧
    ∀ v : c, ((componentGraph H c).neighborSet v).Nonempty

/-- Component form of “one terminal tree and terminal-free cycles”.  This is
an intermediate criterion: the existence of the matching is supplied later. -/
def IsResidualTerminalTreeCycles (H : SimpleGraph V) (S : Set V) : Prop :=
  ∃ c₀ : H.ConnectedComponent,
    S ⊆ c₀.supp ∧
      IsResidualTreeComponent H c₀ ∧
      ∀ c : H.ConnectedComponent, c ≠ c₀ →
        IsResidualCycleComponent H c ∧ Disjoint S c.supp

lemma IsResidualTreeComponent.isAcyclic
    (H : SimpleGraph V) (c : H.ConnectedComponent)
    (h : IsResidualTreeComponent H c) :
    (componentGraph H c).IsAcyclic := by
  exact SimpleGraph.IsTree.isAcyclic h

lemma IsResidualTreeComponent.connected
    (H : SimpleGraph V) (c : H.ConnectedComponent)
    (h : IsResidualTreeComponent H c) :
    (componentGraph H c).Connected := by
  exact SimpleGraph.IsTree.connected h

lemma IsResidualCycleComponent.isCycles
    (H : SimpleGraph V) (c : H.ConnectedComponent)
    (h : IsResidualCycleComponent H c) :
    (componentGraph H c).IsCycles := by
  exact h.1

lemma IsResidualCycleComponent.neighborSet_nonempty
    (H : SimpleGraph V) (c : H.ConnectedComponent)
    (h : IsResidualCycleComponent H c) (v : c) :
    ((componentGraph H c).neighborSet v).Nonempty := by
  exact h.2 v

lemma IsResidualCycleComponent.neighborSet_ncard_eq_two
    (H : SimpleGraph V) (c : H.ConnectedComponent)
    (h : IsResidualCycleComponent H c) (v : c) :
    ((componentGraph H c).neighborSet v).ncard = 2 := by
  exact h.1 (h.2 v)

lemma IsResidualTerminalTreeCycles.terminals_in_tree
    (H : SimpleGraph V) (S : Set V)
    (h : IsResidualTerminalTreeCycles H S) :
    ∃ c₀ : H.ConnectedComponent,
      S ⊆ c₀.supp ∧ IsResidualTreeComponent H c₀ := by
  rcases h with ⟨c₀, hS, htree, _⟩
  exact ⟨c₀, hS, htree⟩

lemma IsResidualTerminalTreeCycles.other_components_are_cycles
    (H : SimpleGraph V) (S : Set V)
    (h : IsResidualTerminalTreeCycles H S) :
    ∃ c₀ : H.ConnectedComponent,
      S ⊆ c₀.supp ∧ IsResidualTreeComponent H c₀ ∧
        ∀ c : H.ConnectedComponent, c ≠ c₀ →
          IsResidualCycleComponent H c ∧ Disjoint S c.supp := by
  exact h

end ThreeDecomposition

/-!
## Component identity (Lemma 3.1)

For every component `L` of `H - M`, `z(L) - t(L) = 2 ρ(L) - 2`.
-/

namespace ThreeDecomposition

open SimpleGraph

universe u

variable {V : Type u}

lemma component_identity [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (M : G.Subgraph)
    (c : (deletedMatching G M).ConnectedComponent)
    [Fintype c]
    [DecidableRel (componentGraph (deletedMatching G M) c).Adj]
    [DecidablePred (fun v : V => v ∈ M.verts)]
    (hM : M.IsMatching) (h23 : Is23Graph G) :
    componentExposureCount G M c - componentTerminalCount G M c =
      2 * cyclomaticNumber (componentGraph (deletedMatching G M) c) - 2 := by
  classical
  have hbridge : ∀ v : c,
      (componentGraph (deletedMatching G M) c).degree v =
        (componentGraph (deletedMatching G M) c).spanningCoe.degree (v : V) := by
    intro v
    calc
      (componentGraph (deletedMatching G M) c).degree v =
          (deletedMatching G M).degree (v : V) :=
        componentGraph_degree_eq_ambient_degree (deletedMatching G M) c v.property
      _ = (componentGraph (deletedMatching G M) c).spanningCoe.degree (v : V) := by
        symm
        exact component_spanningCoe_degree_eq (deletedMatching G M) c v.property
  have hsum := component_defect_sum_eq_exposure_sub_terminal_of_degree_bridge
    G M c hM h23 hbridge
  have hgeneric := degree_defect_eq_cyclomatic_sub_two
    (componentGraph (deletedMatching G M) c)
  exact hsum.symm.trans hgeneric

lemma connected_isTree_of_cyclomatic_zero [Fintype V]
    (K : SimpleGraph V) [DecidableRel K.Adj]
    (hconn : K.Connected) (hcycl : cyclomaticNumber K = 0) :
    K.IsTree := by
  apply (SimpleGraph.isTree_iff_connected_and_card).2
  refine ⟨hconn, ?_⟩
  have hcard : K.edgeFinset.card + 1 = Fintype.card V := by
    unfold cyclomaticNumber at hcycl
    omega
  rw [Nat.card_eq_fintype_card (α := K.edgeSet), ← K.edgeFinset_card,
    Nat.card_eq_fintype_card (α := V)]
  exact hcard

lemma component_isResidualTree_of_cyclomatic_zero
    (H : SimpleGraph V)
    (c : H.ConnectedComponent)
    [Fintype c]
    [DecidableRel (componentGraph H c).Adj]
    (hcycl : cyclomaticNumber (componentGraph H c) = 0) :
    IsResidualTreeComponent H c := by
  exact connected_isTree_of_cyclomatic_zero (componentGraph H c)
    (componentGraph_connected H c) hcycl

lemma component_isResidualCycle_of_degree_two
    (H : SimpleGraph V)
    (c : H.ConnectedComponent)
    [Fintype c]
    [DecidableRel (componentGraph H c).Adj]
    (hdeg : ∀ v : c, (componentGraph H c).degree v = 2) :
    IsResidualCycleComponent H c := by
  classical
  refine ⟨isCycles_of_degree_eq_two (componentGraph H c) hdeg, ?_⟩
  intro v
  have hcard : ((componentGraph H c).neighborSet v).ncard = 2 := by
    rw [← Set.fintypeCard_eq_ncard, (componentGraph H c).card_neighborSet_eq_degree]
    exact hdeg v
  exact Set.nonempty_of_ncard_ne_zero (by omega)

end ThreeDecomposition
