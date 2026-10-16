import ThreeDecomposition.MatchingComplement.Components
import ThreeDecomposition.MatchingComplement.Counting

/-!
# The terminal criterion (Lemma 3.2)

This module proves Lemma 3.2 of the paper (`terminalSelectionStatement_iff_exists_component`),
its reachability form (`terminalSelectionStatement_of_reachable`), and its two parity
consequences (`terminalSelectionStatement_of_isPerfectMatching` for `k = 2` and
`terminalSelectionStatement_of_all_but_one_terminal` for the inductive step `k ≥ 3`).

## Assembly of the residual component decomposition
-/

namespace ThreeDecomposition

open SimpleGraph

universe u

variable {V : Type u} [Fintype V]

lemma terminal_statement_of_component_decomposition
    (G : SimpleGraph V) [DecidableRel G.Adj] (M : G.Subgraph)
    (S : Set V)
    (hM : M.IsMatching)
    (c₀ : (deletedMatching G M).ConnectedComponent)
    (hS : S ⊆ c₀.supp)
    (hTree : IsResidualTreeComponent (deletedMatching G M) c₀)
    (hCycles : ∀ c : (deletedMatching G M).ConnectedComponent, c ≠ c₀ →
      IsResidualCycleComponent (deletedMatching G M) c)
    (hsize : (M.edgeSet.ncard : ℤ) = cyclomaticNumber G) :
    TerminalSelectionStatement G S := by
  classical
  let H : SimpleGraph V := deletedMatching G M
  have houtside : ∀ v : V, v ∉ c₀.supp → H.degree v = 2 := by
    intro v hvout
    let c : H.ConnectedComponent := H.connectedComponentMk v
    have hvmem : v ∈ c.supp := by
      simp [c]
    have hcne : c ≠ c₀ := by
      intro heq
      apply hvout
      apply (c₀.mem_supp_iff v).2
      simpa [c] using heq
    have hcyc : IsResidualCycleComponent H c := by
      exact hCycles c hcne
    have hvne : ((componentGraph H c).neighborSet ⟨v, hvmem⟩).Nonempty :=
      hcyc.neighborSet_nonempty H c ⟨v, hvmem⟩
    have hcard : ((componentGraph H c).neighborSet ⟨v, hvmem⟩).ncard = 2 :=
      hcyc.isCycles H c hvne
    have hcard' : Fintype.card ((componentGraph H c).neighborSet ⟨v, hvmem⟩) = 2 := by
      exact (Set.fintypeCard_eq_ncard _).trans hcard
    have hdegc : (componentGraph H c).degree ⟨v, hvmem⟩ = 2 := by
      calc
        (componentGraph H c).degree ⟨v, hvmem⟩ =
            Fintype.card ((componentGraph H c).neighborSet ⟨v, hvmem⟩) :=
          ((componentGraph H c).card_neighborSet_eq_degree ⟨v, hvmem⟩).symm
        _ = 2 := hcard'
    calc
      H.degree v = (componentGraph H c).degree ⟨v, hvmem⟩ := by
        symm
        exact componentGraph_degree_eq_ambient_degree H c hvmem
      _ = 2 := hdegc
  refine ⟨M, hM, hsize, ?_⟩
  refine ⟨hM, c₀.supp, componentGraph H c₀, ?_, hS, ?_⟩
  · change (componentGraph H c₀).IsTree
    exact hTree
  · refine ⟨?_, ?_, ?_⟩
    · intro u v huv
      exact (ConnectedComponent.adj_spanningCoe_toSimpleGraph c₀).mp huv |>.2
    · intro v
      cases v with
      | mk val hval =>
        exact (componentGraph_degree_eq_ambient_degree H c₀ hval).symm
    · intro v hv
      exact houtside v hv

end ThreeDecomposition

/-!
## Count-zero criteria for residual components
-/

namespace ThreeDecomposition

open SimpleGraph

universe u

variable {V : Type u}

lemma componentExposureCount_eq_zero_iff
    (G : SimpleGraph V) [DecidableRel G.Adj] (M : G.Subgraph)
    (c : (deletedMatching G M).ConnectedComponent)
    [Fintype c] [DecidablePred (fun v : V => v ∈ M.verts)] :
    componentExposureCount G M c = 0 ↔
      ∀ v : c, (v : V) ∈ M.verts := by
  classical
  constructor
  · intro h v
    by_contra hv
    have hnon : ∀ w : c, w ∈ Finset.univ →
        0 ≤ (if (w : V) ∉ M.verts then (1 : ℤ) else 0) := by
      intro w _
      split <;> norm_num
    have hle := Finset.single_le_sum hnon (Finset.mem_univ v)
    have hle' : (if (v : V) ∉ M.verts then (1 : ℤ) else 0) ≤
        componentExposureCount G M c := by
      simpa [componentExposureCount] using hle
    rw [h] at hle'
    simp [hv] at hle'
  · intro hall
    unfold componentExposureCount
    apply (Finset.sum_eq_zero_iff_of_nonneg (s := Finset.univ) ?_).2
    · intro v hv
      by_cases hnot : (v : V) ∉ M.verts
      · exact (hnot (hall v)).elim
      · simp [hnot]
    · intro v hv
      have hnot : ¬((v : V) ∉ M.verts) := fun h => h (hall v)
      simp [hnot]

variable [Fintype V]

lemma componentTerminalCount_eq_zero_iff
    (G : SimpleGraph V) [DecidableRel G.Adj] (M : G.Subgraph)
    (c : (deletedMatching G M).ConnectedComponent)
    [Fintype c] :
    componentTerminalCount G M c = 0 ↔
      ∀ v : c, (v : V) ∉ terminals G := by
  classical
  constructor
  · intro h v
    by_contra hv
    have hnon : ∀ w : c, w ∈ Finset.univ →
        0 ≤ (if (w : V) ∈ terminals G then (1 : ℤ) else 0) := by
      intro w _
      split <;> norm_num
    have hle := Finset.single_le_sum hnon (Finset.mem_univ v)
    have hle' : (if (v : V) ∈ terminals G then (1 : ℤ) else 0) ≤
        componentTerminalCount G M c := by
      simpa [componentTerminalCount] using hle
    rw [h] at hle'
    simp [hv] at hle'
  · intro hall
    unfold componentTerminalCount
    apply (Finset.sum_eq_zero_iff_of_nonneg (s := Finset.univ) ?_).2
    · intro v hv
      by_cases hterm : (v : V) ∈ terminals G
      · exact ((hall v) hterm).elim
      · simp [hterm]
    · intro v hv
      have hterm : ¬((v : V) ∈ terminals G) := hall v
      simp [hterm]

lemma component_degree_eq_two_of_no_exposure_no_terminal
    (G : SimpleGraph V) [DecidableRel G.Adj] (M : G.Subgraph)
    (c : (deletedMatching G M).ConnectedComponent)
    [Fintype c]
    [∀ v, Fintype ((componentGraph (deletedMatching G M) c).neighborSet v)]
    [DecidablePred (fun v : V => v ∈ M.verts)]
    (hM : M.IsMatching) (h23 : Is23Graph G)
    (hexp : componentExposureCount G M c = 0)
    (hterm : componentTerminalCount G M c = 0) :
    ∀ v : c, (componentGraph (deletedMatching G M) c).degree v = 2 := by
  classical
  have hcovered : ∀ v : c, (v : V) ∈ M.verts :=
    (componentExposureCount_eq_zero_iff G M c).mp hexp
  have hnoterm : ∀ v : c, (v : V) ∉ terminals G :=
    (componentTerminalCount_eq_zero_iff G M c).mp hterm
  intro v
  have hdef := component_degree_sub_two_eq_terminal_exposure
    G M c hM h23 v.property
  have hsp := component_spanningCoe_degree_eq
    (deletedMatching G M) c v.property
  rw [hsp] at hdef
  have hamb : (deletedMatching G M).degree (v : V) = 2 := by
    simp [hcovered v, hnoterm v] at hdef
    omega
  calc
    (componentGraph (deletedMatching G M) c).degree v =
        (deletedMatching G M).degree (v : V) := by
      exact componentGraph_degree_eq_ambient_degree
        (deletedMatching G M) c v.property
    _ = 2 := hamb

lemma component_isResidualCycle_of_no_exposure_no_terminal
    (G : SimpleGraph V) [DecidableRel G.Adj] (M : G.Subgraph)
    (c : (deletedMatching G M).ConnectedComponent)
    [Fintype c]
    [DecidablePred (fun v : V => v ∈ M.verts)]
    (hM : M.IsMatching) (h23 : Is23Graph G)
    (hexp : componentExposureCount G M c = 0)
    (hterm : componentTerminalCount G M c = 0) :
    IsResidualCycleComponent (deletedMatching G M) c := by
  classical
  apply component_isResidualCycle_of_degree_two
  exact component_degree_eq_two_of_no_exposure_no_terminal
    G M c hM h23 hexp hterm

lemma terminal_statement_of_counted_components
    (G : SimpleGraph V) [DecidableRel G.Adj] (M : G.Subgraph)
    (S : Set V)
    (c₀ : (deletedMatching G M).ConnectedComponent)
    [Fintype c₀]
    [DecidablePred (fun v : V => v ∈ M.verts)]
    (hM : M.IsMatching) (h23 : Is23Graph G)
    (hS : S ⊆ c₀.supp)
    (hmain : componentExposureCount G M c₀ - componentTerminalCount G M c₀ = -2)
    (hother : ∀ (c : (deletedMatching G M).ConnectedComponent), c ≠ c₀ →
      ∀ [Fintype c],
        componentExposureCount G M c = 0 ∧ componentTerminalCount G M c = 0)
    (hsize : (M.edgeSet.ncard : ℤ) = cyclomaticNumber G) :
    TerminalSelectionStatement G S := by
  classical
  have hidentity := component_identity G M c₀ hM h23
  have hcycl : cyclomaticNumber (componentGraph (deletedMatching G M) c₀) = 0 := by
    omega
  have htree : IsResidualTreeComponent (deletedMatching G M) c₀ :=
    component_isResidualTree_of_cyclomatic_zero
      (deletedMatching G M) c₀ hcycl
  have hcycles : ∀ c : (deletedMatching G M).ConnectedComponent, c ≠ c₀ →
      IsResidualCycleComponent (deletedMatching G M) c := by
    intro c hc
    let : Fintype c := Fintype.ofFinite c
    exact component_isResidualCycle_of_no_exposure_no_terminal
      G M c hM h23 (hother c hc).1 (hother c hc).2
  exact terminal_statement_of_component_decomposition
    G M S hM c₀ hS htree hcycles hsize

end ThreeDecomposition

/-!
## Equivalence and parity consequences (Lemma 3.2)

Let `M` be a matching of size `cyclomaticNumber G` in a `{2,3}`-graph `G`.  If one component of
`G - M` contains every terminal, then that component is a tree containing every exposed vertex
and all other components are terminal-free cycles (`terminal_criterion`).  Conversely, a
terminal tree-and-cycles decomposition determines its tree as a connected component of
`G - M` containing every exposed vertex
(`exists_residual_tree_component_of_isTerminalTreeCycles_terminals`).
-/

namespace ThreeDecomposition

open SimpleGraph

universe u

section Generic

variable {V : Type u}

/-- A connected finite graph has nonnegative cyclomatic number. -/
theorem cyclomaticNumber_nonneg_of_connected {W : Type*} [Fintype W] (K : SimpleGraph W)
    [DecidableRel K.Adj] (hK : K.Connected) : 0 ≤ cyclomaticNumber K := by
  have h := hK.card_vert_le_card_edgeSet_add_one
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, ← edgeFinset_card] at h
  unfold cyclomaticNumber
  omega

lemma sum_ite_eq_ncard_supp_inter {H : SimpleGraph V} (c : H.ConnectedComponent) [Fintype c]
    (p : V → Prop) [DecidablePred p] :
    (∑ v : c, if p v then (1 : ℤ) else 0) = ((c.supp ∩ {v | p v}).ncard : ℤ) := by
  classical
  rw [Finset.sum_boole, ← Fintype.card_subtype, ← Nat.card_eq_fintype_card,
    ← Nat.card_coe_set_eq]
  exact_mod_cast Nat.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter (· ∈ c) p)

lemma isResidualTreeComponent_of_induce_eq {H : SimpleGraph V} {c : H.ConnectedComponent}
    {U : Set V} {T : SimpleGraph U} (hT : T.IsTree) (hind : H.induce U = T)
    (hU : U = c.supp) : IsResidualTreeComponent H c := by
  subst hU hind
  exact hT

lemma isResidualCycleComponent_of_ncard_neighborSet_eq_two [Finite V]
    (H : SimpleGraph V) (c : H.ConnectedComponent)
    (h : ∀ v ∈ c.supp, (H.neighborSet v).ncard = 2) :
    IsResidualCycleComponent H c := by
  classical
  have := Fintype.ofFinite V
  apply component_isResidualCycle_of_degree_two
  rintro ⟨v, hv⟩
  rw [componentGraph_degree_eq_ambient_degree H c hv, ← ncard_neighborSet]
  exact h v hv

/-- A tree `T` on a vertex set `U` that lies inside `H` and realizes the full `H`-degree of
each of its vertices is a connected component of `H`. -/
theorem exists_connectedComponent_of_isTree [Finite V] {H : SimpleGraph V} {U : Set V}
    {T : SimpleGraph U} (hT : T.IsTree) (hle : T.spanningCoe ≤ H)
    (hdeg : ∀ v : U, (H.neighborSet v).ncard = (T.neighborSet v).ncard) :
    ∃ c : H.ConnectedComponent, c.supp = U ∧ IsResidualTreeComponent H c := by
  have hnbr : ∀ v : U, T.spanningCoe.neighborSet v = H.neighborSet v := by
    intro v
    have hsub : T.spanningCoe.neighborSet v ⊆ H.neighborSet v := fun w hw => hle hw
    have hcard : (T.spanningCoe.neighborSet v).ncard = (T.neighborSet v).ncard := by
      rw [show (v : V) = Function.Embedding.subtype _ v from rfl, neighborSet_map,
        Set.ncard_image_of_injective _ (Function.Embedding.subtype _).injective]
    exact Set.eq_of_subset_of_ncard_le hsub (by rw [hdeg v, hcard])
  have hadj : ∀ (v : U) (w : V), H.Adj v w ↔ T.spanningCoe.Adj v w := fun v w => by
    rw [← mem_neighborSet, ← mem_neighborSet, hnbr]
  have hclosed : ∀ v w : V, v ∈ U → H.Adj v w → w ∈ U := by
    intro v w hv hvw
    obtain ⟨a, b, -, -, rfl⟩ := (map_adj _ _ _ _).mp ((hadj ⟨v, hv⟩ w).mp hvw)
    exact b.2
  have hind : H.induce U = T := by
    calc H.induce U = T.spanningCoe.induce U := by
          ext x y
          exact hadj x y
      _ = T := induce_spanningCoe
  obtain ⟨u₀⟩ := hT.connected.nonempty
  have hU : U = (H.connectedComponentMk (u₀ : V)).supp := by
    ext v
    constructor
    · intro hv
      have hr : T.Reachable u₀ ⟨v, hv⟩ := hT.connected.preconnected _ _
      exact (ConnectedComponent.sound
        ((hr.map (Embedding.spanningCoe T).toHom).mono hle)).symm
    · intro hv
      have hr : H.Reachable u₀ v := ConnectedComponent.exact hv.symm
      clear hv
      rw [reachable_iff_reflTransGen] at hr
      induction hr with
      | refl => exact u₀.2
      | tail _ hbc ih => exact hclosed _ _ ih hbc
  exact ⟨_, hU.symm, isResidualTreeComponent_of_induce_eq hT hind hU⟩

end Generic

variable {V : Type u} [Fintype V]

/-! ## Component counts as cardinalities -/

lemma componentTerminalCount_eq_ncard (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : G.Subgraph) (c : (deletedMatching G M).ConnectedComponent) [Fintype c] :
    componentTerminalCount G M c = ((c.supp ∩ terminals G).ncard : ℤ) :=
  sum_ite_eq_ncard_supp_inter c (· ∈ terminals G)

omit [Fintype V] in
lemma componentExposureCount_eq_ncard (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : G.Subgraph) (c : (deletedMatching G M).ConnectedComponent) [Fintype c]
    [DecidablePred (· ∈ M.verts)] :
    componentExposureCount G M c = ((c.supp ∩ M.vertsᶜ).ncard : ℤ) :=
  sum_ite_eq_ncard_supp_inter c (· ∉ M.verts)

/-- Lemma 3.1 in cardinality form: every residual component `c` has a nonnegative integer `ρ`
(its cyclomatic number) with `z(c) - t(c) = 2ρ - 2`, and `c` is a tree when `ρ = 0`. -/
theorem exists_component_identity (G : SimpleGraph V) [DecidableRel G.Adj] (h23 : Is23Graph G)
    {M : G.Subgraph} (hM : M.IsMatching) (c : (deletedMatching G M).ConnectedComponent) :
    ∃ ρ : ℤ, 0 ≤ ρ ∧
      ((c.supp ∩ M.vertsᶜ).ncard : ℤ) - (c.supp ∩ terminals G).ncard = 2 * ρ - 2 ∧
      (ρ = 0 → IsResidualTreeComponent (deletedMatching G M) c) := by
  classical
  refine ⟨cyclomaticNumber (componentGraph (deletedMatching G M) c),
    cyclomaticNumber_nonneg_of_connected _ (componentGraph_connected _ c), ?_,
    component_isResidualTree_of_cyclomatic_zero _ c⟩
  rw [← componentExposureCount_eq_ncard, ← componentTerminalCount_eq_ncard]
  exact component_identity G M c hM h23

/-- `t(c) ≤ z(c) + 2` for every residual component. -/
theorem ncard_supp_inter_terminals_le (G : SimpleGraph V) [DecidableRel G.Adj]
    (h23 : Is23Graph G) {M : G.Subgraph} (hM : M.IsMatching)
    (c : (deletedMatching G M).ConnectedComponent) :
    (c.supp ∩ terminals G).ncard ≤ (c.supp ∩ M.vertsᶜ).ncard + 2 := by
  obtain ⟨ρ, hρ, hid, -⟩ := exists_component_identity G h23 hM c
  omega

/-- `z(c) + t(c)` is even for every residual component. -/
theorem even_ncard_supp_inter_add (G : SimpleGraph V) [DecidableRel G.Adj]
    (h23 : Is23Graph G) {M : G.Subgraph} (hM : M.IsMatching)
    (c : (deletedMatching G M).ConnectedComponent) :
    Even ((c.supp ∩ M.vertsᶜ).ncard + (c.supp ∩ terminals G).ncard) := by
  obtain ⟨ρ, -, hid, -⟩ := exists_component_identity G h23 hM c
  rw [← Int.even_coe_nat]
  exact ⟨ρ - 1 + (c.supp ∩ terminals G).ncard, by push_cast; omega⟩

/-- A residual component with `t(c) = z(c) + 2` is a tree. -/
theorem isResidualTreeComponent_of_ncard_eq (G : SimpleGraph V) [DecidableRel G.Adj]
    (h23 : Is23Graph G) {M : G.Subgraph} (hM : M.IsMatching)
    (c : (deletedMatching G M).ConnectedComponent)
    (h : (c.supp ∩ terminals G).ncard = (c.supp ∩ M.vertsᶜ).ncard + 2) :
    IsResidualTreeComponent (deletedMatching G M) c := by
  obtain ⟨ρ, -, hid, htree⟩ := exists_component_identity G h23 hM c
  exact htree (by omega)

/-- A residual component without exposed vertices and without terminals is a cycle. -/
theorem isResidualCycleComponent_of_subset_verts (G : SimpleGraph V) [DecidableRel G.Adj]
    (h23 : Is23Graph G) {M : G.Subgraph} (hM : M.IsMatching)
    (c : (deletedMatching G M).ConnectedComponent) (hcov : c.supp ⊆ M.verts)
    (hterm : Disjoint c.supp (terminals G)) :
    IsResidualCycleComponent (deletedMatching G M) c := by
  classical
  apply component_isResidualCycle_of_no_exposure_no_terminal G M c hM h23
  · rw [componentExposureCount_eq_ncard, ← Set.sdiff_eq, Set.sdiff_eq_empty.mpr hcov,
      Set.ncard_empty, Nat.cast_zero]
  · rw [componentTerminalCount_eq_ncard, Set.disjoint_iff_inter_eq_empty.mp hterm,
      Set.ncard_empty, Nat.cast_zero]

/-! ## Lemma 3.2 -/

/-- Lemma 3.2, (i) ⇒ (ii) with the “moreover” clause, componentwise: if a matching of target
size leaves all terminals in one residual component `c₀`, then `c₀` is a tree containing every
exposed vertex and every other residual component is a terminal-free cycle. -/
theorem terminal_criterion_components (G : SimpleGraph V) [DecidableRel G.Adj]
    (h23 : Is23Graph G) {M : G.Subgraph} (hM : M.IsMatching)
    (hsize : (M.edgeSet.ncard : ℤ) = cyclomaticNumber G)
    (c₀ : (deletedMatching G M).ConnectedComponent) (hS : terminals G ⊆ c₀.supp) :
    (∀ v, v ∉ M.verts → v ∈ c₀.supp) ∧
      IsResidualTreeComponent (deletedMatching G M) c₀ ∧
      ∀ c, c ≠ c₀ →
        IsResidualCycleComponent (deletedMatching G M) c ∧ Disjoint (terminals G) c.supp := by
  have hexp := ncard_compl_verts_eq_ncard_terminals_sub_two G h23 hM hsize
  have ht : c₀.supp ∩ terminals G = terminals G := Set.inter_eq_right.mpr hS
  have hz : (c₀.supp ∩ M.vertsᶜ).ncard ≤ M.vertsᶜ.ncard :=
    Set.ncard_le_ncard Set.inter_subset_right
  have hle := ncard_supp_inter_terminals_le G h23 hM c₀
  rw [ht] at hle
  have hzeq : c₀.supp ∩ M.vertsᶜ = M.vertsᶜ :=
    Set.eq_of_subset_of_ncard_le Set.inter_subset_right (by omega)
  have hcov : M.vertsᶜ ⊆ c₀.supp := Set.inter_eq_right.mp hzeq
  refine ⟨fun v hv => hcov hv,
    isResidualTreeComponent_of_ncard_eq G h23 hM c₀ (by rw [ht, hzeq]; omega), fun c hc => ?_⟩
  have hdisj : Disjoint c.supp c₀.supp := Set.disjoint_left.mpr fun v hv hv₀ =>
    hc (ConnectedComponent.eq_of_common_vertex hv hv₀)
  refine ⟨isResidualCycleComponent_of_subset_verts G h23 hM c ?_ (hdisj.mono_right hS),
    (hdisj.mono_right hS).symm⟩
  intro v hv
  by_contra hvM
  exact Set.disjoint_left.mp hdisj hv (hcov hvM)

/-- Lemma 3.2, (i) ⇒ (ii): a matching of target size whose residual graph has one component
`c₀` containing all terminals solves the terminal selection problem, and `c₀` contains every
exposed vertex. -/
theorem terminal_criterion (G : SimpleGraph V) [DecidableRel G.Adj]
    (h23 : Is23Graph G) {M : G.Subgraph} (hM : M.IsMatching)
    (hsize : (M.edgeSet.ncard : ℤ) = cyclomaticNumber G)
    (c₀ : (deletedMatching G M).ConnectedComponent) (hS : terminals G ⊆ c₀.supp) :
    TerminalSelectionStatement G (terminals G) ∧ ∀ v, v ∉ M.verts → v ∈ c₀.supp := by
  classical
  obtain ⟨hexp, htree, hcyc⟩ := terminal_criterion_components G h23 hM hsize c₀ hS
  exact ⟨terminal_statement_of_component_decomposition G M _ hM c₀ hS htree
    (fun c hc => (hcyc c hc).1) hsize, hexp⟩

/-! ## Extracting the tree component -/

/-- The tree of a terminal tree-and-cycles decomposition is a connected component of the
residual graph; every residual vertex outside it has degree two, and every other residual
component is a cycle. -/
theorem exists_residual_tree_component_of_isTerminalTreeCycles (G : SimpleGraph V)
    [DecidableRel G.Adj] {S : Set V} {M : G.Subgraph} (h : IsTerminalTreeCycles G S M) :
    ∃ c₀ : (deletedMatching G M).ConnectedComponent, S ⊆ c₀.supp ∧
      (∀ v, v ∉ c₀.supp → ((deletedMatching G M).neighborSet v).ncard = 2) ∧
      IsResidualTreeComponent (deletedMatching G M) c₀ ∧
      ∀ c, c ≠ c₀ → IsResidualCycleComponent (deletedMatching G M) c := by
  classical
  obtain ⟨-, U, T, hT, hSU, hle, hdegU, hdegOut⟩ := h
  simp only [← ncard_neighborSet] at hdegU hdegOut
  obtain ⟨c₀, hc₀, htree⟩ := exists_connectedComponent_of_isTree hT hle hdegU
  subst hc₀
  exact ⟨c₀, hSU, hdegOut, htree, fun c hc =>
    isResidualCycleComponent_of_ncard_neighborSet_eq_two _ c fun v hv =>
      hdegOut v fun hv₀ => hc (ConnectedComponent.eq_of_common_vertex hv hv₀)⟩

theorem IsTerminalTreeCycles.isResidualTerminalTreeCycles {G : SimpleGraph V}
    [DecidableRel G.Adj] {S : Set V} {M : G.Subgraph} (h : IsTerminalTreeCycles G S M) :
    IsResidualTerminalTreeCycles (deletedMatching G M) S := by
  obtain ⟨c₀, hS, -, htree, hcyc⟩ := exists_residual_tree_component_of_isTerminalTreeCycles G h
  exact ⟨c₀, hS, htree, fun c hc => ⟨hcyc c hc, Set.disjoint_left.mpr fun v hv hvc =>
    hc (ConnectedComponent.eq_of_common_vertex hvc (hS hv))⟩⟩

/-- For the terminal set itself, the tree component also contains every exposed vertex:
outside the tree every residual degree is two, so an exposed vertex there would be a
terminal. -/
theorem exists_residual_tree_component_of_isTerminalTreeCycles_terminals (G : SimpleGraph V)
    [DecidableRel G.Adj] {M : G.Subgraph} (h : IsTerminalTreeCycles G (terminals G) M) :
    ∃ c₀ : (deletedMatching G M).ConnectedComponent, terminals G ⊆ c₀.supp ∧
      (∀ v, v ∉ M.verts → v ∈ c₀.supp) ∧
      IsResidualTreeComponent (deletedMatching G M) c₀ ∧
      ∀ c, c ≠ c₀ → IsResidualCycleComponent (deletedMatching G M) c := by
  classical
  obtain ⟨c₀, hS, hout, htree, hcyc⟩ := exists_residual_tree_component_of_isTerminalTreeCycles G h
  refine ⟨c₀, hS, fun v hv => ?_, htree, hcyc⟩
  by_contra hv₀
  have h2 := hout v hv₀
  rw [ncard_neighborSet, deletedMatching_degree_eq_of_not_mem G M hv] at h2
  exact hv₀ (hS h2)

/-- A solution of the terminal selection problem, presented through residual components. -/
theorem TerminalSelectionStatement.exists_residual_tree_component {G : SimpleGraph V}
    [DecidableRel G.Adj] (h : TerminalSelectionStatement G (terminals G)) :
    ∃ M : G.Subgraph, M.IsMatching ∧ (M.edgeSet.ncard : ℤ) = cyclomaticNumber G ∧
      ∃ c₀ : (deletedMatching G M).ConnectedComponent, terminals G ⊆ c₀.supp ∧
        (∀ v, v ∉ M.verts → v ∈ c₀.supp) ∧
        IsResidualTreeComponent (deletedMatching G M) c₀ ∧
        ∀ c, c ≠ c₀ → IsResidualCycleComponent (deletedMatching G M) c := by
  obtain ⟨M, hM, hsize, h⟩ := h
  exact ⟨M, hM, hsize, exists_residual_tree_component_of_isTerminalTreeCycles_terminals G h⟩

/-- Lemma 3.2 as an equivalence: the terminal selection problem is solved exactly when some
matching of target size leaves all terminals in one residual component. -/
theorem terminalSelectionStatement_iff_exists_component (G : SimpleGraph V) [DecidableRel G.Adj]
    (h23 : Is23Graph G) :
    TerminalSelectionStatement G (terminals G) ↔
      ∃ M : G.Subgraph, M.IsMatching ∧ (M.edgeSet.ncard : ℤ) = cyclomaticNumber G ∧
        ∃ c₀ : (deletedMatching G M).ConnectedComponent, terminals G ⊆ c₀.supp := by
  constructor
  · intro h
    obtain ⟨M, hM, hsize, c₀, hS, -⟩ := h.exists_residual_tree_component
    exact ⟨M, hM, hsize, c₀, hS⟩
  · rintro ⟨M, hM, hsize, c₀, hS⟩
    exact (terminal_criterion G h23 hM hsize c₀ hS).1

/-! ## Parity consequences -/

/-- The case `k = 2`: a perfect matching of a `{2,3}`-graph with two terminals solves the
terminal selection problem.  Here `z = 0` in every component, so the component of a terminal
has `t ≤ 2` and `t` even, hence contains both terminals. -/
theorem terminalSelectionStatement_of_isPerfectMatching (G : SimpleGraph V) [DecidableRel G.Adj]
    (h23 : Is23Graph G) (hk : (terminals G).ncard = 2) {M : G.Subgraph}
    (hM : M.IsPerfectMatching) :
    TerminalSelectionStatement G (terminals G) := by
  obtain ⟨s, t, -, hst⟩ := Set.ncard_eq_two.mp hk
  let c := (deletedMatching G M).connectedComponentMk s
  have hz : c.supp ∩ M.vertsᶜ = ∅ := by simp [hM.2.verts_eq_univ]
  have hle := ncard_supp_inter_terminals_le G h23 hM.1 c
  have hev := even_ncard_supp_inter_add G h23 hM.1 c
  rw [hz, Set.ncard_empty] at hle hev
  rw [zero_add, Nat.even_iff] at hev
  have hpos : 0 < (c.supp ∩ terminals G).ncard :=
    (Set.ncard_pos (Set.toFinite _)).mpr
      ⟨s, ConnectedComponent.connectedComponentMk_mem, by rw [hst]; simp⟩
  have heq : c.supp ∩ terminals G = terminals G :=
    Set.eq_of_subset_of_ncard_le Set.inter_subset_right (by omega)
  exact (terminal_criterion G h23 hM.1
    (ncard_edgeSet_eq_cyclomaticNumber_of_isPerfectMatching G h23 hk hM) c
    (Set.inter_eq_right.mp heq)).1

/-- The closing parity argument: under a matching of target size, a residual component that
contains every exposed vertex and every terminal other than `s` contains all terminals, since
`z(c) = k - 2`, `t(c) ∈ {k - 1, k}` and `z(c) + t(c)` is even. -/
theorem terminals_subset_of_all_but_one_terminal (G : SimpleGraph V) [DecidableRel G.Adj]
    (h23 : Is23Graph G) {M : G.Subgraph} (hM : M.IsMatching)
    (hsize : (M.edgeSet.ncard : ℤ) = cyclomaticNumber G)
    (c : (deletedMatching G M).ConnectedComponent) (s : V)
    (hexp : ∀ v, v ∉ M.verts → v ∈ c.supp)
    (hterm : ∀ v ∈ terminals G, v ≠ s → v ∈ c.supp) :
    terminals G ⊆ c.supp := by
  have hk := ncard_compl_verts_eq_ncard_terminals_sub_two G h23 hM hsize
  have hz : c.supp ∩ M.vertsᶜ = M.vertsᶜ := Set.inter_eq_right.mpr hexp
  have hev := even_ncard_supp_inter_add G h23 hM c
  rw [hz, Nat.even_iff] at hev
  have h1 : (terminals G \ {s}).ncard ≤ (c.supp ∩ terminals G).ncard :=
    Set.ncard_le_ncard fun v hv => ⟨hterm v hv.1 hv.2, hv.1⟩
  have h2 := Set.ncard_le_ncard_sdiff_add_ncard (terminals G) {s}
  rw [Set.ncard_singleton] at h2
  have heq : c.supp ∩ terminals G = terminals G :=
    Set.eq_of_subset_of_ncard_le Set.inter_subset_right (by omega)
  exact Set.inter_eq_right.mp heq

/-- The closing parity lemma of the induction: a residual component containing every exposed
vertex and every terminal except possibly `s` yields a solution. -/
theorem terminalSelectionStatement_of_all_but_one_terminal (G : SimpleGraph V)
    [DecidableRel G.Adj] (h23 : Is23Graph G) {M : G.Subgraph} (hM : M.IsMatching)
    (hsize : (M.edgeSet.ncard : ℤ) = cyclomaticNumber G)
    (c : (deletedMatching G M).ConnectedComponent) (s : V)
    (hexp : ∀ v, v ∉ M.verts → v ∈ c.supp)
    (hterm : ∀ v ∈ terminals G, v ≠ s → v ∈ c.supp) :
    TerminalSelectionStatement G (terminals G) :=
  (terminal_criterion G h23 hM hsize c
    (terminals_subset_of_all_but_one_terminal G h23 hM hsize c s hexp hterm)).1

end ThreeDecomposition

/-!
## Reachability form of Lemma 3.2

The lifting and restoration steps transport residual reachability rather than components, so
both directions of Lemma 3.2 are restated here with all terminals reachable from one vertex.
-/

namespace ThreeDecomposition

open SimpleGraph

lemma mem_supp_mk_iff_reachable {V : Type*} {H : SimpleGraph V} {q v : V} :
    v ∈ (H.connectedComponentMk q).supp ↔ H.Reachable q v :=
  (ConnectedComponent.mem_supp_iff _ _).trans (ConnectedComponent.eq.trans reachable_comm)

variable {V : Type*} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Lemma 3.2 in reachability form, extraction: a solution provides a matching of target size
whose residual graph connects every terminal to a given terminal `r`. -/
theorem TerminalSelectionStatement.exists_reachable
    (h : TerminalSelectionStatement G (terminals G)) {r : V} (hr : r ∈ terminals G) :
    ∃ M : G.Subgraph, M.IsMatching ∧ (M.edgeSet.ncard : ℤ) = cyclomaticNumber G ∧
      ∀ t ∈ terminals G, (deletedMatching G M).Reachable r t := by
  obtain ⟨M, hM, hsize, c₀, hS, -⟩ := h.exists_residual_tree_component
  exact ⟨M, hM, hsize, fun t ht ↦ ConnectedComponent.exact ((hS hr).trans (hS ht).symm)⟩

/-- Lemma 3.2 in reachability form, criterion: a matching of target size whose residual graph
connects every terminal to one vertex `r` solves the terminal selection problem. -/
theorem terminalSelectionStatement_of_reachable (h23 : Is23Graph G) {M : G.Subgraph}
    (hM : M.IsMatching) (hsize : (M.edgeSet.ncard : ℤ) = cyclomaticNumber G) (r : V)
    (hr : ∀ t ∈ terminals G, (deletedMatching G M).Reachable r t) :
    TerminalSelectionStatement G (terminals G) :=
  (terminal_criterion G h23 hM hsize ((deletedMatching G M).connectedComponentMk r)
    fun t ht ↦ mem_supp_mk_iff_reachable.2 (hr t ht)).1

end ThreeDecomposition
