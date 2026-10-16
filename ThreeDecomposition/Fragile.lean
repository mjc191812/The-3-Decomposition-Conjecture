import ThreeDecomposition.Basic.Fragile
import ThreeDecomposition.Interfaces
import ThreeDecomposition.Basic.Lemmas
import ThreeDecomposition.MatchingComplement.TerminalCriterion
import ThreeDecomposition.Statement
import ThreeDecomposition.MatchingComplement.Main

/-!
# Fragile subcubic simple graphs (Theorem 1.4)

This module proves Theorem 1.4 of the paper (`fragileDecompositionTheorem_of_protectedCycle`):
every finite connected simple fragile subcubic graph admits an edge partition into a spanning
tree and a matching.

* **Splitting along a bridge**: a bridge splits `G` into two smaller connected simple fragile
  subcubic graphs whose tree–matching decompositions combine
  (`BridgeSplit.hasTreeMatchingDecomposition`).
* **Bridgeless `{2,3}`-graphs**: Theorem 2.2 rules out `k ≤ 1` (`two_le_ncard_terminals`) and
  eliminates residual cycles in the matching complement provided by Theorem 1.3
  (`hasTreeMatchingDecomposition_of_terminalSelection`).
* **Strong induction on `|V(G)|`**: combines the tree case, the bridge split, and the bridgeless
  case (`hasTreeMatchingDecomposition_of_card`).

## Splitting a graph along a bridge
-/

namespace ThreeDecomposition

open SimpleGraph

variable {V : Type*}

/-- A graph `D` is connected if it contains connected graphs on two shores covering `V`
together with an edge between the shores. -/
theorem connected_of_shores {D : SimpleGraph V} {X Y : Set V} {x y : V}
    (hcover : ∀ v, v ∈ X ∨ v ∈ Y) (hx : x ∈ X) (hy : y ∈ Y)
    {KX : SimpleGraph X} {KY : SimpleGraph Y} (hKX : KX.Connected) (hKY : KY.Connected)
    (hXD : ∀ a b, KX.Adj a b → D.Adj a b) (hYD : ∀ a b, KY.Adj a b → D.Adj a b)
    (hxy : D.Adj x y) : D.Connected := by
  let fX : KX →g D := ⟨Subtype.val, fun h => hXD _ _ h⟩
  let fY : KY →g D := ⟨Subtype.val, fun h => hYD _ _ h⟩
  refine (connected_iff_exists_forall_reachable D).mpr ⟨x, fun v => ?_⟩
  rcases hcover v with hv | hv
  · exact (hKX.preconnected ⟨x, hx⟩ ⟨v, hv⟩).map fX
  · exact hxy.reachable.trans ((hKY.preconnected ⟨y, hy⟩ ⟨v, hv⟩).map fY)

/-- Both endpoints of an edge lifted from the subtype `↥s` lie in `s`. -/
theorem mem_of_mem_image_sym2Map_val {s : Set V} {S : Set (Sym2 s)} {e : Sym2 V}
    (he : e ∈ Sym2.map Subtype.val '' S) {w : V} (hw : w ∈ e) : w ∈ s := by
  obtain ⟨e, -, rfl⟩ := he
  obtain ⟨a, -, rfl⟩ := Sym2.mem_map.mp hw
  exact a.2

/-- Edges lifted from disjoint vertex sets are distinct. -/
theorem disjoint_image_sym2Map_val {s t : Set V} (hst : Disjoint s t) (S : Set (Sym2 s))
    (S' : Set (Sym2 t)) : Disjoint (Sym2.map Subtype.val '' S) (Sym2.map Subtype.val '' S') := by
  refine Set.disjoint_left.mpr fun e he he' => ?_
  induction e using Sym2.ind with
  | h a b =>
    exact Set.disjoint_left.mp hst (mem_of_mem_image_sym2Map_val he (Sym2.mem_mk_left a b))
      (mem_of_mem_image_sym2Map_val he' (Sym2.mem_mk_left a b))

/-- Degrees do not increase in an induced subgraph. -/
theorem degree_induce_le (G : SimpleGraph V) (s : Set V) (v : s) [Fintype (G.neighborSet v)]
    [Fintype ((G.induce s).neighborSet v)] : (G.induce s).degree v ≤ G.degree v := by
  rw [← ncard_neighborSet, ← ncard_neighborSet,
    ← Set.ncard_image_of_injective _ Subtype.val_injective]
  refine Set.ncard_le_ncard ?_ (Set.toFinite _)
  rintro _ ⟨w, hw, rfl⟩
  exact hw

/-- An induced subgraph of a subcubic graph is subcubic. -/
theorem IsSubcubic.induce [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]
    (hG : IsSubcubic G) (s : Set V) [Fintype s] [DecidableRel (G.induce s).Adj] :
    IsSubcubic (G.induce s) :=
  fun v => (degree_induce_le G s v).trans (hG v)

/-- After deleting an edge `s(x, y)` of a connected graph, every vertex is reachable from `x`
or from `y`. -/
theorem reachable_deleteEdges_or {G : SimpleGraph V} (hconn : G.Connected) (x y v : V) :
    (G.deleteEdges {s(x, y)}).Reachable x v ∨ (G.deleteEdges {s(x, y)}).Reachable y v := by
  have hr := hconn.preconnected x v
  rw [reachable_iff_reflTransGen] at hr
  induction hr with
  | refl => exact Or.inl Reachable.rfl
  | @tail b c _ hbc ih =>
    by_cases he : s(b, c) = s(x, y)
    · rcases Sym2.eq_iff.mp he with ⟨-, rfl⟩ | ⟨-, rfl⟩
      · exact Or.inr Reachable.rfl
      · exact Or.inl Reachable.rfl
    · have hadj : (G.deleteEdges {s(x, y)}).Adj b c := by
        rw [deleteEdges_adj, Set.mem_singleton_iff]
        exact ⟨hbc, he⟩
      exact ih.imp (fun h => h.trans hadj.reachable) (fun h => h.trans hadj.reachable)

/-- `X` and `Y` partition the vertices of `G`, and `s(x, y)` is the only edge between them. -/
structure BridgeSplit (G : SimpleGraph V) (X Y : Set V) (x y : V) : Prop where
  /-- `Y` is the complement of `X`. -/
  mem_right_iff : ∀ v, v ∈ Y ↔ v ∉ X
  left_mem : x ∈ X
  right_mem : y ∈ Y
  adj : G.Adj x y
  /-- The bridge is the only edge from `X` to `Y`. -/
  eq_of_adj : ∀ ⦃u v⦄, G.Adj u v → u ∈ X → v ∈ Y → u = x ∧ v = y

/-- A bridge `s(x, y)` of a connected graph splits it into the components of `x` and `y` in
`G - s(x, y)`; both shores induce connected graphs. -/
theorem exists_bridgeSplit {G : SimpleGraph V} (hconn : G.Connected) {x y : V} (hadj : G.Adj x y)
    (hbr : G.IsBridge s(x, y)) :
    ∃ X Y : Set V, BridgeSplit G X Y x y ∧ (G.induce X).Connected ∧ (G.induce Y).Connected := by
  set G' := G.deleteEdges {s(x, y)} with hG'
  have hxy : ¬G'.Reachable x y := isBridge_iff.mp hbr
  have hmem : ∀ v w, v ∈ (G'.connectedComponentMk w).supp ↔ G'.Reachable v w := fun v w => by
    rw [ConnectedComponent.mem_supp_iff, ConnectedComponent.eq]
  have hconnC : ∀ c : G'.ConnectedComponent, (G.induce c.supp).Connected := by
    intro c
    have hc : (G'.induce c.supp).Connected := c.connected_toSimpleGraph
    exact hc.mono fun a b hab => (deleteEdges_le {s(x, y)} : G' ≤ G) hab
  refine ⟨(G'.connectedComponentMk x).supp, (G'.connectedComponentMk y).supp,
    ⟨fun v => ?_, ConnectedComponent.connectedComponentMk_mem,
      ConnectedComponent.connectedComponentMk_mem, hadj, fun u v huv hu hv => ?_⟩,
    hconnC _, hconnC _⟩
  · rw [hmem, hmem]
    refine ⟨fun hvy hvx => hxy (hvx.symm.trans hvy), fun hvx => ?_⟩
    rcases reachable_deleteEdges_or hconn x y v with h | h
    · exact absurd h.symm hvx
    · exact h.symm
  · rw [hmem] at hu hv
    by_cases he : s(u, v) = s(x, y)
    · rcases Sym2.eq_iff.mp he with h | ⟨rfl, rfl⟩
      · exact h
      · exact absurd hu.symm hxy
    · have hadj' : G'.Adj u v := by
        rw [hG', deleteEdges_adj, Set.mem_singleton_iff]
        exact ⟨huv, he⟩
      exact absurd (hu.symm.trans (hadj'.reachable.trans hv)) hxy

namespace BridgeSplit

variable {G : SimpleGraph V} {X Y : Set V} {x y : V}

/-- The roles of the two shores can be exchanged. -/
theorem symm (h : BridgeSplit G X Y x y) : BridgeSplit G Y X y x where
  mem_right_iff v := by rw [h.mem_right_iff, not_not]
  left_mem := h.right_mem
  right_mem := h.left_mem
  adj := h.adj.symm
  eq_of_adj _ _ huv hu hv := (h.eq_of_adj huv.symm hv hu).symm

theorem cover (h : BridgeSplit G X Y x y) (v : V) : v ∈ X ∨ v ∈ Y := by
  rw [h.mem_right_iff]
  exact em _

theorem notMem_left (h : BridgeSplit G X Y x y) {v : V} (hv : v ∈ Y) : v ∉ X :=
  (h.mem_right_iff v).mp hv

theorem disjoint (h : BridgeSplit G X Y x y) : Disjoint X Y :=
  Set.disjoint_left.mpr fun _ hvX hvY => h.notMem_left hvY hvX

/-- A shore of a fragile graph is fragile: if deleting the edges of a cycle of the shore `X`
left it connected, then together with the connected shore `Y` and the untouched bridge, `G`
would stay connected. -/
theorem isFragile_induce_left (h : BridgeSplit G X Y x y) (hfrag : IsFragile G)
    (hY : (G.induce Y).Connected) : IsFragile (G.induce X) := by
  intro u p hp hconn
  let f := Embedding.induce (G := G) X
  have hedge : ∀ a b : V, s(a, b) ∈ (p.map f.toHom).edges → a ∈ X := by
    intro a b he
    have hw := Walk.fst_mem_support_of_mem_edges _ he
    rw [Walk.support_map, List.mem_map] at hw
    obtain ⟨c, -, rfl⟩ := hw
    exact c.2
  refine hfrag _ (hp.map (f := f.toHom) f.injective)
    (connected_of_shores h.cover h.left_mem h.right_mem hconn hY ?_ ?_ ?_)
  · intro a b hab
    rw [deleteEdges_adj] at hab ⊢
    refine ⟨hab.1, fun hmem => hab.2 ?_⟩
    rw [Set.mem_ofPred_eq, Walk.edges_map] at hmem
    exact (List.mem_map_of_injective (Sym2.map.injective f.injective)).mp hmem
  · intro a b hab
    rw [deleteEdges_adj]
    exact ⟨hab, fun hmem => h.notMem_left a.2 (hedge a b hmem)⟩
  · rw [deleteEdges_adj]
    refine ⟨h.adj, fun hmem => h.notMem_left h.right_mem (hedge y x ?_)⟩
    rwa [Sym2.eq_swap]

/-- Tree–matching decompositions of the two shores combine, through the bridge, into a
tree–matching decomposition of `G`. -/
theorem hasTreeMatchingDecomposition [Finite V] (h : BridgeSplit G X Y x y)
    (hX : HasTreeMatchingDecomposition (G.induce X))
    (hY : HasTreeMatchingDecomposition (G.induce Y)) : HasTreeMatchingDecomposition G := by
  obtain ⟨TX, MX, hTXG, hTX, hMX, hdX, huX⟩ := hX
  obtain ⟨TY, MY, hTYG, hTY, hMY, hdY, huY⟩ := hY
  have hxy : x ≠ y := h.adj.ne
  set A := Sym2.map ((↑) : X → V) '' TX.edgeSet
  set B := Sym2.map ((↑) : Y → V) '' TY.edgeSet
  set C := Sym2.map ((↑) : X → V) '' MX.edgeSet
  set D := Sym2.map ((↑) : Y → V) '' MY.edgeSet
  let T : SimpleGraph V := TX.map (Function.Embedding.subtype (· ∈ X)) ⊔
    TY.map (Function.Embedding.subtype (· ∈ Y)) ⊔ edge x y
  let M : G.Subgraph := MX.map (Embedding.induce X).toHom ⊔ MY.map (Embedding.induce Y).toHom
  have hT : T.edgeSet = A ∪ B ∪ {s(x, y)} := by
    simp only [T, edgeSet_sup, edgeSet_map, edgeSet_edge_of_ne hxy]
    rfl
  have hM : M.edgeSet = C ∪ D := by
    simp only [M, Subgraph.edgeSet_sup, Subgraph.edgeSet_map]
    rfl
  have hTG : T ≤ G := by
    refine sup_le (sup_le ?_ ?_) ((edge_le_iff (G := G)).mpr (Or.inr h.adj))
    · intro u v huv
      obtain ⟨a, b, hab, rfl, rfl⟩ := (map_adj _ _ _ _).mp huv
      exact hTXG hab
    · intro u v huv
      obtain ⟨a, b, hab, rfl, rfl⟩ := (map_adj _ _ _ _).mp huv
      exact hTYG hab
  have hAB : Disjoint A B := disjoint_image_sym2Map_val h.disjoint _ _
  have hbX : ∀ {S : Set (Sym2 X)}, s(x, y) ∉ Sym2.map Subtype.val '' S := fun hb =>
    h.notMem_left h.right_mem (mem_of_mem_image_sym2Map_val hb (Sym2.mem_mk_right x y))
  have hbY : ∀ {S : Set (Sym2 Y)}, s(x, y) ∉ Sym2.map Subtype.val '' S := fun hb =>
    h.notMem_left (mem_of_mem_image_sym2Map_val hb (Sym2.mem_mk_left x y)) h.left_mem
  refine ⟨T, M, hTG, ?_, ?_, ?_, ?_⟩
  · rw [isTree_iff_connected_and_card]
    refine ⟨connected_of_shores h.cover h.left_mem h.right_mem hTX.connected hTY.connected
      (fun a b hab => Or.inl (Or.inl (map_adj_apply.mpr hab)))
      (fun a b hab => Or.inl (Or.inr (map_adj_apply.mpr hab)))
      (Or.inr ((edge_adj x y x y).mpr ⟨Or.inl ⟨rfl, rfl⟩, hxy⟩)), ?_⟩
    have hcardX := (isTree_iff_connected_and_card.mp hTX).2
    have hcardY := (isTree_iff_connected_and_card.mp hTY).2
    have hABb : Disjoint (A ∪ B) {s(x, y)} := by
      rw [Set.disjoint_singleton_right]
      rintro (hb | hb)
      · exact hbX hb
      · exact hbY hb
    have hAcard : A.ncard = TX.edgeSet.ncard :=
      Set.ncard_image_of_injective _ (Sym2.map.injective Subtype.val_injective)
    have hBcard : B.ncard = TY.edgeSet.ncard :=
      Set.ncard_image_of_injective _ (Sym2.map.injective Subtype.val_injective)
    have hV : Nat.card X + Nat.card Y = Nat.card V := by
      rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq, show Y = Xᶜ from Set.ext h.mem_right_iff,
        Set.ncard_add_ncard_compl]
    rw [Nat.card_coe_set_eq] at hcardX hcardY ⊢
    rw [hT, Set.ncard_union_eq hABb (Set.toFinite _) (Set.toFinite _),
      Set.ncard_union_eq hAB (Set.toFinite _) (Set.toFinite _), Set.ncard_singleton, hAcard,
      hBcard]
    omega
  · refine (hMX.map _ (Embedding.induce (G := G) X).injective).sup
      (hMY.map _ (Embedding.induce (G := G) Y).injective)
      (Set.disjoint_left.mpr fun v hv hv' => ?_)
    obtain ⟨a, -, rfl⟩ := Subgraph.support_subset_verts _ hv
    obtain ⟨b, -, hb⟩ := Subgraph.support_subset_verts _ hv'
    have hab : (b : V) = a := hb
    exact h.notMem_left (hab ▸ b.2) a.2
  · rw [hT, hM]
    refine Set.disjoint_left.mpr fun e heT heM => ?_
    rcases heT with (heA | heB) | rfl
    · rcases heM with heC | heD
      · obtain ⟨e₁, he₁, rfl⟩ := heA
        obtain ⟨e₂, he₂, heq⟩ := heC
        cases Sym2.map.injective Subtype.val_injective heq
        exact Set.disjoint_left.mp hdX he₁ he₂
      · exact Set.disjoint_left.mp (disjoint_image_sym2Map_val h.disjoint _ _) heA heD
    · rcases heM with heC | heD
      · exact Set.disjoint_left.mp (disjoint_image_sym2Map_val h.disjoint _ _) heC heB
      · obtain ⟨e₁, he₁, rfl⟩ := heB
        obtain ⟨e₂, he₂, heq⟩ := heD
        cases Sym2.map.injective Subtype.val_injective heq
        exact Set.disjoint_left.mp hdY he₁ he₂
    · rcases heM with heC | heD
      · exact hbX heC
      · exact hbY heD
  · refine Set.Subset.antisymm (Set.union_subset (edgeSet_mono hTG) M.edgeSet_subset) ?_
    rw [hT, hM]
    intro e he
    induction e using Sym2.ind with
    | h u v =>
      rw [mem_edgeSet] at he
      rcases h.cover u with hu | hu <;> rcases h.cover v with hv | hv
      · have hmem : s((⟨u, hu⟩ : X), ⟨v, hv⟩) ∈ TX.edgeSet ∪ MX.edgeSet := by
          rw [huX]
          exact he
        rcases hmem with hmem | hmem
        · exact Or.inl (Or.inl (Or.inl ⟨_, hmem, rfl⟩))
        · exact Or.inr (Or.inl ⟨_, hmem, rfl⟩)
      · obtain ⟨rfl, rfl⟩ := h.eq_of_adj he hu hv
        exact Or.inl (Or.inr rfl)
      · obtain ⟨rfl, rfl⟩ := h.eq_of_adj he.symm hv hu
        exact Or.inl (Or.inr Sym2.eq_swap)
      · have hmem : s((⟨u, hu⟩ : Y), ⟨v, hv⟩) ∈ TY.edgeSet ∪ MY.edgeSet := by
          rw [huY]
          exact he
        rcases hmem with hmem | hmem
        · exact Or.inl (Or.inl (Or.inr ⟨_, hmem, rfl⟩))
        · exact Or.inr (Or.inr ⟨_, hmem, rfl⟩)

end BridgeSplit

end ThreeDecomposition

/-!
## Bridgeless fragile `{2,3}`-graphs
-/

namespace ThreeDecomposition

open SimpleGraph

universe u

variable {V : Type u} [Fintype V]

/-- Theorem 2.2 rules out fragility: if `G` has a cycle edge-disjoint from a connected subgraph
`Q` and every vertex outside `Q` has degree at least three, then `G` is not fragile. -/
theorem not_isFragile_of_protectedCycle (hP : ProtectedCycleTheorem.{u}) {G : SimpleGraph V}
    [DecidableRel G.Adj] (hconn : G.Connected) (Q : G.Subgraph) (hQ : Q.Connected)
    (hcyc : ∃ (x : V) (p : G.Walk x x), p.IsCycle ∧ ∀ e ∈ p.edges, e ∉ Q.edgeSet)
    (hdeg : ∀ x, x ∉ Q.verts → 3 ≤ G.degree x) : ¬IsFragile G := by
  classical
  intro hfrag
  obtain ⟨x, p, hp, -, hc⟩ := hP V G Q hconn hQ hcyc hdeg
  exact hfrag p hp hc

/-- A connected bridgeless fragile `{2,3}`-graph has at least two terminals. -/
theorem two_le_ncard_terminals (hP : ProtectedCycleTheorem.{u}) {G : SimpleGraph V}
    [DecidableRel G.Adj] (hconn : G.Connected) (hbridge : IsBridgeless G) (h23 : Is23Graph G)
    (hfrag : IsFragile G) : 2 ≤ (terminals G).ncard := by
  classical
  by_contra hk
  push Not at hk
  obtain ⟨v, hv⟩ : ∃ v : V, ∀ w ∈ terminals G, w = v := by
    rcases (terminals G).eq_empty_or_nonempty with h | ⟨s, hs⟩
    · obtain ⟨v⟩ := hconn.nonempty
      exact ⟨v, fun w hw => by simp [h] at hw⟩
    · exact ⟨s, fun w hw => (Set.ncard_le_one (Set.toFinite _)).mp (by omega) w hw s hs⟩
  obtain ⟨w, hvw⟩ : ∃ w, G.Adj v w := by
    rw [← degree_pos_iff_exists_adj]
    rcases h23 v with h | h <;> omega
  obtain ⟨x, p, hp, -⟩ := hbridge.exists_cycle_mem (e := s(v, w)) hvw
  refine not_isFragile_of_protectedCycle hP hconn (G.singletonSubgraph v)
    Subgraph.singletonSubgraph_connected ⟨x, p, hp, fun e _ he => ?_⟩ (fun z hz => ?_) hfrag
  · induction e using Sym2.ind with
    | h a b => simp at he
  · rw [singletonSubgraph_verts, Set.mem_singleton_iff] at hz
    rcases h23 z with h | h
    · exact absurd (hv z h) hz
    · omega

/-- Theorem 1.4 for a connected bridgeless fragile `{2,3}`-graph, given the conclusion of
Theorem 1.3 for it: the residual graph of the terminal-selection matching is a spanning tree. -/
theorem hasTreeMatchingDecomposition_of_terminalSelection (hP : ProtectedCycleTheorem.{u})
    {G : SimpleGraph V} [DecidableRel G.Adj] (hconn : G.Connected) (hbridge : IsBridgeless G)
    (h23 : Is23Graph G) (hfrag : IsFragile G)
    (hTS : 2 ≤ (terminals G).ncard → TerminalSelectionStatement G (terminals G)) :
    HasTreeMatchingDecomposition G := by
  classical
  obtain ⟨M, hM, -, c₀, hS, -, htree, hcyc⟩ :=
    (hTS (two_le_ncard_terminals hP hconn hbridge h23 hfrag)).exists_residual_tree_component
  have hHG : deletedMatching G M ≤ G := deleteEdges_le _
  have hall : ∀ c : (deletedMatching G M).ConnectedComponent, c = c₀ := by
    intro c
    by_contra hc
    obtain ⟨hcycles, hne⟩ := hcyc c hc
    let v₀ : c := ⟨c.out, c.out_eq⟩
    obtain ⟨q, hq, -⟩ := hcycles.exists_cycle_toSubgraph_verts_eq_connectedComponentSupp
      (c := (componentGraph (deletedMatching G M) c).connectedComponentMk v₀)
      ConnectedComponent.connectedComponentMk_mem (hne v₀)
    let f : componentGraph (deletedMatching G M) c →g G :=
      (Hom.ofLE hHG).comp c.toSimpleGraph_hom
    have hf : Function.Injective f := Subtype.val_injective
    have hsupp : ∀ w ∈ (q.map f).support, w ∈ c.supp := by
      intro w hw
      rw [Walk.support_map, List.mem_map] at hw
      obtain ⟨a, -, rfl⟩ := hw
      exact a.2
    have hQ : ((⊤ : G.Subgraph).induce c₀.supp).Connected := by
      rw [← connected_induce_iff]
      have h₀ : ((deletedMatching G M).induce c₀.supp).Connected := c₀.connected_toSimpleGraph
      exact h₀.mono fun a b hab => hHG hab
    refine not_isFragile_of_protectedCycle hP hconn _ hQ
      ⟨_, q.map f, hq.map hf, fun e he heQ => ?_⟩ (fun z hz => ?_) hfrag
    · induction e using Sym2.ind with
      | h a b =>
        have ha : a ∈ c₀.supp := ((⊤ : G.Subgraph).induce c₀.supp).edge_vert heQ
        exact hc (ConnectedComponent.eq_of_common_vertex
          (hsupp a (Walk.fst_mem_support_of_mem_edges _ he)) ha)
    · rcases h23 z with h | h
      · exact absurd (hS h) hz
      · omega
  have hmem : ∀ v, v ∈ c₀.supp := fun v =>
    (ConnectedComponent.mem_supp_iff _ _).mpr (hall _)
  have hHconn : (deletedMatching G M).Connected := by
    obtain ⟨v⟩ := hconn.nonempty
    exact (connected_iff_exists_forall_reachable _).mpr
      ⟨v, fun w => ConnectedComponent.exact ((hall _).trans (hall _).symm)⟩
  let e : deletedMatching G M ↪g componentGraph (deletedMatching G M) c₀ :=
    { toFun := fun v => ⟨v, hmem v⟩
      inj' := fun a b hab => congrArg Subtype.val hab
      map_rel_iff' := Iff.rfl }
  have hHedge : (deletedMatching G M).edgeSet = G.edgeSet \ M.edgeSet := edgeSet_deleteEdges _
  refine ⟨deletedMatching G M, M, hHG, ⟨hHconn, htree.isAcyclic.embedding e⟩, hM, ?_, ?_⟩
  · rw [hHedge]
    exact Set.disjoint_sdiff_left
  · rw [hHedge]
    exact Set.sdiff_union_of_subset M.edgeSet_subset

end ThreeDecomposition

/-!
## Assembly of Theorem 1.4 (`fragileDecompositionTheorem_of_protectedCycle`)
-/

namespace ThreeDecomposition

open SimpleGraph

universe u

/-- A tree is its own decomposition, with the empty matching. -/
theorem hasTreeMatchingDecomposition_of_isTree {V : Type*} {G : SimpleGraph V} (hG : G.IsTree) :
    HasTreeMatchingDecomposition G :=
  ⟨G, ⊥, le_rfl, hG, fun _ hv => absurd hv (by simp), by simp, by simp⟩

section

variable {V : Type u} [Fintype V]

/-- Theorem 1.4, core case: a connected bridgeless fragile `{2,3}`-graph has a tree–matching
decomposition. -/
theorem hasTreeMatchingDecomposition_of_isBridgeless (hP : ProtectedCycleTheorem.{u})
    {G : SimpleGraph V} [DecidableRel G.Adj] (hconn : G.Connected) (hbridge : IsBridgeless G)
    (h23 : Is23Graph G) (hfrag : IsFragile G) : HasTreeMatchingDecomposition G := by
  classical
  exact hasTreeMatchingDecomposition_of_terminalSelection hP hconn hbridge h23 hfrag
    (terminal_selection G hconn hbridge h23)

/-- A connected bridgeless subcubic graph with a cycle has all degrees two or three. -/
theorem is23Graph_of_isBridgeless {G : SimpleGraph V} [DecidableRel G.Adj] (hconn : G.Connected)
    (hbridge : IsBridgeless G) (hcyc : ¬G.IsAcyclic) (hsub : IsSubcubic G) : Is23Graph G := by
  have : Nontrivial V := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    exact hcyc IsAcyclic.of_subsingleton
  intro v
  have hpos := hconn.preconnected.degree_pos_of_nontrivial v
  have hne : G.degree v ≠ 1 := by
    intro h1
    obtain ⟨w, hvw, huniq⟩ := degree_eq_one_iff_existsUnique_adj.mp h1
    have hr := hbridge (e := s(v, w)) hvw
    rw [isBridge_iff, not_not] at hr
    obtain ⟨p⟩ := hr
    cases p with
    | nil => exact hvw.ne rfl
    | cons h _ =>
      rw [deleteEdges_adj, Set.mem_singleton_iff] at h
      exact h.2 (by rw [huniq _ h.1])
  have := hsub v
  omega

end

/-- Theorem 1.4 for graphs on `n` vertices, by strong induction on `n`. -/
theorem hasTreeMatchingDecomposition_of_card (hP : ProtectedCycleTheorem.{u}) (n : ℕ) :
    ∀ (V : Type u) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj],
      Fintype.card V = n → G.Connected → IsFragile G → IsSubcubic G →
        HasTreeMatchingDecomposition G := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro V _ G _ hn hconn hfrag hsub
  classical
  by_cases hacyc : G.IsAcyclic
  · exact hasTreeMatchingDecomposition_of_isTree ⟨hconn, hacyc⟩
  by_cases hbridge : IsBridgeless G
  · exact hasTreeMatchingDecomposition_of_isBridgeless hP hconn hbridge
      (is23Graph_of_isBridgeless hconn hbridge hacyc hsub) hfrag
  obtain ⟨⟨x, y⟩, hxy, hbr⟩ : ∃ e, e ∈ G.edgeSet ∧ G.IsBridge e := by
    simpa [IsBridgeless] using hbridge
  obtain ⟨X, Y, h, hX, hY⟩ := exists_bridgeSplit hconn hxy hbr
  refine h.hasTreeMatchingDecomposition ?_ ?_
  · exact ih _ (hn ▸ Fintype.card_subtype_lt (h.notMem_left h.right_mem)) X (G.induce X) rfl
      hX (h.isFragile_induce_left hfrag hY) (hsub.induce X)
  · exact ih _ (hn ▸ Fintype.card_subtype_lt (h.symm.notMem_left h.left_mem)) Y (G.induce Y) rfl
      hY (h.symm.isFragile_induce_left hfrag hX) (hsub.induce Y)

/-- Theorem 1.4 from Theorem 2.2: every finite connected simple fragile subcubic graph has an
edge partition into a spanning tree and a matching. -/
theorem fragileDecompositionTheorem_of_protectedCycle (hP : ProtectedCycleTheorem.{u}) :
    FragileDecompositionTheorem.{u} :=
  fun V _ _ G _ hconn hfrag hsub =>
    hasTreeMatchingDecomposition_of_card hP _ V G rfl hconn hfrag hsub

end ThreeDecomposition
