import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.SimpleGraph.Finite
import ThreeDecomposition.Interfaces

/-!
# Removable cycles avoiding a connected subgraph (Theorem 2.2)

This module proves Theorem 2.2 of the paper (`protectedCycleTheorem`, due to Borse and Waphare):
if `G` is a finite connected simple graph, `Q` is a connected subgraph, `G` contains a cycle
edge-disjoint from `Q`, and every vertex outside `Q` has degree at least three, then `G` contains
a cycle `C` edge-disjoint from `Q` such that `G - E(C)` is connected.

## Walk, cycle and forest helpers
-/

namespace ThreeDecomposition

open SimpleGraph

variable {V : Type*}

/-- A longest path of a finite acyclic graph with at least one edge is nontrivial, and each of
its endpoints is adjacent only to its neighbour on the path. -/
theorem exists_isPath_forall_adj_eq_of_isAcyclic [Finite V] {K : SimpleGraph V}
    (hK : K.IsAcyclic) {a b : V} (hab : K.Adj a b) :
    ∃ (u v : V) (p : K.Walk u v), p.IsPath ∧ ¬p.Nil ∧
      (∀ w, K.Adj u w → w = p.snd) ∧ (∀ w, K.Adj v w → w = p.penultimate) := by
  have : Nonempty V := ⟨a⟩
  obtain ⟨u, v, p, hp, hmax⟩ := Walk.exists_isPath_forall_isPath_length_le_length K
  have hnil : ¬p.Nil := by
    intro h
    have := hmax a b (Walk.cons hab Walk.nil) (Walk.IsPath.nil.cons (by simp [hab.ne]))
    rw [← Walk.length_eq_zero_iff] at h
    simp [h] at this
  refine ⟨u, v, p, hp, hnil, fun w hw ↦ ?_, fun w hw ↦ ?_⟩
  · refine hK.eq_snd_of_adj_start hp hw ?_
    by_contra hws
    have := hmax _ _ (p.cons hw.symm) (hp.cons hws)
    simp at this
  · refine hK.eq_penultimate_of_adj_end hp hw ?_
    by_contra hws
    have := hmax _ _ (p.concat hw) (hp.concat hws hw)
    simp at this

variable {G : SimpleGraph V}

/-- Two vertices of a cycle `C` are joined by a walk all of whose edges are edges of `C`
different from a prescribed edge `e` of `C`. -/
theorem exists_walk_forall_mem_edges_of_isCycle {x u v : V} {C : G.Walk x x} (hC : C.IsCycle)
    {e : Sym2 V} (he : e ∈ C.edges) (hu : u ∈ C.support) (hv : v ∈ C.support) :
    ∃ q : G.Walk u v, ∀ f ∈ q.edges, f ∈ C.edges ∧ f ≠ e := by
  classical
  set R := G.deleteEdges {f | f ∉ C.edges} with hR
  have hCR : ∀ f ∈ C.edges, f ∈ R.edgeSet := fun f hf ↦ by
    rw [hR, edgeSet_deleteEdges]
    exact ⟨C.edges_subset_edgeSet hf, by simpa using hf⟩
  set C₀ := C.transfer R hCR with hC₀
  have hnb : ¬R.IsBridge e := fun hb ↦
    hb.notMem_edges_of_isCycle (hC.transfer hCR) (by rwa [Walk.edges_transfer])
  have hsupp : ∀ y ∈ C.support, R.Reachable y x := fun y hy ↦
    ⟨C₀.dropUntil y (by rw [hC₀, Walk.support_transfer]; exact hy)⟩
  obtain ⟨q⟩ := ((hsupp u hu).trans (hsupp v hv).symm).reachable_deleteEdges_of_not_isBridge hnb
  refine ⟨q.mapLe ((deleteEdges_le _).trans (deleteEdges_le _)), fun f hf ↦ ?_⟩
  rw [Walk.edges_mapLe_eq_edges] at hf
  have hfR := q.edges_subset_edgeSet hf
  rw [edgeSet_deleteEdges, hR, edgeSet_deleteEdges] at hfR
  exact ⟨by simpa using hfR.1.2, by simpa using hfR.2⟩

/-- A vertex all of whose edges are edges of a cycle has degree at most two. -/
theorem degree_le_two_of_forall_adj_mem_edges {x w : V} [Fintype (G.neighborSet w)]
    {C : G.Walk x x} (hC : C.IsCycle) (h : ∀ b, G.Adj w b → s(w, b) ∈ C.edges) :
    G.degree w ≤ 2 := by
  by_cases hwC : w ∈ C.support
  · have hle : G.neighborSet w ⊆ C.toSubgraph.neighborSet w := fun b hb ↦
      Walk.adj_toSubgraph_iff_mem_edges.mpr (h b hb)
    have h2 := hC.ncard_neighborSet_toSubgraph_eq_two hwC
    have := Set.ncard_le_ncard hle (Set.finite_of_ncard_ne_zero (by omega))
    rwa [h2, ← Nat.card_coe_set_eq,
      Nat.card_eq_fintype_card, card_neighborSet_eq_degree] at this
  · by_contra! hw
    obtain ⟨b, hb⟩ := G.degree_pos_iff_exists_adj w |>.mp (by omega)
    exact hwC (C.fst_mem_support_of_mem_edges (h b hb))

end ThreeDecomposition

/-!
## Connectivity of `G - E(C)`

Let `H` be a connected subgraph of `G` such that every vertex outside `H` has degree at least
three, let `C` be a cycle edge-disjoint from `H`, and let `e` be an edge of `C` such that
`F - e` is a forest, where `F = G - E(H)`.  Then `G - E(C)` is connected
(`connected_deleteEdges_of_isAcyclic`).
-/

namespace ThreeDecomposition

open SimpleGraph

variable {V : Type*} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- If `C` is a cycle edge-disjoint from a connected subgraph `H`, every vertex outside `H` has
degree at least three, and deleting an edge `e` of `C` from the spanning graph of the edges
outside `H` leaves a forest, then deleting the edges of `C` from `G` leaves a connected graph. -/
theorem connected_deleteEdges_of_isAcyclic {H : G.Subgraph} (hH : H.Connected)
    (hdeg : ∀ x, x ∉ H.verts → 3 ≤ G.degree x)
    {x : V} {C : G.Walk x x} (hC : C.IsCycle) (hCH : ∀ f ∈ C.edges, f ∉ H.edgeSet)
    {e : Sym2 V} (he : e ∈ C.edges)
    (hacyc : (G.deleteEdges (H.edgeSet ∪ {e})).IsAcyclic) :
    (G.deleteEdges {f | f ∈ C.edges}).Connected := by
  classical
  set G' := G.deleteEdges {f | f ∈ C.edges} with hG'
  set Fe := G.deleteEdges (H.edgeSet ∪ {e}) with hFe
  obtain ⟨q₀, hq₀⟩ := hH.nonempty
  have hHG' : ∀ ⦃a b : V⦄, H.Adj a b → G'.Adj a b := fun a b h ↦
    deleteEdges_adj.mpr ⟨H.adj_sub h, fun hm ↦ hCH _ hm (H.mem_edgeSet.mpr h)⟩
  have hHreach : ∀ q ∈ H.verts, G'.Reachable q q₀ := fun q hq ↦
    (hH ⟨q, hq⟩ ⟨q₀, hq₀⟩).map ⟨Subtype.val, fun h ↦ hHG' h⟩
  rw [connected_iff_exists_forall_reachable]
  refine ⟨q₀, fun w ↦ ?_⟩
  by_contra hw
  replace hw : ¬G'.Reachable w q₀ := fun h ↦ hw h.symm
  let K : SimpleGraph V :=
    { Adj := fun a b ↦ G'.Adj a b ∧ ¬G'.Reachable a q₀
      symm := ⟨fun a b h ↦ ⟨h.1.symm, fun hb ↦ h.2 (h.1.reachable.trans hb)⟩⟩
      loopless := ⟨fun a h ↦ G'.loopless.irrefl a h.1⟩ }
  have hKG' : K ≤ G' := fun a b h ↦ h.1
  have hKFe : K ≤ Fe := by
    intro a b ⟨hab, ha⟩
    rw [hG', deleteEdges_adj] at hab
    refine deleteEdges_adj.mpr ⟨hab.1, ?_⟩
    rintro (h | h)
    · exact ha (hHreach a (H.mem_edgeSet.mp h).fst_mem)
    · exact hab.2 ((Set.mem_singleton_iff.mp h) ▸ he)
  obtain ⟨b, hwb⟩ : ∃ b, K.Adj w b := by
    by_contra! hno
    have h2 := degree_le_two_of_forall_adj_mem_edges hC fun b hb ↦ by
      by_contra hm
      exact hno b ⟨deleteEdges_adj.mpr ⟨hb, hm⟩, hw⟩
    have h3 := hdeg w fun h ↦ hw (hHreach w h)
    omega
  obtain ⟨u, v, p, hp, hnil, hu, hv⟩ :=
    exists_isPath_forall_adj_eq_of_isAcyclic (hacyc.anti hKFe) hwb
  have hend : ∀ y z, K.Adj y z → (∀ t, K.Adj y t → t = z) → y ∈ C.support := by
    intro y z hyz huniq
    by_contra hy
    have hy3 : 3 ≤ G.degree y := hdeg y fun h ↦ hyz.2 (hHreach y h)
    have hsub : G.neighborFinset y ⊆ {z} := by
      intro t ht
      rw [mem_neighborFinset] at ht
      rw [Finset.mem_singleton]
      exact huniq t
        ⟨deleteEdges_adj.mpr ⟨ht, fun hm ↦ hy (C.fst_mem_support_of_mem_edges hm)⟩, hyz.2⟩
    have := Finset.card_le_card hsub
    rw [card_neighborFinset_eq_degree, Finset.card_singleton] at this
    omega
  obtain ⟨q, hq⟩ := exists_walk_forall_mem_edges_of_isCycle hC he
    (hend u p.snd (p.adj_snd hnil) hu) (hend v p.penultimate (p.adj_penultimate hnil).symm hv)
  have hqFe : ∀ f ∈ q.edges, f ∈ Fe.edgeSet := fun f hf ↦ by
    rw [hFe, edgeSet_deleteEdges]
    refine ⟨q.edges_subset_edgeSet hf, ?_⟩
    rintro (h | h)
    · exact hCH f (hq f hf).1 h
    · exact (hq f hf).2 h
  have hpq : (⟨p.mapLe hKFe, hp.mapLe hKFe⟩ : Fe.Path u v) = (q.transfer Fe hqFe).toPath :=
    (hacyc.subsingleton_path u v).elim _ _
  obtain ⟨f, hf⟩ := List.exists_mem_of_ne_nil p.edges (by rwa [Ne, Walk.edges_eq_nil])
  have hfC : f ∉ C.edges := by
    have := edgeSet_mono hKG' (p.edges_subset_edgeSet hf)
    rw [hG', edgeSet_deleteEdges] at this
    exact this.2
  have hfq : f ∈ (q.transfer Fe hqFe).toPath.1.edges := by
    rw [← hpq, Walk.edges_mapLe_eq_edges]
    exact hf
  have := Walk.edges_toPath_subset_edges _ hfq
  rw [Walk.edges_transfer] at this
  exact hfC (hq f this).1

end ThreeDecomposition

/-!
## Proof of Theorem 2.2 (`protectedCycleTheorem`)

Among the connected subgraphs `H ⊇ Q` whose edge-complement contains a cycle, choose a maximal
one.  A cycle `C` in the edge-complement passes through an edge `e` leaving `H`, and maximality
makes `F - e` a forest; `connected_deleteEdges_of_isAcyclic` then shows that `G - E(C)` is
connected.
-/

namespace ThreeDecomposition

open SimpleGraph

universe u

variable {V : Type*} {G : SimpleGraph V}

/-- If `G` is connected and has a cycle edge-disjoint from a connected subgraph `H`, then some
edge of `G` outside `H` has an endpoint in `H`. -/
theorem exists_adj_mem_verts_notMem_edgeSet {H : G.Subgraph} (hG : G.Connected)
    (hH : H.Connected) {y : V} {c : G.Walk y y} (hc : c.IsCycle)
    (hcH : ∀ f ∈ c.edges, f ∉ H.edgeSet) :
    ∃ a b, G.Adj a b ∧ a ∈ H.verts ∧ s(a, b) ∉ H.edgeSet := by
  by_cases hy : y ∈ H.verts
  · exact ⟨y, c.snd, c.adj_snd hc.not_nil, hy, hcH _ (Walk.mk_start_snd_mem_edges hc.not_nil)⟩
  · obtain ⟨q₀, hq₀⟩ := hH.nonempty
    obtain ⟨d, -, hd₁, hd₂⟩ := (hG.preconnected q₀ y).some.exists_boundary_dart H.verts hq₀ hy
    exact ⟨d.fst, d.snd, d.adj, hd₁, fun h ↦ hd₂ (H.mem_edgeSet.mp h).snd_mem⟩

/-- **Theorem 2.2** (Borse–Waphare).  Let `G` be a connected finite simple graph and `Q` a
connected subgraph.  If `G` has a cycle edge-disjoint from `Q` and every vertex outside `Q` has
degree at least three, then `G` has a cycle `C` edge-disjoint from `Q` such that `G - E(C)` is
connected. -/
theorem protectedCycleTheorem : ProtectedCycleTheorem.{u} := by
  intro V _ _ G _ Q hG hQ ⟨x, C, hC, hCQ⟩ hdeg
  obtain ⟨H, hQH, hHmax⟩ := Finite.exists_le_maximal
    (p := fun H : G.Subgraph ↦ Q ≤ H ∧ H.Connected ∧
      ∃ (y : V) (c : G.Walk y y), c.IsCycle ∧ ∀ f ∈ c.edges, f ∉ H.edgeSet)
    ⟨le_rfl, hQ, x, C, hC, hCQ⟩
  obtain ⟨-, hHconn, y, c, hc, hcH⟩ := hHmax.prop
  have hM : ∀ a b (hab : G.Adj a b), a ∈ H.verts → s(a, b) ∉ H.edgeSet →
      ∀ (z : V) (c' : G.Walk z z), c'.IsCycle → (∀ f ∈ c'.edges, f ∉ H.edgeSet) →
        s(a, b) ∈ c'.edges := by
    intro a b hab ha hnot z c' hc' hc'H
    by_contra hmem
    have hle := hHmax.le_of_ge (y := H ⊔ G.subgraphOfAdj hab)
      ⟨hQH.trans le_sup_left,
        Subgraph.connected_sup hHconn.preconnected
          (Subgraph.subgraphOfAdj_connected hab).preconnected ⟨a, ha, by simp⟩,
        z, c', hc', fun f hf hfH ↦ by
          rw [Subgraph.edgeSet_sup, edgeSet_subgraphOfAdj] at hfH
          rcases hfH with hfH | hfH
          · exact hc'H f hf hfH
          · exact hmem (Set.mem_singleton_iff.mp hfH ▸ hf)⟩
      le_sup_left
    exact hnot (Subgraph.edgeSet_mono hle (by simp))
  obtain ⟨a, b, hab, ha, hnot⟩ := exists_adj_mem_verts_notMem_edgeSet hG hHconn hc hcH
  refine ⟨y, c, hc, fun f hf hfQ ↦ hcH f hf (Subgraph.edgeSet_mono hQH hfQ), ?_⟩
  refine connected_deleteEdges_of_isAcyclic hHconn (fun z hz ↦ hdeg z fun h ↦ hz (hQH.1 h))
    hc hcH (hM a b hab ha hnot y c hc hcH) fun z c' hc' ↦ ?_
  have hc'G : ∀ f ∈ c'.edges, f ∈ G.edgeSet ∧ f ∉ H.edgeSet ∪ {s(a, b)} := fun f hf ↦ by
    have h := c'.edges_subset_edgeSet hf
    rw [edgeSet_deleteEdges] at h
    exact h
  have := hM a b hab ha hnot z (c'.mapLe (deleteEdges_le _)) (hc'.mapLe _)
    fun f hf hfH ↦ (hc'G f (by rwa [Walk.edges_mapLe_eq_edges] at hf)).2 (Or.inl hfH)
  rw [Walk.edges_mapLe_eq_edges] at this
  exact (hc'G _ this).2 (Or.inr rfl)

end ThreeDecomposition
