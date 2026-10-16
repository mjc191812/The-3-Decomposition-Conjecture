import ThreeDecomposition.Basic.Definitions

/-!
# Alternating-path exchange (Lemma 3.3)

This module proves Lemma 3.3 of the paper (`first_entry`, `first_entry_reachable`): given
matchings `M, N` of `G`, a component `Q` of `G - M`, and an `M`-exposed, `N`-covered vertex
`x ∉ Q` such that all other `M`-exposed vertices and all `N`-exposed vertices lie in `Q`, there
is a matching `M'` with `|M'| = |M|` such that the component of `G - M'` containing `Q` contains
every vertex exposed by `M'`.

## Exchanging one matching edge

Given a matching `M`, a matching edge `s(y, z)` and a graph edge `s(x, y)` whose
endpoint `x` is exposed by `M`, `replaceEdge M hxy z` replaces `s(y, z)` with `s(x, y)`.
-/

namespace ThreeDecomposition

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- Deleting both endpoints of a matching edge from a matching leaves a matching. -/
lemma isMatching_deleteVerts_pair {M : G.Subgraph} (hM : M.IsMatching) {y z : V}
    (hyz : M.Adj y z) : (M.deleteVerts {y, z}).IsMatching := by
  intro v hv
  simp only [Subgraph.deleteVerts_verts, Set.mem_sdiff, Set.mem_insert_iff,
    Set.mem_singleton_iff, not_or] at hv
  obtain ⟨hvM, hvy, hvz⟩ := hv
  obtain ⟨w, hvw, huniq⟩ := hM hvM
  refine ⟨w, ?_, fun w' hw' => huniq w' (Subgraph.deleteVerts_adj.mp hw').2.2.2.2⟩
  have hwy : w ≠ y := by
    rintro rfl
    exact hvz (hM.eq_of_adj_right hvw hyz.symm)
  have hwz : w ≠ z := by
    rintro rfl
    exact hvy (hM.eq_of_adj_right hvw hyz)
  simp [hvM, hvy, hvz, hvw.snd_mem, hwy, hwz, hvw]

/-- Replace the matching edge `s(y, z)` of `M` by the graph edge `s(x, y)`. -/
def replaceEdge (M : G.Subgraph) {x y : V} (hxy : G.Adj x y) (z : V) : G.Subgraph :=
  M.deleteVerts {y, z} ⊔ G.subgraphOfAdj hxy

variable {M : G.Subgraph} {x y z : V} (hxy : G.Adj x y)

lemma replaceEdge_verts :
    (replaceEdge M hxy z).verts = M.verts \ {y, z} ∪ {x, y} := rfl

lemma replaceEdge_adj {u v : V} :
    (replaceEdge M hxy z).Adj u v ↔
      (M.Adj u v ∧ u ≠ y ∧ u ≠ z ∧ v ≠ y ∧ v ≠ z) ∨ s(x, y) = s(u, v) := by
  simp only [replaceEdge, Subgraph.sup_adj, Subgraph.deleteVerts_adj, subgraphOfAdj_adj,
    Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
  constructor
  · rintro (⟨-, ⟨hu1, hu2⟩, -, ⟨hv1, hv2⟩, h⟩ | h)
    · exact Or.inl ⟨h, hu1, hu2, hv1, hv2⟩
    · exact Or.inr h
  · rintro (⟨h, hu1, hu2, hv1, hv2⟩ | h)
    · exact Or.inl ⟨h.fst_mem, ⟨hu1, hu2⟩, h.snd_mem, ⟨hv1, hv2⟩, h⟩
    · exact Or.inr h

/-- Replacing a matching edge by an edge to an exposed vertex gives a matching. -/
lemma isMatching_replaceEdge (hM : M.IsMatching) (hyz : M.Adj y z) (hx : x ∉ M.verts) :
    (replaceEdge M hxy z).IsMatching := by
  refine (isMatching_deleteVerts_pair hM hyz).sup (Subgraph.IsMatching.subgraphOfAdj hxy) ?_
  rw [(isMatching_deleteVerts_pair hM hyz).support_eq_verts, support_subgraphOfAdj,
    Set.disjoint_left]
  rintro v ⟨hvM, hvyz⟩ (rfl | rfl)
  · exact hx hvM
  · exact hvyz (Set.mem_insert _ _)

lemma edgeSet_replaceEdge (hM : M.IsMatching) (hyz : M.Adj y z) :
    (replaceEdge M hxy z).edgeSet = insert s(x, y) (M.edgeSet \ {s(y, z)}) := by
  ext e
  induction e using Sym2.ind with
  | _ u v =>
    simp only [Subgraph.mem_edgeSet, replaceEdge_adj, Set.mem_insert_iff, Set.mem_sdiff,
      Set.mem_singleton_iff]
    constructor
    · rintro (⟨h, hu1, hu2, hv1, hv2⟩ | h)
      · refine Or.inr ⟨h, ?_⟩
        rw [Sym2.eq_iff]
        rintro (⟨rfl, -⟩ | ⟨rfl, -⟩) <;> simp_all
      · exact Or.inl h.symm
    · rintro (h | ⟨h, hne⟩)
      · exact Or.inr h.symm
      · refine Or.inl ⟨h, ?_, ?_, ?_, ?_⟩
        · rintro rfl
          exact hne (by rw [hM.eq_of_adj_left h hyz])
        · rintro rfl
          exact hne (by rw [hM.eq_of_adj_left h hyz.symm, Sym2.eq_swap])
        · rintro rfl
          exact hne (by rw [hM.eq_of_adj_right h hyz.symm, Sym2.eq_swap])
        · rintro rfl
          exact hne (by rw [hM.eq_of_adj_right h hyz])

/-- The exchange preserves the number of matching edges. -/
lemma ncard_edgeSet_replaceEdge [Finite V] (hM : M.IsMatching) (hyz : M.Adj y z)
    (hx : x ∉ M.verts) :
    (replaceEdge M hxy z).edgeSet.ncard = M.edgeSet.ncard := by
  rw [edgeSet_replaceEdge hxy hM hyz, Set.ncard_insert_of_notMem,
    Set.ncard_sdiff_singleton_add_one (Subgraph.mem_edgeSet.mpr hyz)]
  rintro ⟨h, -⟩
  exact hx (Subgraph.mem_edgeSet.mp h).fst_mem

/-- A vertex exposed after the exchange is `z` or was exposed before and differs from `x`. -/
lemma eq_or_notMem_of_notMem_replaceEdge_verts {v : V} (hv : v ∉ (replaceEdge M hxy z).verts) :
    v = z ∨ (v ∉ M.verts ∧ v ≠ x) := by
  simp only [replaceEdge_verts, Set.mem_union, Set.mem_sdiff, Set.mem_insert_iff,
    Set.mem_singleton_iff, not_or, not_and, not_not] at hv
  obtain ⟨h, hvx, hvy⟩ := hv
  by_cases hvM : v ∈ M.verts
  · exact Or.inl (h hvM hvy)
  · exact Or.inr ⟨hvM, hvx⟩

lemma notMem_replaceEdge_verts (hzx : z ≠ x) (hzy : z ≠ y) :
    z ∉ (replaceEdge M hxy z).verts := by
  simp [replaceEdge_verts, hzx, hzy]

end ThreeDecomposition

/-!
## Transferring reachability under edge modifications outside `Q`
-/

namespace ThreeDecomposition

open SimpleGraph

variable {V : Type*}

/-- Reachability from `q` transfers from `H` to `H'` as soon as every `H`-edge starting
at a vertex reachable from `q` in both graphs is an `H'`-edge. -/
theorem reachable_of_reachable_of_adj {H H' : SimpleGraph V} {q v : V}
    (h : ∀ ⦃u w : V⦄, H.Reachable q u → H'.Reachable q u → H.Adj u w → H'.Adj u w)
    (hv : H.Reachable q v) : H'.Reachable q v := by
  obtain ⟨p⟩ := hv
  suffices ∀ u (p : H.Walk u v), H.Reachable q u → H'.Reachable q u → H'.Reachable q v from
    this q p (Reachable.refl q) (Reachable.refl q)
  clear p
  intro u p
  induction p with
  | nil => exact fun _ hu' => hu'
  | cons hadj _ ih =>
    exact fun hu hu' =>
      ih (hu.trans hadj.reachable) (hu'.trans (h hu hu' hadj).reachable)

variable {G : SimpleGraph V} {A B : Set (Sym2 V)} {q v : V}

/-- Adding edges to the deleted set keeps everything reachable from `q`, provided no
added edge touches a vertex reachable from `q` before the change. -/
theorem reachable_deleteEdges_of_reachable
    (h : ∀ e ∈ B \ A, ∀ u ∈ e, ¬(G.deleteEdges A).Reachable q u)
    (hv : (G.deleteEdges A).Reachable q v) : (G.deleteEdges B).Reachable q v := by
  refine reachable_of_reachable_of_adj (fun u w hu _ huw => ?_) hv
  rw [deleteEdges_adj] at huw ⊢
  refine ⟨huw.1, fun hB => h _ ⟨hB, huw.2⟩ u (Sym2.mem_mk_left u w) hu⟩

/-- Removing edges from the deleted set adds nothing to what is reachable from `q`,
provided no removed edge touches a vertex reachable from `q` before the change. -/
theorem reachable_deleteEdges_of_reachable'
    (h : ∀ e ∈ A \ B, ∀ u ∈ e, ¬(G.deleteEdges A).Reachable q u)
    (hv : (G.deleteEdges B).Reachable q v) : (G.deleteEdges A).Reachable q v := by
  refine reachable_of_reachable_of_adj (fun u w _ hu huw => ?_) hv
  rw [deleteEdges_adj] at huw ⊢
  refine ⟨huw.1, fun hA => h _ ⟨hA, huw.2⟩ u (Sym2.mem_mk_left u w) hu⟩

end ThreeDecomposition

/-!
## Proof of Lemma 3.3 (`first_entry`)

The paper flips the prefix of the alternating path of `M ∆ N` from `x` up to its first
entry into `Q`.  Here the prefix is flipped one edge pair at a time by strong induction on
`|N \ M|`: with `y` the `N`-partner of `x` and `z` the `M`-partner of `y`, replace `s(y, z)` by
`s(x, y)`.
-/

namespace ThreeDecomposition

open SimpleGraph

variable {V : Type*} [Finite V]

/-- Reachability form of the first-entry lemma, with `Q` the component of `q`.  The new
matching keeps everything reachable from `q`. -/
theorem first_entry_reachable (G : SimpleGraph V) [DecidableRel G.Adj]
    (M N : G.Subgraph) (hM : M.IsMatching) (hN : N.IsMatching) (q x : V)
    (hxq : ¬(deletedMatching G M).Reachable q x) (hxM : x ∉ M.verts) (hxN : x ∈ N.verts)
    (hMexp : ∀ v, v ∉ M.verts → v ≠ x → (deletedMatching G M).Reachable q v)
    (hNexp : ∀ v, v ∉ N.verts → (deletedMatching G M).Reachable q v) :
    ∃ M' : G.Subgraph, M'.IsMatching ∧ M'.edgeSet.ncard = M.edgeSet.ncard ∧
      (∀ v, (deletedMatching G M).Reachable q v → (deletedMatching G M').Reachable q v) ∧
      ∀ v, v ∉ M'.verts → (deletedMatching G M').Reachable q v := by
  obtain ⟨n, hn⟩ : ∃ n, (N.edgeSet \ M.edgeSet).ncard = n := ⟨_, rfl⟩
  induction n using Nat.strong_induction_on generalizing M x with
  | _ n ih =>
  obtain ⟨y, hxy, -⟩ := hN hxN
  have hGxy : G.Adj x y := hxy.adj_sub
  have hxyM : s(x, y) ∉ M.edgeSet := fun h => hxM (Subgraph.mem_edgeSet.mp h).fst_mem
  have hres : (deletedMatching G M).Adj x y := deleteEdges_adj.mpr ⟨hGxy, hxyM⟩
  have hyq : ¬(deletedMatching G M).Reachable q y := fun h => hxq (h.trans hres.symm.reachable)
  have hyM : y ∈ M.verts := by
    by_contra h
    exact hyq (hMexp y h hGxy.ne.symm)
  obtain ⟨z, hyz, -⟩ := hM hyM
  have hzx : z ≠ x := fun h => hxM (h ▸ hyz.snd_mem)
  have hzy : z ≠ y := hyz.ne.symm
  set M₁ := replaceEdge M hGxy z
  have hM₁ : M₁.IsMatching := isMatching_replaceEdge hGxy hM hyz hxM
  have hcard : M₁.edgeSet.ncard = M.edgeSet.ncard := ncard_edgeSet_replaceEdge hGxy hM hyz hxM
  have hE : M₁.edgeSet = insert s(x, y) (M.edgeSet \ {s(y, z)}) :=
    edgeSet_replaceEdge hGxy hM hyz
  have hfwd : ∀ v, (deletedMatching G M).Reachable q v → (deletedMatching G M₁).Reachable q v := by
    refine fun v hv => reachable_deleteEdges_of_reachable (fun e he u hu => ?_) hv
    obtain ⟨he₁, he₂⟩ := he
    rw [hE] at he₁
    obtain rfl : e = s(x, y) := by
      rcases he₁ with h | ⟨h, -⟩
      · exact h
      · exact absurd h he₂
    rcases Sym2.mem_iff.mp hu with rfl | rfl
    · exact hxq
    · exact hyq
  have hexp₁ : ∀ v, v ∉ M₁.verts → v ≠ z → (deletedMatching G M₁).Reachable q v := by
    intro v hv hvz
    obtain ⟨hvM, hvx⟩ := (eq_or_notMem_of_notMem_replaceEdge_verts hGxy hv).resolve_left hvz
    exact hfwd _ (hMexp v hvM hvx)
  by_cases hzq : (deletedMatching G M).Reachable q z
  · refine ⟨M₁, hM₁, hcard, hfwd, fun v hv => ?_⟩
    by_cases hvz : v = z
    · exact hvz ▸ hfwd _ hzq
    · exact hexp₁ v hv hvz
  · have hbwd : ∀ v, (deletedMatching G M₁).Reachable q v →
        (deletedMatching G M).Reachable q v := by
      refine fun v hv => reachable_deleteEdges_of_reachable' (fun e he u hu => ?_) hv
      obtain ⟨he₁, he₂⟩ := he
      rw [hE] at he₂
      obtain rfl : e = s(y, z) := by
        by_contra h
        exact he₂ (Set.mem_insert_of_mem _ ⟨he₁, h⟩)
      rcases Sym2.mem_iff.mp hu with rfl | rfl
      · exact hyq
      · exact hzq
    have hzN : z ∈ N.verts := by
      by_contra h
      exact hzq (hNexp z h)
    have hlt : (N.edgeSet \ M₁.edgeSet).ncard < n := by
      rw [← hn]
      refine Set.ncard_lt_ncard ((Set.ssubset_iff_of_subset fun e he => ?_).mpr
        ⟨s(x, y), ⟨hxy, hxyM⟩, fun h => h.2 (hE ▸ Set.mem_insert _ _)⟩)
      refine ⟨he.1, fun heM => he.2 ?_⟩
      rw [hE]
      refine Set.mem_insert_of_mem _ ⟨heM, ?_⟩
      rintro rfl
      exact hzx (hN.eq_of_adj_left (Subgraph.mem_edgeSet.mp he.1) hxy.symm)
    obtain ⟨M', hM', hcard', hreach, hexp⟩ :=
      ih _ hlt M₁ hM₁ z (fun h => hzq (hbwd _ h))
        (notMem_replaceEdge_verts hGxy hzx hzy) hzN hexp₁ (fun v hv => hfwd _ (hNexp v hv)) rfl
    exact ⟨M', hM', hcard'.trans hcard, fun v hv => hreach v (hfwd v hv), hexp⟩

/-- **Lemma 3.3 (first entry).**  Let `M, N` be matchings of `G` and `Q` a component of
`G - M`.  Suppose `x ∉ Q` is exposed by `M` and covered by `N`, every other `M`-exposed
vertex lies in `Q`, and every `N`-exposed vertex lies in `Q`.  Then there is a matching
`M'` with `|M'| = |M|` such that the component of `G - M'` containing `Q` contains every
vertex exposed by `M'`. -/
theorem first_entry (G : SimpleGraph V) [DecidableRel G.Adj]
    (M N : G.Subgraph) (hM : M.IsMatching) (hN : N.IsMatching)
    (Q : (deletedMatching G M).ConnectedComponent) (x : V)
    (hxQ : x ∉ Q.supp) (hxM : x ∉ M.verts) (hxN : x ∈ N.verts)
    (hMexp : ∀ v, v ∉ M.verts → v ≠ x → v ∈ Q.supp)
    (hNexp : ∀ v, v ∉ N.verts → v ∈ Q.supp) :
    ∃ M' : G.Subgraph, M'.IsMatching ∧ M'.edgeSet.ncard = M.edgeSet.ncard ∧
      ∃ Q' : (deletedMatching G M').ConnectedComponent,
        Q.supp ⊆ Q'.supp ∧ ∀ v, v ∉ M'.verts → v ∈ Q'.supp := by
  induction Q using ConnectedComponent.ind with
  | h q =>
  have mem_iff : ∀ {H : SimpleGraph V} {v : V},
      v ∈ (H.connectedComponentMk q).supp ↔ H.Reachable q v := fun {H v} =>
    (ConnectedComponent.mem_supp_iff _ _).trans (ConnectedComponent.eq.trans reachable_comm)
  obtain ⟨M', hM', hcard, hreach, hexp⟩ :=
    first_entry_reachable G M N hM hN q x (mt mem_iff.mpr hxQ) hxM hxN
      (fun v hv hvx => mem_iff.mp (hMexp v hv hvx)) (fun v hv => mem_iff.mp (hNexp v hv))
  exact ⟨M', hM', hcard, (deletedMatching G M').connectedComponentMk q,
    fun v hv => mem_iff.mpr (hreach v (mem_iff.mp hv)), fun v hv => mem_iff.mpr (hexp v hv)⟩

end ThreeDecomposition
