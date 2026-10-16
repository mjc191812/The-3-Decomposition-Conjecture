import ThreeDecomposition.MatchingComplement.TerminalCriterion
import ThreeDecomposition.MatchingComplement.Normalization
import ThreeDecomposition.FirstEntry
import ThreeDecomposition.Induction

/-!
# Lifting solutions through the two reductions (Lemma 3.4)

This module proves `adjacentTerminalLift` (Lemma 3.4(a)) and `triangleLift` (Lemma 3.4(b)),
showing that a solution of the terminal selection problem for the reduced graph lifts to the
original graph `G`.

## Lifting Lemma 3.4(a): adjacent terminals

Contracting the edge between two adjacent terminals `u` and `v` is implemented as the
suppression of `v` (with neighbours `u` and `y`).  If `uy ∉ MJ`, `MJ` is kept and `uy` becomes
the residual path `u v y`; if `uy ∈ MJ`, `uy` is replaced by `vy` and `uv` is residual.
-/

namespace ThreeDecomposition

open SimpleGraph

universe u

namespace IsSuppressible

variable {V : Type*} {G H : SimpleGraph V} {v u y : V}

/-- The local step of Reduction 1: a matching `N` of `H = G + uy` exposing `v` gives a matching
of `G` of the same size such that `uv` is a residual edge and the ends of every residual edge
of `H` avoiding `v` are joined in the residual graph of `G`. -/
theorem exists_lift [Finite V] [DecidableRel G.Adj] (hs : IsSuppressible G v u y)
    (hle : G ≤ H) (hH : ∀ ⦃p q : V⦄, H.Adj p q → G.Adj p q ∨ s(p, q) = s(u, y))
    {N : H.Subgraph} (hN : N.IsMatching) (hv : v ∉ N.verts) :
    ∃ M : G.Subgraph, M.IsMatching ∧ M.edgeSet.ncard = N.edgeSet.ncard ∧
      (deletedMatching G M).Adj u v ∧
      ∀ ⦃p q : V⦄, p ≠ v → q ≠ v → H.Adj p q → ¬N.Adj p q →
        (deletedMatching G M).Reachable p q := by
  have hvN : ∀ ⦃w : V⦄, ¬N.Adj v w := fun _ h ↦ hv h.fst_mem
  by_cases huy : N.Adj u y
  · have hvy : H.Adj v y := hle hs.adj_right
    have hsub : ∀ ⦃p q : V⦄, (replaceEdge N hvy u).Adj p q → G.Adj p q := by
      intro p q hpq
      rcases (replaceEdge_adj hvy).1 hpq with ⟨hpq, hpy, hpu, -, -⟩ | hpq
      · refine (hH (N.adj_sub hpq)).resolve_right fun h ↦ ?_
        rcases Sym2.eq_iff.1 h with ⟨rfl, -⟩ | ⟨rfl, -⟩
        exacts [hpu rfl, hpy rfl]
      · exact (G.adj_congr_of_sym2 hpq.symm).2 hs.adj_right
    have hMadj : ∀ ⦃p q : V⦄, (transferSubgraph _ hsub).Adj p q → p ≠ v → q ≠ v →
        N.Adj p q := by
      intro p q hpq hp hq
      rcases (replaceEdge_adj hvy).1 hpq with ⟨hpq, -⟩ | hpq
      · exact hpq
      · rcases Sym2.eq_iff.1 hpq with ⟨rfl, -⟩ | ⟨rfl, -⟩
        exacts [(hp rfl).elim, (hq rfl).elim]
    refine ⟨transferSubgraph _ hsub,
      isMatching_transferSubgraph hsub (isMatching_replaceEdge hvy hN huy.symm hv),
      ncard_edgeSet_replaceEdge hvy hN huy.symm hv,
      deletedMatching_adj.2 ⟨hs.adj_left.symm, fun h ↦ ?_⟩, ?_⟩
    · rcases (replaceEdge_adj hvy).1 h with ⟨h, -⟩ | h
      · exact hvN h.symm
      · rcases Sym2.eq_iff.1 h with ⟨h, -⟩ | ⟨-, h⟩
        exacts [hs.left_ne h.symm, hs.ne h.symm]
    intro p q hp hq hpq hN'
    rcases hH hpq with hpq | hpq
    · exact (deletedMatching_adj.2 ⟨hpq, fun h ↦ hN' (hMadj h hp hq)⟩).reachable
    · exact absurd ((Subgraph.adj_congr_of_sym2 hpq).2 huy) hN'
  · have hsub : ∀ ⦃p q : V⦄, N.Adj p q → G.Adj p q := fun p q hpq ↦
      (hH (N.adj_sub hpq)).resolve_right fun h ↦ huy ((Subgraph.adj_congr_of_sym2 h.symm).2 hpq)
    have huv : (deletedMatching G (transferSubgraph N hsub)).Adj u v :=
      deletedMatching_adj.2 ⟨hs.adj_left.symm, fun h ↦ hvN h.symm⟩
    have huy' : (deletedMatching G (transferSubgraph N hsub)).Reachable u y :=
      huv.reachable.trans (deletedMatching_adj.2 ⟨hs.adj_right, fun h ↦ hvN h⟩).reachable
    refine ⟨transferSubgraph N hsub, isMatching_transferSubgraph hsub hN, rfl, huv, ?_⟩
    intro p q _ _ hpq hN'
    rcases hH hpq with hpq | hpq
    · exact (deletedMatching_adj.2 ⟨hpq, hN'⟩).reachable
    · exact reachable_of_sym2_eq hpq huy'

end IsSuppressible

/-- Reduction 1 lifts: if `u` and `v` are adjacent terminals and the graph obtained by
suppressing `v` solves the terminal selection problem, then so does `G`. -/
theorem adjacentTerminalLift : AdjacentTerminalLift.{u} := by
  intro V _ _ G _ u v y h23 hs hu hJ
  have hu' : (⟨u, hs.left_ne⟩ : {w // w ≠ v}) ∈ terminals (suppress G v u y) :=
    (hs.mem_terminals_suppress_iff _).2 hu
  obtain ⟨MJ, hMJ, hsize, hreach⟩ := hJ.exists_reachable hu'
  have hH : ∀ ⦃p q : V⦄, (G ⊔ edge u y).Adj p q → G.Adj p q ∨ s(p, q) = s(u, y) := by
    intro p q h
    rw [sup_adj, edge_adj] at h
    rcases h with h | ⟨h, -⟩
    exacts [Or.inl h, Or.inr (Sym2.eq_iff.2 h)]
  have hJH : ∀ ⦃p q : {w // w ≠ v}⦄, (suppress G v u y).Adj p q → (G ⊔ edge u y).Adj p q :=
    fun _ _ h ↦ h
  obtain ⟨M, hM, hcard, huv, hlift⟩ := hs.exists_lift le_sup_left hH
    (isMatching_imageSubgraph Subtype.val_injective hMJ) (notMem_imageSubgraph_verts fun w ↦ w.2)
  refine terminalSelectionStatement_of_reachable h23 hM ?_ u fun t ht ↦ ?_
  · rw [hcard, ncard_edgeSet_imageSubgraph Subtype.val_injective fun _ _ h ↦ hJH h.adj_sub, hsize,
      hs.cyclomaticNumber_suppress]
  by_cases htv : t = v
  · subst htv
    exact huv.reachable
  refine reachable_map_of_adj Subtype.val (fun p q hpq ↦ ?_)
    (hreach ⟨t, htv⟩ ((hs.mem_terminals_suppress_iff _).2 ht))
  obtain ⟨hadj, hnot⟩ := deletedMatching_adj.1 hpq
  exact hlift p.2 q.2 (hJH hadj) fun h ↦ hnot (adj_of_imageSubgraph_adj Subtype.val_injective h)

end ThreeDecomposition

/-!
## Lifting Lemma 3.4(b): triangle at a terminal

Lemma 3.4(b) replaces the triangle `sab` at the terminal `s` by the edges `sx` and `sy`, where
`x` and `y` are the third neighbours of `a` and `b`.  A matching `MJ` of `J` of size `q - 1`
is lifted to a matching of `G` of size `q` by adding `ab` (if neither `sx` nor `sy` lies in `MJ`)
or replacing `sx` by `ax` and `sb` (and symmetrically for `sy`).
-/

namespace ThreeDecomposition

open SimpleGraph

universe u

namespace IsReplaceableTriangle

variable {V : Type*} {G H : SimpleGraph V} {s a b x y : V} [Finite V] [DecidableRel G.Adj]

/-- Case (a) of the lift of Reduction 2: if neither `sx` nor `sy` is a matching edge, add the
edge `ab`. -/
lemma exists_lift_of_not_adj (hT : IsReplaceableTriangle G s a b x y)
    (hH : ∀ ⦃p q : V⦄, H.Adj p q → G.Adj p q ∨ s(p, q) = s(s, x) ∨ s(p, q) = s(s, y))
    {N : H.Subgraph} (hN : N.IsMatching) (ha : a ∉ N.verts) (hb : b ∉ N.verts)
    (hsx : ¬N.Adj s x) (hsy : ¬N.Adj s y) :
    ∃ M : G.Subgraph, M.IsMatching ∧ M.edgeSet.ncard = N.edgeSet.ncard + 1 ∧
      ∀ ⦃p q : V⦄, p ≠ a → p ≠ b → q ≠ a → q ≠ b → H.Adj p q → ¬N.Adj p q →
        (deletedMatching G M).Reachable p q := by
  have hsub : ∀ ⦃p q : V⦄, N.Adj p q → G.Adj p q := fun p q hpq ↦ by
    rcases hH (N.adj_sub hpq) with h | h | h
    · exact h
    · exact absurd ((Subgraph.adj_congr_of_sym2 h.symm).2 hpq) hsx
    · exact absurd ((Subgraph.adj_congr_of_sym2 h.symm).2 hpq) hsy
  have hN' := isMatching_transferSubgraph hsub hN
  have hna : ∀ {w : V}, ¬N.Adj a w := fun h ↦ ha h.fst_mem
  have hnb : ∀ {w : V}, ¬N.Adj b w := fun h ↦ hb h.fst_mem
  have hres : ∀ ⦃p q : V⦄, G.Adj p q → ¬N.Adj p q → s(a, b) ≠ s(p, q) →
      (deletedMatching G (transferSubgraph N hsub ⊔ G.subgraphOfAdj hT.adj_ab)).Reachable p q :=
    fun _ _ hpq hnpq hab ↦
      Adj.reachable (deletedMatching_adj.2 ⟨hpq, fun h ↦ h.elim hnpq hab⟩)
  refine ⟨transferSubgraph N hsub ⊔ G.subgraphOfAdj hT.adj_ab,
    hN'.sup (.subgraphOfAdj _) ?_, ?_, ?_⟩
  · rw [hN'.support_eq_verts, support_subgraphOfAdj, Set.disjoint_right]
    rintro w (rfl | rfl)
    exacts [ha, hb]
  · rw [Subgraph.edgeSet_sup, edgeSet_subgraphOfAdj, Set.union_singleton,
      Set.ncard_insert_of_notMem (show s(a, b) ∉ (transferSubgraph N hsub).edgeSet from hna),
      edgeSet_transferSubgraph]
  intro p q hpa _ hqa _ hpq hnpq
  rcases hH hpq with h | h | h
  · exact hres h hnpq (sym2_mk_ne_of_left hpa.symm hqa.symm)
  · exact reachable_of_sym2_eq h <|
      (hres hT.adj_sa (fun h ↦ hna h.symm)
        (sym2_mk_ne_of_right hT.s_ne_b.symm hT.a_ne_b.symm)).trans
        (hres hT.adj_ax hna (sym2_mk_ne_of_right hT.a_ne_b.symm hT.x_ne_b.symm))
  · exact reachable_of_sym2_eq h <|
      (hres hT.adj_sb (fun h ↦ hnb h.symm) (sym2_mk_ne_of_left hT.s_ne_a.symm hT.a_ne_b)).trans
        (hres hT.adj_by hnb (sym2_mk_ne_of_left hT.a_ne_b hT.y_ne_a.symm))

/-- Case (b) of the lift of Reduction 2: if `sx` is a matching edge, replace it by `ax` and add
the edge `sb`. -/
lemma exists_lift_of_adj (hT : IsReplaceableTriangle G s a b x y) (hle : G ≤ H)
    (hH : ∀ ⦃p q : V⦄, H.Adj p q → G.Adj p q ∨ s(p, q) = s(s, x) ∨ s(p, q) = s(s, y))
    {N : H.Subgraph} (hN : N.IsMatching) (ha : a ∉ N.verts) (hb : b ∉ N.verts)
    (hsx : N.Adj s x) :
    ∃ M : G.Subgraph, M.IsMatching ∧ M.edgeSet.ncard = N.edgeSet.ncard + 1 ∧
      ∀ ⦃p q : V⦄, p ≠ a → p ≠ b → q ≠ a → q ≠ b → H.Adj p q → ¬N.Adj p q →
        (deletedMatching G M).Reachable p q := by
  have hax : H.Adj a x := hle hT.adj_ax
  have hsub : ∀ ⦃p q : V⦄, (replaceEdge N hax s).Adj p q → G.Adj p q := by
    intro p q hpq
    rcases (replaceEdge_adj hax).1 hpq with ⟨hpq, -, hps, -, hqs⟩ | h
    · rcases hH (N.adj_sub hpq) with h | h | h
      · exact h
      · exact absurd h.symm (sym2_mk_ne_of_left hps.symm hqs.symm)
      · exact absurd h.symm (sym2_mk_ne_of_left hps.symm hqs.symm)
    · exact (G.adj_congr_of_sym2 h.symm).2 hT.adj_ax
  have hR := isMatching_transferSubgraph hsub (isMatching_replaceEdge hax hN hsx.symm ha)
  have hsR : s ∉ (replaceEdge N hax s).verts :=
    notMem_replaceEdge_verts hax hT.s_ne_a hT.x_ne_s.symm
  have hbR : b ∉ (replaceEdge N hax s).verts := by
    rw [replaceEdge_verts]
    rintro (⟨h, -⟩ | h | h)
    exacts [hb h, hT.a_ne_b h.symm, hT.x_ne_b h.symm]
  have hna : ∀ {w : V}, ¬N.Adj a w := fun h ↦ ha h.fst_mem
  have hnb : ∀ {w : V}, ¬N.Adj b w := fun h ↦ hb h.fst_mem
  have hres : ∀ ⦃p q : V⦄, G.Adj p q → ¬N.Adj p q → s(a, x) ≠ s(p, q) → s(s, b) ≠ s(p, q) →
      (deletedMatching G (transferSubgraph _ hsub ⊔ G.subgraphOfAdj hT.adj_sb)).Reachable p q :=
    fun p q hpq hnpq hax' hsb ↦ Adj.reachable (deletedMatching_adj.2 ⟨hpq, fun h ↦ h.elim
      (fun h ↦ ((replaceEdge_adj hax).1 h).elim (fun h ↦ hnpq h.1) hax') hsb⟩)
  refine ⟨transferSubgraph _ hsub ⊔ G.subgraphOfAdj hT.adj_sb,
    hR.sup (.subgraphOfAdj _) ?_, ?_, ?_⟩
  · rw [hR.support_eq_verts, support_subgraphOfAdj, Set.disjoint_right]
    rintro w (rfl | rfl)
    exacts [hsR, hbR]
  · rw [Subgraph.edgeSet_sup, edgeSet_subgraphOfAdj, Set.union_singleton,
      Set.ncard_insert_of_notMem (show s(s, b) ∉ (transferSubgraph _ hsub).edgeSet from
        fun h ↦ hbR (Subgraph.mem_edgeSet.1 h).snd_mem),
      edgeSet_transferSubgraph, ncard_edgeSet_replaceEdge hax hN hsx.symm ha]
  intro p q hpa hpb hqa hqb hpq hnpq
  rcases hH hpq with h | h | h
  · exact hres h hnpq (sym2_mk_ne_of_left hpa.symm hqa.symm)
      (sym2_mk_ne_of_right hpb.symm hqb.symm)
  · exact absurd ((Subgraph.adj_congr_of_sym2 h).2 hsx) hnpq
  · refine reachable_of_sym2_eq h <|
      ((hres hT.adj_sa (fun h ↦ hna h.symm) ?_ ?_).trans (hres hT.adj_ab hna ?_ ?_)).trans
        (hres hT.adj_by hnb ?_ ?_)
    · exact sym2_mk_ne_of_right hT.x_ne_s hT.x_ne_a
    · exact sym2_mk_ne_of_right hT.s_ne_b.symm hT.a_ne_b.symm
    · exact sym2_mk_ne_of_right hT.x_ne_a hT.x_ne_b
    · exact sym2_mk_ne_of_left hT.s_ne_a hT.s_ne_b
    · exact sym2_mk_ne_of_left hT.a_ne_b hT.y_ne_a.symm
    · exact sym2_mk_ne_of_left hT.s_ne_b hT.y_ne_s.symm

/-- The local step of Reduction 2: a matching `N` of `H = G + sx + sy` exposing `a` and `b`
gives a matching of `G` with one more edge such that the ends of every residual edge of `H`
avoiding `a` and `b` are joined in the residual graph of `G`. -/
theorem exists_lift (hT : IsReplaceableTriangle G s a b x y) (hle : G ≤ H)
    (hH : ∀ ⦃p q : V⦄, H.Adj p q → G.Adj p q ∨ s(p, q) = s(s, x) ∨ s(p, q) = s(s, y))
    {N : H.Subgraph} (hN : N.IsMatching) (ha : a ∉ N.verts) (hb : b ∉ N.verts) :
    ∃ M : G.Subgraph, M.IsMatching ∧ M.edgeSet.ncard = N.edgeSet.ncard + 1 ∧
      ∀ ⦃p q : V⦄, p ≠ a → p ≠ b → q ≠ a → q ≠ b → H.Adj p q → ¬N.Adj p q →
        (deletedMatching G M).Reachable p q := by
  by_cases hsx : N.Adj s x
  · exact hT.exists_lift_of_adj hle hH hN ha hb hsx
  by_cases hsy : N.Adj s y
  · obtain ⟨M, hM, hcard, hreach⟩ := hT.symm.exists_lift_of_adj hle
      (fun _ _ hpq ↦ (hH hpq).imp_right Or.symm) hN hb ha hsy
    exact ⟨M, hM, hcard, fun _ _ hpa hpb hqa hqb ↦ hreach hpb hpa hqb hqa⟩
  · exact hT.exists_lift_of_not_adj hH hN ha hb hsx hsy

end IsReplaceableTriangle

/-- Reduction 2 lifts: if replacing the triangle `sab` at the terminal `s` by the edges `sx` and
`sy` gives a graph solving the terminal selection problem, then `G` solves it. -/
theorem triangleLift : TriangleLift.{u} := by
  intro V _ _ G _ s a b x y h23 hT hJ
  obtain ⟨MJ, hMJ, hsize, hreach⟩ :=
    hJ.exists_reachable ((hT.mem_terminals_replaceTriangle_iff hT.sVert).2 hT.degree_s)
  have hH : ∀ ⦃p q : V⦄, (G ⊔ edge s x ⊔ edge s y).Adj p q →
      G.Adj p q ∨ s(p, q) = s(s, x) ∨ s(p, q) = s(s, y) := by
    intro p q h
    rw [sup_adj, sup_adj, edge_adj, edge_adj] at h
    rcases h with (h | ⟨h, -⟩) | ⟨h, -⟩
    exacts [Or.inl h, Or.inr (Or.inl (Sym2.eq_iff.2 h)), Or.inr (Or.inr (Sym2.eq_iff.2 h))]
  have hJH : ∀ ⦃p q : {w // w ≠ a ∧ w ≠ b}⦄, (replaceTriangle G s a b x y).Adj p q →
      (G ⊔ edge s x ⊔ edge s y).Adj p q := fun _ _ h ↦ h
  obtain ⟨M, hM, hcard, hlift⟩ := hT.exists_lift (le_sup_left.trans le_sup_left) hH
    (isMatching_imageSubgraph Subtype.val_injective hMJ)
    (notMem_imageSubgraph_verts fun w ↦ w.2.1) (notMem_imageSubgraph_verts fun w ↦ w.2.2)
  refine terminalSelectionStatement_of_reachable h23 hM ?_ s fun t ht ↦ ?_
  · rw [hcard, ncard_edgeSet_imageSubgraph Subtype.val_injective fun _ _ h ↦ hJH h.adj_sub,
      ← hT.cyclomaticNumber_replaceTriangle, ← hsize]
    push_cast
    rfl
  have h2 : G.degree t = 2 := ht
  have hta : t ≠ a := fun h ↦ by have := hT.degree_a; rw [← h] at this; omega
  have htb : t ≠ b := fun h ↦ by have := hT.degree_b; rw [← h] at this; omega
  refine reachable_map_of_adj Subtype.val (fun p q hpq ↦ ?_)
    (hreach ⟨t, hta, htb⟩ ((hT.mem_terminals_replaceTriangle_iff _).2 ht))
  obtain ⟨hadj, hnot⟩ := deletedMatching_adj.1 hpq
  exact hlift p.2.1 p.2.2 q.2.1 q.2.2 (hJH hadj) fun h ↦
    hnot (adj_of_imageSubgraph_adj Subtype.val_injective h)

end ThreeDecomposition
