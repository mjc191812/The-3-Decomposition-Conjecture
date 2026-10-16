import ThreeDecomposition.Basic.Definitions

/-!
# Normalization and transport lemmas for matching complements

This module provides basic unfolding lemmas for `deletedMatching G M = G.deleteEdges M.edgeSet`
together with transport of matchings and residual reachability along vertex maps (used in
`Lift.lean` and `Restore.lean`).

## Residual edges
-/

namespace ThreeDecomposition

open SimpleGraph

universe u

variable {V : Type u}

lemma deletedMatching_le
    (G : SimpleGraph V) [DecidableRel G.Adj] (M : G.Subgraph) :
    deletedMatching G M ≤ G := by
  exact SimpleGraph.deleteEdges_le _

/-- An edge is residual exactly when it is an edge of `G` outside the matching. -/
lemma deletedMatching_adj {G : SimpleGraph V} [DecidableRel G.Adj] {M : G.Subgraph} {u v : V} :
    (deletedMatching G M).Adj u v ↔ G.Adj u v ∧ ¬M.Adj u v :=
  deleteEdges_adj

lemma deletedMatching_not_adj_of_matching_adj
    (G : SimpleGraph V) [DecidableRel G.Adj] (M : G.Subgraph)
    {u v : V} (huv : M.Adj u v) :
    ¬(deletedMatching G M).Adj u v :=
  fun hres ↦ (deletedMatching_adj.1 hres).2 huv

lemma deletedMatching_edgeSet_disjoint_matching
    (G : SimpleGraph V) [DecidableRel G.Adj] (M : G.Subgraph) :
    Disjoint (deletedMatching G M).edgeSet M.edgeSet := by
  rw [Set.disjoint_left]
  intro e heH heM
  induction e using Sym2.inductionOn with
  | _ u v =>
      have hres : (deletedMatching G M).Adj u v :=
        (SimpleGraph.mem_edgeSet (deletedMatching G M)).mp heH
      exact (deletedMatching_adj.1 hres).2 (M.mem_edgeSet.mp heM)

end ThreeDecomposition

/-!
## Transporting matchings and reachability from a reduced graph

The local reductions produce a graph `J` on a vertex subtype `{v // p v}`, and a solution of the
terminal selection problem for `J` is lifted to the original graph `G`.

* `ThreeDecomposition.imageSubgraph`: pushes a matching `M` of `J` forward along an injective
  vertex map `φ`.
* `ThreeDecomposition.transferSubgraph`: reads a subgraph of `H` with edges in `G` as a subgraph
  of `G`.
* `ThreeDecomposition.reachable_map_of_adj`: transports residual reachability edge by edge.
-/

namespace ThreeDecomposition

open SimpleGraph

section Image

variable {V W : Type*}

/-- The `G`-edges `φ u φ v` with `uv` an edge of `M`, together with their endpoints. -/
def imageSubgraph (G : SimpleGraph V) {H : SimpleGraph W} (M : H.Subgraph) (φ : W → V) :
    G.Subgraph where
  verts := {x | ∃ y, G.Adj x y ∧ ∃ u v, M.Adj u v ∧ φ u = x ∧ φ v = y}
  Adj x y := G.Adj x y ∧ ∃ u v, M.Adj u v ∧ φ u = x ∧ φ v = y
  adj_sub h := h.1
  edge_vert h := ⟨_, h⟩
  symm := ⟨by
    rintro _ _ ⟨hxy, u, v, huv, rfl, rfl⟩
    exact ⟨hxy.symm, v, u, huv.symm, rfl, rfl⟩⟩

variable {G : SimpleGraph V} {H : SimpleGraph W} {M : H.Subgraph} {φ : W → V}

lemma imageSubgraph_adj {x y : V} :
    (imageSubgraph G M φ).Adj x y ↔ G.Adj x y ∧ ∃ u v, M.Adj u v ∧ φ u = x ∧ φ v = y :=
  Iff.rfl

lemma mem_imageSubgraph_verts {x : V} :
    x ∈ (imageSubgraph G M φ).verts ↔ ∃ y, (imageSubgraph G M φ).Adj x y :=
  Iff.rfl

lemma imageSubgraph_adj_of_adj {u v : W} (huv : M.Adj u v) (hG : G.Adj (φ u) (φ v)) :
    (imageSubgraph G M φ).Adj (φ u) (φ v) :=
  ⟨hG, u, v, huv, rfl, rfl⟩

lemma adj_of_imageSubgraph_adj (hφ : φ.Injective) {u v : W}
    (h : (imageSubgraph G M φ).Adj (φ u) (φ v)) : M.Adj u v := by
  obtain ⟨-, u', v', huv, hu, hv⟩ := h
  rwa [← hφ hu, ← hφ hv]

lemma map_mem_imageSubgraph_verts {u v : W} (huv : M.Adj u v) (hG : G.Adj (φ u) (φ v)) :
    φ u ∈ (imageSubgraph G M φ).verts :=
  (imageSubgraph_adj_of_adj huv hG).fst_mem

/-- A vertex outside the range of `φ` is exposed by the image. -/
lemma notMem_imageSubgraph_verts {x : V} (hx : ∀ w, φ w ≠ x) :
    x ∉ (imageSubgraph G M φ).verts := by
  rintro ⟨y, -, u, v, -, hu, -⟩
  exact hx u hu

/-- The image of a matching under an injective vertex map is a matching. -/
theorem isMatching_imageSubgraph (hφ : φ.Injective) (hM : M.IsMatching) :
    (imageSubgraph G M φ).IsMatching := by
  rintro _ ⟨y, hxy, u, v, huv, rfl, rfl⟩
  refine ⟨φ v, ⟨hxy, u, v, huv, rfl, rfl⟩, ?_⟩
  rintro _ ⟨-, u', v', huv', hu, rfl⟩
  rw [hφ hu] at huv'
  rw [hM.eq_of_adj_left huv' huv]

/-- If `φ` sends the edges of `M` to edges of `G`, the edges of the image are the images of the
edges of `M`. -/
theorem edgeSet_imageSubgraph (hG : ∀ ⦃u v⦄, M.Adj u v → G.Adj (φ u) (φ v)) :
    (imageSubgraph G M φ).edgeSet = Sym2.map φ '' M.edgeSet := by
  ext e
  induction e using Sym2.ind with
  | _ x y =>
    simp only [Subgraph.mem_edgeSet, Set.mem_image]
    constructor
    · rintro ⟨-, u, v, huv, rfl, rfl⟩
      exact ⟨s(u, v), huv, rfl⟩
    · rintro ⟨e, he, hxy⟩
      induction e using Sym2.ind with
      | _ u v =>
        rw [Subgraph.mem_edgeSet] at he
        rw [Sym2.map_mk, Sym2.eq_iff] at hxy
        rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact imageSubgraph_adj_of_adj he (hG he)
        · exact imageSubgraph_adj_of_adj he.symm (hG he.symm)

/-- An injective vertex map sending the edges of `M` to edges of `G` preserves the number of
edges. -/
theorem ncard_edgeSet_imageSubgraph (hφ : φ.Injective)
    (hG : ∀ ⦃u v⦄, M.Adj u v → G.Adj (φ u) (φ v)) :
    (imageSubgraph G M φ).edgeSet.ncard = M.edgeSet.ncard := by
  rw [edgeSet_imageSubgraph hG, Set.ncard_image_of_injective _ (Sym2.map.injective hφ)]

end Image

section Transfer

variable {V : Type*} {G H : SimpleGraph V}

/-- A subgraph of `H` all of whose edges are edges of `G`, viewed as a subgraph of `G`. -/
@[simps]
def transferSubgraph (N : H.Subgraph) (h : ∀ ⦃p q : V⦄, N.Adj p q → G.Adj p q) :
    G.Subgraph where
  verts := N.verts
  Adj := N.Adj
  adj_sub hpq := h hpq
  edge_vert := N.edge_vert
  symm := N.symm

variable {N : H.Subgraph} (h : ∀ ⦃p q : V⦄, N.Adj p q → G.Adj p q)

lemma isMatching_transferSubgraph (hN : N.IsMatching) : (transferSubgraph N h).IsMatching :=
  hN

@[simp]
lemma edgeSet_transferSubgraph : (transferSubgraph N h).edgeSet = N.edgeSet :=
  rfl

end Transfer

section Reachable

variable {V W : Type*}

/-- Reachability is transported along a map sending the ends of every edge to reachable
vertices. -/
theorem reachable_map_of_adj {H : SimpleGraph W} {K : SimpleGraph V} (f : W → V)
    (h : ∀ ⦃p q : W⦄, H.Adj p q → K.Reachable (f p) (f q)) {p q : W} (hpq : H.Reachable p q) :
    K.Reachable (f p) (f q) := by
  rw [reachable_iff_reflTransGen] at hpq ⊢
  exact Relation.ReflTransGen.lift' f
    (fun a b hab ↦ (reachable_iff_reflTransGen _ _).1 (h hab)) _ _ hpq

lemma reachable_of_sym2_eq {K : SimpleGraph V} {p q u w : V} (h : s(p, q) = s(u, w))
    (huw : K.Reachable u w) : K.Reachable p q := by
  rcases Sym2.eq_iff.1 h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  exacts [huw, huw.symm]

end Reachable

section Sym2

variable {V : Type*}

lemma sym2_mk_ne_of_left {c d p q : V} (hp : c ≠ p) (hq : c ≠ q) : s(c, d) ≠ s(p, q) :=
  fun h ↦ (Sym2.mem_iff.1 (h ▸ Sym2.mem_mk_left c d)).elim hp hq

lemma sym2_mk_ne_of_right {c d p q : V} (hp : d ≠ p) (hq : d ≠ q) : s(c, d) ≠ s(p, q) :=
  fun h ↦ (Sym2.mem_iff.1 (h ▸ Sym2.mem_mk_right c d)).elim hp hq

end Sym2

end ThreeDecomposition
