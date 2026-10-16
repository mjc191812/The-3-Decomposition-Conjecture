import ThreeDecomposition.Basic
import ThreeDecomposition.External.SpecifiedEdgeMatching
import Mathlib.Combinatorics.SimpleGraph.CycleGraph

/-!
# Auxiliary cubic completions: the base case `k = 2` and Lemma 3.5

This module constructs the two cubic extensions to which Schönberger's theorem
(`exists_perfect_matching_containing_edge`) is applied:

* **Base case `k = 2`** (`exists_isPerfectMatching_of_ncard_terminals_eq_two`): attaches a copy
  of `K₄ - 01` to the two terminals `s, t` and restricts a perfect matching containing an edge
  of `G` at `s`.
* **Comparison matching for `k ≥ 3`, Lemma 3.5** (`exists_comparison_matching`): attaches a
  `k`-cycle on new vertices to the `k` terminals and restricts a perfect matching to obtain a
  matching of `G` that covers all degree-three vertices and at least one terminal.

## Extending a graph by new vertices

Given `G : SimpleGraph V`, a graph `H` on a type `W` of new vertices and a spoke relation
`S : V → W → Prop`, `extendGraph G H S` on `V ⊕ W` consists of `G`, `H`, and the spokes
`inl v - inr a` for `S v a`.
-/

namespace ThreeDecomposition

open SimpleGraph

section Restrict

variable {V X : Type*} {G : SimpleGraph V} {K : SimpleGraph X}

/-- The restriction of a subgraph `P` of `K` along a graph embedding `f : G ↪g K`: its edges are
the `P`-edges between vertices in the image of `f`, and its vertices are the endpoints of these
edges. -/
def restrictSubgraph (f : G ↪g K) (P : K.Subgraph) : G.Subgraph where
  verts := {v | ∃ w, P.Adj (f v) (f w)}
  Adj u v := P.Adj (f u) (f v)
  adj_sub h := f.map_adj_iff.mp (P.adj_sub h)
  edge_vert h := ⟨_, h⟩
  symm.symm _ _ h := h.symm

@[simp]
lemma restrictSubgraph_adj (f : G ↪g K) (P : K.Subgraph) {u v : V} :
    (restrictSubgraph f P).Adj u v ↔ P.Adj (f u) (f v) :=
  Iff.rfl

@[simp]
lemma mem_restrictSubgraph_verts (f : G ↪g K) (P : K.Subgraph) {v : V} :
    v ∈ (restrictSubgraph f P).verts ↔ ∃ w, P.Adj (f v) (f w) :=
  Iff.rfl

/-- The restriction of a matching along an embedding is a matching. -/
lemma isMatching_restrictSubgraph (f : G ↪g K) {P : K.Subgraph} (hP : P.IsMatching) :
    (restrictSubgraph f P).IsMatching := by
  rintro v ⟨w, hw⟩
  exact ⟨w, hw, fun w' hw' => f.injective (hP.eq_of_adj_left hw' hw)⟩

/-- The restriction of a perfect matching along an embedding `f` covers every vertex `v` such
that every neighbour of `f v` lies in the image of `f`. -/
lemma mem_restrictSubgraph_verts_of_neighborSet_subset (f : G ↪g K) {P : K.Subgraph}
    (hP : P.IsPerfectMatching) {v : V} (hv : K.neighborSet (f v) ⊆ Set.range f) :
    v ∈ (restrictSubgraph f P).verts := by
  obtain ⟨y, hy, -⟩ := Subgraph.isPerfectMatching_iff.mp hP (f v)
  obtain ⟨w, rfl⟩ := hv (P.adj_sub hy)
  exact ⟨w, hy⟩

end Restrict

/-- If `x - z - y` is a walk of length two, then `x` and `y` stay reachable after deleting the
edge `s(x, y)`. -/
lemma reachable_deleteEdges_of_adj_of_adj {X : Type*} {K : SimpleGraph X} {x y z : X}
    (hxz : K.Adj x z) (hzy : K.Adj z y) : (K.deleteEdges {s(x, y)}).Reachable x y := by
  refine (Adj.reachable (v := z) ?_).trans (Adj.reachable ?_)
  · exact (deleteEdges_adj ..).mpr ⟨hxz, fun h => hzy.ne (Sym2.congr_right.mp h)⟩
  · exact (deleteEdges_adj ..).mpr ⟨hzy, fun h => hxz.ne.symm (Sym2.congr_left.mp h)⟩

section Extend

variable {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W} {S : V → W → Prop}

/-- The extension of `G` by the graph `H` on new vertices along the spoke relation `S`: the graph
on `V ⊕ W` containing `G` on the left, `H` on the right, and an edge `inl v - inr a` whenever
`S v a`. -/
def extendGraph (G : SimpleGraph V) (H : SimpleGraph W) (S : V → W → Prop) :
    SimpleGraph (V ⊕ W) where
  Adj
    | .inl u, .inl v => G.Adj u v
    | .inr a, .inr b => H.Adj a b
    | .inl u, .inr b => S u b
    | .inr a, .inl v => S v a
  symm := ⟨by rintro (u | a) (v | b) h <;> first | exact h | exact h.symm⟩
  loopless := ⟨by rintro (u | a) h; exacts [G.loopless.irrefl u h, H.loopless.irrefl a h]⟩

@[simp]
lemma extendGraph_adj_inl_inl {u v : V} :
    (extendGraph G H S).Adj (.inl u) (.inl v) ↔ G.Adj u v :=
  Iff.rfl

@[simp]
lemma extendGraph_adj_inr_inr {a b : W} :
    (extendGraph G H S).Adj (.inr a) (.inr b) ↔ H.Adj a b :=
  Iff.rfl

@[simp]
lemma extendGraph_adj_inl_inr {v : V} {a : W} :
    (extendGraph G H S).Adj (.inl v) (.inr a) ↔ S v a :=
  Iff.rfl

@[simp]
lemma extendGraph_adj_inr_inl {v : V} {a : W} :
    (extendGraph G H S).Adj (.inr a) (.inl v) ↔ S v a :=
  Iff.rfl

variable (G H S) in
/-- The embedding of `G` into its extension `extendGraph G H S`. -/
@[simps]
def extendGraphInl : G ↪g extendGraph G H S where
  toFun := Sum.inl
  inj' := Sum.inl_injective
  map_rel_iff' := Iff.rfl

variable (G H S) in
/-- The embedding of `H` into the extension `extendGraph G H S`. -/
@[simps]
def extendGraphInr : H ↪g extendGraph G H S where
  toFun := Sum.inr
  inj' := Sum.inr_injective
  map_rel_iff' := Iff.rfl

lemma extendGraph_neighborSet_inl (v : V) :
    (extendGraph G H S).neighborSet (.inl v) =
      Sum.inl '' G.neighborSet v ∪ Sum.inr '' {a | S v a} := by
  ext (w | b) <;> simp

lemma extendGraph_neighborSet_inr (a : W) :
    (extendGraph G H S).neighborSet (.inr a) =
      Sum.inl '' {v | S v a} ∪ Sum.inr '' H.neighborSet a := by
  ext (w | b) <;> simp

lemma ncard_neighborSet_extendGraph_inl [Finite V] [Finite W] (v : V) :
    ((extendGraph G H S).neighborSet (.inl v)).ncard =
      (G.neighborSet v).ncard + {a | S v a}.ncard := by
  rw [extendGraph_neighborSet_inl, Set.ncard_union_eq Set.disjoint_image_inl_image_inr,
    Set.ncard_image_of_injective _ Sum.inl_injective,
    Set.ncard_image_of_injective _ Sum.inr_injective]

lemma ncard_neighborSet_extendGraph_inr [Finite V] [Finite W] (a : W) :
    ((extendGraph G H S).neighborSet (.inr a)).ncard =
      {v | S v a}.ncard + (H.neighborSet a).ncard := by
  rw [extendGraph_neighborSet_inr, Set.ncard_union_eq Set.disjoint_image_inl_image_inr,
    Set.ncard_image_of_injective _ Sum.inl_injective,
    Set.ncard_image_of_injective _ Sum.inr_injective]

/-- The restriction to `G` of a perfect matching of `extendGraph G H S` covers every vertex of `G`
that carries no spoke. -/
lemma mem_restrictSubgraph_extendGraphInl_verts {P : (extendGraph G H S).Subgraph}
    (hP : P.IsPerfectMatching) {v : V} (hv : ∀ a, ¬S v a) :
    v ∈ (restrictSubgraph (extendGraphInl G H S) P).verts := by
  refine mem_restrictSubgraph_verts_of_neighborSet_subset _ hP ?_
  rintro (w | a) h
  · exact ⟨w, rfl⟩
  · exact absurd h (hv a)

lemma extendGraph_reachable_inl {u v : V} (h : G.Reachable u v) :
    (extendGraph G H S).Reachable (.inl u) (.inl v) :=
  h.map (extendGraphInl G H S).toHom

/-- An extension of a connected graph is connected as soon as every new vertex is reachable from
some old vertex. -/
lemma extendGraph_connected (hG : G.Connected)
    (h : ∀ a, ∃ v, (extendGraph G H S).Reachable (.inl v) (.inr a)) :
    (extendGraph G H S).Connected := by
  obtain ⟨v₀⟩ := hG.nonempty
  refine (connected_iff_exists_forall_reachable _).mpr ⟨.inl v₀, ?_⟩
  rintro (v | a)
  · exact extendGraph_reachable_inl (hG.preconnected _ _)
  · obtain ⟨v, hv⟩ := h a
    exact (extendGraph_reachable_inl (hG.preconnected _ _)).trans hv

/-- Reachability in `G` lifts to the extension with any new edge deleted. -/
lemma extendGraph_reachable_deleteEdges_inl {e : Sym2 (V ⊕ W)}
    (he : ∀ u v, e ≠ s(.inl u, .inl v)) {u v : V} (h : G.Reachable u v) :
    ((extendGraph G H S).deleteEdges {e}).Reachable (.inl u) (.inl v) :=
  h.map ⟨Sum.inl, fun {a b} hab => by simpa [Ne.symm (he a b)] using hab⟩

/-- A non-bridge of `G` is not a bridge of its extension. -/
lemma not_isBridge_extendGraph_inl {u v : V} (h : ¬G.IsBridge s(u, v)) :
    ¬(extendGraph G H S).IsBridge s(.inl u, .inl v) := by
  rw [isBridge_iff, not_not] at h ⊢
  refine h.map ⟨Sum.inl, fun {a b} hab => ?_⟩
  simp only [deleteEdges_adj, Set.mem_singleton_iff] at hab ⊢
  refine ⟨hab.1, fun h' => hab.2 ?_⟩
  simpa using h'

/-- An extension of a bridgeless graph is bridgeless as soon as no new edge is a bridge, i.e. the
endpoints of each new edge stay reachable after deleting it. -/
lemma isBridgeless_extendGraph [DecidableRel G.Adj] [DecidableRel (extendGraph G H S).Adj]
    (hG : IsBridgeless G)
    (hH : ∀ a b, H.Adj a b →
      ((extendGraph G H S).deleteEdges {s(.inr a, .inr b)}).Reachable (.inr a) (.inr b))
    (hS : ∀ v a, S v a →
      ((extendGraph G H S).deleteEdges {s(.inl v, .inr a)}).Reachable (.inl v) (.inr a)) :
    IsBridgeless (extendGraph G H S) := by
  intro e he
  induction e using Sym2.ind with
  | _ x y =>
    rw [mem_edgeSet] at he
    rcases x with u | a <;> rcases y with v | b
    · exact not_isBridge_extendGraph_inl (hG he)
    · exact isBridge_iff.not_left.mpr (hS u b he)
    · rw [Sym2.eq_swap]
      exact isBridge_iff.not_left.mpr (hS v a he)
    · exact isBridge_iff.not_left.mpr (hH a b he)

end Extend

end ThreeDecomposition

/-!
## The base case `k = 2`

Let `G` be a connected bridgeless `{2,3}`-graph with two terminals `s ≠ t`.  Following Section 3.4
of the paper, we attach the gadget `K₄ - 01` on `Fin 4` by the spokes `s - 0` and `t - 1`.  The
resulting graph `baseCompletion G s t` on `V ⊕ Fin 4` is cubic, connected and bridgeless.  A
perfect matching through an edge of `G` at `s` cannot use the spoke at `s`; the gadget then
forces the spoke at `t` out of the matching as well, so the matching restricts to a perfect
matching of `G`.
-/

namespace ThreeDecomposition

open SimpleGraph

universe u

/-- The gadget of the base case: `K₄` on `Fin 4` minus the edge `0 1`. -/
def baseGadget : SimpleGraph (Fin 4) where
  Adj a b := a ≠ b ∧ a.val + b.val ≠ 1
  symm := ⟨fun _ _ h => ⟨h.1.symm, by omega⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

instance : DecidableRel baseGadget.Adj := fun a b =>
  inferInstanceAs (Decidable (a ≠ b ∧ a.val + b.val ≠ 1))

/-- `baseGadget` is `K₄` minus the edge `0 1`. -/
lemma baseGadget_eq : baseGadget = ⊤ \ edge 0 1 := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [baseGadget, edge_adj]

/-- Every edge of `baseGadget` lies on a triangle. -/
lemma baseGadget_exists_triangle :
    ∀ a b, baseGadget.Adj a b → ∃ c, baseGadget.Adj a c ∧ baseGadget.Adj c b := by
  decide

/-- The spokes of the base case: `s` is joined to gadget vertex `0` and `t` to gadget vertex `1`. -/
def baseSpoke {V : Type*} (s t v : V) (a : Fin 4) : Prop :=
  v = s ∧ a = 0 ∨ v = t ∧ a = 1

/-- The simple cubic completion of a graph with two terminals `s, t`: the gadget `K₄ - 01` is
attached to `G` by the spokes `s - 0` and `t - 1`. -/
abbrev baseCompletion {V : Type*} (G : SimpleGraph V) (s t : V) : SimpleGraph (V ⊕ Fin 4) :=
  extendGraph G baseGadget (baseSpoke s t)

section BaseCompletion

variable {V : Type*} {G : SimpleGraph V} {s t : V}

/-- `baseCompletion G s t` is cubic when `s, t` are the only terminals of the `{2,3}`-graph `G`. -/
lemma baseCompletion_ncard_neighborSet [Fintype V] [DecidableRel G.Adj] (hG : Is23Graph G)
    (hst : s ≠ t) (hterm : ∀ v, G.degree v = 2 ↔ v = s ∨ v = t) (x : V ⊕ Fin 4) :
    ((baseCompletion G s t).neighborSet x).ncard = 3 := by
  rcases x with v | a
  · rw [ncard_neighborSet_extendGraph_inl, ncard_neighborSet]
    by_cases hs : v = s
    · subst hs
      have h : {a | baseSpoke v t v a} = {0} := by ext a; simp [baseSpoke, hst]
      rw [h, Set.ncard_singleton, (hterm v).2 (Or.inl rfl)]
    by_cases ht : v = t
    · subst ht
      have h : {a | baseSpoke s v v a} = {1} := by ext a; simp [baseSpoke, Ne.symm hst]
      rw [h, Set.ncard_singleton, (hterm v).2 (Or.inr rfl)]
    have h : {a | baseSpoke s t v a} = ∅ := by ext a; simp [baseSpoke, hs, ht]
    have h3 : G.degree v = 3 := (hG v).resolve_left fun h2 => by
      rcases (hterm v).1 h2 with h' | h' <;> contradiction
    rw [h, Set.ncard_empty, h3]
  · rw [ncard_neighborSet_extendGraph_inr, ncard_neighborSet]
    obtain rfl | rfl | rfl | rfl : a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 := by revert a; decide
    · have h : {v | baseSpoke s t v 0} = {s} := by ext v; simp [baseSpoke]
      rw [h, Set.ncard_singleton]
      decide
    · have h : {v | baseSpoke s t v 1} = {t} := by ext v; simp [baseSpoke]
      rw [h, Set.ncard_singleton]
      decide
    · have h : {v | baseSpoke s t v 2} = ∅ := by ext v; simp [baseSpoke]
      rw [h, Set.ncard_empty]
      decide
    · have h : {v | baseSpoke s t v 3} = ∅ := by ext v; simp [baseSpoke]
      rw [h, Set.ncard_empty]
      decide

/-- `baseCompletion G s t` is connected when `G` is. -/
lemma baseCompletion_connected (hG : G.Connected) : (baseCompletion G s t).Connected := by
  refine extendGraph_connected hG fun a => ?_
  have h0 : (baseCompletion G s t).Reachable (.inl s) (.inr 0) :=
    Adj.reachable (by simp [baseSpoke])
  have h1 : (baseCompletion G s t).Reachable (.inl t) (.inr 1) :=
    Adj.reachable (by simp [baseSpoke])
  obtain rfl | rfl | rfl | rfl : a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 := by revert a; decide
  · exact ⟨s, h0⟩
  · exact ⟨t, h1⟩
  · exact ⟨s, h0.trans (Adj.reachable (show baseGadget.Adj 0 2 by decide))⟩
  · exact ⟨s, h0.trans (Adj.reachable (show baseGadget.Adj 0 3 by decide))⟩

/-- `baseCompletion G s t` is bridgeless when `G` is connected and bridgeless: gadget edges lie on
triangles, and each spoke lies on a cycle through a `G`-path from `s` to `t`. -/
lemma baseCompletion_isBridgeless [DecidableRel G.Adj]
    [DecidableRel (baseCompletion G s t).Adj] (hconn : G.Connected) (hbr : IsBridgeless G)
    (hst : s ≠ t) : IsBridgeless (baseCompletion G s t) := by
  refine isBridgeless_extendGraph hbr (fun a b hab => ?_) ?_
  · obtain ⟨c, hac, hcb⟩ := baseGadget_exists_triangle a b hab
    exact reachable_deleteEdges_of_adj_of_adj (K := baseCompletion G s t) (z := .inr c) hac hcb
  rintro v a (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
  · refine (extendGraph_reachable_deleteEdges_inl (by simp) (hconn.preconnected v t)).trans ?_
    refine (Adj.reachable (v := .inr 1) ?_).trans
      ((Adj.reachable (v := .inr 2) ?_).trans (Adj.reachable ?_))
    · simp [baseSpoke, Ne.symm hst]
    · simp only [deleteEdges_adj, extendGraph_adj_inr_inr, Set.mem_singleton_iff]
      exact ⟨by decide, by simp⟩
    · simp only [deleteEdges_adj, extendGraph_adj_inr_inr, Set.mem_singleton_iff]
      exact ⟨by decide, by simp⟩
  · refine (extendGraph_reachable_deleteEdges_inl (by simp) (hconn.preconnected v s)).trans ?_
    refine (Adj.reachable (v := .inr 0) ?_).trans
      ((Adj.reachable (v := .inr 2) ?_).trans (Adj.reachable ?_))
    · simp [baseSpoke, hst]
    · simp only [deleteEdges_adj, extendGraph_adj_inr_inr, Set.mem_singleton_iff]
      exact ⟨by decide, by simp⟩
    · simp only [deleteEdges_adj, extendGraph_adj_inr_inr, Set.mem_singleton_iff]
      exact ⟨by decide, by simp⟩

/-- In a perfect matching of `baseCompletion G s t` that contains an old edge at `s`, the spoke at
`t` is unused. -/
lemma not_adj_inl_inr_one_of_isPerfectMatching {P : (baseCompletion G s t).Subgraph}
    (hP : P.IsPerfectMatching) {x : V} (hsx : P.Adj (.inl s) (.inl x)) :
    ¬P.Adj (.inl t) (.inr 1) := by
  intro h1
  have hM := hP.1
  have key : ∀ a : Fin 4, a ≠ 1 → ∃ b, b ≠ 1 ∧ P.Adj (.inr a) (.inr b) := by
    intro a ha
    obtain ⟨z, hz, -⟩ := Subgraph.isPerfectMatching_iff.mp hP (.inr a)
    rcases z with v | b
    · exfalso
      rcases (P.adj_sub hz : baseSpoke s t v a) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact absurd (hM.eq_of_adj_left hz.symm hsx) (by simp)
      · exact ha rfl
    · refine ⟨b, ?_, hz⟩
      rintro rfl
      exact absurd (hM.eq_of_adj_right hz h1) (by simp)
  obtain ⟨b₀, hb₀, h₀⟩ := key 0 (by decide)
  obtain ⟨b₂, hb₂, h₂⟩ := key 2 (by decide)
  obtain ⟨b₃, hb₃, h₃⟩ := key 3 (by decide)
  have e₀ : ∀ b : Fin 4, baseGadget.Adj 0 b → b = 2 ∨ b = 3 := by decide
  have e₂ : ∀ b : Fin 4, b ≠ 1 → baseGadget.Adj 2 b → b = 0 ∨ b = 3 := by decide
  have e₃ : ∀ b : Fin 4, b ≠ 1 → baseGadget.Adj 3 b → b = 0 ∨ b = 2 := by decide
  rcases e₀ b₀ (P.adj_sub h₀) with rfl | rfl <;>
    rcases e₂ b₂ hb₂ (P.adj_sub h₂) with rfl | rfl <;>
    rcases e₃ b₃ hb₃ (P.adj_sub h₃) with rfl | rfl
  · simpa using hM.eq_of_adj_left h₀ h₃.symm
  · simpa using hM.eq_of_adj_left h₂ h₃.symm
  · simpa using hM.eq_of_adj_left h₀ h₃.symm
  · simpa using hM.eq_of_adj_left h₂ h₀.symm
  · simpa using hM.eq_of_adj_left h₀ h₂.symm
  · simpa using hM.eq_of_adj_left h₃ h₀.symm
  · simpa using hM.eq_of_adj_left h₃ h₂.symm
  · simpa using hM.eq_of_adj_left h₃ h₀.symm

end BaseCompletion

variable {V : Type u} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- A connected bridgeless `{2,3}`-graph whose terminals are exactly `s ≠ t` has a perfect
matching. -/
theorem exists_isPerfectMatching_of_terminals_eq_pair (hconn : G.Connected)
    (hbr : IsBridgeless G) (hG : Is23Graph G) {s t : V} (hst : s ≠ t)
    (hterm : ∀ v, G.degree v = 2 ↔ v = s ∨ v = t) :
    ∃ M : G.Subgraph, M.IsPerfectMatching := by
  classical
  obtain ⟨x, hx⟩ := (G.degree_pos_iff_exists_adj s).mp (by rw [(hterm s).2 (Or.inl rfl)]; norm_num)
  obtain ⟨P, hP, hPsx⟩ := exists_perfect_matching_containing_edge (baseCompletion G s t)
    (baseCompletion_connected hconn) (baseCompletion_isBridgeless hconn hbr hst)
    (baseCompletion_ncard_neighborSet hG hst hterm)
    (show (baseCompletion G s t).Adj (.inl s) (.inl x) from hx)
  refine ⟨restrictSubgraph (extendGraphInl G baseGadget (baseSpoke s t)) P,
    isMatching_restrictSubgraph _ hP.1, fun v => ?_⟩
  obtain ⟨z, hz, -⟩ := Subgraph.isPerfectMatching_iff.mp hP (.inl v)
  rcases z with w | a
  · exact ⟨w, hz⟩
  · exfalso
    rcases (P.adj_sub hz : baseSpoke s t v a) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd (hP.1.eq_of_adj_left hz hPsx) (by simp)
    · exact not_adj_inl_inr_one_of_isPerfectMatching hP hPsx hz

/-- **Base case `k = 2`.** A connected bridgeless `{2,3}`-graph with exactly two terminals has a
perfect matching. -/
theorem exists_isPerfectMatching_of_ncard_terminals_eq_two (hconn : G.Connected)
    (hbr : IsBridgeless G) (hG : Is23Graph G) (hk : (terminals G).ncard = 2) :
    ∃ M : G.Subgraph, M.IsPerfectMatching := by
  obtain ⟨s, t, hst, hS⟩ := Set.ncard_eq_two.mp hk
  exact exists_isPerfectMatching_of_terminals_eq_pair hconn hbr hG hst fun v => by
    simpa using Set.ext_iff.mp hS v

end ThreeDecomposition

/-!
## The comparison matching for `k ≥ 3` terminals (Section 3.3, Lemma 3.5)

Section 3.3 of the paper completes `G` to a bridgeless cubic graph by identifying the `k ≥ 3`
terminals with the leaves of a ternary tree.  Here we use a `k`-cycle on new vertices `Fin k`,
the new vertex `j` being joined to the `j`-th terminal (`ringCompletion`).  Restricting a
perfect matching through a prescribed edge of `G` at a terminal yields a matching `N` of `G`
that exposes only terminals and covers at least one terminal (`exists_comparison_matching`).
-/

namespace ThreeDecomposition

open SimpleGraph

universe u

/-- The cubic completion of a graph whose terminals are enumerated by `f : Fin k → V`: a `k`-cycle
on new vertices `Fin k`, with the new vertex `j` joined to the terminal `f j`. -/
abbrev ringCompletion {V : Type*} (G : SimpleGraph V) {k : ℕ} (f : Fin k → V) :
    SimpleGraph (V ⊕ Fin k) :=
  extendGraph G (cycleGraph k) (fun v j => v = f j)

section RingCompletion

variable {V : Type*} {G : SimpleGraph V} {n : ℕ} {f : Fin (n + 3) → V}

/-- `ringCompletion G f` is cubic when `f` enumerates the terminals of the `{2,3}`-graph `G`
without repetition. -/
lemma ringCompletion_ncard_neighborSet [Fintype V] [DecidableRel G.Adj] (hG : Is23Graph G)
    (hf : f.Injective) (hterm : ∀ v, G.degree v = 2 ↔ ∃ j, f j = v) (x : V ⊕ Fin (n + 3)) :
    ((ringCompletion G f).neighborSet x).ncard = 3 := by
  rcases x with v | a
  · rw [ncard_neighborSet_extendGraph_inl, ncard_neighborSet]
    by_cases hv : ∃ j, f j = v
    · obtain ⟨j, rfl⟩ := hv
      have h : {a | f j = f a} = {j} := by ext a; simp [hf.eq_iff, eq_comm]
      rw [h, Set.ncard_singleton, (hterm (f j)).2 ⟨j, rfl⟩]
    · have h : {a | v = f a} = ∅ := Set.eq_empty_of_forall_notMem fun a ha => hv ⟨a, ha.symm⟩
      have h3 : G.degree v = 3 := (hG v).resolve_left fun h2 => hv ((hterm v).1 h2)
      rw [h, Set.ncard_empty, h3]
  · rw [ncard_neighborSet_extendGraph_inr, ncard_neighborSet, cycleGraph_degree_three_le,
      Set.ofPred_eq_eq_singleton, Set.ncard_singleton]

/-- `ringCompletion G f` is connected when `G` is. -/
lemma ringCompletion_connected (hG : G.Connected) : (ringCompletion G f).Connected :=
  extendGraph_connected hG fun a => ⟨f a, Adj.reachable (by simp)⟩

/-- `ringCompletion G f` is bridgeless when `G` is connected and bridgeless: the new edge `a b`
lies on the cycle `a - f a ~ f b - b`, and the spoke at `a` on the cycle
`f a ~ f (a + 1) - (a + 1) - a`, where `~` is a path of `G`. -/
lemma ringCompletion_isBridgeless [DecidableRel G.Adj] [DecidableRel (ringCompletion G f).Adj]
    (hconn : G.Connected) (hbr : IsBridgeless G) : IsBridgeless (ringCompletion G f) := by
  refine isBridgeless_extendGraph hbr (fun a b hab => ?_) ?_
  · refine (Adj.reachable (v := .inl (f a)) (by simp)).trans ?_
    refine (extendGraph_reachable_deleteEdges_inl (by simp)
      (hconn.preconnected (f a) (f b))).trans ?_
    exact Adj.reachable (by simp)
  · rintro v a rfl
    refine (extendGraph_reachable_deleteEdges_inl (by simp)
      (hconn.preconnected (f a) (f (a + 1)))).trans ?_
    refine (Adj.reachable (v := .inr (a + 1)) (by simp)).trans (Adj.reachable ?_)
    simp [cycleGraph_adj']

end RingCompletion

variable {V : Type u} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The comparison matching, for an explicit enumeration `f` of the terminals. -/
theorem exists_comparison_matching_of_enum {n : ℕ} {f : Fin (n + 3) → V} (hconn : G.Connected)
    (hbr : IsBridgeless G) (hG : Is23Graph G) (hf : f.Injective)
    (hterm : ∀ v, G.degree v = 2 ↔ ∃ j, f j = v) :
    ∃ N : G.Subgraph, N.IsMatching ∧ (∀ v, v ∉ N.verts → v ∈ terminals G) ∧
      ∃ s ∈ terminals G, s ∈ N.verts := by
  classical
  obtain ⟨x, hx⟩ :=
    (G.degree_pos_iff_exists_adj (f 0)).mp (by rw [(hterm _).2 ⟨0, rfl⟩]; norm_num)
  obtain ⟨P, hP, hPx⟩ := exists_perfect_matching_containing_edge (ringCompletion G f)
    (ringCompletion_connected hconn) (ringCompletion_isBridgeless hconn hbr)
    (ringCompletion_ncard_neighborSet hG hf hterm)
    (show (ringCompletion G f).Adj (.inl (f 0)) (.inl x) from hx)
  refine ⟨restrictSubgraph (extendGraphInl _ _ _) P, isMatching_restrictSubgraph _ hP.1,
    fun v hv => ?_, f 0, (hterm _).2 ⟨0, rfl⟩, x, hPx⟩
  by_contra hvt
  exact hv (mem_restrictSubgraph_extendGraphInl_verts hP fun a ha =>
    hvt ((hterm v).2 ⟨a, ha.symm⟩))

/-- **Comparison matching (Section 3.3).** A connected bridgeless `{2,3}`-graph with at least three
terminals has a matching `N` such that every vertex exposed by `N` is a terminal and some terminal
is covered by `N`. -/
theorem exists_comparison_matching (hconn : G.Connected) (hbr : IsBridgeless G)
    (hG : Is23Graph G) (hk : 3 ≤ (terminals G).ncard) :
    ∃ N : G.Subgraph, N.IsMatching ∧ (∀ v, v ∉ N.verts → v ∈ terminals G) ∧
      ∃ s ∈ terminals G, s ∈ N.verts := by
  obtain ⟨n, hn⟩ : ∃ n, (terminals G).ncard = n + 3 := ⟨_, (Nat.sub_add_cancel hk).symm⟩
  let e : terminals G ≃ Fin (n + 3) :=
    (Finite.equivFin _).trans (finCongr (by rw [Nat.card_coe_set_eq, hn]))
  refine exists_comparison_matching_of_enum (f := fun j => (e.symm j : V)) hconn hbr hG
    (fun i j hij => e.symm.injective (Subtype.ext hij)) fun v => ⟨fun hv => ?_, ?_⟩
  · exact ⟨e ⟨v, hv⟩, by simp⟩
  · rintro ⟨j, rfl⟩
    exact (e.symm j).2

end ThreeDecomposition
