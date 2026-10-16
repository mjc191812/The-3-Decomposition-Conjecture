import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Data.Set.Card

/-!
# Loopless multigraphs

A loopless multigraph on a vertex type `V` with edge type `E` assigns to every edge an
unordered pair of distinct ends.  Parallel edges are allowed; a parallel pair is a cycle of
length two.  Subgraphs are given by their edge sets `F : Set E` and always keep every vertex
(deleting edges never deletes vertices).

These are the definitions used in the statements of 2DC and 3DC.
-/

namespace ThreeDecomposition

/-- A loopless multigraph: every edge has two distinct ends. -/
structure LooplessMultigraph (V : Type*) (E : Type*) where
  ends : E → Sym2 V
  loopless : ∀ e, ¬(ends e).IsDiag

namespace LooplessMultigraph

variable {V E : Type*} (G : LooplessMultigraph V E)

/-- The simple graph on `V` in which `u` and `v` are adjacent iff some edge of `F` has ends
`u` and `v`.  Connectivity of the spanning subgraph with edge set `F` is connectivity of this
graph. -/
def adjGraph (F : Set E) : SimpleGraph V where
  Adj u v := ∃ e ∈ F, G.ends e = s(u, v)
  symm := ⟨fun _ _ ⟨e, he, h⟩ => ⟨e, he, h.trans Sym2.eq_swap⟩⟩
  loopless := ⟨fun _ ⟨e, _, h⟩ => G.loopless e (h ▸ Sym2.mk_isDiag_iff.mpr rfl)⟩

/-- The multigraph is connected. -/
def Connected : Prop :=
  (G.adjGraph Set.univ).Connected

/-- The edges of `F` incident with `v`. -/
def incidentIn (F : Set E) (v : V) : Set E :=
  {e | e ∈ F ∧ v ∈ G.ends e}

/-- The degree of `v`: the number of edges incident with `v` (parallel edges counted
separately). -/
noncomputable def degree (v : V) : ℕ :=
  (G.incidentIn Set.univ v).ncard

/-- `F` is a matching: no two edges of `F` share an end. -/
def IsMatching (F : Set E) : Prop :=
  ∀ v, (G.incidentIn F v).Subsingleton

/-- `F` is the edge set of a `2`-regular subgraph (not necessarily spanning, possibly empty):
every vertex meets either no edge or exactly two edges of `F`. -/
def IsTwoRegular (F : Set E) : Prop :=
  ∀ v, (G.incidentIn F v).ncard = 0 ∨ (G.incidentIn F v).ncard = 2

/-- `F` is the edge set of a spanning tree: no two edges of `F` are parallel, and the graph
they form on all of `V` is a tree. -/
def IsSpanningTree (F : Set E) : Prop :=
  Set.InjOn G.ends F ∧ (G.adjGraph F).IsTree

/-- `F` is the edge set of a cycle: a nonempty connected `2`-regular subgraph. -/
def IsCycle (F : Set E) : Prop :=
  F.Nonempty ∧ G.IsTwoRegular F ∧
    ∀ u v, (G.incidentIn F u).Nonempty → (G.incidentIn F v).Nonempty →
      (G.adjGraph F).Reachable u v

/-- Every cycle is separating: deleting the edges of any cycle disconnects the multigraph. -/
def IsFragile : Prop :=
  ∀ F, G.IsCycle F → ¬(G.adjGraph Fᶜ).Connected

end LooplessMultigraph

end ThreeDecomposition
