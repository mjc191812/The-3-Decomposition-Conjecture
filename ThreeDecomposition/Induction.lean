import ThreeDecomposition.Reduction
import ThreeDecomposition.Statement
import ThreeDecomposition.Extension
import ThreeDecomposition.MatchingComplement.TerminalCriterion

/-!
# Induction assembly for Theorem 1.3

This module states the three lifting interfaces (`AdjacentTerminalLift`, `TriangleLift`,
`RestorationLift`) and derives Theorem 1.3 (`terminalSelectionTheorem_of_lifts`) from them by
strong induction on the number `k` of terminals and, for fixed `k`, on the number of vertices.

## Lifting interfaces
-/

namespace ThreeDecomposition

open SimpleGraph

universe u

/-- Reduction 1: `u` and `v` are adjacent terminals, and `v` (with neighbours `u` and `y`) is
suppressed, which is the paper's contraction of the edge `uv`. -/
def AdjacentTerminalLift : Prop :=
  ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (u v y : V),
    Is23Graph G → IsSuppressible G v u y → G.degree u = 2 →
    TerminalSelectionStatement (suppress G v u y) (terminals (suppress G v u y)) →
    TerminalSelectionStatement G (terminals G)

/-- Reduction 2: the triangle `s a b` at the terminal `s` is replaced by `s` joined to the
outer neighbours `x` of `a` and `y` of `b`. -/
def TriangleLift : Prop :=
  ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (s a b x y : V),
    Is23Graph G → IsReplaceableTriangle G s a b x y →
    TerminalSelectionStatement (replaceTriangle G s a b x y)
      (terminals (replaceTriangle G s a b x y)) →
    TerminalSelectionStatement G (terminals G)

/-- The inductive step: the terminal `s` with cubic, non-adjacent neighbours `a`, `b` is
suppressed; `N` is a comparison matching exposing only terminals and covering `s`. -/
def RestorationLift : Prop :=
  ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (s a b : V) (N : G.Subgraph),
    Is23Graph G → IsSuppressible G s a b → G.degree a = 3 → G.degree b = 3 →
    N.IsMatching → (∀ x, x ∉ N.verts → x ∈ terminals G) → s ∈ N.verts →
    TerminalSelectionStatement (suppress G s a b) (terminals (suppress G s a b)) →
    TerminalSelectionStatement G (terminals G)

end ThreeDecomposition

/-!
## Strong induction for Theorem 1.3

* `k = 2`: a perfect matching (the base case) solves the problem.
* `k ≥ 3` and two terminals `u, v` are adjacent: if their other neighbours coincide, `G` is a
  triangle, solved directly by one edge (`terminalSelectionStatement_of_triangle`); otherwise
  `v` is suppressed, which lowers `k` by one (`AdjacentTerminalLift`).
* `k ≥ 3`, the terminals are independent, and the neighbours of some terminal are adjacent:
  the triangle is replaced, which keeps `k` and removes two vertices (`TriangleLift`).
* Otherwise, the comparison matching covers some terminal `s`, whose neighbours have degree
  three and are non-adjacent; `s` is suppressed, which lowers `k` by one (`RestorationLift`).
-/

namespace ThreeDecomposition

open SimpleGraph Finset

universe u

section Triangle

variable {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- A `{2,3}`-graph that is the triangle `u v x` and has at least three terminals: the single
edge `uv` solves the terminal selection problem, leaving the path `u - x - v`. -/
theorem terminalSelectionStatement_of_triangle (h23 : Is23Graph G) {u v x : V}
    (huv : G.Adj u v) (hux : G.Adj u x) (hvx : G.Adj v x)
    (huniv : (univ : Finset V) = {u, v, x}) (hk : 3 ≤ (terminals G).ncard) :
    TerminalSelectionStatement G (terminals G) := by
  set M := G.subgraphOfAdj huv
  have hM : M.IsMatching := Subgraph.IsMatching.subgraphOfAdj huv
  have hcard : Fintype.card V = 3 := by
    rw [← card_univ, huniv, card_insert_of_notMem (by simp [huv.ne, hux.ne]), card_pair hvx.ne]
  have hsize : (M.edgeSet.ncard : ℤ) = cyclomaticNumber G := by
    have h := twice_targetMatchingSize G h23
    have hT : #(terminalFinset G) ≤ Fintype.card V := card_le_univ _
    rw [ncard_terminals] at hk
    rw [edgeSet_subgraphOfAdj, Set.ncard_singleton]
    unfold targetMatchingSize at h
    push_cast
    omega
  have hdel : ∀ p q, G.Adj p q → s(p, q) ≠ s(u, v) → (deletedMatching G M).Adj p q := by
    intro p q hpq hne
    rw [deletedMatching, deleteEdges_adj, edgeSet_subgraphOfAdj]
    exact ⟨hpq, hne⟩
  have hx : (deletedMatching G M).Reachable u x :=
    (hdel u x hux (by simp [hvx.ne', huv.ne])).reachable
  have hv : (deletedMatching G M).Reachable u v :=
    hx.trans (hdel x v hvx.symm (by simp [hux.ne', hvx.ne'])).reachable
  refine (terminal_criterion G h23 hM hsize ((deletedMatching G M).connectedComponentMk u)
    fun w _ ↦ ?_).1
  have hw : w ∈ ({u, v, x} : Finset V) := huniv ▸ mem_univ w
  simp only [mem_insert, mem_singleton] at hw
  rw [ConnectedComponent.mem_supp_iff, ConnectedComponent.eq]
  rcases hw with rfl | rfl | rfl
  · rfl
  · exact hv.symm
  · exact hx.symm

end Triangle

/-- **Theorem 1.3 from the lifting steps.**  Strong induction on the number of terminals and
then on the number of vertices: the case `k = 2` is the perfect matching of the base case; for
`k ≥ 3`, two adjacent terminals are contracted (or form the whole graph, a triangle), a triangle
at a terminal is replaced, and otherwise a terminal covered by the comparison matching is
suppressed. -/
theorem terminalSelectionTheorem_of_lifts (h1 : AdjacentTerminalLift.{u})
    (h2 : TriangleLift.{u}) (h3 : RestorationLift.{u}) : TerminalSelectionTheorem.{u} := by
  suffices H : ∀ k n : ℕ, ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : SimpleGraph V)
      [DecidableRel G.Adj], (terminals G).ncard = k → Fintype.card V = n → G.Connected →
      IsBridgeless G → Is23Graph G → 2 ≤ k → TerminalSelectionStatement G (terminals G) from
    fun V _ _ G _ hconn hbr h23 hk ↦ H _ _ V G rfl rfl hconn hbr h23 hk
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ihk =>
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ihn =>
  intro V _ _ G _ hk hn hconn hbr h23 hk2
  rcases hk2.eq_or_lt with rfl | hk3
  · obtain ⟨M, hM⟩ := exists_isPerfectMatching_of_ncard_terminals_eq_two hconn hbr h23 hk
    exact terminalSelectionStatement_of_isPerfectMatching G h23 hk hM
  by_cases hA : ∃ u v, G.Adj u v ∧ G.degree u = 2 ∧ G.degree v = 2
  · obtain ⟨u, v, huv, hu, hv⟩ := hA
    obtain ⟨x, hux, hxv⟩ := exists_adj_notMem_of_card_lt (G := G) (v := u) {v}
      (by rw [hu, card_singleton]; norm_num)
    obtain ⟨y, hvy, hyu⟩ := exists_adj_notMem_of_card_lt (G := G) (v := v) {u}
      (by rw [hv, card_singleton]; norm_num)
    rw [mem_singleton] at hxv hyu
    by_cases hxy : x = y
    · subst hxy
      exact terminalSelectionStatement_of_triangle h23 huv hux hvy
        (eq_triangle_of_adj_terminals hconn hbr h23 huv hux hvy hu hv).2 (by omega)
    · have hs := isSuppressible_of_adj_terminals huv hu hv hux hxv hvy hyu hxy
      have hk' := hs.ncard_terminals_suppress
      exact h1 V G u v y h23 hs hu (ihk _ (by omega) _ _ (suppress G v u y) rfl rfl
        (hs.connected_suppress hconn) (hs.isBridgeless_suppress hbr) (hs.is23Graph_suppress h23)
        (by omega))
  push Not at hA
  have hcubic : ∀ s w, G.degree s = 2 → G.Adj s w → G.degree w = 3 := fun s w hs hsw ↦
    (h23 w).resolve_left (hA s w hsw hs)
  by_cases hB : ∃ s a b, G.degree s = 2 ∧ G.Adj s a ∧ G.Adj s b ∧ G.Adj a b
  · obtain ⟨s, a, b, hs, hsa, hsb, hab⟩ := hB
    obtain ⟨x, hax, hx⟩ := exists_adj_notMem_of_card_lt (G := G) (v := a) {s, b}
      (by rw [hcubic s a hs hsa]; exact card_le_two.trans_lt (by norm_num))
    obtain ⟨y, hby, hy⟩ := exists_adj_notMem_of_card_lt (G := G) (v := b) {s, a}
      (by rw [hcubic s b hs hsb]; exact card_le_two.trans_lt (by norm_num))
    simp only [mem_insert, mem_singleton, not_or] at hx hy
    have hxy := ne_of_triangle hconn hbr h23 (by rw [← ncard_terminals]; omega) hs hsa hsb hab
      hax hby hx.1
    have hr := isReplaceableTriangle_of h23 hs hsa hsb hab hax hx.1 hx.2 hby hy.1 hy.2 hxy
    have hcard := hr.card_vertices
    exact h2 V G s a b x y h23 hr (ihn _ (by omega) _ (replaceTriangle G s a b x y)
      (by rw [hr.ncard_terminals_replaceTriangle, hk]) rfl (hr.connected_replaceTriangle hconn)
      (hr.isBridgeless_replaceTriangle hbr) (hr.is23Graph_replaceTriangle h23) (by omega))
  push Not at hB
  obtain ⟨N, hN, hNexp, s, hs, hsN⟩ := exists_comparison_matching hconn hbr h23 (by omega)
  obtain ⟨a, b, hab, hsa, hsb, -⟩ := exists_neighbors_of_degree_eq_two hs
  have hsupp := IsSuppressible.of_degree_eq_two hs hsa hsb hab (hB s a b hs hsa hsb)
  have hk' := hsupp.ncard_terminals_suppress
  exact h3 V G s a b N h23 hsupp (hcubic s a hs hsa) (hcubic s b hs hsb) hN hNexp hsN
    (ihk _ (by omega) _ _ (suppress G s a b) rfl rfl (hsupp.connected_suppress hconn)
      (hsupp.isBridgeless_suppress hbr) (hsupp.is23Graph_suppress h23) (by omega))

end ThreeDecomposition
