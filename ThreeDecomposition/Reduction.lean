import ThreeDecomposition.Basic.Lemmas
import ThreeDecomposition.MatchingComplement.Normalization

/-!
# Graph reductions (Section 3.2, Lemma 3.4)

This module defines the two local graph reductions used in Section 3.2 (Lemma 3.4) and Section 3.4
of the paper—vertex suppression (`suppress`) and triangle replacement at a terminal
(`replaceTriangle`)—and proves that both preserve connectivity, bridgelessness, and the
`{2,3}`-graph property, together with the configuration analysis excluding degenerate common
neighbours (`eq_triangle_of_adj_terminals`, `ne_of_adj_terminals`, `ne_of_triangle`).

## Graphs on a vertex subtype
-/

namespace ThreeDecomposition

open SimpleGraph Finset

variable {V : Type*} [Fintype V] {p : V → Prop} [DecidablePred p]

/-- The degree of a vertex of a graph on `{v // p v}` whose adjacency is pulled back from `H`
is the number of `H`-neighbours satisfying `p`. -/
theorem degree_eq_card_filter_of_adj_iff (G' : SimpleGraph {v // p v}) [DecidableRel G'.Adj]
    (H : SimpleGraph V) [DecidableRel H.Adj] (hadj : ∀ u v, G'.Adj u v ↔ H.Adj u v)
    (v : {v // p v}) :
    G'.degree v = #((H.neighborFinset v).filter p) := by
  rw [← card_neighborFinset_eq_degree, ← Finset.card_subtype]
  congr 1
  ext w
  simp [hadj]

section DegreeEq

variable {G : SimpleGraph V} [DecidableRel G.Adj] {G' : SimpleGraph {v // p v}}
  [DecidableRel G'.Adj]

lemma mem_terminals_iff_of_degree_eq (hdeg : ∀ v, G'.degree v = G.degree v)
    (v : {v // p v}) : v ∈ terminals G' ↔ (v : V) ∈ terminals G := by
  simp [hdeg]

lemma is23Graph_of_degree_eq (hdeg : ∀ v, G'.degree v = G.degree v) (hG : Is23Graph G) :
    Is23Graph G' :=
  fun v ↦ hdeg v ▸ hG v

lemma card_terminalFinset_of_degree_eq (hdeg : ∀ v, G'.degree v = G.degree v) :
    #(terminalFinset G') = #((terminalFinset G).filter p) := by
  rw [← Finset.card_subtype]
  congr 1
  ext v
  simp [terminalFinset, hdeg]

lemma two_mul_card_edgeFinset_of_degree_eq (hdeg : ∀ v, G'.degree v = G.degree v) :
    2 * #G'.edgeFinset = ∑ v ∈ univ.filter p, G.degree v := by
  classical
  rw [← sum_degrees_eq_twice_card_edges,
    Finset.sum_subtype (p := p) (univ.filter p) (by simp) fun v ↦ G.degree v]
  exact Finset.sum_congr rfl fun v _ ↦ hdeg v

end DegreeEq

lemma ncard_terminals (G : SimpleGraph V) [DecidableRel G.Adj] :
    (terminals G).ncard = #(terminalFinset G) := by
  classical
  rw [Set.ncard_eq_toFinset_card', terminals_eq_terminalFinset]

section Card

variable [DecidableEq V]

lemma card_subtype_ne_add_one (s : V) : Fintype.card {v // v ≠ s} + 1 = Fintype.card V := by
  rw [Fintype.card_subtype, filter_ne', card_erase_add_one (mem_univ s), card_univ]

lemma card_subtype_ne (s : V) : Fintype.card {v // v ≠ s} = Fintype.card V - 1 := by
  have := card_subtype_ne_add_one s
  omega

lemma filter_ne_and_ne_eq (a b : V) :
    univ.filter (fun v : V ↦ v ≠ a ∧ v ≠ b) = (univ.erase a).erase b := by
  ext v
  simp [and_comm]

lemma card_subtype_ne_and_ne_add_two {a b : V} (hab : a ≠ b) :
    Fintype.card {v // v ≠ a ∧ v ≠ b} + 2 = Fintype.card V := by
  rw [Fintype.card_subtype, filter_ne_and_ne_eq, ← card_univ,
    ← card_erase_add_one (mem_univ a), ← card_erase_add_one (mem_erase.2 ⟨hab.symm, mem_univ b⟩)]

omit [Fintype V] in
lemma card_insert_erase {N : Finset V} {c d : V} (hc : c ∉ N) (hd : d ∈ N) :
    #(insert c (N.erase d)) = #N := by
  rw [card_insert_of_notMem fun hc' ↦ hc (mem_of_mem_erase hc'), card_erase_add_one hd]

end Card

end ThreeDecomposition

/-!
## Transporting reachability along edge-collapsing maps

A map `f : V → W` is *edge-collapsing* from `G` to `G'` if it sends every edge of `G` either to
an edge of `G'` or to a single vertex (`IsCollapseMap`).  Such maps preserve reachability and
certify non-bridges (`IsCollapseMap.not_isBridge`).
-/

namespace ThreeDecomposition

open SimpleGraph

variable {V W : Type*}

/-- `f` sends every edge of `G` either to an edge of `G'` or to a single vertex. -/
def IsCollapseMap (G : SimpleGraph V) (G' : SimpleGraph W) (f : V → W) : Prop :=
  ∀ ⦃u v : V⦄, G.Adj u v → f u = f v ∨ G'.Adj (f u) (f v)

namespace IsCollapseMap

variable {G H : SimpleGraph V} {G' H' : SimpleGraph W} {f : V → W}

lemma of_hom (φ : G →g G') : IsCollapseMap G G' φ :=
  fun _ _ h ↦ Or.inr (φ.map_adj h)

lemma mono (hf : IsCollapseMap G G' f) (hH : H ≤ G) (hH' : G' ≤ H') : IsCollapseMap H H' f :=
  fun _ _ h ↦ (hf (hH h)).imp_right fun h' ↦ hH' h'

/-- Criterion for an edge-collapsing map between graphs with deleted edge sets. -/
lemma deleteEdges {D : Set (Sym2 V)} {D' : Set (Sym2 W)}
    (h : ∀ ⦃u v : V⦄, G.Adj u v → s(u, v) ∉ D →
      f u = f v ∨ (G'.Adj (f u) (f v) ∧ s(f u, f v) ∉ D')) :
    IsCollapseMap (G.deleteEdges D) (G'.deleteEdges D') f := by
  intro u v huv
  rw [deleteEdges_adj] at huv ⊢
  exact h huv.1 huv.2

/-- Edge-collapsing maps preserve reachability. -/
theorem reachable (hf : IsCollapseMap G G' f) {u v : V} (h : G.Reachable u v) :
    G'.Reachable (f u) (f v) :=
  reachable_map_of_adj f (fun _ _ hab ↦ (hf hab).elim (fun heq ↦ heq ▸ .refl _) Adj.reachable) h

/-- Surjective edge-collapsing maps preserve preconnectivity. -/
theorem preconnected (hf : IsCollapseMap G G' f) (hsurj : Function.Surjective f)
    (hG : G.Preconnected) : G'.Preconnected := by
  intro x y
  obtain ⟨u, rfl⟩ := hsurj x
  obtain ⟨v, rfl⟩ := hsurj y
  exact hf.reachable (hG u v)

/-- Surjective edge-collapsing maps preserve connectivity. -/
theorem connected (hf : IsCollapseMap G G' f) (hsurj : Function.Surjective f)
    (hG : G.Connected) : G'.Connected :=
  haveI := hG.nonempty.map f
  ⟨hf.preconnected hsurj hG.preconnected⟩

/-- Non-bridge criterion: if `u` and `v` are reachable in `G` after deleting `D`, and `f` is
edge-collapsing from `G.deleteEdges D` to `G'.deleteEdges {s(x, y)}` with `f u = x` and
`f v = y`, then `s(x, y)` is not a bridge of `G'`. -/
theorem not_isBridge {D : Set (Sym2 V)} {u v : V} {x y : W}
    (hf : IsCollapseMap (G.deleteEdges D) (G'.deleteEdges {s(x, y)}) f)
    (hu : f u = x) (hv : f v = y) (huv : (G.deleteEdges D).Reachable u v) :
    ¬G'.IsBridge s(x, y) := by
  subst hu hv
  rw [isBridge_iff, not_not]
  exact hf.reachable huv

end IsCollapseMap

/-- If `S` is closed under `G`-adjacency, then every vertex reachable from a vertex of `S` lies
in `S`. -/
theorem mem_of_reachable_of_closed {G : SimpleGraph V} {S : Set V}
    (hS : ∀ ⦃u v : V⦄, G.Adj u v → u ∈ S → v ∈ S) {u v : V} (hu : u ∈ S)
    (h : G.Reachable u v) : v ∈ S := by
  rw [reachable_iff_reflTransGen] at h
  induction h with
  | refl => exact hu
  | tail _ hbc ih => exact hS hbc ih

/-- If `S` is closed under adjacency in `G` with the edge `s(u, v)` deleted, `u ∈ S` and
`v ∉ S`, then `s(u, v)` is a bridge of `G`. -/
theorem isBridge_of_closed {G : SimpleGraph V} {S : Set V} {u v : V}
    (hS : ∀ ⦃p q : V⦄, G.Adj p q → s(p, q) ≠ s(u, v) → p ∈ S → q ∈ S)
    (hu : u ∈ S) (hv : v ∉ S) : G.IsBridge s(u, v) := by
  rw [isBridge_iff]
  intro h
  refine hv (mem_of_reachable_of_closed (fun p q hpq hp ↦ ?_) hu h)
  rw [deleteEdges_adj, Set.mem_singleton_iff] at hpq
  exact hS hpq.1 hpq.2 hp

section Retract

variable {p : V → Prop} [DecidablePred p]

/-- The retraction of `V` onto `{v // p v}` that fixes the vertices satisfying `p` and sends
every other vertex to `t`. -/
def subtypeRetract (t : {v // p v}) (v : V) : {v // p v} :=
  if h : p v then ⟨v, h⟩ else t

lemma subtypeRetract_of_pos (t : {v // p v}) {v : V} (h : p v) :
    subtypeRetract t v = ⟨v, h⟩ := by
  simp [subtypeRetract, h]

lemma subtypeRetract_of_neg (t : {v // p v}) {v : V} (h : ¬p v) :
    subtypeRetract t v = t := by
  simp [subtypeRetract, h]

@[simp]
lemma subtypeRetract_coe (t : {v // p v}) (v : {v // p v}) :
    subtypeRetract t (v : V) = v :=
  subtypeRetract_of_pos t v.2

lemma subtypeRetract_surjective (t : {v // p v}) : Function.Surjective (subtypeRetract t) :=
  fun v ↦ ⟨v, subtypeRetract_coe t v⟩

end Retract

end ThreeDecomposition

/-!
## Suppressing a terminal

Let `s` be a vertex whose neighbours are two distinct non-adjacent vertices `a` and `b`.
Suppressing `s` deletes `s` and joins `a` and `b` by a new edge (`suppress`).  This operation
serves both Lemma 3.4(a) (contracting the edge between two adjacent terminals `u, v` is the
suppression of `v`) and the inductive step `k ≥ 3` in Section 3.4.
-/

namespace ThreeDecomposition

open SimpleGraph Finset

variable {V : Type*}

/-- Suppression of `s` with neighbours `a` and `b`: the graph on `{v // v ≠ s}` whose edges are
the edges of `G` among the remaining vertices together with the edge `ab`.  Since
`SimpleGraph.edge a a = ⊥`, this is a simple graph without any hypothesis on `a` and `b`. -/
def suppress (G : SimpleGraph V) (s a b : V) : SimpleGraph {v // v ≠ s} :=
  (G ⊔ edge a b).comap Subtype.val

/-- The hypotheses for suppressing `s`: its neighbours are exactly the two distinct non-adjacent
vertices `a` and `b`. -/
structure IsSuppressible (G : SimpleGraph V) (s a b : V) : Prop where
  adj_left : G.Adj s a
  adj_right : G.Adj s b
  ne : a ≠ b
  not_adj : ¬G.Adj a b
  eq_or_eq_of_adj : ∀ ⦃w : V⦄, G.Adj s w → w = a ∨ w = b

variable {G : SimpleGraph V} {s a b : V}

lemma suppress_adj {u v : {v // v ≠ s}} :
    (suppress G s a b).Adj u v ↔
      G.Adj u v ∨ ((u : V) = a ∧ (v : V) = b ∨ (u : V) = b ∧ (v : V) = a) ∧ (u : V) ≠ v := by
  simp only [suppress, comap_adj, sup_adj, edge_adj]

instance [DecidableEq V] [DecidableRel G.Adj] : DecidableRel (suppress G s a b).Adj :=
  inferInstanceAs (DecidableRel ((G ⊔ edge a b).comap Subtype.val).Adj)

namespace IsSuppressible

variable (h : IsSuppressible G s a b)
include h

lemma left_ne : a ≠ s := h.adj_left.ne'

lemma right_ne : b ≠ s := h.adj_right.ne'

lemma adj_iff {w : V} : G.Adj s w ↔ w = a ∨ w = b :=
  ⟨fun hw ↦ h.eq_or_eq_of_adj hw, by rintro (rfl | rfl); exacts [h.adj_left, h.adj_right]⟩

lemma suppress_adj_iff {u v : {v // v ≠ s}} :
    (suppress G s a b).Adj u v ↔
      G.Adj u v ∨ ((u : V) = a ∧ (v : V) = b) ∨ ((u : V) = b ∧ (v : V) = a) := by
  rw [suppress_adj]
  have := h.ne
  constructor
  · rintro (huv | ⟨huv, -⟩)
    · exact Or.inl huv
    · exact Or.inr huv
  · rintro (huv | huv)
    · exact Or.inl huv
    · refine Or.inr ⟨huv, ?_⟩
      rcases huv with ⟨hu, hv⟩ | ⟨hu, hv⟩ <;> rw [hu, hv] <;> tauto

lemma symm : IsSuppressible G s b a :=
  ⟨h.adj_right, h.adj_left, h.ne.symm, fun hba ↦ h.not_adj hba.symm,
    fun _ hw ↦ (h.eq_or_eq_of_adj hw).symm⟩

section Finite

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

lemma neighborFinset_self : G.neighborFinset s = {a, b} := by
  ext w
  simp [h.adj_iff]

omit [DecidableEq V] in
lemma degree_self : G.degree s = 2 := by
  classical
  rw [← card_neighborFinset_eq_degree, h.neighborFinset_self, card_pair h.ne]

omit [DecidableEq V] in
lemma mem_terminals : s ∈ terminals G := h.degree_self

/-- Suppression does not change the degree of any remaining vertex. -/
theorem degree_suppress (v : {v // v ≠ s}) : (suppress G s a b).degree v = G.degree v := by
  rw [degree_eq_card_filter_of_adj_iff (suppress G s a b) (G ⊔ edge a b) fun _ _ ↦ Iff.rfl,
    ← card_neighborFinset_eq_degree]
  obtain ⟨v, hv⟩ := v
  have hne := h.ne
  have hab := h.not_adj
  have hsa := h.adj_left
  have hsb := h.adj_right
  have hrange := h.eq_or_eq_of_adj
  dsimp only
  by_cases hva : v = a
  · subst hva
    have : ((G ⊔ edge v b).neighborFinset v).filter (· ≠ s) =
        insert b ((G.neighborFinset v).erase s) := by
      ext w
      simp only [mem_filter, mem_neighborFinset, sup_adj, edge_adj, mem_insert, mem_erase]
      grind [G.adj_symm]
    rw [this, card_insert_erase (by simpa using hab) (by simpa using hsa.symm)]
  by_cases hvb : v = b
  · subst hvb
    have : ((G ⊔ edge a v).neighborFinset v).filter (· ≠ s) =
        insert a ((G.neighborFinset v).erase s) := by
      ext w
      simp only [mem_filter, mem_neighborFinset, sup_adj, edge_adj, mem_insert, mem_erase]
      grind [G.adj_symm]
    rw [this, card_insert_erase (by simpa using fun h' ↦ hab h'.symm)
      (by simpa using hsb.symm)]
  · congr 1
    ext w
    simp only [mem_filter, mem_neighborFinset, sup_adj, edge_adj]
    grind [G.adj_symm]

theorem is23Graph_suppress (hG : Is23Graph G) : Is23Graph (suppress G s a b) :=
  is23Graph_of_degree_eq h.degree_suppress hG

lemma mem_terminals_suppress_iff (v : {v // v ≠ s}) :
    v ∈ terminals (suppress G s a b) ↔ (v : V) ∈ terminals G :=
  mem_terminals_iff_of_degree_eq h.degree_suppress v

/-- Suppression removes exactly one terminal, namely `s`. -/
theorem card_terminalFinset_suppress :
    #(terminalFinset (suppress G s a b)) + 1 = #(terminalFinset G) := by
  rw [card_terminalFinset_of_degree_eq h.degree_suppress, filter_ne',
    card_erase_add_one (by simpa [terminalFinset] using h.degree_self)]

theorem ncard_terminals_suppress :
    (terminals (suppress G s a b)).ncard + 1 = (terminals G).ncard := by
  rw [ncard_terminals, ncard_terminals, h.card_terminalFinset_suppress]

/-- Suppression removes exactly one edge. -/
theorem card_edgeFinset_suppress :
    #(suppress G s a b).edgeFinset + 1 = #G.edgeFinset := by
  have h1 := two_mul_card_edgeFinset_of_degree_eq h.degree_suppress
  have h2 := sum_erase_add univ (fun v ↦ G.degree v) (mem_univ s)
  have h3 := G.sum_degrees_eq_twice_card_edges
  rw [filter_ne'] at h1
  rw [h.degree_self] at h2
  omega

/-- Suppression preserves the cyclomatic number, i.e. the target matching size. -/
theorem cyclomaticNumber_suppress :
    cyclomaticNumber (suppress G s a b) = cyclomaticNumber G := by
  have h1 := h.card_edgeFinset_suppress
  have h2 := card_subtype_ne_add_one (V := V) s
  unfold cyclomaticNumber
  omega

end Finite

/-- The retraction `V → {v // v ≠ s}` sending `s` to `t ∈ {a, b}` is edge-collapsing from `G`
to the suppressed graph, also after deleting edge sets `D` and `D'`, provided old edges outside
`D` stay outside `D'`, and the new edge `ab` is outside `D'` whenever some edge `sr` with
`r ≠ t` is outside `D`. -/
lemma isCollapseMap_deleteEdges [DecidableEq V] (t : {v // v ≠ s})
    (ht : (t : V) = a ∨ (t : V) = b)
    {D : Set (Sym2 V)} {D' : Set (Sym2 {v // v ≠ s})}
    (hold : ∀ u v : {v // v ≠ s}, G.Adj u v → s((u : V), v) ∉ D → s(u, v) ∉ D')
    (hnew : ∀ u v : {v // v ≠ s}, (u : V) = a → (v : V) = b →
      (∃ r, G.Adj s r ∧ r ≠ t ∧ s(s, r) ∉ D) → s(u, v) ∉ D') :
    IsCollapseMap (G.deleteEdges D) ((suppress G s a b).deleteEdges D') (subtypeRetract t) := by
  have key : ∀ q, G.Adj s q → s(s, q) ∉ D →
      subtypeRetract t s = subtypeRetract t q ∨
        ((suppress G s a b).Adj (subtypeRetract t s) (subtypeRetract t q) ∧
          s(subtypeRetract t s, subtypeRetract t q) ∉ D') := by
    intro q hq hD
    have hqs : q ≠ s := hq.ne'
    rw [subtypeRetract_of_neg t (not_not.2 rfl), subtypeRetract_of_pos t hqs]
    by_cases hqt : q = t
    · exact Or.inl (Subtype.ext hqt.symm)
    right
    have hex : ∃ r, G.Adj s r ∧ r ≠ t ∧ s(s, r) ∉ D := ⟨q, hq, hqt, hD⟩
    rcases h.eq_or_eq_of_adj hq with rfl | rfl <;> rcases ht with ht | ht
    · exact absurd ht.symm hqt
    · refine ⟨h.suppress_adj_iff.2 (Or.inr (Or.inr ⟨ht, rfl⟩)), ?_⟩
      rw [Sym2.eq_swap]
      exact hnew _ _ rfl ht hex
    · exact ⟨h.suppress_adj_iff.2 (Or.inr (Or.inl ⟨ht, rfl⟩)), hnew _ _ ht rfl hex⟩
    · exact absurd ht.symm hqt
  refine IsCollapseMap.deleteEdges fun p q hpq hD ↦ ?_
  by_cases hp : p = s
  · subst hp
    exact key q hpq hD
  by_cases hq : q = s
  · subst hq
    rw [Sym2.eq_swap] at hD
    rcases key p hpq.symm hD with heq | ⟨hadj, hD'⟩
    · exact Or.inl heq.symm
    · exact Or.inr ⟨hadj.symm, by rwa [Sym2.eq_swap]⟩
  rw [subtypeRetract_of_pos t hp, subtypeRetract_of_pos t hq]
  exact Or.inr ⟨h.suppress_adj_iff.2 (Or.inl hpq), hold ⟨p, hp⟩ ⟨q, hq⟩ hpq hD⟩

/-- Suppression preserves connectivity. -/
theorem connected_suppress (hG : G.Connected) : (suppress G s a b).Connected := by
  classical
  have hf := h.isCollapseMap_deleteEdges (D := ∅) (D' := ∅) ⟨a, h.left_ne⟩ (Or.inl rfl)
    (fun _ _ _ _ ↦ Set.notMem_empty _) (fun _ _ _ _ _ ↦ Set.notMem_empty _)
  rw [deleteEdges_empty, deleteEdges_empty] at hf
  exact hf.connected (subtypeRetract_surjective _) hG

/-- The new edge `ab` of the suppressed graph is not a bridge, since `sa` is not a bridge
of `G`. -/
lemma not_isBridge_new (hsa : ¬G.IsBridge s(s, a)) {u v : {v // v ≠ s}} (hu : (u : V) = a)
    (hv : (v : V) = b) : ¬(suppress G s a b).IsBridge s(u, v) := by
  classical
  rw [isBridge_iff, not_not] at hsa
  rw [Sym2.eq_swap]
  refine IsCollapseMap.not_isBridge (h.isCollapseMap_deleteEdges v (Or.inr hv) ?_ ?_)
    (subtypeRetract_of_neg v (not_not.2 rfl)) (hu ▸ subtypeRetract_coe v u) hsa
  · intro p q hpq _ hmem
    rw [Set.mem_singleton_iff, Sym2.eq_iff, Subtype.ext_iff, Subtype.ext_iff, Subtype.ext_iff,
      Subtype.ext_iff, hu, hv] at hmem
    rcases hmem with ⟨hp, hq⟩ | ⟨hp, hq⟩
    · exact h.not_adj (hp ▸ hq ▸ hpq).symm
    · exact h.not_adj (hp ▸ hq ▸ hpq)
  · rintro _ _ _ _ ⟨r, hr, hrb, hD⟩
    rcases h.eq_or_eq_of_adj hr with rfl | rfl
    · exact absurd rfl hD
    · exact absurd hv.symm hrb

/-- An old edge of the suppressed graph is not a bridge, since it is not a bridge of `G`. -/
lemma not_isBridge_old {u v : {v // v ≠ s}} (huv : G.Adj u v)
    (hnb : ¬G.IsBridge s((u : V), v)) : ¬(suppress G s a b).IsBridge s(u, v) := by
  classical
  rw [isBridge_iff, not_not] at hnb
  refine IsCollapseMap.not_isBridge
    (h.isCollapseMap_deleteEdges ⟨a, h.left_ne⟩ (Or.inl rfl) ?_ ?_)
    (subtypeRetract_coe _ u) (subtypeRetract_coe _ v) hnb
  · intro p q _ hD hmem
    rw [Set.mem_singleton_iff] at hD hmem
    exact hD (by simpa using congrArg (Sym2.map Subtype.val) hmem)
  · intro p q hp hq _ hmem
    rw [Set.mem_singleton_iff, Sym2.eq_iff, Subtype.ext_iff, Subtype.ext_iff, Subtype.ext_iff,
      Subtype.ext_iff, hp, hq] at hmem
    rcases hmem with ⟨hu, hv⟩ | ⟨hu, hv⟩
    · exact h.not_adj (hu ▸ hv ▸ huv)
    · exact h.not_adj (hu ▸ hv ▸ huv).symm

/-- Suppression preserves bridgelessness. -/
theorem isBridgeless_suppress [DecidableEq V] [DecidableRel G.Adj]
    (hG : IsBridgeless G) : IsBridgeless (suppress G s a b) := by
  intro e he
  induction e using Sym2.ind with
  | _ u v =>
    rw [mem_edgeSet, h.suppress_adj_iff] at he
    rcases he with huv | ⟨hu, hv⟩ | ⟨hu, hv⟩
    · exact h.not_isBridge_old huv (hG huv)
    · exact h.not_isBridge_new (hG h.adj_left) hu hv
    · rw [Sym2.eq_swap]
      exact h.not_isBridge_new (hG h.adj_left) hv hu

/-- Suppression preserves the hypotheses of the terminal-selection theorem. -/
theorem isTerminalSelectionInstance_suppress [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (hG : IsTerminalSelectionInstance G) : IsTerminalSelectionInstance (suppress G s a b) :=
  ⟨h.connected_suppress hG.1, h.isBridgeless_suppress hG.2.1, h.is23Graph_suppress hG.2.2⟩

end IsSuppressible

end ThreeDecomposition

/-!
## Replacing a triangle at a terminal (Lemma 3.4(b))

Let `s` be a terminal with neighbours `a` and `b` such that `ab` is an edge, the neighbours of
`a` are `s, b, x`, those of `b` are `s, a, y`, and `x ≠ y` lie outside `{s, a, b}`.  Lemma 3.4(b)
replaces the triangle `sab` by a single terminal joined to `x` and `y` (`replaceTriangle`).
-/

namespace ThreeDecomposition

open SimpleGraph Finset

variable {V : Type*}

/-- Triangle replacement: the graph on `{v // v ≠ a ∧ v ≠ b}` whose edges are the edges of `G`
among the remaining vertices together with `sx` and `sy`.  Since `SimpleGraph.edge v v = ⊥`,
this is a simple graph without any hypothesis on the vertices. -/
def replaceTriangle (G : SimpleGraph V) (s a b x y : V) : SimpleGraph {v // v ≠ a ∧ v ≠ b} :=
  (G ⊔ edge s x ⊔ edge s y).comap Subtype.val

/-- The hypotheses for replacing the triangle `sab`: `N(s) = {a, b}`, `N(a) = {s, b, x}`,
`N(b) = {s, a, y}`, and `x ≠ y` lie outside `{s, a, b}`. -/
structure IsReplaceableTriangle (G : SimpleGraph V) (s a b x y : V) : Prop where
  adj_sa : G.Adj s a
  adj_sb : G.Adj s b
  adj_ab : G.Adj a b
  adj_ax : G.Adj a x
  adj_by : G.Adj b y
  eq_of_adj_s : ∀ ⦃w : V⦄, G.Adj s w → w = a ∨ w = b
  eq_of_adj_a : ∀ ⦃w : V⦄, G.Adj a w → w = s ∨ w = b ∨ w = x
  eq_of_adj_b : ∀ ⦃w : V⦄, G.Adj b w → w = s ∨ w = a ∨ w = y
  x_ne_y : x ≠ y
  x_ne_s : x ≠ s
  x_ne_b : x ≠ b
  y_ne_s : y ≠ s
  y_ne_a : y ≠ a

variable {G : SimpleGraph V} {s a b x y : V}

lemma replaceTriangle_adj {u v : {v // v ≠ a ∧ v ≠ b}} :
    (replaceTriangle G s a b x y).Adj u v ↔
      (G.Adj u v ∨ ((u : V) = s ∧ (v : V) = x ∨ (u : V) = x ∧ (v : V) = s) ∧ (u : V) ≠ v) ∨
        ((u : V) = s ∧ (v : V) = y ∨ (u : V) = y ∧ (v : V) = s) ∧ (u : V) ≠ v := by
  simp only [replaceTriangle, comap_adj, sup_adj, edge_adj]

instance [DecidableEq V] [DecidableRel G.Adj] :
    DecidableRel (replaceTriangle G s a b x y).Adj :=
  inferInstanceAs (DecidableRel ((G ⊔ edge s x ⊔ edge s y).comap Subtype.val).Adj)

namespace IsReplaceableTriangle

variable (h : IsReplaceableTriangle G s a b x y)
include h

lemma s_ne_a : s ≠ a := h.adj_sa.ne

lemma s_ne_b : s ≠ b := h.adj_sb.ne

lemma a_ne_b : a ≠ b := h.adj_ab.ne

lemma x_ne_a : x ≠ a := h.adj_ax.ne'

lemma y_ne_b : y ≠ b := h.adj_by.ne'

lemma s_mem : s ≠ a ∧ s ≠ b := ⟨h.s_ne_a, h.s_ne_b⟩

lemma x_mem : x ≠ a ∧ x ≠ b := ⟨h.x_ne_a, h.x_ne_b⟩

lemma y_mem : y ≠ a ∧ y ≠ b := ⟨h.y_ne_a, h.y_ne_b⟩

/-- The terminal `s` as a vertex of the reduced graph. -/
def sVert : {v // v ≠ a ∧ v ≠ b} := ⟨s, h.s_mem⟩

lemma symm : IsReplaceableTriangle G s b a y x :=
  ⟨h.adj_sb, h.adj_sa, h.adj_ab.symm, h.adj_by, h.adj_ax,
    fun _ hw ↦ (h.eq_of_adj_s hw).symm, h.eq_of_adj_b, h.eq_of_adj_a, h.x_ne_y.symm, h.y_ne_s,
    h.y_ne_a, h.x_ne_s, h.x_ne_b⟩

lemma replaceTriangle_adj_iff {u v : {v // v ≠ a ∧ v ≠ b}} :
    (replaceTriangle G s a b x y).Adj u v ↔
      G.Adj u v ∨ ((u : V) = s ∧ (v : V) = x) ∨ ((u : V) = x ∧ (v : V) = s) ∨
        ((u : V) = s ∧ (v : V) = y) ∨ ((u : V) = y ∧ (v : V) = s) := by
  rw [replaceTriangle_adj]
  have := h.x_ne_s
  have := h.y_ne_s
  constructor
  · rintro ((huv | ⟨huv | huv, -⟩) | ⟨huv | huv, -⟩) <;> tauto
  · rintro (huv | ⟨hu, hv⟩ | ⟨hu, hv⟩ | ⟨hu, hv⟩ | ⟨hu, hv⟩)
    · exact Or.inl (Or.inl huv)
    · exact Or.inl (Or.inr ⟨Or.inl ⟨hu, hv⟩, by rw [hu, hv]; tauto⟩)
    · exact Or.inl (Or.inr ⟨Or.inr ⟨hu, hv⟩, by rw [hu, hv]; tauto⟩)
    · exact Or.inr ⟨Or.inl ⟨hu, hv⟩, by rw [hu, hv]; tauto⟩
    · exact Or.inr ⟨Or.inr ⟨hu, hv⟩, by rw [hu, hv]; tauto⟩

section Finite

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

lemma neighborFinset_s : G.neighborFinset s = {a, b} := by
  ext w
  simp only [mem_neighborFinset, mem_insert, mem_singleton]
  exact ⟨fun hw ↦ h.eq_of_adj_s hw, by rintro (rfl | rfl); exacts [h.adj_sa, h.adj_sb]⟩

lemma neighborFinset_a : G.neighborFinset a = {s, b, x} := by
  ext w
  simp only [mem_neighborFinset, mem_insert, mem_singleton]
  exact ⟨fun hw ↦ h.eq_of_adj_a hw,
    by rintro (rfl | rfl | rfl); exacts [h.adj_sa.symm, h.adj_ab, h.adj_ax]⟩

lemma neighborFinset_b : G.neighborFinset b = {s, a, y} := by
  ext w
  simp only [mem_neighborFinset, mem_insert, mem_singleton]
  exact ⟨fun hw ↦ h.eq_of_adj_b hw,
    by rintro (rfl | rfl | rfl); exacts [h.adj_sb.symm, h.adj_ab.symm, h.adj_by]⟩

omit [DecidableEq V] in
lemma degree_s : G.degree s = 2 := by
  classical
  rw [← card_neighborFinset_eq_degree, h.neighborFinset_s, card_pair h.a_ne_b]

omit [DecidableEq V] in
lemma degree_a : G.degree a = 3 := by
  classical
  rw [← card_neighborFinset_eq_degree, h.neighborFinset_a, card_insert_of_notMem,
    card_pair h.x_ne_b.symm]
  simp [h.s_ne_b, h.x_ne_s.symm]

omit [DecidableEq V] in
lemma degree_b : G.degree b = 3 := by
  classical
  rw [← card_neighborFinset_eq_degree, h.neighborFinset_b, card_insert_of_notMem,
    card_pair h.y_ne_a.symm]
  simp [h.s_ne_a, h.y_ne_s.symm]

omit [DecidableRel G.Adj] in
lemma card_vertices : Fintype.card {v // v ≠ a ∧ v ≠ b} + 2 = Fintype.card V :=
  card_subtype_ne_and_ne_add_two h.a_ne_b

/-- Triangle replacement does not change the degree of any remaining vertex. -/
theorem degree_replaceTriangle (v : {v // v ≠ a ∧ v ≠ b}) :
    (replaceTriangle G s a b x y).degree v = G.degree v := by
  rw [degree_eq_card_filter_of_adj_iff (replaceTriangle G s a b x y)
      (G ⊔ edge s x ⊔ edge s y) fun _ _ ↦ Iff.rfl, ← card_neighborFinset_eq_degree]
  obtain ⟨v, hva, hvb⟩ := v
  have hsa := h.adj_sa
  have hsb := h.adj_sb
  have hab := h.adj_ab
  have hax := h.adj_ax
  have hby := h.adj_by
  have hs := h.eq_of_adj_s
  have ha := h.eq_of_adj_a
  have hb := h.eq_of_adj_b
  have hxy := h.x_ne_y
  have hxs := h.x_ne_s
  have hxb := h.x_ne_b
  have hys := h.y_ne_s
  have hya := h.y_ne_a
  dsimp only
  by_cases hvs : v = s
  · subst hvs
    have : ((G ⊔ edge v x ⊔ edge v y).neighborFinset v).filter (fun w ↦ w ≠ a ∧ w ≠ b) =
        {x, y} := by
      ext w
      simp only [mem_filter, mem_neighborFinset, sup_adj, edge_adj, mem_insert, mem_singleton]
      grind [G.adj_symm]
    rw [this, h.neighborFinset_s, card_pair hxy, card_pair h.a_ne_b]
  by_cases hvx : v = x
  · subst hvx
    have : ((G ⊔ edge s v ⊔ edge s y).neighborFinset v).filter (fun w ↦ w ≠ a ∧ w ≠ b) =
        insert s ((G.neighborFinset v).erase a) := by
      ext w
      simp only [mem_filter, mem_neighborFinset, sup_adj, edge_adj, mem_insert, mem_erase]
      grind [G.adj_symm]
    rw [this, card_insert_erase (by simpa using fun h' ↦ hxs (hs h'.symm |>.elim
      (fun h'' ↦ absurd h'' hva) fun h'' ↦ absurd h'' hvb)) (by simpa using hax.symm)]
  by_cases hvy : v = y
  · subst hvy
    have : ((G ⊔ edge s x ⊔ edge s v).neighborFinset v).filter (fun w ↦ w ≠ a ∧ w ≠ b) =
        insert s ((G.neighborFinset v).erase b) := by
      ext w
      simp only [mem_filter, mem_neighborFinset, sup_adj, edge_adj, mem_insert, mem_erase]
      grind [G.adj_symm]
    rw [this, card_insert_erase (by simpa using fun h' ↦ hys (hs h'.symm |>.elim
      (fun h'' ↦ absurd h'' hva) fun h'' ↦ absurd h'' hvb)) (by simpa using hby.symm)]
  · congr 1
    ext w
    simp only [mem_filter, mem_neighborFinset, sup_adj, edge_adj]
    grind [G.adj_symm]

theorem is23Graph_replaceTriangle (hG : Is23Graph G) : Is23Graph (replaceTriangle G s a b x y) :=
  is23Graph_of_degree_eq h.degree_replaceTriangle hG

lemma mem_terminals_replaceTriangle_iff (v : {v // v ≠ a ∧ v ≠ b}) :
    v ∈ terminals (replaceTriangle G s a b x y) ↔ (v : V) ∈ terminals G :=
  mem_terminals_iff_of_degree_eq h.degree_replaceTriangle v

/-- Triangle replacement keeps the number of terminals. -/
theorem card_terminalFinset_replaceTriangle :
    #(terminalFinset (replaceTriangle G s a b x y)) = #(terminalFinset G) := by
  rw [card_terminalFinset_of_degree_eq h.degree_replaceTriangle, filter_true_of_mem]
  intro v hv
  simp only [terminalFinset, mem_filter, mem_univ, true_and] at hv
  refine ⟨?_, ?_⟩ <;> rintro rfl
  · rw [h.degree_a] at hv
    exact absurd hv (by decide)
  · rw [h.degree_b] at hv
    exact absurd hv (by decide)

theorem ncard_terminals_replaceTriangle :
    (terminals (replaceTriangle G s a b x y)).ncard = (terminals G).ncard := by
  rw [ncard_terminals, ncard_terminals, h.card_terminalFinset_replaceTriangle]

/-- Triangle replacement removes exactly three edges. -/
theorem card_edgeFinset_replaceTriangle :
    #(replaceTriangle G s a b x y).edgeFinset + 3 = #G.edgeFinset := by
  have h1 := two_mul_card_edgeFinset_of_degree_eq h.degree_replaceTriangle
  rw [filter_ne_and_ne_eq] at h1
  have h2 := sum_erase_add (univ.erase a) (fun v ↦ G.degree v)
    (mem_erase.2 ⟨h.a_ne_b.symm, mem_univ b⟩)
  have h3 := sum_erase_add univ (fun v ↦ G.degree v) (mem_univ a)
  have h4 := G.sum_degrees_eq_twice_card_edges
  rw [h.degree_b] at h2
  rw [h.degree_a] at h3
  omega

/-- Triangle replacement lowers the cyclomatic number by one. -/
theorem cyclomaticNumber_replaceTriangle :
    cyclomaticNumber (replaceTriangle G s a b x y) + 1 = cyclomaticNumber G := by
  have h1 := h.card_edgeFinset_replaceTriangle
  have h2 := h.card_vertices
  unfold cyclomaticNumber
  omega

end Finite

/-- The retraction `V → {v // v ≠ a ∧ v ≠ b}` sending `a` and `b` to `s` is edge-collapsing
from `G` to the reduced graph, also after deleting edge sets `D` and `D'`, provided old edges
outside `D` stay outside `D'`, the new edge `sx` is outside `D'` when `ax ∉ D`, and the new
edge `sy` is outside `D'` when `by ∉ D`. -/
lemma isCollapseMap_deleteEdges [DecidableEq V]
    {D : Set (Sym2 V)} {D' : Set (Sym2 {v // v ≠ a ∧ v ≠ b})}
    (hold : ∀ u v : {v // v ≠ a ∧ v ≠ b}, G.Adj u v → s((u : V), v) ∉ D → s(u, v) ∉ D')
    (hx : ∀ u v : {v // v ≠ a ∧ v ≠ b}, (u : V) = s → (v : V) = x → s(a, x) ∉ D →
      s(u, v) ∉ D')
    (hy : ∀ u v : {v // v ≠ a ∧ v ≠ b}, (u : V) = s → (v : V) = y → s(b, y) ∉ D →
      s(u, v) ∉ D') :
    IsCollapseMap (G.deleteEdges D) ((replaceTriangle G s a b x y).deleteEdges D')
      (subtypeRetract h.sVert) := by
  set f := subtypeRetract h.sVert with hf
  have hfa : f a = h.sVert := subtypeRetract_of_neg h.sVert fun h' ↦ h'.1 rfl
  have hfb : f b = h.sVert := subtypeRetract_of_neg h.sVert fun h' ↦ h'.2 rfl
  have hfs : f s = h.sVert := subtypeRetract_of_pos h.sVert h.s_mem
  have hfx : f x = ⟨x, h.x_mem⟩ := subtypeRetract_of_pos h.sVert h.x_mem
  have hfy : f y = ⟨y, h.y_mem⟩ := subtypeRetract_of_pos h.sVert h.y_mem
  have key : ∀ p q, ¬(p ≠ a ∧ p ≠ b) → G.Adj p q → s(p, q) ∉ D →
      f p = f q ∨ ((replaceTriangle G s a b x y).Adj (f p) (f q) ∧ s(f p, f q) ∉ D') := by
    intro p q hp hpq hD
    have hp' : p = a ∨ p = b := by tauto
    rcases hp' with rfl | rfl
    · rcases h.eq_of_adj_a hpq with rfl | rfl | rfl
      · exact Or.inl (hfa.trans hfs.symm)
      · exact Or.inl (hfa.trans hfb.symm)
      · rw [hfa, hfx]
        exact Or.inr ⟨h.replaceTriangle_adj_iff.2 (Or.inr (Or.inl ⟨rfl, rfl⟩)),
          hx _ _ rfl rfl hD⟩
    · rcases h.eq_of_adj_b hpq with rfl | rfl | rfl
      · exact Or.inl (hfb.trans hfs.symm)
      · exact Or.inl (hfb.trans hfa.symm)
      · rw [hfb, hfy]
        exact Or.inr ⟨h.replaceTriangle_adj_iff.2 (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))),
          hy _ _ rfl rfl hD⟩
  refine IsCollapseMap.deleteEdges fun p q hpq hD ↦ ?_
  by_cases hp : p ≠ a ∧ p ≠ b
  · by_cases hq : q ≠ a ∧ q ≠ b
    · rw [hf, subtypeRetract_of_pos h.sVert hp, subtypeRetract_of_pos h.sVert hq]
      exact Or.inr ⟨h.replaceTriangle_adj_iff.2 (Or.inl hpq), hold ⟨p, hp⟩ ⟨q, hq⟩ hpq hD⟩
    · rw [Sym2.eq_swap] at hD
      rcases key q p hq hpq.symm hD with heq | ⟨hadj, hD'⟩
      · exact Or.inl heq.symm
      · exact Or.inr ⟨hadj.symm, by rwa [Sym2.eq_swap]⟩
  · exact key p q hp hpq hD

/-- Triangle replacement preserves connectivity. -/
theorem connected_replaceTriangle (hG : G.Connected) :
    (replaceTriangle G s a b x y).Connected := by
  classical
  have hf := h.isCollapseMap_deleteEdges (D := ∅) (D' := ∅)
    (fun _ _ _ _ ↦ Set.notMem_empty _) (fun _ _ _ _ _ ↦ Set.notMem_empty _)
    (fun _ _ _ _ _ ↦ Set.notMem_empty _)
  rw [deleteEdges_empty, deleteEdges_empty] at hf
  exact hf.connected (subtypeRetract_surjective _) hG

/-- An old edge of the reduced graph is not a bridge, since it is not a bridge of `G`. -/
lemma not_isBridge_old {u v : {v // v ≠ a ∧ v ≠ b}} (huv : G.Adj u v)
    (hnb : ¬G.IsBridge s((u : V), v)) : ¬(replaceTriangle G s a b x y).IsBridge s(u, v) := by
  classical
  rw [isBridge_iff, not_not] at hnb
  have hsx : ∀ p q : {v // v ≠ a ∧ v ≠ b}, (p : V) = s → (q : V) = x → s(p, q) ≠ s(u, v) := by
    intro p q hp hq hmem
    rw [Sym2.eq_iff, Subtype.ext_iff, Subtype.ext_iff, Subtype.ext_iff, Subtype.ext_iff, hp,
      hq] at hmem
    rcases hmem with ⟨hu, hv⟩ | ⟨hu, hv⟩
    · rcases h.eq_of_adj_s (hu ▸ hv ▸ huv) with h' | h'
      exacts [h.x_ne_a h', h.x_ne_b h']
    · rcases h.eq_of_adj_s (hu ▸ hv ▸ huv).symm with h' | h'
      exacts [h.x_ne_a h', h.x_ne_b h']
  have hsy : ∀ p q : {v // v ≠ a ∧ v ≠ b}, (p : V) = s → (q : V) = y → s(p, q) ≠ s(u, v) := by
    intro p q hp hq hmem
    rw [Sym2.eq_iff, Subtype.ext_iff, Subtype.ext_iff, Subtype.ext_iff, Subtype.ext_iff, hp,
      hq] at hmem
    rcases hmem with ⟨hu, hv⟩ | ⟨hu, hv⟩
    · rcases h.eq_of_adj_s (hu ▸ hv ▸ huv) with h' | h'
      exacts [h.y_ne_a h', h.y_ne_b h']
    · rcases h.eq_of_adj_s (hu ▸ hv ▸ huv).symm with h' | h'
      exacts [h.y_ne_a h', h.y_ne_b h']
  refine IsCollapseMap.not_isBridge (h.isCollapseMap_deleteEdges ?_ ?_ ?_)
    (subtypeRetract_coe _ u) (subtypeRetract_coe _ v) hnb
  · intro p q _ hD hmem
    rw [Set.mem_singleton_iff] at hD hmem
    exact hD (by simpa using congrArg (Sym2.map Subtype.val) hmem)
  · intro p q hp hq _ hmem
    exact hsx p q hp hq (Set.mem_singleton_iff.1 hmem)
  · intro p q hp hq _ hmem
    exact hsy p q hp hq (Set.mem_singleton_iff.1 hmem)

/-- The new edge `sx` is not a bridge, since `ax` is not a bridge of `G`. -/
lemma not_isBridge_sx (hax : ¬G.IsBridge s(a, x)) {u v : {v // v ≠ a ∧ v ≠ b}}
    (hu : (u : V) = s) (hv : (v : V) = x) : ¬(replaceTriangle G s a b x y).IsBridge s(u, v) := by
  classical
  rw [isBridge_iff, not_not] at hax
  have hfu : subtypeRetract h.sVert a = u :=
    (subtypeRetract_of_neg h.sVert fun h' ↦ h'.1 rfl).trans (Subtype.ext hu.symm)
  have hfv : subtypeRetract h.sVert x = v :=
    (subtypeRetract_of_pos h.sVert h.x_mem).trans (Subtype.ext hv.symm)
  refine IsCollapseMap.not_isBridge (h.isCollapseMap_deleteEdges ?_ ?_ ?_) hfu hfv hax
  · intro p q hpq _ hmem
    rw [Set.mem_singleton_iff, Sym2.eq_iff, Subtype.ext_iff, Subtype.ext_iff, Subtype.ext_iff,
      Subtype.ext_iff, hu, hv] at hmem
    rcases hmem with ⟨hp, hq⟩ | ⟨hp, hq⟩
    · rcases h.eq_of_adj_s (hp ▸ hq ▸ hpq) with h' | h'
      exacts [h.x_ne_a h', h.x_ne_b h']
    · rcases h.eq_of_adj_s (hp ▸ hq ▸ hpq).symm with h' | h'
      exacts [h.x_ne_a h', h.x_ne_b h']
  · intro _ _ _ _ hD
    exact absurd rfl hD
  · intro p q hp hq _ hmem
    rw [Set.mem_singleton_iff, Sym2.eq_iff, Subtype.ext_iff, Subtype.ext_iff, Subtype.ext_iff,
      Subtype.ext_iff, hu, hv, hp, hq] at hmem
    rcases hmem with ⟨-, h'⟩ | ⟨h', -⟩
    exacts [h.x_ne_y h'.symm, h.x_ne_s h'.symm]

/-- The new edge `sy` is not a bridge, since `by` is not a bridge of `G`. -/
lemma not_isBridge_sy (hby : ¬G.IsBridge s(b, y)) {u v : {v // v ≠ a ∧ v ≠ b}}
    (hu : (u : V) = s) (hv : (v : V) = y) : ¬(replaceTriangle G s a b x y).IsBridge s(u, v) := by
  classical
  rw [isBridge_iff, not_not] at hby
  have hfu : subtypeRetract h.sVert b = u :=
    (subtypeRetract_of_neg h.sVert fun h' ↦ h'.2 rfl).trans (Subtype.ext hu.symm)
  have hfv : subtypeRetract h.sVert y = v :=
    (subtypeRetract_of_pos h.sVert h.y_mem).trans (Subtype.ext hv.symm)
  refine IsCollapseMap.not_isBridge (h.isCollapseMap_deleteEdges ?_ ?_ ?_) hfu hfv hby
  · intro p q hpq _ hmem
    rw [Set.mem_singleton_iff, Sym2.eq_iff, Subtype.ext_iff, Subtype.ext_iff, Subtype.ext_iff,
      Subtype.ext_iff, hu, hv] at hmem
    rcases hmem with ⟨hp, hq⟩ | ⟨hp, hq⟩
    · rcases h.eq_of_adj_s (hp ▸ hq ▸ hpq) with h' | h'
      exacts [h.y_ne_a h', h.y_ne_b h']
    · rcases h.eq_of_adj_s (hp ▸ hq ▸ hpq).symm with h' | h'
      exacts [h.y_ne_a h', h.y_ne_b h']
  · intro p q hp hq _ hmem
    rw [Set.mem_singleton_iff, Sym2.eq_iff, Subtype.ext_iff, Subtype.ext_iff, Subtype.ext_iff,
      Subtype.ext_iff, hu, hv, hp, hq] at hmem
    rcases hmem with ⟨-, h'⟩ | ⟨h', -⟩
    exacts [h.x_ne_y h', h.y_ne_s h'.symm]
  · intro _ _ _ _ hD
    exact absurd rfl hD

/-- Triangle replacement preserves bridgelessness. -/
theorem isBridgeless_replaceTriangle [DecidableEq V] [DecidableRel G.Adj]
    (hG : IsBridgeless G) : IsBridgeless (replaceTriangle G s a b x y) := by
  intro e he
  induction e using Sym2.ind with
  | _ u v =>
    rw [mem_edgeSet, h.replaceTriangle_adj_iff] at he
    rcases he with huv | ⟨hu, hv⟩ | ⟨hu, hv⟩ | ⟨hu, hv⟩ | ⟨hu, hv⟩
    · exact h.not_isBridge_old huv (hG huv)
    · exact h.not_isBridge_sx (hG h.adj_ax) hu hv
    · rw [Sym2.eq_swap]
      exact h.not_isBridge_sx (hG h.adj_ax) hv hu
    · exact h.not_isBridge_sy (hG h.adj_by) hu hv
    · rw [Sym2.eq_swap]
      exact h.not_isBridge_sy (hG h.adj_by) hv hu

/-- Triangle replacement preserves the hypotheses of the terminal-selection theorem. -/
theorem isTerminalSelectionInstance_replaceTriangle [Fintype V] [DecidableEq V]
    [DecidableRel G.Adj] (hG : IsTerminalSelectionInstance G) :
    IsTerminalSelectionInstance (replaceTriangle G s a b x y) :=
  ⟨h.connected_replaceTriangle hG.1, h.isBridgeless_replaceTriangle hG.2.1,
    h.is23Graph_replaceTriangle hG.2.2⟩

end IsReplaceableTriangle

end ThreeDecomposition

/-!
## Local configurations of Lemma 3.4(a) and (b)

Proves the `x ≠ y` arguments of Lemma 3.4(a) and (b) for a connected bridgeless `{2,3}`-graph,
and derives `isSuppressible_of_adj_terminals` and `isReplaceableTriangle_of`.
-/

namespace ThreeDecomposition

open SimpleGraph Finset

variable {V : Type*} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

section Neighbors

/-- A set of neighbours of `v` with at least `G.degree v` elements is the whole
neighbourhood. -/
lemma neighborFinset_eq_of_subset {v : V} {S : Finset V} (hS : S ⊆ G.neighborFinset v)
    (hcard : G.degree v ≤ #S) : G.neighborFinset v = S :=
  (eq_of_subset_of_card_le hS (by rwa [card_neighborFinset_eq_degree])).symm

/-- A vertex has a neighbour outside every set with fewer elements than its degree. -/
lemma exists_adj_notMem_of_card_lt {v : V} (S : Finset V) (h : #S < G.degree v) :
    ∃ w, G.Adj v w ∧ w ∉ S := by
  rw [← card_neighborFinset_eq_degree] at h
  obtain ⟨w, hw, hwS⟩ := exists_mem_notMem_of_card_lt_card h
  exact ⟨w, (mem_neighborFinset _ _ _).1 hw, hwS⟩

lemma eq_or_eq_of_degree_eq_two {v p q w : V} (hv : G.degree v = 2) (hp : G.Adj v p)
    (hq : G.Adj v q) (hpq : p ≠ q) (hw : G.Adj v w) : w = p ∨ w = q := by
  classical
  have hN : G.neighborFinset v = {p, q} := by
    refine neighborFinset_eq_of_subset (fun z hz ↦ ?_) (by rw [hv, card_pair hpq])
    rcases mem_insert.1 hz with rfl | hz
    · simpa using hp
    · rw [mem_singleton.1 hz]
      simpa using hq
  have hw' : w ∈ G.neighborFinset v := (mem_neighborFinset _ _ _).2 hw
  simpa [hN] using hw'

/-- A vertex of degree two has exactly two neighbours. -/
lemma exists_neighbors_of_degree_eq_two {v : V} (hv : G.degree v = 2) :
    ∃ p q, p ≠ q ∧ G.Adj v p ∧ G.Adj v q ∧ ∀ ⦃w⦄, G.Adj v w → w = p ∨ w = q := by
  classical
  rw [← card_neighborFinset_eq_degree, card_eq_two] at hv
  obtain ⟨p, q, hpq, hN⟩ := hv
  have hmem : ∀ w, G.Adj v w ↔ w = p ∨ w = q := fun w ↦ by
    rw [← mem_neighborFinset, hN, mem_insert, mem_singleton]
  exact ⟨p, q, hpq, (hmem p).2 (Or.inl rfl), (hmem q).2 (Or.inr rfl), fun w hw ↦ (hmem w).1 hw⟩

lemma eq_or_eq_or_eq_of_degree_le_three {v p q r w : V} (hv : G.degree v ≤ 3)
    (hp : G.Adj v p) (hq : G.Adj v q) (hr : G.Adj v r) (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (hw : G.Adj v w) : w = p ∨ w = q ∨ w = r := by
  classical
  have hN : G.neighborFinset v = {p, q, r} := by
    refine neighborFinset_eq_of_subset (fun z hz ↦ ?_) ?_
    · simp only [mem_insert, mem_singleton] at hz
      rcases hz with rfl | rfl | rfl <;> simpa
    · rw [card_insert_of_notMem (by simp [hpq, hpr]), card_pair hqr]
      exact hv
  have hw' : w ∈ G.neighborFinset v := (mem_neighborFinset _ _ _).2 hw
  simpa [hN] using hw'

lemma degree_eq_three_of_adj (h23 : Is23Graph G) {v p q r : V} (hp : G.Adj v p)
    (hq : G.Adj v q) (hr : G.Adj v r) (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) :
    G.degree v = 3 := by
  classical
  have hsub : ({p, q, r} : Finset V) ⊆ G.neighborFinset v := by
    intro z hz
    simp only [mem_insert, mem_singleton] at hz
    rcases hz with rfl | rfl | rfl <;> simpa
  have hcard := card_le_card hsub
  rw [card_insert_of_notMem (by simp [hpq, hpr]), card_pair hqr,
    card_neighborFinset_eq_degree] at hcard
  rcases h23 v with h | h <;> omega

end Neighbors

section Configurations

/-- **Reduction 1, `x = y`.** In a connected bridgeless `{2,3}`-graph, if two adjacent
terminals `u, v` have a common neighbour `x`, then `G` is the triangle on `{u, v, x}`: `x` is a
terminal too and these are all the vertices. -/
theorem eq_triangle_of_adj_terminals [DecidableEq V] (hconn : G.Connected)
    (hbr : IsBridgeless G) (h23 : Is23Graph G) {u v x : V} (huv : G.Adj u v)
    (hux : G.Adj u x) (hvx : G.Adj v x) (hu : G.degree u = 2) (hv : G.degree v = 2) :
    G.degree x = 2 ∧ (univ : Finset V) = {u, v, x} := by
  have hNu : ∀ ⦃w⦄, G.Adj u w → w = v ∨ w = x :=
    fun _ ↦ eq_or_eq_of_degree_eq_two hu huv hux hvx.ne
  have hNv : ∀ ⦃w⦄, G.Adj v w → w = u ∨ w = x :=
    fun _ ↦ eq_or_eq_of_degree_eq_two hv huv.symm hvx hux.ne
  have hx2 : G.degree x = 2 := by
    rcases h23 x with h2 | h3
    · exact h2
    exfalso
    obtain ⟨z, hxz, hz⟩ := exists_adj_notMem_of_card_lt {u, v}
      (by rw [h3]; exact (card_le_two).trans_lt (by norm_num))
    simp only [mem_insert, mem_singleton, not_or] at hz
    have hNx : ∀ ⦃w⦄, G.Adj x w → w = u ∨ w = v ∨ w = z := fun _ ↦
      eq_or_eq_or_eq_of_degree_le_three h3.le hux.symm hvx.symm hxz huv.ne
        (Ne.symm hz.1) (Ne.symm hz.2)
    refine hbr hxz (isBridge_of_closed (S := {u, v, x}) (fun p q hpq hne hp ↦ ?_)
      (by simp) ?_)
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp ⊢
      rcases hp with rfl | rfl | rfl
      · rcases hNu hpq with rfl | rfl <;> simp
      · rcases hNv hpq with rfl | rfl <;> simp
      · rcases hNx hpq with rfl | rfl | rfl
        · simp
        · simp
        · exact absurd rfl hne
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨hz.1, hz.2, hxz.ne'⟩
  have hNx : ∀ ⦃w⦄, G.Adj x w → w = u ∨ w = v :=
    fun _ ↦ eq_or_eq_of_degree_eq_two hx2 hux.symm hvx.symm huv.ne
  refine ⟨hx2, Eq.symm (eq_univ_of_forall fun w ↦ ?_)⟩
  have hw := mem_of_reachable_of_closed (S := {u, v, x}) (fun p q hpq hp ↦ ?_) (by simp)
    (hconn.preconnected u w)
  · simpa using hw
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp ⊢
    rcases hp with rfl | rfl | rfl
    · rcases hNu hpq with rfl | rfl <;> simp
    · rcases hNv hpq with rfl | rfl <;> simp
    · rcases hNx hpq with rfl | rfl <;> simp

theorem card_eq_three_of_adj_terminals (hconn : G.Connected) (hbr : IsBridgeless G)
    (h23 : Is23Graph G) {u v x : V} (huv : G.Adj u v) (hux : G.Adj u x) (hvx : G.Adj v x)
    (hu : G.degree u = 2) (hv : G.degree v = 2) : Fintype.card V = 3 := by
  classical
  rw [← card_univ, (eq_triangle_of_adj_terminals hconn hbr h23 huv hux hvx hu hv).2,
    card_insert_of_notMem (by simp [huv.ne, hux.ne]), card_pair hvx.ne]

/-- **Reduction 1, `x ≠ y`.** Unless `G` is the triangle, the other neighbours of two adjacent
terminals are distinct. -/
theorem ne_of_adj_terminals (hconn : G.Connected) (hbr : IsBridgeless G) (h23 : Is23Graph G)
    (hcard : Fintype.card V ≠ 3) {u v x y : V} (huv : G.Adj u v) (hu : G.degree u = 2)
    (hv : G.degree v = 2) (hux : G.Adj u x) (hvy : G.Adj v y) : x ≠ y := by
  rintro rfl
  exact hcard (card_eq_three_of_adj_terminals hconn hbr h23 huv hux hvy hu hv)

/-- A terminal whose two neighbours are distinct and non-adjacent can be suppressed. -/
theorem IsSuppressible.of_degree_eq_two {s a b : V} (hs : G.degree s = 2) (hsa : G.Adj s a)
    (hsb : G.Adj s b) (hab : a ≠ b) (hnadj : ¬G.Adj a b) : IsSuppressible G s a b :=
  ⟨hsa, hsb, hab, hnadj, fun _ hw ↦ eq_or_eq_of_degree_eq_two hs hsa hsb hab hw⟩

/-- Reduction 1 as a suppression: if `u, v` are adjacent terminals whose other neighbours `x`
(of `u`) and `y` (of `v`) are distinct, then `v` can be suppressed; the suppressed graph is the
contraction of `uv`. -/
theorem isSuppressible_of_adj_terminals {u v x y : V} (huv : G.Adj u v)
    (hu : G.degree u = 2) (hv : G.degree v = 2) (hux : G.Adj u x) (hxv : x ≠ v)
    (hvy : G.Adj v y) (hyu : y ≠ u) (hxy : x ≠ y) : IsSuppressible G v u y where
  adj_left := huv.symm
  adj_right := hvy
  ne := hyu.symm
  not_adj huy := by
    rcases eq_or_eq_of_degree_eq_two hu huv hux hxv.symm huy with h | h
    exacts [hvy.ne' h, hxy h.symm]
  eq_or_eq_of_adj _ hw := eq_or_eq_of_degree_eq_two hv huv.symm hvy hyu.symm hw

/-- **Reduction 2, `x = y`.** In a connected bridgeless `{2,3}`-graph, if a terminal `s` lies on
a triangle `sab` and `a` and `b` have a common neighbour `x ≠ s`, then `G` has exactly four
vertices and exactly two terminals. -/
theorem card_eq_four_of_triangle_common_neighbor (hconn : G.Connected) (hbr : IsBridgeless G)
    (h23 : Is23Graph G) {s a b x : V} (hs : G.degree s = 2) (hsa : G.Adj s a)
    (hsb : G.Adj s b) (hab : G.Adj a b) (hax : G.Adj a x) (hbx : G.Adj b x) (hxs : x ≠ s) :
    Fintype.card V = 4 ∧ #(terminalFinset G) = 2 := by
  classical
  have hxa : x ≠ a := hax.ne'
  have hxb : x ≠ b := hbx.ne'
  have hNs : ∀ ⦃w⦄, G.Adj s w → w = a ∨ w = b :=
    fun _ ↦ eq_or_eq_of_degree_eq_two hs hsa hsb hab.ne
  have hNa : ∀ ⦃w⦄, G.Adj a w → w = s ∨ w = b ∨ w = x := fun _ ↦
    eq_or_eq_or_eq_of_degree_le_three (by rcases h23 a with h | h <;> omega) hsa.symm hab hax
      hsb.ne hxs.symm hxb.symm
  have hNb : ∀ ⦃w⦄, G.Adj b w → w = s ∨ w = a ∨ w = x := fun _ ↦
    eq_or_eq_or_eq_of_degree_le_three (by rcases h23 b with h | h <;> omega) hsb.symm hab.symm
      hbx hsa.ne hxs.symm hxa.symm
  have ha3 : G.degree a = 3 :=
    degree_eq_three_of_adj h23 hsa.symm hab hax hsb.ne hxs.symm hxb.symm
  have hb3 : G.degree b = 3 :=
    degree_eq_three_of_adj h23 hsb.symm hab.symm hbx hsa.ne hxs.symm hxa.symm
  have hx2 : G.degree x = 2 := by
    rcases h23 x with h2 | h3
    · exact h2
    exfalso
    obtain ⟨z, hxz, hz⟩ := exists_adj_notMem_of_card_lt {a, b}
      (by rw [h3]; exact (card_le_two).trans_lt (by norm_num))
    simp only [mem_insert, mem_singleton, not_or] at hz
    have hzs : z ≠ s := by
      rintro rfl
      rcases hNs hxz.symm with h | h
      exacts [hxa h, hxb h]
    have hNx : ∀ ⦃w⦄, G.Adj x w → w = a ∨ w = b ∨ w = z := fun _ ↦
      eq_or_eq_or_eq_of_degree_le_three h3.le hax.symm hbx.symm hxz hab.ne
        (Ne.symm hz.1) (Ne.symm hz.2)
    refine hbr hxz (isBridge_of_closed (S := {s, a, b, x}) (fun p q hpq hne hp ↦ ?_)
      (by simp) ?_)
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp ⊢
      rcases hp with rfl | rfl | rfl | rfl
      · rcases hNs hpq with rfl | rfl <;> simp
      · rcases hNa hpq with rfl | rfl | rfl <;> simp
      · rcases hNb hpq with rfl | rfl | rfl <;> simp
      · rcases hNx hpq with rfl | rfl | rfl
        · simp
        · simp
        · exact absurd rfl hne
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨hzs, hz.1, hz.2, hxz.ne'⟩
  have hNx : ∀ ⦃w⦄, G.Adj x w → w = a ∨ w = b :=
    fun _ ↦ eq_or_eq_of_degree_eq_two hx2 hax.symm hbx.symm hab.ne
  have huniv : (univ : Finset V) = {s, a, b, x} := by
    refine Eq.symm (eq_univ_of_forall fun w ↦ ?_)
    have hw := mem_of_reachable_of_closed (S := {s, a, b, x}) (fun p q hpq hp ↦ ?_) (by simp)
      (hconn.preconnected s w)
    · simpa using hw
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp ⊢
      rcases hp with rfl | rfl | rfl | rfl
      · rcases hNs hpq with rfl | rfl <;> simp
      · rcases hNa hpq with rfl | rfl | rfl <;> simp
      · rcases hNb hpq with rfl | rfl | rfl <;> simp
      · rcases hNx hpq with rfl | rfl <;> simp
  refine ⟨?_, ?_⟩
  · rw [← card_univ, huniv, card_insert_of_notMem (by simp [hsa.ne, hsb.ne, hxs.symm]),
      card_insert_of_notMem (by simp [hab.ne, hxa.symm]), card_pair hxb.symm]
  · have hT : terminalFinset G = {s, x} := by
      ext w
      have hw : w ∈ (univ : Finset V) := mem_univ w
      rw [huniv] at hw
      simp only [mem_insert, mem_singleton] at hw
      simp only [terminalFinset, mem_filter, mem_univ, true_and, mem_insert, mem_singleton]
      rcases hw with rfl | rfl | rfl | rfl
      · simp [hs]
      · simp [ha3, hsa.ne', hxa.symm]
      · simp [hb3, hsb.ne', hxb.symm]
      · simp [hx2]
    rw [hT, card_pair hxs.symm]

/-- **Reduction 2, `x ≠ y`.** If `G` has at least three terminals, then the third neighbours
of the two other vertices of a triangle through a terminal are distinct. -/
theorem ne_of_triangle (hconn : G.Connected) (hbr : IsBridgeless G) (h23 : Is23Graph G)
    (hk : 3 ≤ #(terminalFinset G)) {s a b x y : V} (hs : G.degree s = 2) (hsa : G.Adj s a)
    (hsb : G.Adj s b) (hab : G.Adj a b) (hax : G.Adj a x) (hby : G.Adj b y) (hxs : x ≠ s) :
    x ≠ y := by
  rintro rfl
  have := (card_eq_four_of_triangle_common_neighbor hconn hbr h23 hs hsa hsb hab hax hby hxs).2
  omega

/-- The hypotheses of triangle replacement, from a terminal `s` on a triangle `sab` whose
third neighbours `x` of `a` and `y` of `b` are distinct. -/
theorem isReplaceableTriangle_of (h23 : Is23Graph G) {s a b x y : V} (hs : G.degree s = 2)
    (hsa : G.Adj s a) (hsb : G.Adj s b) (hab : G.Adj a b) (hax : G.Adj a x) (hxs : x ≠ s)
    (hxb : x ≠ b) (hby : G.Adj b y) (hys : y ≠ s) (hya : y ≠ a) (hxy : x ≠ y) :
    IsReplaceableTriangle G s a b x y where
  adj_sa := hsa
  adj_sb := hsb
  adj_ab := hab
  adj_ax := hax
  adj_by := hby
  eq_of_adj_s _ hw := eq_or_eq_of_degree_eq_two hs hsa hsb hab.ne hw
  eq_of_adj_a _ hw := eq_or_eq_or_eq_of_degree_le_three (by rcases h23 a with h | h <;> omega)
    hsa.symm hab hax hsb.ne hxs.symm hxb.symm hw
  eq_of_adj_b _ hw := eq_or_eq_or_eq_of_degree_le_three (by rcases h23 b with h | h <;> omega)
    hsb.symm hab.symm hby hsa.ne hys.symm hya.symm hw
  x_ne_y := hxy
  x_ne_s := hxs
  x_ne_b := hxb
  y_ne_s := hys
  y_ne_a := hya

end Configurations

end ThreeDecomposition
