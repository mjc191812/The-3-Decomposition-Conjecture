import ThreeDecomposition.Multigraph.Defs
import ThreeDecomposition.Statement
import Mathlib.Data.Set.Finite.Lemmas

/-!
# Loopless multigraphs: Corollary 1.5, 2DC and 3DC

This module develops the theory of `LooplessMultigraph` (Section 4 of the paper):
* **Basic API**: degrees, handshake identity, spanning trees, and cycles of length two.
* **Parallel-edge reduction**: deleting one edge `f` of a parallel pair `{e, f}` in a connected
  fragile subcubic multigraph preserves connectivity and fragility, and makes all remaining edges
  incident with the ends of `e` bridges (`parallel_diff_hypotheses`, `parallel_extend`).
* **Corollary 1.5** (`LooplessMultigraph.exists_isSpanningTree_isMatching`): extends Theorem 1.4
  to loopless multigraphs by strong induction on the number of edges.
* **Corollary 4.1 (2DC) and Theorem 1.2 (3DC)**:
  `twoDecompositionConjecture_of_fragileDecomposition` and
  `threeDecompositionConjecture_of_fragileDecomposition`.

## Basic API for loopless multigraphs
-/

namespace ThreeDecomposition

open SimpleGraph

namespace LooplessMultigraph

variable {V E : Type*}

section Reachability

variable {H K : SimpleGraph V}

theorem reachable_of_forall_adj {a b : V} (h : H.Reachable a b)
    (hHK : ∀ x y, H.Adj x y → K.Reachable x y) : K.Reachable a b := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => rfl
  | cons hadj _ ih => exact (hHK _ _ hadj).trans ih

theorem connected_of_forall_adj (h : H.Connected)
    (hHK : ∀ x y, H.Adj x y → K.Reachable x y) : K.Connected :=
  (connected_iff K).2
    ⟨fun _ _ => reachable_of_forall_adj (h.preconnected _ _) hHK, h.nonempty⟩

theorem mem_of_reachable_of_closed {P : Set V} (hP : ∀ x y, K.Adj x y → x ∈ P → y ∈ P)
    {a b : V} (h : K.Reachable a b) (ha : a ∈ P) : b ∈ P := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => exact ha
  | cons hadj _ ih => exact ih (hP _ _ hadj ha)

theorem reachable_of_mem_support {x z y : V} (p : H.Walk x z)
    (hK : ∀ d ∈ p.edges, d ∈ K.edgeSet) (hy : y ∈ p.support) : K.Reachable x y := by
  induction p with
  | nil =>
    rw [Walk.mem_support_nil_iff] at hy
    rw [hy]
  | cons h q ih =>
    rw [Walk.support_cons, List.mem_cons] at hy
    simp only [Walk.edges_cons, List.mem_cons, forall_eq_or_imp] at hK
    rcases hy with rfl | hy
    · rfl
    · exact (Adj.reachable hK.1).trans (ih hK.2 hy)

end Reachability

variable (G : LooplessMultigraph V E)

theorem exists_ends_eq (e : E) : ∃ a b, a ≠ b ∧ G.ends e = s(a, b) := by
  have h := G.loopless e
  generalize G.ends e = z at h ⊢
  induction z using Sym2.ind with
  | _ a b => exact ⟨a, b, fun hab => h (Sym2.mk_isDiag_iff.2 hab), rfl⟩

theorem ne_of_ends_eq {e : E} {a b : V} (h : G.ends e = s(a, b)) : a ≠ b := fun hab =>
  G.loopless e (h ▸ Sym2.mk_isDiag_iff.2 hab)

theorem adjGraph_adj {F : Set E} {u v : V} :
    (G.adjGraph F).Adj u v ↔ ∃ e ∈ F, G.ends e = s(u, v) :=
  Iff.rfl

theorem adjGraph_mono {F F' : Set E} (h : F ⊆ F') : G.adjGraph F ≤ G.adjGraph F' :=
  fun _ _ ⟨e, he, hee⟩ => ⟨e, h he, hee⟩

theorem edgeSet_adjGraph (F : Set E) : (G.adjGraph F).edgeSet = G.ends '' F := by
  ext d
  induction d using Sym2.ind with
  | _ a b => exact Iff.rfl

theorem ends_mem_edgeSet {F : Set E} {e : E} (he : e ∈ F) :
    G.ends e ∈ (G.adjGraph F).edgeSet := by
  rw [edgeSet_adjGraph]
  exact Set.mem_image_of_mem _ he

theorem reachable_of_mem_ends {F : Set E} {e : E} (he : e ∈ F) {u v : V}
    (hu : u ∈ G.ends e) (hv : v ∈ G.ends e) : (G.adjGraph F).Reachable u v := by
  by_cases huv : u = v
  · rw [huv]
  · exact Adj.reachable ⟨e, he, (Sym2.mem_and_mem_iff huv).1 ⟨hu, hv⟩⟩

theorem incidentIn_mono {F F' : Set E} (h : F ⊆ F') (v : V) :
    G.incidentIn F v ⊆ G.incidentIn F' v :=
  fun _ he => ⟨h he.1, he.2⟩

theorem incidentIn_union (F F' : Set E) (v : V) :
    G.incidentIn (F ∪ F') v = G.incidentIn F v ∪ G.incidentIn F' v := by
  ext e
  simp only [incidentIn, Set.mem_union, Set.mem_ofPred_eq]
  tauto

theorem incidentIn_univ (v : V) : G.incidentIn Set.univ v = {e | v ∈ G.ends e} := by
  ext e
  simp [incidentIn]

theorem degree_eq (v : V) : G.degree v = (G.incidentIn Set.univ v).ncard :=
  rfl

/-- The end of `e` other than `v` (an arbitrary value if `v` is not an end of `e`). -/
noncomputable def otherEnd (e : E) (v : V) : V :=
  haveI := Classical.dec (v ∈ G.ends e)
  if h : v ∈ G.ends e then Sym2.Mem.other h else v

theorem ends_eq_otherEnd {e : E} {v : V} (h : v ∈ G.ends e) :
    G.ends e = s(v, G.otherEnd e v) := by
  simp only [otherEnd, h, ↓reduceDIte, Sym2.other_spec]

theorem image_otherEnd_incidentIn (F : Set E) (v : V) :
    (G.otherEnd · v) '' G.incidentIn F v = (G.adjGraph F).neighborSet v := by
  ext w
  constructor
  · rintro ⟨e, ⟨he, hve⟩, rfl⟩
    exact ⟨e, he, G.ends_eq_otherEnd hve⟩
  · rintro ⟨e, he, hew⟩
    have hve : v ∈ G.ends e := hew ▸ Sym2.mem_mk_left v w
    refine ⟨e, ⟨he, hve⟩, ?_⟩
    rw [← Sym2.congr_right, ← G.ends_eq_otherEnd hve, hew]

theorem ncard_neighborSet_le [Finite E] (F : Set E) (v : V) :
    ((G.adjGraph F).neighborSet v).ncard ≤ (G.incidentIn F v).ncard := by
  rw [← G.image_otherEnd_incidentIn]
  exact Set.ncard_image_le

theorem ncard_incidentIn_eq {F : Set E} (hF : Set.InjOn G.ends F) (v : V) :
    (G.incidentIn F v).ncard = ((G.adjGraph F).neighborSet v).ncard := by
  rw [← G.image_otherEnd_incidentIn, Set.InjOn.ncard_image]
  rintro e ⟨he, hve⟩ f ⟨hf, hvf⟩ hef
  refine hF he hf ?_
  rw [G.ends_eq_otherEnd hve, G.ends_eq_otherEnd hvf]
  exact congrArg _ hef

theorem degree_adjGraph_le [Fintype V] [Finite E] (F : Set E)
    [DecidableRel (G.adjGraph F).Adj] (v : V) :
    (G.adjGraph F).degree v ≤ (G.incidentIn F v).ncard := by
  rw [← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
  exact G.ncard_neighborSet_le F v

/-- The handshake identity: every edge has exactly two ends. -/
theorem sum_degree [Fintype V] [Fintype E] : ∑ v, G.degree v = 2 * Fintype.card E := by
  classical
  have h1 : ∀ v, G.degree v = (Finset.univ.bipartiteAbove (fun v e => v ∈ G.ends e) v).card := by
    intro v
    rw [degree_eq, incidentIn_univ, Set.ncard_eq_toFinset_card']
    congr 1
    ext e
    simp [Finset.bipartiteAbove]
  have h2 : ∀ e, (Finset.univ.bipartiteBelow (fun v e => v ∈ G.ends e) e).card = 2 := by
    intro e
    obtain ⟨a, b, hab, he⟩ := G.exists_ends_eq e
    have : Finset.univ.bipartiteBelow (fun v e => v ∈ G.ends e) e = {a, b} := by
      ext x
      simp [Finset.bipartiteBelow, he]
    rw [this, Finset.card_pair hab]
  simp_rw [h1]
  rw [Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow]
  simp [h2, mul_comm]

/-- A spanning tree has one edge fewer than there are vertices. -/
theorem IsSpanningTree.ncard_add_one [Finite V] {G : LooplessMultigraph V E} {T : Set E}
    (hT : G.IsSpanningTree T) : T.ncard + 1 = Nat.card V := by
  have h := ((isTree_iff_connected_and_card).1 hT.2).2
  rwa [Nat.card_coe_set_eq, edgeSet_adjGraph, hT.1.ncard_image] at h

theorem IsSpanningTree.connected {G : LooplessMultigraph V E} {T : Set E}
    (hT : G.IsSpanningTree T) : (G.adjGraph T).Connected :=
  hT.2.connected

theorem isTwoRegular_empty : G.IsTwoRegular ∅ := fun v => Or.inl (by simp [incidentIn])

/-- Two distinct parallel edges form a cycle. -/
theorem isCycle_pair {e f : E} (hef : e ≠ f) (h : G.ends e = G.ends f) :
    G.IsCycle {e, f} := by
  refine ⟨⟨e, Set.mem_insert _ _⟩, fun v => ?_, fun u v ⟨g, hg, hug⟩ ⟨g', hg', hvg'⟩ => ?_⟩
  · by_cases hv : v ∈ G.ends e
    · right
      have : G.incidentIn {e, f} v = {e, f} := by
        ext g
        simp only [incidentIn, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_ofPred_eq]
        constructor
        · exact fun h => h.1
        · rintro (rfl | rfl)
          · exact ⟨Or.inl rfl, hv⟩
          · exact ⟨Or.inr rfl, h ▸ hv⟩
      rw [this, Set.ncard_pair hef]
    · left
      have : G.incidentIn {e, f} v = ∅ := by
        ext g
        simp only [incidentIn, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_ofPred_eq,
          Set.mem_empty_iff_false, iff_false, not_and]
        rintro (rfl | rfl)
        · exact hv
        · exact h ▸ hv
      rw [this, Set.ncard_empty]
  · have hends : ∀ g ∈ ({e, f} : Set E), G.ends g = G.ends e := by
      rintro g (rfl | rfl)
      · rfl
      · exact h.symm
    exact G.reachable_of_mem_ends (Set.mem_insert e {f}) (hends g hg ▸ hug)
      (hends g' hg' ▸ hvg')

/-- The spanning subgraph with edge set `S` is fragile: deleting the edges of any cycle
contained in `S` disconnects it. -/
def IsFragileOn (S : Set E) : Prop :=
  ∀ D ⊆ S, G.IsCycle D → ¬(G.adjGraph (S \ D)).Connected

theorem isFragileOn_univ_iff : G.IsFragileOn Set.univ ↔ G.IsFragile := by
  simp only [IsFragileOn, IsFragile, Set.subset_univ, true_imp_iff, Set.compl_eq_univ_sdiff]

theorem IsFragileOn.mono {G : LooplessMultigraph V E} {S S' : Set E} (h : G.IsFragileOn S)
    (hS : S' ⊆ S) :
    G.IsFragileOn S' := fun D hD hcyc hconn =>
  h D (hD.trans hS) hcyc (hconn.mono (G.adjGraph_mono (Set.sdiff_subset_sdiff_left hS)))

end LooplessMultigraph

end ThreeDecomposition

/-!
## Removing one edge of a parallel pair
-/

namespace ThreeDecomposition

open SimpleGraph

namespace LooplessMultigraph

variable {V E : Type*} (G : LooplessMultigraph V E)

theorem adjGraph_diff_singleton_of_ends_eq {S : Set E} {e f : E} (he : e ∈ S) (hef : e ≠ f)
    (hends : G.ends e = G.ends f) : G.adjGraph (S \ {f}) = G.adjGraph S := by
  refine le_antisymm (G.adjGraph_mono Set.sdiff_subset) fun x y ⟨g, hg, hgxy⟩ => ?_
  by_cases hgf : g = f
  · subst hgf
    exact ⟨e, ⟨he, hef⟩, hends.trans hgxy⟩
  · exact ⟨g, ⟨hg, hgf⟩, hgxy⟩

variable {G} {S : Set E} {e f : E}

/-- The ends of a parallel pair are separated by deleting the pair. -/
theorem not_reachable_diff_pair (hconn : (G.adjGraph S).Connected) (hfrag : G.IsFragileOn S)
    (he : e ∈ S) (hf : f ∈ S) (hef : e ≠ f) (hends : G.ends e = G.ends f) {u v : V}
    (huv : G.ends e = s(u, v)) : ¬(G.adjGraph (S \ {e, f})).Reachable u v := by
  intro hr
  refine hfrag {e, f} (Set.insert_subset he (Set.singleton_subset_iff.2 hf))
    (G.isCycle_pair hef hends) (connected_of_forall_adj hconn fun x y ⟨g, hg, hgxy⟩ => ?_)
  by_cases hgef : g ∈ ({e, f} : Set E)
  · have hg' : G.ends g = s(u, v) := by
      rcases hgef with rfl | rfl
      · exact huv
      · exact hends ▸ huv
    rw [hg', Sym2.eq_iff] at hgxy
    rcases hgxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hr
    · exact hr.symm
  · exact Adj.reachable ⟨g, ⟨hg, hgef⟩, hgxy⟩

theorem false_of_four_mem_of_ncard_le_three {s : Set E} [Finite E] (h : s.ncard ≤ 3) {a b c d : E}
    (ha : a ∈ s) (hb : b ∈ s) (hc : c ∈ s) (hd : d ∈ s) (hab : a ≠ b) (hac : a ≠ c)
    (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) : False := by
  have hsub : ({a, b, c, d} : Set E) ⊆ s := by
    simp only [Set.insert_subset_iff, Set.singleton_subset_iff]
    exact ⟨ha, hb, hc, hd⟩
  have h4 : ({a, b, c, d} : Set E).ncard = 4 := by
    rw [Set.ncard_insert_of_notMem, Set.ncard_insert_of_notMem, Set.ncard_pair hcd] <;>
      simp [*]
  have := Set.ncard_le_ncard hsub
  omega

/-- In `S \ {f}`, every edge at an end `u` of `e` is a bridge. -/
theorem not_connected_diff_of_mem_ends [Finite E] (hconn : (G.adjGraph S).Connected)
    (hdeg : ∀ v, (G.incidentIn S v).ncard ≤ 3) (hfrag : G.IsFragileOn S)
    (he : e ∈ S) (hf : f ∈ S) (hef : e ≠ f) (hends : G.ends e = G.ends f) {u v : V}
    (huv : G.ends e = s(u, v)) {g : E} (hg : g ∈ S \ {f}) (hug : u ∈ G.ends g) :
    ¬(G.adjGraph ((S \ {f}) \ {g})).Connected := by
  have hsep := not_reachable_diff_pair hconn hfrag he hf hef hends huv
  by_cases hge : g = e
  · subst hge
    intro hc
    refine hsep ?_
    have : (S \ {f}) \ {g} = S \ {g, f} := by
      ext x
      simp only [Set.mem_sdiff, Set.mem_singleton_iff, Set.mem_insert_iff]
      tauto
    rw [this] at hc
    exact hc.preconnected u v
  obtain ⟨w, hw⟩ := Sym2.mem_iff_exists.1 hug
  have hgf : g ≠ f := hg.2
  set K := G.adjGraph (S \ {e, f})
  have hclosed : ∀ x y, (G.adjGraph ((S \ {f}) \ {g})).Adj x y →
      x ∈ insert u {z | K.Reachable v z} → y ∈ insert u {z | K.Reachable v z} := by
    rintro x y ⟨h, ⟨⟨hhS, hhf⟩, hhg⟩, hxy⟩ hx
    by_cases hhe : h = e
    · subst hhe
      rw [huv, Sym2.eq_iff] at hxy
      rcases hxy with ⟨-, hy⟩ | ⟨hy, -⟩
      · exact Or.inr (hy ▸ Reachable.refl _)
      · exact Or.inl hy.symm
    have hK : K.Adj x y := ⟨h, ⟨hhS, by rintro (h' | h') <;> contradiction⟩, hxy⟩
    rcases hx with rfl | hx
    · exfalso
      have hxh : x ∈ G.ends h := hxy ▸ Sym2.mem_mk_left x y
      have hxe : x ∈ G.ends e := huv ▸ Sym2.mem_mk_left x v
      have hxf : x ∈ G.ends f := hends ▸ hxe
      exact false_of_four_mem_of_ncard_le_three (hdeg x) ⟨hhS, hxh⟩ ⟨he, hxe⟩ ⟨hf, hxf⟩
        ⟨hg.1, hug⟩ hhe hhf hhg hef (Ne.symm hge) (Ne.symm hgf)
    · exact Or.inr (Reachable.trans hx hK.reachable)
  intro hc
  have hwmem := mem_of_reachable_of_closed hclosed (hc.preconnected u w) (Set.mem_insert u _)
  rcases hwmem with rfl | hvw
  · exact G.ne_of_ends_eq hw rfl
  · have hKgw : K.Adj w u :=
      ⟨g, ⟨hg.1, by rintro (h' | h') <;> contradiction⟩, hw.trans Sym2.eq_swap⟩
    exact hsep (hvw.trans hKgw.reachable).symm

/-- `S \ {f}` keeps connectivity, the degree bound and fragility. -/
theorem parallel_diff_hypotheses [Finite E] (hconn : (G.adjGraph S).Connected)
    (hdeg : ∀ v, (G.incidentIn S v).ncard ≤ 3) (hfrag : G.IsFragileOn S)
    (he : e ∈ S) (hef : e ≠ f) (hends : G.ends e = G.ends f) :
    (G.adjGraph (S \ {f})).Connected ∧ (∀ v, (G.incidentIn (S \ {f}) v).ncard ≤ 3) ∧
      G.IsFragileOn (S \ {f}) := by
  refine ⟨?_, fun v => (Set.ncard_le_ncard (G.incidentIn_mono Set.sdiff_subset v)).trans (hdeg v),
    hfrag.mono Set.sdiff_subset⟩
  rw [G.adjGraph_diff_singleton_of_ends_eq he hef hends]
  exact hconn

/-- A tree–matching decomposition of `S \ {f}` extends to one of `S` by adding `f` to the
matching. -/
theorem parallel_extend [Finite E] (hconn : (G.adjGraph S).Connected)
    (hdeg : ∀ v, (G.incidentIn S v).ncard ≤ 3) (hfrag : G.IsFragileOn S)
    (he : e ∈ S) (hf : f ∈ S) (hef : e ≠ f) (hends : G.ends e = G.ends f) {T M : Set E}
    (hT : G.IsSpanningTree T) (hM : G.IsMatching M) (hTM : Disjoint T M)
    (hunion : T ∪ M = S \ {f}) :
    G.IsSpanningTree T ∧ G.IsMatching (insert f M) ∧ Disjoint T (insert f M) ∧
      T ∪ insert f M = S := by
  obtain ⟨a, b, -, hab⟩ := G.exists_ends_eq e
  have hcover : ∀ x ∈ G.ends e, ∀ g ∈ M, x ∉ G.ends g := by
    intro x hx g hgM hxg
    have hgS : g ∈ S \ {f} := hunion.subset (Or.inr hgM)
    have hgT : g ∉ T := fun hgT => Set.disjoint_left.1 hTM hgT hgM
    have hTsub : T ⊆ (S \ {f}) \ {g} := fun t ht =>
      ⟨hunion.subset (Or.inl ht), fun htg => hgT (htg ▸ ht)⟩
    have hc := hT.connected.mono (G.adjGraph_mono hTsub)
    rw [hab, Sym2.mem_iff] at hx
    rcases hx with rfl | rfl
    · exact not_connected_diff_of_mem_ends hconn hdeg hfrag he hf hef hends hab hgS hxg hc
    · exact not_connected_diff_of_mem_ends hconn hdeg hfrag he hf hef hends
        (hab.trans Sym2.eq_swap) hgS hxg hc
  refine ⟨hT, fun x => ?_, ?_, ?_⟩
  · by_cases hx : x ∈ G.ends f
    · refine (Set.subsingleton_singleton (a := f)).anti fun g ⟨hg, hxg⟩ => ?_
      rcases hg with rfl | hg
      · rfl
      · exact absurd hxg (hcover x (hends ▸ hx) g hg)
    · refine (hM x).anti fun g ⟨hg, hxg⟩ => ⟨?_, hxg⟩
      rcases hg with rfl | hg
      · exact absurd hxg hx
      · exact hg
  · refine Set.disjoint_left.2 fun g hgT hg => ?_
    rcases hg with hgf | hg
    · exact (hunion.subset (Or.inl hgT) : g ∈ S \ {f}).2 hgf
    · exact Set.disjoint_left.1 hTM hgT hg
  · rw [Set.union_insert, hunion, Set.insert_sdiff_singleton, Set.insert_eq_of_mem hf]

end LooplessMultigraph

end ThreeDecomposition

/-!
## Small multigraph examples (theta graph and digon)
-/

namespace ThreeDecomposition

open SimpleGraph

namespace LooplessMultigraph

theorem mem_ends_zero_one (x : Fin 2) : x ∈ s((0 : Fin 2), 1) := by
  fin_cases x <;> simp

/-- Two vertices joined by three parallel edges. -/
def theta : LooplessMultigraph (Fin 2) (Fin 3) where
  ends _ := s(0, 1)
  loopless _ := by simp

/-- Two vertices joined by two parallel edges. -/
def digon : LooplessMultigraph (Fin 2) (Fin 2) where
  ends _ := s(0, 1)
  loopless _ := by simp

theorem theta_connected : theta.Connected :=
  (connected_iff _).2 ⟨fun x y => theta.reachable_of_mem_ends (Set.mem_univ 0)
    (mem_ends_zero_one x) (mem_ends_zero_one y), inferInstance⟩

theorem theta_degree (x : Fin 2) : theta.degree x = 3 := by
  have : theta.incidentIn Set.univ x = Set.univ :=
    Set.eq_univ_of_forall fun _ => ⟨Set.mem_univ _, mem_ends_zero_one x⟩
  rw [degree_eq, this, Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin]

theorem theta_isCycle_pair : theta.IsCycle {0, 1} :=
  theta.isCycle_pair (by decide) rfl

theorem theta_isSpanningTree : theta.IsSpanningTree {0} := by
  refine ⟨Set.injOn_singleton _ _, isTree_iff_connected_and_card.2 ⟨?_, ?_⟩⟩
  · exact (connected_iff _).2 ⟨fun x y => theta.reachable_of_mem_ends (Set.mem_singleton 0)
      (mem_ends_zero_one x) (mem_ends_zero_one y), inferInstance⟩
  · rw [Nat.card_coe_set_eq, edgeSet_adjGraph, Set.image_singleton, Set.ncard_singleton]
    simp

theorem theta_not_isSpanningTree_pair : ¬theta.IsSpanningTree {0, 1} := fun h =>
  absurd (h.1 (x₁ := 0) (x₂ := 1) (by simp) (by simp) rfl) (by decide)

theorem theta_not_isFragile : ¬theta.IsFragile := fun h =>
  h {0, 1} theta_isCycle_pair <| (connected_iff _).2
    ⟨fun x y => theta.reachable_of_mem_ends (e := 2) (by simp)
      (mem_ends_zero_one x) (mem_ends_zero_one y), inferInstance⟩

theorem isMatching_empty {V E : Type*} (G : LooplessMultigraph V E) : G.IsMatching ∅ :=
  fun _ => Set.subsingleton_empty.anti fun _ he => he.1

theorem theta_not_isMatching_pair : ¬theta.IsMatching {0, 1} := fun h =>
  absurd (h 0 (x := 0) (y := 1) ⟨by simp, mem_ends_zero_one 0⟩ ⟨by simp, mem_ends_zero_one 0⟩)
    (by decide)

example : ∃ T C M : Set (Fin 3), theta.IsSpanningTree T ∧ theta.IsTwoRegular C ∧
    theta.IsMatching M ∧ Disjoint T C ∧ Disjoint T M ∧ Disjoint C M ∧
    T ∪ C ∪ M = Set.univ := by
  refine ⟨{0}, {1, 2}, ∅, theta_isSpanningTree,
    (theta.isCycle_pair (e := 1) (f := 2) (by decide) rfl).2.1,
    isMatching_empty _, by simp, by simp, by simp, ?_⟩
  ext e
  fin_cases e <;> simp

theorem digon_connected : digon.Connected :=
  (connected_iff _).2 ⟨fun x y => digon.reachable_of_mem_ends (Set.mem_univ 0)
    (mem_ends_zero_one x) (mem_ends_zero_one y), inferInstance⟩

theorem digon_degree (x : Fin 2) : digon.degree x = 2 := by
  have : digon.incidentIn Set.univ x = Set.univ :=
    Set.eq_univ_of_forall fun _ => ⟨Set.mem_univ _, mem_ends_zero_one x⟩
  rw [degree_eq, this, Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin]

theorem digon_isFragile : digon.IsFragile := by
  intro F hF hconn
  have hF0 : digon.incidentIn F 0 = F := by
    ext e
    exact ⟨fun he => he.1, fun he => ⟨he, mem_ends_zero_one 0⟩⟩
  have hFuniv : F = Set.univ := by
    have h2 := hF.2.1 0
    rw [hF0] at h2
    rcases h2 with h2 | h2
    · exact absurd ((Set.ncard_pos).2 hF.1) (by omega)
    · exact Set.eq_of_subset_of_ncard_le (Set.subset_univ F)
        (by rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin, h2])
  subst hFuniv
  have hclosed : ∀ x y, (digon.adjGraph Set.univᶜ).Adj x y →
      x ∈ ({0} : Set (Fin 2)) → y ∈ ({0} : Set (Fin 2)) :=
    fun _ _ ⟨e, he, _⟩ => absurd (Set.mem_univ e) he
  have : (1 : Fin 2) ∈ ({0} : Set (Fin 2)) :=
    mem_of_reachable_of_closed hclosed (hconn.preconnected 0 1) rfl
  exact absurd this (by decide)

example : ∃ T M : Set (Fin 2), digon.IsSpanningTree T ∧ digon.IsMatching M ∧ M.Nonempty ∧
    Disjoint T M ∧ T ∪ M = Set.univ := by
  refine ⟨{0}, {1}, ⟨Set.injOn_singleton _ _, isTree_iff_connected_and_card.2 ⟨?_, ?_⟩⟩,
    fun v => Set.subsingleton_singleton.anti fun _ he => he.1, Set.singleton_nonempty 1,
    by simp, ?_⟩
  · exact (connected_iff _).2 ⟨fun x y => digon.reachable_of_mem_ends (Set.mem_singleton 0)
      (mem_ends_zero_one x) (mem_ends_zero_one y), inferInstance⟩
  · rw [Nat.card_coe_set_eq, edgeSet_adjGraph, Set.image_singleton, Set.ncard_singleton]
    simp
  · ext e
    fin_cases e <;> simp

end LooplessMultigraph

end ThreeDecomposition

/-!
## Edge sets without parallel edges
-/

namespace ThreeDecomposition

open SimpleGraph

universe u

namespace LooplessMultigraph

section

variable {V E : Type*} {G : LooplessMultigraph V E} {S : Set E}

/-- The edges of `S` lying on a cycle of `G.adjGraph S` form a cycle of `G`. -/
theorem isCycle_of_walk (hinj : Set.InjOn G.ends S) {x : V} {p : (G.adjGraph S).Walk x x}
    (hp : p.IsCycle) : G.IsCycle {e | e ∈ S ∧ G.ends e ∈ p.edges} := by
  set D := {e | e ∈ S ∧ G.ends e ∈ p.edges}
  have hadj : ∀ a b, (G.adjGraph D).Adj a b ↔ s(a, b) ∈ p.edges := by
    intro a b
    constructor
    · rintro ⟨e, ⟨-, he⟩, hab⟩
      exact hab ▸ he
    · intro h
      obtain ⟨e, he, hab⟩ := p.edges_subset_edgeSet h
      exact ⟨e, ⟨he, hab ▸ h⟩, hab⟩
  have hnbr : ∀ v, (G.adjGraph D).neighborSet v = p.toSubgraph.neighborSet v := by
    intro v
    ext w
    exact (hadj v w).trans Walk.adj_toSubgraph_iff_mem_edges.symm
  refine ⟨?_, fun v => ?_, fun a b ⟨e, he, hae⟩ ⟨f, hf, hbf⟩ => ?_⟩
  · obtain ⟨e, he⟩ := (hadj x p.snd).2
      (Walk.adj_toSubgraph_iff_mem_edges.1 (p.toSubgraph_adj_snd hp.not_nil))
    exact ⟨e, he.1⟩
  · rw [ncard_incidentIn_eq G (hinj.mono fun e he => he.1), hnbr]
    by_cases hv : v ∈ p.support
    · exact Or.inr (hp.ncard_neighborSet_toSubgraph_eq_two hv)
    · left
      rw [Set.eq_empty_of_forall_notMem (s := p.toSubgraph.neighborSet v)
        fun w hw => hv (Walk.mem_support_of_adj_toSubgraph hw), Set.ncard_empty]
  · have hsupp : ∀ y, ∀ g ∈ D, y ∈ G.ends g → y ∈ p.support := by
      intro y g hg hyg
      obtain ⟨z, hz⟩ := Sym2.mem_iff_exists.1 hyg
      exact p.fst_mem_support_of_mem_edges (hz ▸ hg.2)
    have hreach : ∀ y ∈ p.support, (G.adjGraph D).Reachable x y := fun y hy =>
      reachable_of_mem_support p (fun d hd => by
        induction d using Sym2.ind with
        | _ c c' => exact (hadj c c').2 hd) hy
    exact (hreach a (hsupp a e he hae)).symm.trans (hreach b (hsupp b f hf hbf))

/-- Without parallel edges, the spanning subgraph with edge set `S` is fragile as a simple
graph. -/
theorem isFragile_adjGraph (hinj : Set.InjOn G.ends S) (hfrag : G.IsFragileOn S) :
    ThreeDecomposition.IsFragile (G.adjGraph S) := by
  intro x p hp hconn
  refine hfrag _ (fun e he => he.1) (isCycle_of_walk hinj hp) ?_
  convert hconn using 1
  ext a b
  simp only [adjGraph, Set.mem_sdiff, Set.mem_ofPred_eq, not_and, deleteEdges_adj]
  constructor
  · rintro ⟨e, ⟨he, hep⟩, hab⟩
    exact ⟨⟨e, he, hab⟩, hab ▸ hep he⟩
  · rintro ⟨⟨e, he, hab⟩, hp⟩
    exact ⟨e, ⟨he, fun _ => hab ▸ hp⟩, hab⟩

end

/-- Without parallel edges, Theorem 1.4 decomposes `S` into a spanning tree and a matching. -/
theorem exists_isSpanningTree_isMatching_of_injOn (h : FragileDecompositionTheorem.{u})
    {V : Type u} {E : Type*} [Finite V] [Finite E] {G : LooplessMultigraph V E} {S : Set E}
    (hinj : Set.InjOn G.ends S) (hconn : (G.adjGraph S).Connected)
    (hdeg : ∀ v, (G.incidentIn S v).ncard ≤ 3) (hfrag : G.IsFragileOn S) :
    ∃ T M : Set E, G.IsSpanningTree T ∧ G.IsMatching M ∧ Disjoint T M ∧ T ∪ M = S := by
  classical
  have := Fintype.ofFinite V
  obtain ⟨T, M, hTH, hT, hM, hTM, hunion⟩ := h V (G.adjGraph S) hconn
    (isFragile_adjGraph hinj hfrag) fun v => (G.degree_adjGraph_le S v).trans (hdeg v)
  refine ⟨{e | e ∈ S ∧ G.ends e ∈ T.edgeSet}, {e | e ∈ S ∧ G.ends e ∈ M.edgeSet},
    ⟨hinj.mono fun e he => he.1, ?_⟩, ?_, ?_, ?_⟩
  · convert hT using 1
    ext a b
    constructor
    · rintro ⟨e, ⟨-, he⟩, hab⟩
      rwa [hab] at he
    · intro hab
      obtain ⟨e, he, heab⟩ := hTH hab
      exact ⟨e, ⟨he, heab ▸ hab⟩, heab⟩
  · intro v e ⟨⟨he, heM⟩, hve⟩ f ⟨⟨hf, hfM⟩, hvf⟩
    rw [G.ends_eq_otherEnd hve] at heM
    rw [G.ends_eq_otherEnd hvf] at hfM
    have hvM : v ∈ M.verts := M.edge_vert heM
    have hw : G.otherEnd e v = G.otherEnd f v :=
      (hM hvM).unique (Subgraph.mem_edgeSet.1 heM) (Subgraph.mem_edgeSet.1 hfM)
    refine hinj he hf ?_
    rw [G.ends_eq_otherEnd hve, G.ends_eq_otherEnd hvf, hw]
  · exact Set.disjoint_left.2 fun e ⟨_, heT⟩ ⟨_, heM⟩ => Set.disjoint_left.1 hTM heT heM
  · ext e
    simp only [Set.mem_union, Set.mem_ofPred_eq]
    constructor
    · rintro (⟨he, -⟩ | ⟨he, -⟩) <;> exact he
    · intro he
      have := hunion.symm.subset (G.ends_mem_edgeSet he)
      rcases this with h' | h'
      · exact Or.inl ⟨he, h'⟩
      · exact Or.inr ⟨he, h'⟩

end LooplessMultigraph

end ThreeDecomposition

/-!
## Corollary 1.5: fragile subcubic loopless multigraphs
-/

namespace ThreeDecomposition

open SimpleGraph

universe u

namespace LooplessMultigraph

/-- Theorem 1.4 for loopless multigraphs, stated for the spanning subgraph with edge set `S`:
if it is connected and fragile and every vertex meets at most three edges of `S`, then `S` is
the disjoint union of a spanning tree and a matching. -/
theorem exists_isSpanningTree_isMatching (h : FragileDecompositionTheorem.{u})
    {V : Type u} {E : Type*} [Finite V] [Finite E] (G : LooplessMultigraph V E) (S : Set E)
    (hconn : (G.adjGraph S).Connected) (hdeg : ∀ v, (G.incidentIn S v).ncard ≤ 3)
    (hfrag : G.IsFragileOn S) :
    ∃ T M : Set E, G.IsSpanningTree T ∧ G.IsMatching M ∧ Disjoint T M ∧ T ∪ M = S := by
  induction hn : S.ncard using Nat.strong_induction_on generalizing S with
  | _ n ih =>
  by_cases hinj : Set.InjOn G.ends S
  · exact exists_isSpanningTree_isMatching_of_injOn h hinj hconn hdeg hfrag
  obtain ⟨e, he, f, hf, hends, hef⟩ : ∃ e ∈ S, ∃ f ∈ S, G.ends e = G.ends f ∧ e ≠ f := by
    simpa [Set.InjOn] using hinj
  obtain ⟨hconn', hdeg', hfrag'⟩ := parallel_diff_hypotheses hconn hdeg hfrag he hef hends
  obtain ⟨T, M, hT, hM, hTM, hunion⟩ :=
    ih _ (hn ▸ Set.ncard_sdiff_singleton_lt_of_mem hf) (S \ {f}) hconn' hdeg' hfrag' rfl
  obtain ⟨-, hM', hTM', hunion'⟩ :=
    parallel_extend hconn hdeg hfrag he hf hef hends hT hM hTM hunion
  exact ⟨T, insert f M, hT, hM', hTM', hunion'⟩

end LooplessMultigraph

end ThreeDecomposition

/-!
## Corollary 4.1 (2DC) and Theorem 1.2 (3DC)
-/

namespace ThreeDecomposition

open SimpleGraph

universe u v

namespace LooplessMultigraph

variable {V E : Type*} (G : LooplessMultigraph V E)

theorem isTwoRegular_union [Finite E] (hdeg : ∀ x, G.degree x ≤ 3) {C D : Set E}
    (hC : G.IsTwoRegular C) (hD : G.IsTwoRegular D) (hCD : Disjoint C D) :
    G.IsTwoRegular (C ∪ D) := by
  intro x
  have hdisj : Disjoint (G.incidentIn C x) (G.incidentIn D x) :=
    Set.disjoint_left.2 fun e he he' => Set.disjoint_left.1 hCD he.1 he'.1
  have hle : (G.incidentIn C x ∪ G.incidentIn D x).ncard ≤ 3 :=
    (Set.ncard_le_ncard (Set.union_subset (G.incidentIn_mono (Set.subset_univ C) x)
      (G.incidentIn_mono (Set.subset_univ D) x))).trans (hdeg x)
  rw [Set.ncard_union_eq hdisj] at hle
  rw [G.incidentIn_union, Set.ncard_union_eq hdisj]
  rcases hC x with h1 | h1 <;> rcases hD x with h2 | h2 <;> omega

end LooplessMultigraph

open LooplessMultigraph

/-- Theorem 1.4 implies the 2-Decomposition Conjecture. -/
theorem twoDecompositionConjecture_of_fragileDecomposition
    (h : FragileDecompositionTheorem.{u}) : TwoDecompositionConjecture.{u, v} := by
  intro V E _ _ G hconn hdeg hfrag
  obtain ⟨T, M, hT, hM, hTM, hunion⟩ := exists_isSpanningTree_isMatching h G Set.univ hconn
    (fun x => by rcases hdeg x with h | h <;> rw [← degree_eq] <;> omega)
    ((isFragileOn_univ_iff G).2 hfrag)
  refine ⟨T, M, hT, hM, Set.nonempty_iff_ne_empty.2 ?_, hTM, hunion⟩
  rintro rfl
  rw [Set.union_empty] at hunion
  subst hunion
  have htree := hT.ncard_add_one
  rw [Set.ncard_univ, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card] at htree
  have hsum : ∑ _x : V, 2 ≤ ∑ x, G.degree x :=
    Finset.sum_le_sum fun x _ => by rcases hdeg x with h | h <;> omega
  rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, G.sum_degree] at hsum
  omega

/-- Theorem 1.4 implies the 3-Decomposition Conjecture. -/
theorem threeDecompositionConjecture_of_fragileDecomposition
    (h : FragileDecompositionTheorem.{u}) : ThreeDecompositionConjecture.{u, v} := by
  intro V E _ _ G hconn hdeg
  obtain ⟨C, ⟨hC, hCconn⟩, hCmax⟩ :=
    Set.exists_max_image {C : Set E | G.IsTwoRegular C ∧ (G.adjGraph Cᶜ).Connected} Set.ncard
      (Set.toFinite _) ⟨∅, G.isTwoRegular_empty, by rwa [Set.compl_empty]⟩
  have hdegC : ∀ x, (G.incidentIn Cᶜ x).ncard ≤ 3 := fun x =>
    (Set.ncard_le_ncard (G.incidentIn_mono (Set.subset_univ _) x)).trans (hdeg x).le
  have hfragC : G.IsFragileOn Cᶜ := by
    intro D hDC hD hDconn
    have hCD : Disjoint C D := Set.subset_compl_iff_disjoint_left.1 hDC
    have hmax := hCmax (C ∪ D)
      ⟨G.isTwoRegular_union (fun x => (hdeg x).le) hC hD.2.1 hCD,
        by rwa [Set.compl_union, ← Set.sdiff_eq]⟩
    rw [Set.ncard_union_eq hCD] at hmax
    have := (Set.ncard_pos (Set.toFinite D)).2 hD.1
    omega
  obtain ⟨T, M, hT, hM, hTM, hunion⟩ :=
    exists_isSpanningTree_isMatching h G Cᶜ hCconn hdegC hfragC
  have hTC : T ⊆ Cᶜ := hunion ▸ Set.subset_union_left
  have hMC : M ⊆ Cᶜ := hunion ▸ Set.subset_union_right
  refine ⟨T, C, M, hT, hC, hM, Set.subset_compl_iff_disjoint_right.1 hTC, hTM,
    Set.subset_compl_iff_disjoint_left.1 hMC, ?_⟩
  rw [Set.union_right_comm, hunion, Set.compl_union_self]

end ThreeDecomposition
