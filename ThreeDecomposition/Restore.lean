import ThreeDecomposition.MatchingComplement.Normalization
import ThreeDecomposition.Reduction
import ThreeDecomposition.MatchingComplement.TerminalCriterion
import ThreeDecomposition.FirstEntry
import ThreeDecomposition.Induction

/-!
# Restoring a suppressed terminal (Section 3.4)

This module proves `restorationLift`, the inductive step `k ≥ 3` of Theorem 1.3: given a
terminal `s` with non-adjacent degree-three neighbours `a, b` covered by a comparison matching
`N`, a solution matching of `J = suppress G s a b` is restored to `G` via Cases 1–4 of
Section 3.4, using Lemma 3.3 (`first_entry_reachable`) and the parity argument in Cases 2 and 4.

## Restoring a matching of the suppressed graph

Let `J = suppress G s a b` and let `M` be a matching of `J`.  It is turned into a matching of `G`
with the same number of edges:
* if the new edge `ab` is not in `M`, `imageSubgraph G M Subtype.val` keeps `M` and exposes `s`;
* if `ab ∈ M`, with `{p, t} = {a, b}`, `imageSubgraph G M (redirect s p)` replaces `ab` by `st`,
  covering `s` and exposing `p`.
-/

namespace ThreeDecomposition

open SimpleGraph

variable {V : Type*}

section Redirect

variable [DecidableEq V] {s p : V}

/-- The vertex map `{v // v ≠ s} → V` that sends `p` to `s` and fixes every other vertex. -/
def redirect (s p : V) (x : {v // v ≠ s}) : V :=
  if (x : V) = p then s else x

lemma redirect_of_eq {x : {v // v ≠ s}} (hx : (x : V) = p) : redirect s p x = s := by
  simp [redirect, hx]

lemma redirect_of_ne {x : {v // v ≠ s}} (hx : (x : V) ≠ p) : redirect s p x = x := by
  simp [redirect, hx]

lemma redirect_injective (s p : V) : Function.Injective (redirect s p) := by
  intro x y hxy
  by_cases hx : (x : V) = p <;> by_cases hy : (y : V) = p
  · exact Subtype.ext (hx.trans hy.symm)
  · rw [redirect_of_eq hx, redirect_of_ne hy] at hxy
    exact absurd hxy.symm y.2
  · rw [redirect_of_ne hx, redirect_of_eq hy] at hxy
    exact absurd hxy x.2
  · rw [redirect_of_ne hx, redirect_of_ne hy] at hxy
    exact Subtype.ext hxy

lemma eq_of_redirect_eq {x y : {v // v ≠ s}} (h : redirect s p x = y) : x = y := by
  by_cases hx : (x : V) = p
  · rw [redirect_of_eq hx] at h
    exact absurd h.symm y.2
  · rw [redirect_of_ne hx] at h
    exact Subtype.ext h

lemma redirect_ne_self (hp : p ≠ s) (x : {v // v ≠ s}) : redirect s p x ≠ p := by
  by_cases hx : (x : V) = p
  · rw [redirect_of_eq hx]
    exact hp.symm
  · rwa [redirect_of_ne hx]

variable {G : SimpleGraph V} {H : SimpleGraph {v // v ≠ s}} {M : H.Subgraph}

lemma adj_of_imageSubgraph_redirect_adj {u v : {v // v ≠ s}}
    (huv : (imageSubgraph G M (redirect s p)).Adj u v) : M.Adj u v := by
  obtain ⟨-, u', v', huv', hu, hv⟩ := huv
  rwa [← eq_of_redirect_eq hu, ← eq_of_redirect_eq hv]

end Redirect

namespace IsSuppressible

variable {G : SimpleGraph V} {s a b : V} (h : IsSuppressible G s a b)
  {M : (suppress G s a b).Subgraph}
include h

/-! ### The new edge is not in the matching -/

section Keep

variable (hab : ¬M.Adj ⟨a, h.left_ne⟩ ⟨b, h.right_ne⟩)
include hab

lemma keep_adj {u v : {v // v ≠ s}} (huv : M.Adj u v) : G.Adj u v := by
  rcases h.suppress_adj_iff.1 huv.adj_sub with huv' | ⟨hu, hv⟩ | ⟨hu, hv⟩
  · exact huv'
  · obtain rfl : u = ⟨a, h.left_ne⟩ := Subtype.ext hu
    obtain rfl : v = ⟨b, h.right_ne⟩ := Subtype.ext hv
    exact absurd huv hab
  · obtain rfl : u = ⟨b, h.right_ne⟩ := Subtype.ext hu
    obtain rfl : v = ⟨a, h.left_ne⟩ := Subtype.ext hv
    exact absurd huv.symm hab

lemma ncard_edgeSet_keep :
    (imageSubgraph G M Subtype.val).edgeSet.ncard = M.edgeSet.ncard :=
  ncard_edgeSet_imageSubgraph Subtype.val_injective fun _ _ ↦ h.keep_adj hab

lemma notMem_verts_of_notMem_keep_verts (hM : M.IsMatching) {u : {v // v ≠ s}}
    (hu : (u : V) ∉ (imageSubgraph G M Subtype.val).verts) : u ∉ M.verts := by
  intro huM
  obtain ⟨w, huw, -⟩ := hM huM
  exact hu (map_mem_imageSubgraph_verts huw (h.keep_adj hab huw))

end Keep

/-! ### The new edge is in the matching -/

section Redirect

variable {p t : V} (hpt : IsSuppressible G s p t)
  (hMpt : M.Adj ⟨p, hpt.left_ne⟩ ⟨t, hpt.right_ne⟩)
include hpt hMpt

lemma adj_of_redirect : M.Adj ⟨a, h.left_ne⟩ ⟨b, h.right_ne⟩ := by
  rcases h.eq_or_eq_of_adj hpt.adj_left with rfl | rfl <;>
    rcases h.eq_or_eq_of_adj hpt.adj_right with rfl | rfl
  · exact absurd rfl hpt.ne
  · exact hMpt
  · exact hMpt.symm
  · exact absurd rfl hpt.ne

variable [DecidableEq V]

omit h in
lemma redirect_adj_self : (imageSubgraph G M (redirect s p)).Adj s t :=
  ⟨hpt.adj_right, _, _, hMpt, redirect_of_eq rfl,
    redirect_of_ne (x := ⟨t, hpt.right_ne⟩) hpt.ne.symm⟩

omit h in
lemma mem_redirect_verts_self : s ∈ (imageSubgraph G M (redirect s p)).verts :=
  (hpt.redirect_adj_self hMpt).fst_mem

variable (hM : M.IsMatching)
include hM

omit h in
/-- An edge of `M` that is an old edge of `G` is not affected by the redirection. -/
lemma redirect_eq_of_adj {u v : {v // v ≠ s}} (hG : G.Adj u v) (huv : M.Adj u v) :
    redirect s p u = u := by
  refine redirect_of_ne fun hu ↦ hpt.not_adj ?_
  obtain rfl : u = ⟨p, hpt.left_ne⟩ := Subtype.ext hu
  obtain rfl := hM.eq_of_adj_left huv hMpt
  exact hG

omit h in
lemma redirect_adj_of_adj {u v : {v // v ≠ s}} (hG : G.Adj u v) (huv : M.Adj u v) :
    (imageSubgraph G M (redirect s p)).Adj u v := by
  have := imageSubgraph_adj_of_adj (G := G) (φ := redirect s p) huv
  rw [hpt.redirect_eq_of_adj hMpt hM hG huv, hpt.redirect_eq_of_adj hMpt hM hG.symm huv.symm]
    at this
  exact this hG

lemma redirect_adj {u v : {v // v ≠ s}} (huv : M.Adj u v) :
    G.Adj (redirect s p u) (redirect s p v) := by
  by_cases hu : (u : V) = p
  · obtain rfl : u = ⟨p, hpt.left_ne⟩ := Subtype.ext hu
    obtain rfl := hM.eq_of_adj_left huv hMpt
    rw [redirect_of_eq hu, redirect_of_ne (x := ⟨t, hpt.right_ne⟩) hpt.ne.symm]
    exact hpt.adj_right
  by_cases hv : (v : V) = p
  · obtain rfl : v = ⟨p, hpt.left_ne⟩ := Subtype.ext hv
    obtain rfl := hM.eq_of_adj_right huv hMpt.symm
    rw [redirect_of_eq hv, redirect_of_ne (x := ⟨t, hpt.right_ne⟩) hpt.ne.symm]
    exact hpt.adj_right.symm
  rw [redirect_of_ne hu, redirect_of_ne hv]
  rcases h.suppress_adj_iff.1 huv.adj_sub with huv' | ⟨hua, hvb⟩ | ⟨hub, hva⟩
  · exact huv'
  · rcases h.eq_or_eq_of_adj hpt.adj_left with rfl | rfl
    · exact absurd hua hu
    · exact absurd hvb hv
  · rcases h.eq_or_eq_of_adj hpt.adj_left with rfl | rfl
    · exact absurd hva hv
    · exact absurd hub hu

lemma ncard_edgeSet_redirect :
    (imageSubgraph G M (redirect s p)).edgeSet.ncard = M.edgeSet.ncard :=
  ncard_edgeSet_imageSubgraph (redirect_injective s p) fun _ _ ↦ h.redirect_adj hpt hMpt hM

lemma notMem_verts_of_notMem_redirect_verts {u : {v // v ≠ s}}
    (hu : (u : V) ∉ (imageSubgraph G M (redirect s p)).verts) (hup : (u : V) ≠ p) :
    u ∉ M.verts := by
  intro huM
  obtain ⟨w, huw, -⟩ := hM huM
  have := map_mem_imageSubgraph_verts huw (h.redirect_adj hpt hMpt hM huw)
  rw [redirect_of_ne hup] at this
  exact hu this

end Redirect

/-! ### Transport of reachability -/

variable [DecidableEq V] [DecidableRel G.Adj] {M' : G.Subgraph}

/-- Residual reachability in the suppressed graph gives residual reachability in `G`, when the
matching `M'` of `G` contains no old edge outside `M` and, if `ab ∉ M`, neither `sa` nor `sb`. -/
theorem reachable_deletedMatching_of_suppress
    (hold : ∀ u v : {v // v ≠ s}, M'.Adj u v → M.Adj u v)
    (hnew : ¬M.Adj ⟨a, h.left_ne⟩ ⟨b, h.right_ne⟩ → ¬M'.Adj s a ∧ ¬M'.Adj s b)
    {u v : {v // v ≠ s}} (huv : (deletedMatching (suppress G s a b) M).Reachable u v) :
    (deletedMatching G M').Reachable u v := by
  refine reachable_map_of_adj Subtype.val (fun x y hxy ↦ ?_) huv
  obtain ⟨hJ, hM⟩ := deletedMatching_adj.1 hxy
  rcases h.suppress_adj_iff.1 hJ with hG | ⟨hx, hy⟩ | ⟨hx, hy⟩
  · exact (deletedMatching_adj.2 ⟨hG, fun h' ↦ hM (hold x y h')⟩).reachable
  · obtain rfl : x = ⟨a, h.left_ne⟩ := Subtype.ext hx
    obtain rfl : y = ⟨b, h.right_ne⟩ := Subtype.ext hy
    obtain ⟨hsa, hsb⟩ := hnew hM
    exact (deletedMatching_adj.2 ⟨h.adj_left.symm, fun h' ↦ hsa h'.symm⟩).reachable.trans
      (deletedMatching_adj.2 ⟨h.adj_right, hsb⟩).reachable
  · obtain rfl : x = ⟨b, h.right_ne⟩ := Subtype.ext hx
    obtain rfl : y = ⟨a, h.left_ne⟩ := Subtype.ext hy
    obtain ⟨hsa, hsb⟩ := hnew fun h' ↦ hM h'.symm
    exact (deletedMatching_adj.2 ⟨h.adj_right.symm, fun h' ↦ hsb h'.symm⟩).reachable.trans
      (deletedMatching_adj.2 ⟨h.adj_left, hsa⟩).reachable

/-- Residual reachability in `G` gives residual reachability in the suppressed graph after
collapsing `s` onto `t ∈ {a, b}`, when every old edge of `M` stays in `M'` and, if `ab ∈ M`,
the edge from `s` to the endpoint other than `t` lies in `M'`. -/
theorem reachable_retract_of_deletedMatching (t : {v // v ≠ s}) (ht : (t : V) = a ∨ (t : V) = b)
    (hold : ∀ u v : {v // v ≠ s}, G.Adj u v → M.Adj u v → M'.Adj u v)
    (hnew : ∀ r, G.Adj s r → r ≠ t → ¬M'.Adj s r → ¬M.Adj ⟨a, h.left_ne⟩ ⟨b, h.right_ne⟩)
    {x y : V} (hxy : (deletedMatching G M').Reachable x y) :
    (deletedMatching (suppress G s a b) M).Reachable (subtypeRetract t x)
      (subtypeRetract t y) := by
  refine (h.isCollapseMap_deleteEdges t ht (D := M'.edgeSet) (D' := M.edgeSet) ?_ ?_).reachable
    hxy
  · intro u v huv hM' hM
    exact hM' (Subgraph.mem_edgeSet.2 (hold u v huv (Subgraph.mem_edgeSet.1 hM)))
  · rintro u v hu hv ⟨r, hr, hrt, hrM⟩ hM
    obtain rfl : u = ⟨a, h.left_ne⟩ := Subtype.ext hu
    obtain rfl : v = ⟨b, h.right_ne⟩ := Subtype.ext hv
    exact hnew r hr hrt (fun h' ↦ hrM (Subgraph.mem_edgeSet.2 h')) (Subgraph.mem_edgeSet.1 hM)

end IsSuppressible

end ThreeDecomposition

/-!
## Completing the four restoration cases (`restorationLift`)

The four cases for the new edge `e = ab` are:
1. `e ∉ M` and `a ∈ c₀`: `M` is kept; the residual edge `ab` becomes the residual path
   `a - s - b`, so every terminal is reachable from `q`.
2. `e ∉ M` and `a ∉ c₀`: `M` is kept; `s` is exposed and not reachable from `q`.
3. `e ∈ M` and `p ∈ c₀` for an endpoint `p` of `e`: `e` is replaced by `st`, where `t` is the
   other endpoint; the residual edge `ps` attaches `s` to the component of `q`.
4. `e ∈ M` and `a, b ∉ c₀`: `e` is replaced by `sa`; the degree-three vertex `b` is exposed and
   not reachable from `q`.

Cases 1 and 3 conclude by Lemma 3.2 (`terminalSelectionStatement_of_reachable`); cases 2 and 4
by Lemma 3.3 (`terminalSelectionStatement_of_first_entry`) followed by the parity argument.
-/

namespace ThreeDecomposition

open SimpleGraph

universe u

section Finish

variable {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The resolution of the unsuccessful restoration cases.  Let `M` be a matching of target
size whose exposed vertices other than `x`, and whose terminals other than `s`, are residually
reachable from `q`, while `x` is not.  If `x` is covered by a matching `N` exposing only
terminals and covering `s`, then Lemma 3.3 and the parity argument solve the terminal selection
problem. -/
theorem terminalSelectionStatement_of_first_entry (h23 : Is23Graph G) {M N : G.Subgraph}
    (hM : M.IsMatching) (hN : N.IsMatching) (hsize : (M.edgeSet.ncard : ℤ) = cyclomaticNumber G)
    {q x s : V} (hxq : ¬(deletedMatching G M).Reachable q x) (hxM : x ∉ M.verts)
    (hxN : x ∈ N.verts) (hMexp : ∀ v, v ∉ M.verts → v ≠ x → (deletedMatching G M).Reachable q v)
    (hNexp : ∀ v, v ∉ N.verts → v ∈ terminals G) (hsN : s ∈ N.verts)
    (hterm : ∀ v ∈ terminals G, v ≠ s → (deletedMatching G M).Reachable q v) :
    TerminalSelectionStatement G (terminals G) := by
  obtain ⟨M', hM', hcard, hreach, hexp⟩ := first_entry_reachable G M N hM hN q x hxq hxM hxN
    hMexp fun v hv ↦ hterm v (hNexp v hv) fun hvs ↦ hv (hvs ▸ hsN)
  exact terminalSelectionStatement_of_all_but_one_terminal G h23 hM' (by rw [hcard]; exact hsize)
    ((deletedMatching G M').connectedComponentMk q) s
    (fun v hv ↦ mem_supp_mk_iff_reachable.2 (hexp v hv))
    fun v hv hvs ↦ mem_supp_mk_iff_reachable.2 (hreach v (hterm v hv hvs))

end Finish

namespace IsSuppressible

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
  {s a b : V} (h : IsSuppressible G s a b) (h23 : Is23Graph G)
  {M : (suppress G s a b).Subgraph} (hM : M.IsMatching)
  (hsize : (M.edgeSet.ncard : ℤ) = cyclomaticNumber G) {q : {v // v ≠ s}}
  (hT : ∀ v : {v // v ≠ s}, (v : V) ∈ terminals G →
    (deletedMatching (suppress G s a b) M).Reachable q v)
include h h23 hM hsize hT

section Keep

variable (hab : ¬M.Adj ⟨a, h.left_ne⟩ ⟨b, h.right_ne⟩)
include hab

/-- State 1: `ab ∉ M` and `a` lies in the residual component of `q`. -/
theorem restore_keep_of_reachable
    (haq : (deletedMatching (suppress G s a b) M).Reachable q ⟨a, h.left_ne⟩) :
    TerminalSelectionStatement G (terminals G) := by
  have hs : s ∉ (imageSubgraph G M Subtype.val).verts := notMem_imageSubgraph_verts fun w ↦ w.2
  have fwd {u v} (huv : (deletedMatching (suppress G s a b) M).Reachable u v) :
      (deletedMatching G (imageSubgraph G M Subtype.val)).Reachable u v :=
    h.reachable_deletedMatching_of_suppress
      (fun _ _ huv ↦ adj_of_imageSubgraph_adj Subtype.val_injective huv)
      (fun _ ↦ ⟨fun h' ↦ hs h'.fst_mem, fun h' ↦ hs h'.fst_mem⟩) huv
  refine terminalSelectionStatement_of_reachable h23
    (isMatching_imageSubgraph Subtype.val_injective hM)
    (by rw [h.ncard_edgeSet_keep hab]; exact hsize) q fun v hv ↦ ?_
  by_cases hvs : v = s
  · rw [hvs]
    exact (fwd haq).trans
      (deletedMatching_adj.2 ⟨h.adj_left.symm, fun h' ↦ hs h'.snd_mem⟩).reachable
  · exact fwd (hT ⟨v, hvs⟩ hv)

/-- State 2: `ab ∉ M` and `a` does not lie in the residual component of `q`; then `s` is the
only exposed vertex outside it. -/
theorem restore_keep_of_not_reachable
    (hE : ∀ v, v ∉ M.verts → (deletedMatching (suppress G s a b) M).Reachable q v)
    {N : G.Subgraph} (hN : N.IsMatching) (hNexp : ∀ x, x ∉ N.verts → x ∈ terminals G)
    (hsN : s ∈ N.verts)
    (haq : ¬(deletedMatching (suppress G s a b) M).Reachable q ⟨a, h.left_ne⟩) :
    TerminalSelectionStatement G (terminals G) := by
  have hs : s ∉ (imageSubgraph G M Subtype.val).verts := notMem_imageSubgraph_verts fun w ↦ w.2
  have fwd {u v} (huv : (deletedMatching (suppress G s a b) M).Reachable u v) :
      (deletedMatching G (imageSubgraph G M Subtype.val)).Reachable u v :=
    h.reachable_deletedMatching_of_suppress
      (fun _ _ huv ↦ adj_of_imageSubgraph_adj Subtype.val_injective huv)
      (fun _ ↦ ⟨fun h' ↦ hs h'.fst_mem, fun h' ↦ hs h'.fst_mem⟩) huv
  refine terminalSelectionStatement_of_first_entry G h23
    (isMatching_imageSubgraph Subtype.val_injective hM) hN
    (by rw [h.ncard_edgeSet_keep hab]; exact hsize) (q := q) (x := s) (fun hqs ↦ haq ?_) hs hsN
    (fun v hv hvs ↦ fwd (hE ⟨v, hvs⟩ (h.notMem_verts_of_notMem_keep_verts hab hM hv))) hNexp
    hsN fun v hv hvs ↦ fwd (hT ⟨v, hvs⟩ hv)
  have := h.reachable_retract_of_deletedMatching ⟨a, h.left_ne⟩ (Or.inl rfl)
    (fun _ _ hG huv ↦ imageSubgraph_adj_of_adj huv hG) (fun _ _ _ _ ↦ hab) hqs
  rwa [subtypeRetract_coe,
    subtypeRetract_of_neg (⟨a, h.left_ne⟩ : {v // v ≠ s}) (not_not.2 rfl)] at this

end Keep

section Redirect

variable {p t : V} (hpt : IsSuppressible G s p t) (hMpt : M.Adj ⟨p, hpt.left_ne⟩ ⟨t, hpt.right_ne⟩)
include hpt hMpt

/-- State 3: `ab ∈ M` and its endpoint `p` lies in the residual component of `q`; `ab` is
replaced by `st`. -/
theorem restore_redirect_of_reachable
    (hpq : (deletedMatching (suppress G s a b) M).Reachable q ⟨p, hpt.left_ne⟩) :
    TerminalSelectionStatement G (terminals G) := by
  have hp : p ∉ (imageSubgraph G M (redirect s p)).verts :=
    notMem_imageSubgraph_verts (redirect_ne_self hpt.left_ne)
  have fwd {u v} (huv : (deletedMatching (suppress G s a b) M).Reachable u v) :
      (deletedMatching G (imageSubgraph G M (redirect s p))).Reachable u v :=
    h.reachable_deletedMatching_of_suppress (fun _ _ huv ↦ adj_of_imageSubgraph_redirect_adj huv)
      (fun hab ↦ absurd (h.adj_of_redirect hpt hMpt) hab) huv
  refine terminalSelectionStatement_of_reachable h23
    (isMatching_imageSubgraph (redirect_injective s p) hM)
    (by rw [h.ncard_edgeSet_redirect hpt hMpt hM]; exact hsize) q fun v hv ↦ ?_
  by_cases hvs : v = s
  · rw [hvs]
    exact (fwd hpq).trans
      (deletedMatching_adj.2 ⟨hpt.adj_left.symm, fun h' ↦ hp h'.fst_mem⟩).reachable
  · exact fwd (hT ⟨v, hvs⟩ hv)

/-- State 4: `ab ∈ M` and its endpoint `p` does not lie in the residual component of `q`;
`ab` is replaced by `st`, and the cubic vertex `p` is the only exposed vertex outside the
component. -/
theorem restore_redirect_of_not_reachable
    (hE : ∀ v, v ∉ M.verts → (deletedMatching (suppress G s a b) M).Reachable q v)
    {N : G.Subgraph} (hN : N.IsMatching) (hNexp : ∀ x, x ∉ N.verts → x ∈ terminals G)
    (hsN : s ∈ N.verts) (hdeg : G.degree p = 3)
    (hpq : ¬(deletedMatching (suppress G s a b) M).Reachable q ⟨p, hpt.left_ne⟩) :
    TerminalSelectionStatement G (terminals G) := by
  have hp : p ∉ (imageSubgraph G M (redirect s p)).verts :=
    notMem_imageSubgraph_verts (redirect_ne_self hpt.left_ne)
  have hs := hpt.mem_redirect_verts_self (G := G) hMpt
  have fwd {u v} (huv : (deletedMatching (suppress G s a b) M).Reachable u v) :
      (deletedMatching G (imageSubgraph G M (redirect s p))).Reachable u v :=
    h.reachable_deletedMatching_of_suppress (fun _ _ huv ↦ adj_of_imageSubgraph_redirect_adj huv)
      (fun hab ↦ absurd (h.adj_of_redirect hpt hMpt) hab) huv
  have hpN : p ∈ N.verts := by
    by_contra hpN
    have h2 : G.degree p = 2 := hNexp p hpN
    omega
  refine terminalSelectionStatement_of_first_entry G h23
    (isMatching_imageSubgraph (redirect_injective s p) hM) hN
    (by rw [h.ncard_edgeSet_redirect hpt hMpt hM]; exact hsize) (q := q) (x := p)
    (fun hqp ↦ hpq ?_) hp hpN (fun v hv hvp ↦ ?_) hNexp hsN fun v hv hvs ↦ fwd (hT ⟨v, hvs⟩ hv)
  · have := h.reachable_retract_of_deletedMatching ⟨p, hpt.left_ne⟩
      (h.eq_or_eq_of_adj hpt.adj_left) (fun _ _ hG huv ↦ hpt.redirect_adj_of_adj hMpt hM hG huv)
      (fun r hr hrp hrM ↦ by
        rcases hpt.eq_or_eq_of_adj hr with rfl | rfl
        · exact absurd rfl hrp
        · exact absurd (hpt.redirect_adj_self hMpt) hrM) hqp
    rwa [subtypeRetract_coe,
      subtypeRetract_of_pos (⟨p, hpt.left_ne⟩ : {v // v ≠ s}) hpt.left_ne] at this
  · have hvs : v ≠ s := fun hvs ↦ hv (hvs ▸ hs)
    exact fwd (hE ⟨v, hvs⟩ (h.notMem_verts_of_notMem_redirect_verts hpt hMpt hM hv hvp))

end Redirect

end IsSuppressible

/-- **The inductive step of Theorem 1.3.**  Suppressing a terminal `s` with cubic, non-adjacent
neighbours `a` and `b`, covered by a comparison matching `N` that exposes only terminals, a
solution for the suppressed graph lifts to a solution for `G`. -/
theorem restorationLift : RestorationLift.{u} := by
  intro V _ _ G _ s a b N h23 h ha hb hN hNexp hsN hJ
  obtain ⟨M, hM, hsize, c₀, hS, hexp, -⟩ := hJ.exists_residual_tree_component
  rw [h.cyclomaticNumber_suppress] at hsize
  induction c₀ using ConnectedComponent.ind with
  | h q =>
  have hT : ∀ v : {v // v ≠ s}, (v : V) ∈ terminals G →
      (deletedMatching (suppress G s a b) M).Reachable q v := fun v hv ↦
    mem_supp_mk_iff_reachable.1 (hS ((h.mem_terminals_suppress_iff v).2 hv))
  have hE : ∀ v, v ∉ M.verts → (deletedMatching (suppress G s a b) M).Reachable q v :=
    fun v hv ↦ mem_supp_mk_iff_reachable.1 (hexp v hv)
  by_cases hab : M.Adj ⟨a, h.left_ne⟩ ⟨b, h.right_ne⟩
  · by_cases haq : (deletedMatching (suppress G s a b) M).Reachable q ⟨a, h.left_ne⟩
    · exact h.restore_redirect_of_reachable h23 hM hsize hT h hab haq
    by_cases hbq : (deletedMatching (suppress G s a b) M).Reachable q ⟨b, h.right_ne⟩
    · exact h.restore_redirect_of_reachable h23 hM hsize hT h.symm hab.symm hbq
    · exact h.restore_redirect_of_not_reachable h23 hM hsize hT h hab hE hN hNexp hsN ha haq
  · by_cases haq : (deletedMatching (suppress G s a b) M).Reachable q ⟨a, h.left_ne⟩
    · exact h.restore_keep_of_reachable h23 hM hsize hT hab haq
    · exact h.restore_keep_of_not_reachable h23 hM hsize hT hab hE hN hNexp hsN haq

end ThreeDecomposition
