import ThreeDecomposition.Basic.Definitions
import Mathlib.Combinatorics.SimpleGraph.CycleGraph

/-!
# Basic lemmas on `{2,3}`-graphs and bridgeless graphs

This module collects the elementary degree-sum consequences for `{2,3}`-graphs
(Section 3.1 of the paper), thin wrappers around Mathlib's bridge-and-cycle
characterization, and small sanity-check examples.

## Handshake-derived counting lemmas
-/

namespace ThreeDecomposition

open SimpleGraph
open scoped BigOperators

variable {V : Type*} [Fintype V]

def terminalFinset (G : SimpleGraph V) [DecidableRel G.Adj] : Finset V :=
  Finset.univ.filter (fun v => G.degree v = 2)

def cubicFinset (G : SimpleGraph V) [DecidableRel G.Adj] : Finset V :=
  Finset.univ.filter (fun v => G.degree v = 3)

lemma terminals_eq_terminalFinset (G : SimpleGraph V) [DecidableRel G.Adj] :
    (terminals G).toFinset = terminalFinset G := by
  ext v
  simp [terminals, terminalFinset]

lemma cubicVertices_eq_cubicFinset (G : SimpleGraph V) [DecidableRel G.Adj] :
    (cubicVertices G).toFinset = cubicFinset G := by
  ext v
  simp [cubicVertices, cubicFinset]

lemma terminal_cubic_disjoint (G : SimpleGraph V) [DecidableRel G.Adj] :
    Disjoint (terminalFinset G) (cubicFinset G) := by
  classical
  rw [Finset.disjoint_left]
  intro v h₂ h₃
  simp only [terminalFinset, cubicFinset, Finset.mem_filter, Finset.mem_univ,
    true_and] at h₂ h₃
  omega

lemma terminal_cubic_union [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : Is23Graph G) :
    terminalFinset G ∪ cubicFinset G = Finset.univ := by
  classical
  ext v
  simpa [terminalFinset, cubicFinset] using hG v

lemma degree_ge_two (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : Is23Graph G) (v : V) :
    2 ≤ G.degree v := by
  rcases hG v with h₂ | h₃ <;> omega

lemma terminal_cubic_card_add (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : Is23Graph G) :
    (terminalFinset G).card + (cubicFinset G).card = Fintype.card V := by
  classical
  have hdis := terminal_cubic_disjoint G
  have hun := terminal_cubic_union G hG
  have hc := Finset.card_union_of_disjoint hdis
  rw [hun] at hc
  simp only [Finset.card_univ] at hc
  exact hc.symm

lemma sum_degrees_eq_terminal_cubic (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : Is23Graph G) :
    (∑ v : V, G.degree v) =
      2 * (terminalFinset G).card + 3 * (cubicFinset G).card := by
  classical
  have hdis := terminal_cubic_disjoint G
  have hun := terminal_cubic_union G hG
  have hsum := Finset.sum_union hdis (f := fun v : V => G.degree v)
  rw [hun] at hsum
  rw [hsum]
  have hterm : (terminalFinset G).sum (fun v => G.degree v) =
      2 * (terminalFinset G).card := by
    calc
      (terminalFinset G).sum (fun v => G.degree v) =
          (terminalFinset G).sum (fun _ => (2 : ℕ)) := by
            apply Finset.sum_congr rfl
            intro v hv
            exact (Finset.mem_filter.mp hv).2
      _ = 2 * (terminalFinset G).card := by simp [Nat.mul_comm]
  have hcubic : (cubicFinset G).sum (fun v => G.degree v) =
      3 * (cubicFinset G).card := by
    calc
      (cubicFinset G).sum (fun v => G.degree v) =
          (cubicFinset G).sum (fun _ => (3 : ℕ)) := by
            apply Finset.sum_congr rfl
            intro v hv
            exact (Finset.mem_filter.mp hv).2
      _ = 3 * (cubicFinset G).card := by simp [Nat.mul_comm]
  rw [hterm, hcubic]

lemma edge_card_formula (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : Is23Graph G) :
    2 * G.edgeFinset.card =
      2 * (terminalFinset G).card + 3 * (cubicFinset G).card := by
  rw [← G.sum_degrees_eq_twice_card_edges]
  exact sum_degrees_eq_terminal_cubic G hG

lemma cubicFinset_even (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : Is23Graph G) :
    Even (cubicFinset G).card := by
  have hodd := G.even_card_odd_degree_vertices
  have heq : (Finset.univ.filter (fun v : V => Odd (G.degree v))) = cubicFinset G := by
    ext v
    simp only [cubicFinset, Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hG v with h2 | h3
    · simp [h2]
    · rw [h3]
      decide
  rw [← heq]
  exact hodd

def targetMatchingSize (G : SimpleGraph V) [DecidableRel G.Adj] : ℤ :=
  cyclomaticNumber G

lemma twice_targetMatchingSize (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : Is23Graph G) :
    2 * targetMatchingSize G =
      (Fintype.card V : ℤ) - (terminalFinset G).card + 2 := by
  have hcard : (Fintype.card V : ℤ) =
      (terminalFinset G).card + (cubicFinset G).card := by
    exact_mod_cast (terminal_cubic_card_add G hG).symm
  have hedge := edge_card_formula G hG
  have hedge' : (2 : ℤ) * (G.edgeFinset.card : ℤ) =
      2 * (terminalFinset G).card + 3 * (cubicFinset G).card := by
    exact_mod_cast hedge
  unfold targetMatchingSize cyclomaticNumber
  omega

end ThreeDecomposition

/-!
## Bridgelessness wrappers

Every edge of a bridgeless graph lies on a cycle, and deleting a non-bridge
from a connected graph preserves connectivity.
-/

namespace ThreeDecomposition

open SimpleGraph

variable {V : Type*}

lemma IsBridgeless.not_isBridge {G : SimpleGraph V} [DecidableRel G.Adj]
    (hG : IsBridgeless G) {e : Sym2 V} (he : e ∈ G.edgeSet) :
    ¬ G.IsBridge e := by
  exact hG he

lemma IsBridgeless.exists_cycle_mem {G : SimpleGraph V} [DecidableRel G.Adj]
    (hG : IsBridgeless G) {e : Sym2 V} (he : e ∈ G.edgeSet) :
    ∃ (u : V) (p : G.Walk u u), p.IsCycle ∧ e ∈ p.edges := by
  have hnb : ¬ G.IsBridge e := hG he
  rw [SimpleGraph.isBridge_iff_forall_cycle_notMem he] at hnb
  push Not at hnb
  exact hnb

lemma IsBridgeless.connected_deleteEdges {G : SimpleGraph V} [DecidableRel G.Adj]
    (hconn : G.Connected) (hG : IsBridgeless G)
    {e : Sym2 V} (he : e ∈ G.edgeSet) :
    (G.deleteEdges {e}).Connected := by
  exact hconn.preconnected.connected_deleteEdges_of_not_isBridge (hG he)

end ThreeDecomposition

/-!
## Small finite examples
-/

namespace ThreeDecomposition

open SimpleGraph

example : Is23Graph (cycleGraph 3) := by
  intro v
  left
  simpa using (cycleGraph_degree_three_le (n := 0) (v := v))

example : Is23Graph (cycleGraph 4) := by
  intro v
  left
  simpa using (cycleGraph_degree_three_le (n := 1) (v := v))

example : Is23Graph (completeGraph (Fin 4)) := by
  intro v
  right
  simp [SimpleGraph.degree, Finset.card_compl]

end ThreeDecomposition
