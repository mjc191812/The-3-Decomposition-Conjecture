import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Combinatorics.SimpleGraph.Operations
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-!
# Basic definitions for the matching-complement theorem

The definitions in this file are deliberately thin wrappers around Mathlib's
`SimpleGraph`, finite-degree, subgraph, matching, and edge-deletion APIs.
-/

namespace ThreeDecomposition

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

abbrev terminals (G : SimpleGraph V) [DecidableRel G.Adj] : Set V :=
  {v | G.degree v = 2}

abbrev cubicVertices (G : SimpleGraph V) [DecidableRel G.Adj] : Set V :=
  {v | G.degree v = 3}

def Is23Graph (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  ∀ v : V, G.degree v = 2 ∨ G.degree v = 3

def IsBridgeless (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  ∀ ⦃e : Sym2 V⦄, e ∈ G.edgeSet → ¬G.IsBridge e

def cyclomaticNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℤ :=
  (G.edgeFinset.card : ℤ) - (Fintype.card V : ℤ) + 1

def deletedMatching (G : SimpleGraph V) [DecidableRel G.Adj] (M : G.Subgraph) : SimpleGraph V :=
  G.deleteEdges M.edgeSet

/--
The residual graph consists of a terminal-containing tree and cycle components.
The tree is represented on its own vertex subtype; `spanningCoe` embeds it in
the ambient vertex type.  The degree equations make the residual edges
incident to the tree exactly the tree edges, while every residual vertex
outside the tree has degree two.
-/
def IsTerminalTreeCycles (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Set V) (M : G.Subgraph) : Prop := by
  classical
  exact
  M.IsMatching ∧
    ∃ (U : Set V) (T : SimpleGraph U),
      T.IsTree ∧
      S ⊆ U ∧
      T.spanningCoe ≤ deletedMatching G M ∧
      (∀ v : U, (deletedMatching G M).degree v = T.degree v) ∧
      (∀ v : V, v ∉ U → (deletedMatching G M).degree v = 2)

def TerminalSelectionStatement (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Set V) : Prop :=
  ∃ M : G.Subgraph,
    M.IsMatching ∧
      (M.edgeSet.ncard : ℤ) = cyclomaticNumber G ∧
      IsTerminalTreeCycles G S M

def IsTerminalSelectionInstance (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  G.Connected ∧ IsBridgeless G ∧ Is23Graph G

end ThreeDecomposition
