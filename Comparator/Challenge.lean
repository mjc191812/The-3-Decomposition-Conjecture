import ThreeDecomposition.Statement
import ThreeDecomposition.External.SpecifiedEdgeMatching

/-!
# Comparator challenge

The statements checked by Comparator (https://github.com/leanprover/comparator).  This module
and its imports are the trusted base: `ThreeDecomposition/Statement.lean`, the definition files
it imports, and `ThreeDecomposition/External/SpecifiedEdgeMatching.lean`, which declares the one
permitted non-standard axiom (Schönberger's theorem).  Comparator checks that `Solution` proves
these exact theorems, that the permitted axioms have the same declarations here and there, and
replays the proofs through the Lean kernel.
-/

namespace ThreeDecompositionChallenge

open ThreeDecomposition

universe u v

theorem terminal_selection_theorem : TerminalSelectionTheorem.{u} := sorry

theorem fragile_decomposition_theorem : FragileDecompositionTheorem.{u} := sorry

theorem two_decomposition_conjecture : TwoDecompositionConjecture.{u, v} := sorry

theorem three_decomposition_conjecture : ThreeDecompositionConjecture.{u, v} := sorry

end ThreeDecompositionChallenge
