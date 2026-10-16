import ThreeDecomposition.MainResults

/-!
# Comparator solution

The theorems of `Challenge`, proved by the project's main results.
-/

namespace ThreeDecompositionChallenge

open ThreeDecomposition

universe u v

theorem terminal_selection_theorem : TerminalSelectionTheorem.{u} :=
  terminalSelectionTheorem

theorem fragile_decomposition_theorem : FragileDecompositionTheorem.{u} :=
  fragileDecompositionTheorem

theorem two_decomposition_conjecture : TwoDecompositionConjecture.{u, v} :=
  twoDecompositionConjecture

theorem three_decomposition_conjecture : ThreeDecompositionConjecture.{u, v} :=
  threeDecompositionConjecture

end ThreeDecompositionChallenge
