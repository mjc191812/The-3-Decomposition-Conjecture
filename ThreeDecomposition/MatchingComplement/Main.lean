import ThreeDecomposition.Statement
import ThreeDecomposition.Induction
import ThreeDecomposition.Lift
import ThreeDecomposition.Restore

/-!
# Theorem 1.3: terminal selection

The induction of `Induction.lean` combined with the two reduction lifts (`Lift.lean`) and
the restoration step (`Restore.lean`).
-/

namespace ThreeDecomposition

open SimpleGraph

universe u

theorem terminalSelectionTheorem : TerminalSelectionTheorem.{u} :=
  terminalSelectionTheorem_of_lifts adjacentTerminalLift triangleLift restorationLift

variable {V : Type u} [Fintype V]

/-- **Theorem 1.3.**  A finite connected bridgeless simple `{2,3}`-graph with at least two
terminals has a matching of size `cyclomaticNumber G` whose complement is a tree containing
all terminals together with terminal-free cycles. -/
theorem terminal_selection
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hconn : G.Connected)
    (hbridge : IsBridgeless G)
    (h23 : Is23Graph G)
    (hterm : 2 ≤ (terminals G).ncard) :
    TerminalSelectionStatement G (terminals G) := by
  classical
  exact terminalSelectionTheorem V G hconn hbridge h23 hterm

end ThreeDecomposition
