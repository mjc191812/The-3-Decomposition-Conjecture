# Status

All four statements of `ThreeDecomposition/Statement.lean` are proved, in
`ThreeDecomposition/MainResults.lean` and `ThreeDecomposition/MatchingComplement/Main.lean`:

| Statement | Lean theorem |
|---|---|
| Theorem 1.3 (`TerminalSelectionTheorem`) | `terminalSelectionTheorem`, `terminal_selection` |
| Theorem 1.4 (`FragileDecompositionTheorem`) | `fragileDecompositionTheorem` |
| Corollary 1.5 | `multigraphFragileDecomposition` |
| 2DC (`TwoDecompositionConjecture`) | `twoDecompositionConjecture` |
| 3DC (`ThreeDecompositionConjecture`, Theorem 1.2) | `threeDecompositionConjecture` |

Their axioms are `propext`, `Classical.choice`, `Quot.sound` and the single project axiom
`exists_perfect_matching_containing_edge` (Schönberger's theorem, the paper's external input,
stated for finite simple connected bridgeless cubic graphs).  `lake build` checks this through
`ThreeDecomposition/AxiomAudit.lean`; there is no `sorry` or `admit` in the project.

Theorem 2.2 (Borse–Waphare), which the paper proves, is also formalized
(`protectedCycleTheorem`), as is Corollary 1.5 (`LooplessMultigraph.exists_isSpanningTree_isMatching`).

`lake build` emits no warnings.

## Comparator

`Comparator/config.json` checks the four main theorems with
[Comparator](https://github.com/leanprover/comparator): `Comparator/Solution.lean` must prove
exactly the statements of `Comparator/Challenge.lean`, use no axioms beyond `propext`,
`Quot.sound`, `Classical.choice` and `ThreeDecomposition.exists_perfect_matching_containing_edge`
(whose declaration must also match), and pass a replay through the Lean kernel.  The check
passed locally with comparator v4.34.0 built against Lean v4.34.1, with the landrun sandbox
disabled (Windows); it rejected a solution with a changed statement and a configuration
without the Schönberger axiom.  `.github/workflows/comparator.yml` runs it with landrun on
Linux in GitHub Actions, where it also passes.
