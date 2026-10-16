# Blueprint: from Theorem 1.3 to the 3-Decomposition Conjecture

Targets (all in `ThreeDecomposition/Statement.lean`):

- `TerminalSelectionTheorem` (Theorem 1.3, simple graphs),
- `FragileDecompositionTheorem` (Theorem 1.4, simple graphs),
- `TwoDecompositionConjecture` (2DC, loopless multigraphs),
- `ThreeDecompositionConjecture` (3DC, loopless multigraphs).

The only external result allowed in the final dependency set is Schönberger's
specified-edge perfect matching theorem (`exists_perfect_matching_containing_edge`).

## Shared representation

- Simple graphs: `G : SimpleGraph V` with `[Fintype V] [DecidableEq V] [DecidableRel G.Adj]`;
  matchings are `G.Subgraph`s with `IsMatching`; `deletedMatching G M = G.deleteEdges M.edgeSet`.
- Multigraphs: `LooplessMultigraph V E` (`Multigraph/Defs.lean`), an edge type with an
  unordered pair of distinct ends; subgraphs are edge sets; connectivity and trees go through
  the simple graph `adjGraph F`.
- Non-bridge arguments use reachability after deleting the edge (`SimpleGraph.isBridge_iff`)
  rather than explicit cycles.
- Results that one workstream proves and another consumes are stated as propositions in
  `Interfaces.lean` / `Statement.lean`, so consumers can be written first.

## Dependency graph and modules

| Paper | Lean module | Main result | Status |
|---|---|---|---|
| §3.1 handshake | `Basic/Lemmas` | `twice_targetMatchingSize` | done |
| Lemma 3.1 | `MatchingComplement/Components` | `component_identity` | done |
| Lemma 3.2 | `MatchingComplement/TerminalCriterion` | criterion, extraction, `k = 2`, closing parity | done |
| Lemma 3.3 | `FirstEntry` | `first_entry` | done |
| Lemma 3.4 (graph side) | `Reduction` | suppression, triangle replacement, configurations | done |
| Base case, Lemma 3.5 | `Extension` | gadget perfect matching, comparison matching | done |
| Lemma 3.4 (lifts) | `Lift` | `adjacentTerminalLift`, `triangleLift` | done |
| Restoration cases | `Restore` | `restorationLift` | done |
| Theorem 1.3 induction | `Induction` | `terminalSelectionTheorem_of_lifts` | done |
| Theorem 1.3 | `MatchingComplement/Main` | `terminalSelectionTheorem` | done |
| Theorem 2.2 | `ProtectedCycle` | `protectedCycleTheorem` | done |
| Theorem 1.4 | `Fragile`, `MainResults` | `fragileDecompositionTheorem` | done |
| Corollary 1.5 | `MainResults` | `multigraphFragileDecomposition` | done |
| Corollary 4.1 (2DC), Theorem 1.2 (3DC) | `Multigraph/Theory`, `MainResults` | `twoDecompositionConjecture`, `threeDecompositionConjecture` | done |

## Deviations from the paper's proofs (statements unchanged)

The following proof-level differences are made to facilitate the formal development and do
not affect the correctness of any result.

- Theorem 1.3 is proved by direct strong induction on `k` and `|V|` instead of a minimum
  counterexample.
- Reduction 1 (adjacent terminals) is implemented as the suppression of one terminal rather
  than contraction of the shared edge.
- §3.3: instead of a cubic tree with `k - 2` internal vertices, the terminals are attached to
  a `k`-cycle of new vertices (`Extension.lean`).  The resulting graph is still
  simple, cubic and bridgeless, and the comparison matching keeps the only properties used
  later: it is a matching, it exposes only terminals, and it covers a chosen terminal (the
  specified edge of Schönberger's theorem is an old edge at that terminal).
- Lemma 3.3 exchanges one matching edge at a time (strong induction on `|N \ M|`) instead of
  flipping an alternating-path prefix.

## Acceptance gates

- `lake build` succeeds; it also builds `ThreeDecomposition/AxiomAudit.lean`, which rejects
  undeclared axioms and `sorryAx` in audited theorems.
- No `sorry` or `admit` in the `ThreeDecomposition` library (checked in CI); the four `sorry`s
  in `Comparator/Challenge.lean` are the expected challenge placeholders.
- Mathlib results are reused instead of reproved.
