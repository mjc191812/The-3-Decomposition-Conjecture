# Mathlib API inventory

Lean 4.34.1, Mathlib v4.34.1.

## Reused directly

- Degrees and handshake: `SimpleGraph.degree`, `neighborFinset`,
  `sum_degrees_eq_twice_card_edges`, `even_card_odd_degree_vertices`.
- Connectivity: `Connected`, `Reachable`, `reachable_iff_reflTransGen`,
  `ConnectedComponent`, `ConnectedComponent.toSimpleGraph`,
  `connected_toSimpleGraph`, `Connected.card_vert_le_card_edgeSet_add_one`.
- Bridges: `IsBridge`, `isBridge_iff`, `isBridge_iff_forall_cycle_notMem`,
  `Preconnected.connected_deleteEdges_of_not_isBridge`.
- Trees and cycles: `IsTree`, `IsAcyclic`, `isTree_iff_connected_and_card`,
  `IsAcyclic.isTree_connectedComponent`, `IsCycles`, `IsCycles.toSimpleGraph`.
- Matchings: `Subgraph.IsMatching`, `IsPerfectMatching`, `IsMatching.toEdge`,
  `IsMatching.support_eq_verts`, `IsMatching.even_card`, `IsMatching.map`,
  `IsMatching.sup`.
- Graph constructions: `deleteEdges`, `Subgraph.spanningCoe`, `induce`,
  `SimpleGraph.sum` (`⊕g`), `Subgraph.comap`, `SimpleGraph.edge`.
- Relations: `Relation.ReflTransGen.lift'`.
- Cardinality: `Set.card_ne_eq`.

## Not in Mathlib (developed here)

- `|M.verts| = 2 * |M.edgeSet|` for a non-perfect matching.
- Symmetric difference of two non-perfect matchings; Mathlib's
  `IsPerfectMatching.symmDiff_isCycles` only covers perfect matchings.
- Vertex suppression and triangle replacement on a smaller vertex type.
- Reachability transport along maps that may collapse edges to a vertex.

## Thin project wrappers

`Is23Graph`, `terminals`, `cubicVertices`, `IsBridgeless`, `cyclomaticNumber`,
`deletedMatching`, `IsTerminalTreeCycles`, `TerminalSelectionStatement`.
