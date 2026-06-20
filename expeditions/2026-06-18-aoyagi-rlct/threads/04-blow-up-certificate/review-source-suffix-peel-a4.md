# Review - A4 source suffix one-edge peel

Reviewed objects:

- `DLNFibre.DLN.Aoyagi.paperMatrixChain_succ_left`
- `DLNFibre.DLN.Aoyagi.sourceSuffixFirstEdge`
- `DLNFibre.DLN.Aoyagi.sourceSuffixProduct_peel`
- `reproduction-source-suffix-peel-a4.md`
- `statement-card-a4-source-suffix-peel.md`

Verdict: no blocking source/math or Lean API issue found.

The slice matches Aoyagi's stopped Case 2 right suffix.  The raw chain
right-multiplies by the next edge, `sourceSuffixProduct` starts at source layer
`S+2` and ends at `L+1`, and the peel is correctly stated as the first edge
times the tail suffix.  The `sourceSuffixFirstEdge` wrapper is appropriately
narrow: it reindexes the supplied edge `C^(S+2)` to match the tail endpoint and
does not claim chart production.

## Nonblocking Suggestions Applied

- Wording changed from "nonempty beyond its first edge" to "has a first edge",
  because the boundary case `S+2=L` has a single edge and empty tail.
- The reproduction and statement card now explicitly mention the empty-product
  convention for the tail when `S+2=L`.
- The reproduction now calls the listed names "Lean artifacts" rather than
  "proved theorems", since `sourceSuffixFirstEdge` is a definition.

## Caveats

- This is raw matrix-chain algebra only.
- `sourceSuffixFirstEdge` is a reindexed supplied edge, not a produced
  terminal matrix.
- No empty-suffix identity, chart production, normal-crossing/RLCT, or
  transition invariant is proved.
