**1. VERDICT**

A. Dead as stated.

The proposed per-layer fibre bijection `ChartIdx`-fibre `s ≃ FlatIdx`-fibre `s` cannot exist when the fibre sizes are `[12,12,3]` vs `[9,9,9]`. So the team's “layer-compatible `e`” premise is false, not merely a notation issue.

A different reindexing strategy may still work, but not that one.

**2. THE RIGHT GRADING**

`Matrix.BlockTriangular.det` wants one index type with one grading used for both rows and columns. Your current matrix is square over `Fin N`, but semantically:

- rows are output `Params`/`FlatIdx` coordinates;
- columns are input `ChartIdx` coordinates.

So the natural data is two gradings:

```lean
rowLayer : Fin N → ℕ   -- via Params / FlatIdx
colLayer : Fin N → ℕ   -- via chartIdxEquiv / ChartIdx
```

Your proven locality says:

```lean
Dphi row col = 0 if colLayer col > rowLayer row
```

That is a two-sided row/column grading condition, not directly a `BlockTriangular` condition with one `bLayer`.

Clean formulation: first independently reindex rows and columns into whatever common ordered block index you choose, producing a matrix whose row and column block decompositions have matching block sizes. Then apply block triangular determinant there. Independent row/column permutations change `det` by signs, so `|det|` is unaffected.

**3. CAN THE PROVEN FACT STILL GIVE BLOCK TRIANGULARITY?**

Not by the coarse layer blocks `[12,12,3]` against `[9,9,9]`, because block determinant factorization needs square diagonal blocks. Those coarse input/output layer blocks do not match.

The determinant should factor over a common square decomposition obtained after aligning the dependency relation, not simply over input layers or output layers. Concretely, build the bipartite dependency graph:

```text
input chart slots  --->  output Params slots
```

with edges where derivatives may be nonzero, then find a common ordering/decomposition whose diagonal pieces are square. Inference: this is likely the “SCC condensation” style decomposition you mention, e.g. the hand-built `frameB` with 13 blocks in the `(3,3,3,3)` case.

Your locality gives a coarse one-sided zero pattern. It is necessary structure, but too coarse to produce the desired product unless refined to square matched blocks.

**4. CHEAPEST NEXT CHECK**

Do a structural/#eval check of the actual zero-pattern block sizes after refinement.

Minimal useful check:

1. Construct the boolean dependency matrix `mayDepend row col`.
2. Compute the bipartite/common dependency graph induced by nonzero possibilities.
3. Compute SCCs or the proposed refined blocks.
4. `#eval` the block sizes on both sides and verify each diagonal block has equal row/column cardinality.
5. Verify zeros above/below the proposed block order.

If the 13-block `frameB` decomposition gives matching row/column counts per block and the expected zero pattern, that is the grading to formalize. The layer grading alone is not.