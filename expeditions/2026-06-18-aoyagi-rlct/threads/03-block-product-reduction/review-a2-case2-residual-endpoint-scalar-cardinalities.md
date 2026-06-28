# Review - A2 Case 2 residual endpoint scalar cardinalities

Reviewer: Curie, xhigh read-only review.

## Verdict

PASS.

No blocking formalisation or mathematical accuracy issues were found.  The Lean
rung proves exactly the intended finite cardinality facts: residual columns and
rows from explicit `H 1 = prefixMinNat n S`, `H 2 = n (S + 1)`, and
`r = J + 1`, then feeds them plus explicit `hTau` into the existing
endpoint-cardinality theorem.

## Scope Check

Checked files:

- `lean/DLNFibre/DLN/Aoyagi/Case2ResidualFactorProduct.lean`
- `threads/03-block-product-reduction/reproduction-a2-case2-residual-endpoint-scalar-cardinalities.md`
- `threads/03-block-product-reduction/statement-card-a2-case2-residual-endpoint-scalar-cardinalities.md`

Endpoint order is correct: `q = 0` is `tau` and matches `H 3 - r`, `q = 1`
is residual columns and matches `H 2 - r`, and `q = 2` is residual rows and
matches `H 1 - r`.

The review found no hidden proof of width/rank equalities, `hTau`,
construction of `tau`, canonical labels, source priors, Jacobians, normal
crossings, pole order, or RLCT.

## Nonblocking Fixes Applied

- The Lean docstring now says "Source data, explicit `hTau`, and the displayed
  width/rank identifications" so the remaining `tau` scalar hypothesis is
  explicit.
- The new reproduction, statement card, and ledger entries now use spaced
  Lean-style arithmetic such as `H 2 - r`, `H 3 - r`, `J + 1`, and
  `n (S + 1)`.

## Verification

The reviewer ran:

```text
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.Case2ResidualFactorProduct
```

from `lean/`; the build passed.
