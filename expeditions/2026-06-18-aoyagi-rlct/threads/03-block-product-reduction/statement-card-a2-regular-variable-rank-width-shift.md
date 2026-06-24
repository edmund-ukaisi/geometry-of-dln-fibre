# Statement Card - A2 regular-variable rank-width shift

## Lean targets

- `DLNFibre.DLN.Aoyagi.sourceRangeRankWidth_regularVariableEndpointBounds`
- `DLNFibre.DLN.Aoyagi.AoyagiTheorem2FiniteExponentFormulaHypothesis.of_regularVariableCountShift_rankWidth`
- `DLNFibre.DLN.Aoyagi.AoyagiTheorem2FiniteExponentFormulaHypothesis.of_chart_regularVariableCountShift_rankWidth`

## Files

- Lean: `lean/DLNFibre/DLN/Aoyagi/RegularVariableShift.lean`
- Reproduction:
  `threads/03-block-product-reduction/reproduction-a2-regular-variable-rank-width-shift.md`

## Claim

The finite regular-variable shift only needs the endpoint rank-width
inequalities `r <= H 1` and `r <= H (L+1)`.  These are projections of the
source-range rank-width hypothesis already used by Definition 3.  Therefore
the finite regular-variable shifted formula constructors can be stated with
`hr : forall s, 1 <= s -> s <= L+1 -> r <= H s`, without direct A2
source-rank-stratum data.

## Scope

This is finite exponent-array arithmetic and rank-width provenance only.  It
does not construct regular-suspension charts, prove analytic ideal transport,
prove active-ratio or chart-count facts, produce normal crossings, or extract
pole order/RLCT.

## Verification

Focused Lean check and module build passed:

```text
LEAN_NUM_THREADS=1 ~/.elan/bin/lake env lean DLNFibre/DLN/Aoyagi/RegularVariableShift.lean
LEAN_NUM_THREADS=1 ~/.elan/bin/lake build DLNFibre.DLN.Aoyagi.RegularVariableShift
```

Review:
`threads/03-block-product-reduction/review-a2-regular-variable-rank-width-shift.md`.
