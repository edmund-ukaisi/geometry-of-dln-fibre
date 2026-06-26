# Review - Case 2 finite raw-pivot chart-family boundary

Date: 2026-06-26.

Reviewers: Darwin the 2nd and Kepler the 2nd, xhigh read-only checks.

Status: PASS.

## Verdict

No blocking mathematical or Lean API issue was found.  The theorem is
claim-safe because the predicates are explicitly finite selected-entry algebra:
`ChartRegular` records pivot membership, the selected-entry formula, and
finite center-ideal principalization; `TransitionRegular` records pivot
membership and a concrete `SelectedEntryFiniteAffineTransitionRegularPair`.

## API Check

The target boundary type has only two fields:

```text
p in center -> ChartRegular p
p in center -> q in center -> TransitionRegular p q
```

The proof fills those fields directly and does not call
`Case2ResidualBlockChartFamilyBoundary.exists_trivial`.  Transition data comes
from the already-proved Case 2 all-pivot finite affine transition family via
`SelectedEntryFiniteAffineTransitionRegularFamily.pair`.

## Math Check

The source anchor is Aoyagi's Case 2 selected-entry blow-up calculation on
pp. 19-22.  The finite all-pivot version is a standard completion of the same
elementary calculation, not a claim that Aoyagi printed every pivot chart.

The overlap denominator remains the normalised target coordinate `x_q != 0`.
It is not replaced by the ambient value `u*x_q != 0`, so exceptional-divisor
points with `u = 0` are not wrongly excluded.

## Verification

Focused build passed:

```text
cd lean
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.SelectedEntryNormalCrossing
```

## Residual Boundaries

Analytic atlas construction, chart coverage, analytic transition regularity,
source production, suffix production, analytic Jacobian or volume-form
compatibility, global normal crossings, pole order, and RLCT extraction remain
deferred or separately cited as before.
