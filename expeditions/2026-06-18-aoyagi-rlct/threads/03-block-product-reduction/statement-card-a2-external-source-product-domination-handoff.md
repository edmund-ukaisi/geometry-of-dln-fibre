# Statement Card - A2 external source product-domination handoff

Date: 2026-06-30.

## Lean Target

File:

```text
lean/DLNFibre/DLN/Aoyagi/LocalMeasureHandoff.lean
```

Add generic measure-theoretic helpers:

```text
prod_le_smul_prod_of_le_smul_left
ae_prod_of_left_measure_le_smul
lintegral_prod_lt_top_of_left_measure_le_smul
```

Expected statements:

```text
eta s-finite
  ->
nu <= c • mu
  ->
nu.prod eta <= c • mu.prod eta
```

and finite-product-integral transfer:

```text
eta s-finite
  ->
nu <= c • mu
  ->
c < infinity
  ->
lintegral F (mu.prod eta) < infinity
  ->
lintegral F (nu.prod eta) < infinity
```

## Inputs Used

- `Measure.prod_apply`.
- `lintegral_mono'`.
- `lintegral_smul_measure`.
- Existing `ae_of_measure_le_smul`.
- Existing `lintegral_lt_top_of_measure_le_smul`.

## Mathematical Meaning

This is the generic product-measure step needed after a local external-source
domination theorem.  Once a chart-produced finite integral has been proved for
`mu.prod eta`, any external source measure `nu` dominated by a finite scalar
multiple of `mu` inherits the same finite-product-integral conclusion.

## Nonclaims

- No proof of the domination hypothesis for the original source prior.
- No retained-passive or passive-theta chart-image theorem.
- No Jacobian density comparison for an external prior.
- No normal crossings, pole order, or RLCT extraction.
