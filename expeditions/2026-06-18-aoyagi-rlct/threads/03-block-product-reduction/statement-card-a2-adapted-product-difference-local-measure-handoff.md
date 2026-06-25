# Statement Card - A2 adapted product-difference local-measure handoff

## Statement

At a continuous fixed-base self-base paper chain, the positive local
source-filter lower bound

```text
(c/2) * (regularSquareSum(x) + residualSquareSum(x))
  <= adaptedProductDifferenceSquareSum(x)
```

can be restricted to a sufficiently small measurable source neighborhood and
read as an a.e. statement.  The same comparison also has a product-measure
first-projection form.

## Lean Names

```text
exists_pos_const_open_ae_restrict_source_half_regular_add_residual_squareSum_le_adaptedProductDifferenceSquareSum_selfBase
exists_pos_const_open_ae_restrict_source_prod_fst_half_regular_add_residual_squareSum_le_adaptedProductDifferenceSquareSum_selfBase
```

## Source

Aoyagi p. 13 block product-reduction comparison, as formalised by the preceding
fixed-base adapted product-difference source-filter theorem, plus the existing
local-measure handoff from `nhdsWithin` eventual predicates to restricted
measure a.e. predicates.

## Dependencies

- fixed-base regular-coordinate source data;
- continuity of `Cedge` at the self-base paper chain;
- self-base triangular multiplier local boundedness;
- self-base product-reduction certificate neighborhood;
- measurability of the fixed-base source-rank stratum;
- local-measure handoff lemma for `nhdsWithin`.

## Nonclaims

No original DLN/statistical loss comparison, covariance lower bound,
basis-norm comparison, source-rank openness, p. 13 product chart construction,
Jacobian/prior transport, residual zero-locus nullity, residual negative-power
integrability, normal crossings, pole order, or RLCT extraction is proved.
