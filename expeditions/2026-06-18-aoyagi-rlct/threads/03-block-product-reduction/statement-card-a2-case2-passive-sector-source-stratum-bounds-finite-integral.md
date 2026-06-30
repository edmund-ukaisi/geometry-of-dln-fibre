# Statement card - A2 Case 2 passive-sector source-stratum-bounds finite integral

Date: 2026-06-29.

## Statement

For the endpoint-transported Case 2 passive selected-entry coordinates, finite
passive mass and the selected-entry critical inequality supply the
retained-passive residual-source hypotheses on a punctured sector.  Combining
that with the source-stratum-bounds retained-passive local-measure consumer
gives a local finite-integral theorem whose loss and density assumptions are
stated on `nhdsWithin base sourceStratum`.

Lean target:

```text
exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_case2EndpointTransport_withPassive_puncturedSector_passiveProductMeasure_finiteMass_sourceStratum_bounds
```

## Source reference

Aoyagi PDF pp. 10-13 supplies the retained-passive p.13 local source and
regular-coordinate setup.  Aoyagi PDF pp. 19-22 supplies the selected-entry
Case 2 chart calculation.  The finite passive-sector measure handoff and
source-stratum-bound routing are expedition-built bookkeeping.

## Dependencies

- `exists_open_residualSourceHypotheses_of_case2EndpointTransport_withPassive_puncturedSector_inverseReadout_passiveProductMeasure_finiteMass`
- `exists_open_paperEndpointFixedBaseRetainedPassiveP13LocalSource_coverage_of_selfBase`
- `exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_sourceStratum_bounds_locally_subset_localSource`

## Assumptions Kept Explicit

- finite passive mass;
- positive selected-entry residual radii;
- exponent bounds `0 < t` and
  `2 * t < ((center.erase pivot).card : R) + 1`;
- fixed-base regular-coordinate source data;
- local loss lower bound on the source-rank stratum;
- local density nonnegativity and boundedness on the source-rank stratum;
- Haar measure on the regular-coordinate fiber.

## Nonclaims

This does not prove source-rank coverage; it uses only a local inclusion of
`Ulocal ∩ sourceStratum` into `Ulocal ∩ localSource`.  It also does not prove
determinant-chart Haar transport, source-prior transport, passive/source
Jacobian transport, source-image equality, exact localized residual marginal
equality, normal crossings, pole order, or RLCT.

## Reproduction and review

Reproduction:

```text
threads/03-block-product-reduction/reproduction-a2-case2-passive-sector-source-stratum-bounds-finite-integral.md
```

Review:
`threads/03-block-product-reduction/review-a2-case2-passive-sector-source-stratum-bounds-finite-integral.md`;
PASS by xhigh source/scope reviewer `Mencius the 4th` and xhigh Lean/API
reviewer `Dalton the 4th`.
