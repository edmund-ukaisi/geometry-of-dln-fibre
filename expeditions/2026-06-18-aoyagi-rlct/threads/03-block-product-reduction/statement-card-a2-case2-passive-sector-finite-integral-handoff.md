# Statement card - A2 Case 2 passive-sector finite-integral handoff

Date: 2026-06-29.

## Statement

For the endpoint-transported Case 2 passive selected-entry coordinates, finite
passive mass and the selected-entry critical inequality supply the
retained-passive residual-source hypotheses on a punctured sector.  Combining
that with the retained-passive p.13 local-measure consumer gives a local open
finite-integral theorem for the chart-produced passive product measure.

Lean target:

```text
exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_case2EndpointTransport_withPassive_puncturedSector_passiveProductMeasure_finiteMass
```

## Source reference

Aoyagi PDF pp. 10-13 supplies the retained-passive p.13 local source and
regular-coordinate setup.  Aoyagi PDF pp. 19-22 supplies the selected-entry
Case 2 chart calculation.  The finite passive-sector measure handoff is
expedition-built bookkeeping around those elementary coordinate formulas.

## Dependencies

- `exists_open_residualSourceHypotheses_of_case2EndpointTransport_withPassive_puncturedSector_inverseReadout_passiveProductMeasure_finiteMass`
- `exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_retainedPassiveP13LocalSource`

## Assumptions Kept Explicit

- finite passive mass;
- positive selected-entry residual radii;
- exponent bounds `0 < t` and
  `2 * t < ((center.erase pivot).card : R) + 1`;
- fixed-base regular-coordinate source data;
- local loss lower bound on the retained-passive local source;
- local density nonnegativity and boundedness on the retained-passive local source;
- Haar measure on the regular-coordinate fiber.

## Nonclaims

This does not prove determinant-chart Haar transport, source-prior transport,
source-image equality, source-rank coverage, exact localized residual marginal
equality, normal crossings, pole order, or RLCT.

## Reproduction and review

Reproduction:

```text
threads/03-block-product-reduction/reproduction-a2-case2-passive-sector-finite-integral-handoff.md
```

Review:
`threads/03-block-product-reduction/review-a2-case2-passive-sector-finite-integral-handoff.md`;
PASS by xhigh source/scope reviewer `Fermat the 4th` after documentation
scope repair and xhigh Lean/API reviewer `Curie the 4th`.
