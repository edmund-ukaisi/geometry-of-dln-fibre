# Review - A2 p.13 left-step small-ball section image

Date: 2026-06-26.

Reviewed artifacts:

- `lean/DLNFibre/DLN/Aoyagi/ProductReductionStepRegularDensity.lean`
- `reproduction-a2-p13-left-step-small-ball-section-image.md`
- `statement-card-a2-p13-left-step-small-ball-section-image.md`

## Verdict

No blocking findings.

## Checks

- Xhigh scout `Chandrasekhar the 2nd` confirmed this is the next bankable
  wrapper target and identified the same two-step dependency chain.
- Xhigh reviewer `Pasteur the 2nd` found one low-severity note wording issue:
  several summaries underemphasized the fixed-base edge-matrix measurability
  hypothesis.  The wording has been tightened to match the Lean statement.
- Lean proof uses only
  `exists_pos_radius_le_ae_p13LeftStepRaw_mem_rawDetChartSet_of_ae_regular_mem_ball`
  to obtain raw-chart support from small regular-coordinate ball support, then
  applies
  `map_p13RawOrderTuple_eq_map_leftStepRawOrder_image_of_measurable_edgeMatrix`.
- The conclusion remains exactly the section-image identity

```text
Measure.map Y eta = Measure.map Phi (Measure.map X eta).
```

## Boundary Audit

The theorem quantifies over a local measure on `(x,u)` and assumes a.e. support
in a small regular-coordinate ball.  It does not identify `Measure.map X eta`
with restricted raw Haar measure and does not add an inverse-Jacobian density.

## Verification

Focused build passed:

```text
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.ProductReductionStepRegularDensity
```

The build reports only the existing flexible-tactic warning around the older
raw-preimage algebra proof.
