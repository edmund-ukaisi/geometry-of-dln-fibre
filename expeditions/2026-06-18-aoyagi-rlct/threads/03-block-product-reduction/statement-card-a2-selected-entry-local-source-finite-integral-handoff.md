# Statement Card - A2 selected-entry local-source finite-integral handoff

Date: 2026-06-25.

## Claim

For a center-indexed selected-entry signed-box chart, the local-source p.13
finite-integral theorem no longer needs generic monomial-unit hypotheses:
they are discharged by the explicit selected-entry residual and formal-density
calculation.

## Lean Name

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_localSource_selectedEntryCenter_signedBox_withDensity_edgeMatrix
```

## Inputs Kept Explicit

- finite center and selected pivot;
- local source set and source measurability;
- source chart from center coordinates;
- weighted pushforward identity for the selected-entry formal density;
- equality between the residual block square-sum and the selected-entry
  residual model;
- pivot critical inequality
  `2 * t < (center.erase pivot.1).card + 1`;
- fixed-base edge-matrix measurability;
- p.13 local regular-coordinate loss and density bounds.

## Nonclaims

No chart construction, source coverage, pushforward proof, analytic
Jacobian/source-density theorem, original-loss comparison, normal-crossing
certificate, pole-order theorem, or RLCT extraction is proved.

## Verification

Focused build passed:

```text
cd lean
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.SelectedEntrySignedBoxLocalMeasure
```
