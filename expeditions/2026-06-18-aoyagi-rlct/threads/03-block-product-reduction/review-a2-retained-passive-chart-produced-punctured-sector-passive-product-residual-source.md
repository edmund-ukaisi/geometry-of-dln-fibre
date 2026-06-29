# Review: A2 retained-passive chart-produced punctured-sector passive-product residual source

Route reviewer: `Cicero the 3rd` (`019f141e-bb20-7ba1-955c-a2b733d51d41`)

Implementation reviewer: `Epicurus the 3rd` (`019f1423-87f9-7c23-999f-c3616c97818b`)

Verdict: PASS.

## Scope checked

The reviewers checked:

- the reproduction
  `reproduction-a2-retained-passive-chart-produced-punctured-sector-passive-product-residual-source.md`;
- the statement card
  `statement-card-a2-retained-passive-chart-produced-punctured-sector-passive-product-residual-source.md`;
- the Lean theorem
  `exists_open_residualSourceHypotheses_of_case2EndpointTransport_withPassive_puncturedSector_inverseReadout_passiveProductMeasure_finiteMass`
  in
  `lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveSelectedEntrySourceMeasureHandoff.lean`;
- the supporting APIs for `Measure.map_mono`, `Measure.restrict_le_self`,
  `Measure.map_snd_prod`,
  `SelectedEntrySignedBox.CenterCoord.residual_pos_ae_and_lintegral_rpow_neg_withDensity_sourceDensity`,
  `ae_of_measure_le_smul`, and
  `lintegral_lt_top_of_measure_le_smul`.

## Findings

The theorem shape is correct.  It specializes the residual-source socket to

```text
sourceMeasure = passiveMeasure.prod weightedBox,
```

where `weightedBox` is the raw selected-entry signed-box measure with Aoyagi's
source density.  It keeps finite passive mass, nonnegative exponent, positive
radii, the critical selected-entry inequality, the base determinant hypotheses,
and the base pivot-nonzero hypothesis explicit.

The measure argument uses domination in the correct direction:

```text
Measure.map Prod.snd ((passiveMeasure.prod weightedBox).restrict V)
  <= passiveMeasure Set.univ • weightedBox.
```

This follows from `Measure.restrict_le_self`, `Measure.map_mono` for the
measurable second projection, and `Measure.map_snd_prod`.  No equality of the
restricted marginal with the unrestricted product marginal is asserted.

The selected-entry residual facts are taken from the raw weighted-box theorem

```text
SelectedEntrySignedBox.CenterCoord.residual_pos_ae_and_lintegral_rpow_neg_withDensity_sourceDensity.
```

This is the right object for the residual-source socket's marginal hypotheses;
the proof does not use the chart-map image measure theorem in place of the raw
weighted-box theorem.

The a.e. positivity transfer uses `ae_of_measure_le_smul`, which needs no
finite scalar.  The finite-integral transfer uses
`lintegral_lt_top_of_measure_le_smul` and the explicit hypothesis

```text
passiveMeasure Set.univ < infinity.
```

No positive passive mass or `IsFiniteMeasure passiveMeasure` instance is needed
for this theorem.

The implementation reviewer found no hidden use of quiver material.  The import
path audited from the target file stayed inside `DLNFibre.DLN.Aoyagi` and did
not pass through `DLNFibre.Core`, CTheta/CCodim, quiver-specific modules, or an
RLCT theorem.

## Verification

The controller ran:

```text
cd lean
scripts/lb DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveSelectedEntrySourceMeasureHandoff
scripts/lb DLNFibre
scripts/sorries
git diff --check
rg -n "sorry|axiom|native_decide|#exit" \
  lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveSelectedEntrySourceMeasureHandoff.lean
```

The focused and full builds passed.  The full build produced only pre-existing
replay warnings outside the touched theorem.  `scripts/sorries` reported:

```text
Summary: 0 sorry, 0 #exit, 0 native_decide, 0 axiom
```

The touched-file forbidden-marker scan was clean, and `git diff --check`
passed.

The direct axiom probe for the new theorem reported:

```text
[propext, Classical.choice, Quot.sound]
```

## Nonclaim boundary

This theorem proves only the chart-produced restricted passive-product
residual-source hypotheses.  It does not prove determinant-chart Haar
transport, raw/source Haar transport, external/original source-prior transport,
a passive Jacobian formula, source-image equality, source-rank coverage, normal
crossings, pole order, or RLCT extraction.
