# Review: A2 selected-entry chart-point weighted product measure

## Source-scope scout

Reviewer: `Pascal the 4th`, xhigh read-only source-scope review.

Status: PASS.

Findings:

- Confirmed that the checkpoint is mathematically faithful when kept as
  finite coordinate-product transport.
- Confirmed that the adapter only repackages
  `y : center -> R` as `(y pivot, y|center.erase pivot.1)`.
- Confirmed that, since
  `sourceDensity pivot y = |y pivot| ^ card(center.erase pivot.1)`, the
  pushed density is the chart-point density depending on the first coordinate.
- Confirmed that no positive-radius hypothesis and no pivot-nonzero
  hypothesis are needed.
- Flagged the guardrail that the density must use `|x.1|`, not `x.1`.
- Confirmed this is independent of the quiver paper and should not be
  described as DLN fibre geometry, quiver representation theory, source
  coverage, analytic atlas construction, or RLCT extraction.

## Lean/API scout

Reviewer: `Descartes the 4th`, xhigh read-only Lean/API review.

Status: PASS.

Findings:

- Confirmed that the current imports of
  `SelectedEntryChartPointMeasureBridge.lean` are enough.
- Recommended not importing `ProductReductionStepMeasure`, because its
  `map_withDensity_comp_of_aemeasurable` lemma is private and the dependency
  is unnecessary.
- Recommended a local private copy of the same `withDensity` transport lemma.
- Confirmed that `chartPointDensity` is a clean optional public definition.
- Confirmed that the proof should unfold `sourceDensity` and the adapter
  directly, rather than route through determinant/Jacobian rewrites.
- Typechecked a proof skeleton from the Lake root.

## Implementation review

Reviewer: `Huygens the 4th`, xhigh read-only implementation review.

Status: PASS.

Findings:

- Confirmed the new public theorem proves exactly finite adapter weighted
  measure transport.
- Confirmed `chartPointDensity` uses `|x.1|` with exponent
  `#(center.erase pivot.1)`, matching `CenterCoord.sourceDensity`.
- Found no hidden positivity or pivot-nonzero assumption.
- Confirmed the required measurability is explicitly supplied.
- Confirmed the reproduction note and statement card remain inside the
  nonclaim boundary.
- Ran `git diff --check`, which reported no whitespace issues.

## Verification

Focused build passed via `lean/scripts/lb`:

```text
DLNFibre.DLN.Aoyagi.SelectedEntryChartPointMeasureBridge
```

Only pre-existing replay warnings in
`DLNFibre.DLN.Aoyagi.ProductReductionStepRegularDensity` appeared.

Full `DLNFibre` build passed via `lean/scripts/lb`.  Existing warnings in
older modules were replayed; no new touched-module warning appeared.

The sorry gate passed:

```text
Summary: 0 sorry, 0 #exit, 0 native_decide, 0 axiom
```

`git diff --check` passed.  The touched Lean-file forbidden-marker scan found
no `sorry`, `admit`, `#exit`, `native_decide`, or `axiom`.

Direct axiom probes for the new public definitions/theorems reported only:

```text
[propext, Classical.choice, Quot.sound]
```
