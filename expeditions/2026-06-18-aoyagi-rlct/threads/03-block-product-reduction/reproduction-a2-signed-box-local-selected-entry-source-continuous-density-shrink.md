# A2 signed-box local selected-entry source continuous-density shrink

## Source calculation

Let

```text
source = {y : center -> Real | y pivotNext != 0}
chi = SelectedEntrySignedBox.CenterCoord.chartMap pivotNext.
```

The already formalized local-source continuous-density theorem accepts any
measurable source-coordinate parent

```text
localSource subset source
```

and any measurable regular-coordinate parent

```text
regularSet subset ball(0,R).
```

It then shrinks around any supplied base point

```text
(y0,u0) in localSource x regularSet
```

and proves a finite bound for the supplied continuous edge-family density on
the value-side product

```text
chi '' localSource' x regularSet'.
```

For a selected-entry signed box with prescribed radii `Rbox`, set

```text
sourceBox = signedBoxSet Rbox inter source.
```

This is exactly a valid local-source parent:

```text
MeasurableSet sourceBox
```

by the selected-entry signed-box measurability lemma with the pivot hyperplane
removed, and

```text
sourceBox subset source
```

by the second projection from the intersection.

Therefore, if

```text
y0 in sourceBox,
u0 in regularSet,
regularSet subset ball(0,R),
```

the local-source continuous-density theorem applies with
`localSource = sourceBox`.  It returns a finite `c`, a measurable
`localSource' subset sourceBox` still containing `y0`, and a measurable
`regularSet' subset regularSet` still containing `u0`, such that

```text
ENNReal.ofReal (phi (CedgeProd z)) <= c
```

for all

```text
z in chi '' localSource' x regularSet'.
```

The same weighted selected-entry local-source measure and value-reference
measure as in the parent theorem then give

```text
map productReadback
  (map selectedEntryProductChart'
    (localSelectedEntrySource'.withDensity
      (fun z => ENNReal.ofReal (phi (selectedEntryProductChart' z)))))
<=
c * localValueReference'.restrict (chi '' localSource' x regularSet').
```

No new topology, Jacobian, Haar, or prior calculation is used in this
specialization; the inherited selected-entry source-density and readback
plumbing remains in the parent theorem.

## Aoyagi link

This is the signed-box form of the elementary local p.13 product-coordinate
bookkeeping after the pp.19-21 selected-entry nonzero-pivot chart.  The
substantive continuity-to-local-boundedness and selected-entry local-source
readback calculation were already reproduced in the parent local-source
continuous-density note; the new step is only the signed-box local-source
choice.

## Lean target

Implemented in:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2SelectedEntryProductMeasureHandoff.lean
```

Declaration:

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.exists_pos_radius_le_case2EndpointTransport_selectedEntryValue_productCoordinate_map_signedBoxLocalSelectedEntrySource_withDensity_ofReal_continuousEdgeDensity_exists_shrink_readback_le_smul_localValueReference_restrict_localDomain
```

It specializes:

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.exists_pos_radius_le_case2EndpointTransport_selectedEntryValue_productCoordinate_map_localSelectedEntrySource_withDensity_ofReal_continuousEdgeDensity_exists_shrink_readback_le_smul_localValueReference_restrict_localDomain
```

using:

```text
SelectedEntrySignedBox.CenterCoord.measurableSet_signedBoxSet_inter_pivot_ne_zero
```

## Boundary

The theorem keeps `phi` as a supplied continuous edge-family density.  It does
not identify `phi` with Aoyagi's original prior, prove original-prior
transport, determinant/raw Haar transport, source coverage, source-rank
coverage, residual integrability, normal crossings, pole order, or RLCT
extraction.

## Verification

Local verification on 2026-07-07:

```text
lake env lean DLNFibre/DLN/Aoyagi/RetainedPassiveCase2SelectedEntryProductMeasureHandoff.lean
lake build DLNFibre.DLN.Aoyagi.RetainedPassiveCase2SelectedEntryProductMeasureHandoff
```

passed.  The focused module build replayed pre-existing imported-file style
warnings but produced the target module successfully.

Xhigh read-only reviewer `Peirce the 2nd` passed the theorem-boundary and
reproduction audit.

```text
scripts/sorries DLNFibre/DLN/Aoyagi/RetainedPassiveCase2SelectedEntryProductMeasureHandoff.lean
git diff --check
grep -nP '\t' lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2SelectedEntryProductMeasureHandoff.lean
```

also passed, with `scripts/sorries` reporting
`0 sorry, 0 #exit, 0 native_decide, 0 axiom` and the tab scan finding no
tabs.  A direct `#print axioms` probe for the new declaration reported only:

```text
[propext, Classical.choice, Quot.sound]
```
