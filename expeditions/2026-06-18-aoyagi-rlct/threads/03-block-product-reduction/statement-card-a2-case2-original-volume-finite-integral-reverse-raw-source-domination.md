# Statement card: A2 Case 2 original-volume finite integral from reverse raw-source domination

Status: Lean statement proved and locally verified.

## Lean declaration

```text
exists_open_lintegral_ofReal_loss_rpow_neg_p13RegularCoordinates_lt_top_of_case2PassiveThetaEndpointSourceChart_originalEdgeFamilyPrior_restrict_chartPiece_originalVolume_readback_invHaar_of_restrict_rawSource_le_smul_case2PassiveTheta_rawMap_jacobian_passiveProductMeasure_finiteMass_sourceStratum_bounds
```

File:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaOriginalVolumeReadback.lean
```

## Statement

The theorem returns the same kind of local finite-integral socket as the
raw-pushforward equality wrapper: an open `W` around `z0`, then for each
bounded source-image density a source neighborhood `U` and a same-shrink
source-chart image `V subset W`.

For every measurable chart piece

```text
chartPiece subset U inter sourceStratum
chartPiece subset sourceChart '' V,
```

the finite integral over the original edge-family prior follows from the
finite reverse raw-source domination

```text
m.restrict rawSourceSet
  <= D * Measure.map rawMap (coordinateSourceMeasure.restrict V),
D < infinity.
```

The readback domination scalar supplied to the finite-integral front end is

```text
(cHaar^{-1}) * D.
```

## Nonclaims

The theorem does not prove the reverse raw-source domination.  It only weakens
the downstream finite-integral consumer from exact raw-pushforward equality to
a finite reverse domination hypothesis.  There is no Haar transport,
source-image coverage, source-rank coverage, original source-prior transport,
normal-crossing theorem, pole-order theorem, or RLCT extraction.
