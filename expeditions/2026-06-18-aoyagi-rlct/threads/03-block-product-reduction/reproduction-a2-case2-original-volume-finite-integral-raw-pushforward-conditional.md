# Reproduction - A2 Case 2 original-volume finite integral raw-pushforward conditional

Date: 2026-07-01.

Status: pen-and-paper boundary check and Lean proof complete.

## Question

Can the conditional same-shrink original-volume readback domination be fed into
the existing p.13 finite-integral socket without mixing unrelated local
neighborhoods?

## Calculation

Start from the direct original-volume finite-integral front end.  It returns an
ambient theta-neighborhood `W` and a source-side neighborhood `U`, but still
asks each chart piece for:

```text
AEMeasurable readback (originalVolume.restrict chartPiece)
```

and

```text
Measure.map readback (originalVolume.restrict chartPiece)
  <= Csource • coordinateSourceMeasure.restrict W.
```

Call the same-shrink original-volume readback bridge with this `G := W`.
It returns `V subset W` and the source-chart package.  For any measurable
`chartPiece subset sourceChart '' V`, the explicit hypothesis

```text
Measure.map rawMap (coordinateSourceMeasure.restrict V) =
  rawHaar.restrict rawSourceSet
```

gives the needed readback a.e. measurability and domination with

```text
Csource = ((cHaar^-1 : NNReal) : ENNReal).
```

The finite-integral front end also asks for p.13 source-set containment and a
right-inverse statement on the chart piece.  These follow from the same `V`:

- `chartPiece subset sourceChart '' V` and `sourceChart '' V subset p13SourceSet`;
- if `E = sourceChart z` with `z in V`, then
  `readback E = z in V subset W` and `sourceChart (readback E) = E`.

## Boundary

The theorem is conditional on the raw-Haar raw-source pushforward for
`coordinateSourceMeasure.restrict V`.  It does not prove the local
change-of-variables/Jacobian theorem that would remove this hypothesis.  It
also does not prove determinant-chart Haar transport, source-image coverage,
source-rank coverage, original source-prior transport, scalar normalization,
normal crossings, pole order, or RLCT extraction.

## Lean Check

Lean witness:

```text
exists_open_lintegral_ofReal_loss_rpow_neg_p13RegularCoordinates_lt_top_of_case2PassiveThetaEndpointSourceChart_originalEdgeFamilyPrior_restrict_chartPiece_originalVolume_readback_invHaar_of_case2PassiveTheta_rawMap_eq_restrict_rawSource_jacobian_passiveProductMeasure_finiteMass_sourceStratum_bounds
```

Focused elaboration, focused module build, full local `lake build DLNFibre`,
`lean/scripts/sorries`, `git diff --check`, and direct axiom probe passed.
The direct axiom probe reported only
`[propext, Classical.choice, Quot.sound]`.
