# Reproduction - A2 Case 2 original-volume readback domination same-shrink conditional

Date: 2026-07-01.

Status: pen-and-paper boundary check and Lean proof complete for the
conditional readback-domination adapter.

## Question

Can the same local shrink from the conditional original-volume/source-image
bridge discharge the readback-domination hypothesis required by the
original-volume finite-integral socket?

## Calculation

Fix an ambient local theta set `G` around the Case 2 passive-theta point.  The
same-shrink bridge supplies `V subset G` with:

- `readback (sourceChart z) = z` for `z in V`;
- `sourceChart` injective and continuous on `V`;
- `sourceChart '' V` measurable;
- `sourceChart '' V subset p13SourceSet`;
- for every measurable `chartPiece subset sourceChart '' V`, the explicit
  raw-Haar raw-source pushforward hypothesis

  ```text
  Measure.map rawMap (thetaReference.restrict V) =
    rawHaar.restrict rawSourceSet
  ```

  gives

  ```text
  originalVolume.restrict chartPiece =
    ((Measure.map sourceChart (thetaReference.restrict V)).withDensity
      invHaarDensity).restrict chartPiece
  ```

  where `invHaarDensity` is the constant inverse Haar scalar.

The generic source-chart readback lemma then applies on this same `V`: a
bounded-density identity against `Measure.map sourceChart
(thetaReference.restrict V)` and the local left-inverse/injective/continuous
chart package imply

```text
AEMeasurable readback (originalVolume.restrict chartPiece)
```

and

```text
Measure.map readback (originalVolume.restrict chartPiece)
  <= invHaarScalar • thetaReference.restrict G.
```

The use of `G` on the right is justified by `V subset G`, hence
`thetaReference.restrict V <= thetaReference.restrict G`.

## Boundary

The theorem still assumes the raw-Haar raw-source pushforward.  It is a
same-witness adapter, not a proof of raw-Haar transport, determinant-chart
Haar transport, source-prior transport, source-image coverage, source-rank
coverage, normal crossings, pole order, or RLCT extraction.

## Lean Check

Lean witness:

```text
exists_open_subset_originalEdgeFamilyVolume_restrict_chartPiece_readback_le_smul_sourceReference_same_shrink_of_case2PassiveTheta_rawMap_eq_restrict_rawSource
```

Focused elaboration, focused module build, full local `lake build DLNFibre`,
`lean/scripts/sorries`, `git diff --check`, and direct axiom probe passed.
The direct axiom probe reported only
`[propext, Classical.choice, Quot.sound]`.
