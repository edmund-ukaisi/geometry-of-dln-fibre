# A2 With-Following Readback Product Residual, Original Prior, Unit Source Density

Date: 2026-07-03.

## Local Calculation

Work in the enlarged with-following Case 2 source coordinates.  The unit
source-image-density theorem supplies a local open set `Vsource` with

```text
integral productResidual(z)^{-t}
  over coordinateSourceMeasure.restrict Vsource
  < infinity.
```

Here `coordinateSourceMeasure = baseJ.withDensity (fun _ => 1)`.  The local
source chart has a readback left inverse on `Vsource`:

```text
readback (sourceChart z) = z.
```

Therefore the source-side residual and the edge-family readback residual agree
after pulling back along the source chart:

```text
aoyagiCoordinateSquareSum (readbackProductResidual (sourceChart z))
  = aoyagiCoordinateSquareSum (productResidual z).
```

This converts the source theorem's finite integral into

```text
integral readbackProductResidual(sourceChart z)^{-t}
  over coordinateSourceMeasure.restrict Vsource
  < infinity.
```

Next call the original-prior readback transfer theorem with `G := Vsource`.
It returns a smaller open set `V subset Vsource`.  Chart pieces are required to
satisfy

```text
chartPiece subset sourceChart '' V.
```

For such a chart piece, assume the endpoint weighted-Haar identity and
determinant-density lower bound:

```text
endpointReferenceImage = (rawHaar.restrict Q).withDensity Jprod,
Cdet < infinity,
1 <= Cdet * Jprod(y) for a.e. y with respect to rawHaar.restrict Q.
```

The source-density lower bound needed by the prior-transfer theorem is
immediate with `epsilon = 1`:

```text
1 <= sourceDensity z
```

because `sourceDensity` is definitionally the constant `1`.  A local prior
density upper bound then gives the readback finite-integral transfer
continuation.  Specialize that continuation to a Dirac `PUnit` factor:

```text
F(E, *) = readbackProductResidual(E)^{-t}.
```

The product integral over `PUnit` collapses on both source and target sides, so
the conclusion is exactly

```text
integral readbackProductResidual(E)^{-t}
  over originalPrior.restrict chartPiece
  < infinity.
```

## Lean Artifact

```text
exists_open_lintegral_originalEdgeFamilyPrior_restrict_chartPiece_case2PassiveThetaWithFollowingFactor_readbackProductResidual_of_sourceImageDensity_one_endpointReferenceImage_eq_withDensity_formalProductAbsDet_priorDensity_upper
```

in:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaOriginalVolumeReadbackDetDomination.lean
```

## Boundary

This is still a conditional endpoint-density wrapper.  It assumes the endpoint
reference-image weighted-Haar identity, the determinant-density lower bound,
the prior-density upper bound, and measurability of the readback residual
pullback.  It proves no endpoint Haar transport, no source-image coverage, no
original-prior transport, no normal-crossing statement, no pole order, and no
RLCT statement.

## Verification

Passed from the expedition worktree using local Lean commands:

```text
lake build DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveThetaOriginalVolumeReadbackDetDomination
lake build DLNFibre
lean/scripts/sorries
git diff --check
```

The touched Lean file has no `sorry`, `admit`, `axiom`, or `unsafe` marker.
The theorem's direct axiom probe reports:

```text
[propext, Classical.choice, Quot.sound]
```
