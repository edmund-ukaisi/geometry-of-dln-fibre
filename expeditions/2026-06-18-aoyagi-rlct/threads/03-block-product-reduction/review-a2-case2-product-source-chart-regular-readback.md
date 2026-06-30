# Review - A2 Case 2 product source chart regular readback

Date: 2026-06-30.

## Verdict

PASS after focused and full Lean verification, plus xhigh reviewer audit.

## Soundness Check

The new readback reads only the fixed-base p.13 regular block from an ambient
edge family via the identity edge-family chart.  Its type has no passive-theta
or inverse component:

```text
case2PassiveThetaEndpointProductSourceChartRegularReadback
```

The theorem proves exactly:

```text
regularReadback(productSourceChart(theta,u)) = u
```

under the explicit determinant-chart hypothesis

```text
IsUnit(det(ctopMatrix u)).
```

## Proof Fidelity

The proof uses the regular-coordinate half of

```text
case2PassiveThetaEndpointProductSourceChart_regular_residualBlockCoordinateMap_eq
```

which is the Case 2 `M := 0` specialization of the generic p.13
source-dependent product-coordinate readout.  The comparison between the
identity edge-family chart and the product source chart is justified by

```text
paperEndpointFixedBaseRegularBlockCoordinateMap_congr_point
```

so the proof does not assume a product-chart inverse.

## Boundary

The theorem does not recover `theta` and does not define a readback to
`(theta,u)`.  It does not prove source-image coverage, original/source-prior
transport, Haar transport, a Jacobian formula, normal crossings, pole order, or
RLCT extraction.

## Verification

```text
env LEAN_NUM_THREADS=3 lake env lean DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaSourceImage.lean
env LEAN_NUM_THREADS=3 lake build DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveThetaSourceImage
env LEAN_NUM_THREADS=3 lake build DLNFibre
./scripts/sorries
git diff --check
env LEAN_NUM_THREADS=3 lake env lean /tmp/aoyagi_regular_readback_axioms.lean
```

`./scripts/sorries` reported `0 sorry, 0 #exit, 0 native_decide, 0 axiom`.
The direct axiom probe for the new definition and theorem reported only the
baseline `[propext, Classical.choice, Quot.sound]`.

Xhigh reviewer `Goodall the 2nd` also ran a read-only focused Lean check and
`git diff --check`, and passed the claim/name/nonclaim fidelity audit.
