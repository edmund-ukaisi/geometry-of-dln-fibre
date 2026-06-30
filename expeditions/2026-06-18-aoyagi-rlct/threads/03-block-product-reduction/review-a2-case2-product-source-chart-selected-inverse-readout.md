# Review - A2 Case 2 product source chart selected inverse readout

Date: 2026-06-30.

## Verdict

PASS after focused and full Lean verification, plus xhigh reviewer audit.

## Soundness Check

The theorem proves only:

```text
case2PassiveThetaEndpointInverseReadout(productSourceChart(theta,u))
  =
case2PassiveThetaEndpointInverseReadout(sourceChart theta)
```

It has the same determinant-chart hypothesis as the product-coordinate readout:

```text
IsUnit(det(ctopMatrix u)).
```

## Proof Fidelity

The proof uses the residual-coordinate half of

```text
case2PassiveThetaEndpointProductSourceChart_regular_residualBlockCoordinateMap_eq
```

and transports that equality through the definition of
`case2PassiveThetaEndpointInverseReadout`.  The two identity-edge-family
appearances are justified by

```text
paperEndpointFixedBaseResidualBlockCoordinateMap_congr_point.
```

No sourceReadback retained-data identity or product-chart inverse is assumed.

## Boundary

Xhigh scout `Mendel the 2nd` checked the stronger full-theta recovery target.
The current product APIs recover the regular variables and preserve selected
residual inverse readout, but they do not prove the retained-passive identity

```text
sourceReadback(Eprod) =
  case2PassiveThetaEndpointRetainedData ... theta eNext e
```

for `Eprod` coming from `productSourceChart(theta,u)`.  For arbitrary `u`, that
is conceptually too strong for the current product chart.

## Verification

```text
env LEAN_NUM_THREADS=3 lake env lean DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaSourceImage.lean
env LEAN_NUM_THREADS=3 lake build DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveThetaSourceImage
env LEAN_NUM_THREADS=3 lake build DLNFibre
./scripts/sorries
git diff --check
env LEAN_NUM_THREADS=3 lake env lean /tmp/aoyagi_selected_inverse_axioms.lean
```

`./scripts/sorries` reported `0 sorry, 0 #exit, 0 native_decide, 0 axiom`.
The direct axiom probe reported only the baseline
`[propext, Classical.choice, Quot.sound]`.

Xhigh reviewer `Fermat the 2nd` also ran a focused read-only Lean check and
passed the claim/name/nonclaim fidelity audit.
