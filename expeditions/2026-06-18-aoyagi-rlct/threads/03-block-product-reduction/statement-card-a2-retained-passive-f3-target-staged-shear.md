# Statement Card - A2 Retained-Passive F3 Target-Staged Shear

## Lean File

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesDerivative.lean
```

## Lean Name

```text
fderiv_topologyTupleEdgeRawOrder_F3_targetStaged_shear_apply
```

## Reproduction

```text
reproduction-a2-retained-passive-f3-target-staged-shear.md
```

## Claim

For positive retained-passive tail length, the terminal `F3` shear can use the
target-staged derivative of the earlier lower-left tail:

```text
D(raw F3)
  - targetStagedEarly * LastTop
  + (F3 - Early) * dLastTop
= dF3 * (-LastTop).
```

The theorem substitutes

```text
dEarly =
  retainedPassiveLowerLeftProductTailTargetStagedFDerivAt z v 0 ...
```

into the already-proved terminal `F3` shear.

## Proof Plan

1. Invoke `fderiv_topologyTupleEdgeRawOrder_F3_shear_apply` with `M+1`.
2. Invoke
   `fderiv_retainedPassiveLowerLeftProductTailSum_targetStaged_apply`
   with `M` and `m = 0`.
3. Rewrite the earlier-tail derivative in the `F3` shear.
4. Simplify definitions only; do not commute matrix factors.

## Status

Pen-and-paper reproduction written and Lean implementation proved locally.
Focused `DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinatesDerivative` build
passed.  Independent xhigh review `Bernoulli` passed with no findings.

## Nonclaims

No full derivative-formal-Jacobian equality, no determinant equality, no
target-side linear equivalence, no measure transport, no normal crossings, no
pole order, and no RLCT.
