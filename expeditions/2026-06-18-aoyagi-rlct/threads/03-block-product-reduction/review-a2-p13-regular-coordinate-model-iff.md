# Review - A2 p.13 regular-coordinate model iff

Date: 2026-06-29.

Reviewer: xhigh `Feynman the 2nd`.

Status: PASS.

## Reviewed Claim

The new fixed-base p.13 wrapper in

```text
lean/DLNFibre/DLN/Aoyagi/RegularSuspensionSquareSumIntegrability.lean
```

states only the square-model iff for

```text
residualSquareSum(x) + regularCoordinateSquareSum(u)
```

at exponent

```text
t + aoyagiTheorem2RegularVariableCount N H r / 2.
```

## Findings

No mathematical or formalisation issues were found.

The reviewer checked that `sourceData` is used only through the
regular-coordinate finrank/count rewrite, and that the theorem does not smuggle
in an actual-loss, density, Jacobian, chart-coverage, pole-order,
normal-crossing, or RLCT claim.

The hypotheses expose the reverse-direction requirements:

```text
AEMeasurable residual square-sum,
R > 0,
residual square-sum > 0 a.e.,
residual square-sum <= R^2 a.e.,
t > 0,
[SFinite nu],
[nu.IsAddHaarMeasure].
```

## Reviewer Verification

The reviewer independently ran

```text
lake env lean DLNFibre/DLN/Aoyagi/RegularSuspensionSquareSumIntegrability.lean
```

successfully, checked `git diff --check a65f06ed`, and found no
`sorry`/`admit`/`axiom`/`unsafe` markers in the changed files.
