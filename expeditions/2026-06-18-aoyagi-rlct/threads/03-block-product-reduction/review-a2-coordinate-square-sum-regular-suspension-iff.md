# Review - A2 coordinate-square-sum regular-suspension iff

Date: 2026-06-29.

Reviewer: xhigh `Hooke the 2nd`.

Status: PASS.

## Reviewed Claim

The new wrappers in

```text
lean/DLNFibre/DLN/Aoyagi/RegularSuspensionSquareSumIntegrability.lean
```

specialise the generic local square-model threshold-shift iff to

```text
a(x) = aoyagiCoordinateSquareSum (b x)
```

and to the residual-block expression

```text
a(x) =
  aoyagiCoordinateSquareSum
    (AoyagiResidualBlockCoordinateIndex.value (D x)).
```

## Findings

No blocking issues.

The Lean additions are direct substitutions into the generic square-model
reverse/iff theorem.  The residual-block wrappers only substitute the residual
coordinate-value map; they do not introduce matrix algebra, loss comparison,
density, chart, pole-order, normal-crossing, or RLCT content.

The hypotheses preserve the reverse-side requirements:

```text
AEMeasurable,
R > 0,
positive residual square-sum a.e.,
residual square-sum <= R^2 a.e.,
t > 0,
[SFinite nu],
[nu.IsAddHaarMeasure].
```

The optional reverse wrappers are defensible API because they expose product
finiteness implying residual-power finiteness without forcing users through
the iff theorem.

## Follow-up Applied

The reviewer noted that the statement card summary should mention the ambient
finite-dimensional/Borel/Haar/SFinite assumptions.  The statement card and
reproduction note were amended accordingly.
