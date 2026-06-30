# Review - A2 chart-piece readback-domination handoff

Date: 2026-06-30.

Reviewer: xhigh `Schrodinger the 2nd`.

Status: PASS.

## Scope

Review target files:

```text
lean/DLNFibre/DLN/Aoyagi/LocalMeasureHandoff.lean
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaSourceImage.lean
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaSourceImageJacobianBridge.lean
```

## Controller Check

The proof keeps all source/prior transport obligations explicit.  The new
Aoyagi theorem assumes:

```text
MeasurableSet chartPiece
chartPiece subset sourceLocal
forall E in chartPiece,
  readback E in W and sourceChart (readback E) = E
AEMeasurable readback (externalSourceMeasure.restrict chartPiece)
Measure.map readback (externalSourceMeasure.restrict chartPiece)
  <= Cpull * coordinateSourceMeasure.restrict W
Cpull < infinity
```

The derived domination has the intended target:

```text
externalSourceMeasure.restrict chartPiece
  <= Cpull * sourceImageMeasure.restrict sourceLocal.
```

It then productizes the domination and feeds the existing finite-product
socket.

## Findings

No blocking correctness issue found.

The measure direction is correct: the supplied readback-side domination is
pushed forward through `sourceChart`, recovered on `chartPiece` using the
pointwise right-inverse identity, sharpened to `sourceLocal` using support on
`chartPiece`, and then producted with `nu`.

The helper

```text
measure_le_smul_restrict_of_le_smul_of_restrict_eq_self
```

uses support of the left measure on `U` to replace `nu s` by
`nu (s inter U)` before applying `nu <= c * mu`.  The helper

```text
restrict_le_smul_restrict_of_le_smul_of_subset
```

correctly upgrades domination by `eta` to domination by `eta.restrict t`
because `mu.restrict s` is supported on `t`.

The generic chart-piece helper assumes readback domination and the pointwise
right inverse; it does not assert original-prior transport or image coverage.
The Aoyagi theorem has `[SFinite nu]` for product domination.  The
coordinate/source-image measure identity is the chart-produced density
identity, not an external-prior equality.

## Wording Fix Applied

The reviewer suggested clarifying the main theorem docstring.  The docstring
now states that the usual measurability and local boundedness hypotheses for
`sourceImageDensity` remain present, and that `chartPiece` measurability and
containment in `sourceLocal` are supplied by the caller.

## Review Focus

- inequality direction in the readback-domination hypothesis;
- support sharpening from `sourceImageMeasure` to
  `sourceImageMeasure.restrict sourceLocal`;
- product domination requiring `[SFinite nu]`;
- nonclaim boundary around original prior, source-image equality, Haar
  transport, normal crossings, pole order, and RLCT.
