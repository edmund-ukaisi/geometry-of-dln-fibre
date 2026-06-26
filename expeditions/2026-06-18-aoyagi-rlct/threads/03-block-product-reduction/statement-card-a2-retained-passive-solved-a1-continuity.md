# Statement Card - A2 retained-passive solved-A1 continuity

## Lean Files

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesTopology.lean
```

## Lean Names

```text
DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.continuous_retainedPassiveA1TailAfterFirst
DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.continuous_solvedA1_detChart_subtype
```

## Reproduction

```text
reproduction-a2-retained-passive-solved-a1-continuity.md
```

## Claim

The passive top-left tail product

```text
retainedPassiveA1TailAfterFirst(data.A1seed)
```

is continuous in the nonredundant retained-passive coordinates.

On the determinant-chart subtype, every component of the solved full `A1`
family is continuous:

```text
data ↦ (data.1.toCoordinateData).solvedA1 p.
```

## Method

Tail continuity is proved by decreasing induction over
`residualFactorProduct`: the endpoint product is the constant identity and
each step multiplies the next product by the continuous component
`data.A1seed p`.

For the zero solved component, determinant-chart membership gives unit
determinants for the passive seed blocks; the existing tail-unit theorem gives
`IsUnit det(Tail)`, and the existing matrix-inverse continuity theorem makes
`Tail^-1` continuous on the subtype.  Multiplication by the continuous `Ctop`
projection gives the zero component.  Nonzero components reduce to
`A1seed`.

## Role

This is the first inverse-dependent endpoint continuity fact for the
retained-passive chart.  It prepares the harder `solvedA3` continuity proof,
whose final slot also depends on finite tail sums involving solved `A1`.

## Nonclaims

No continuity of `solvedA3`, `toCoordinateData`, or `edgeMatrix` is proved.
No image openness, source-rank coverage, source/image equality, measure
transport, density/Jacobian theorem, normal crossings, pole order, or RLCT
extraction is proved.

## Verification

Focused check passed on 2026-06-26:

```text
cd lean
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinatesTopology
```

Full-library and hygiene checks passed on 2026-06-26:

```text
cd lean
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre
scripts/sorries
git diff --check
```

The focused check was independently rerun by xhigh reviewer
`Popper the 3rd` and passed.  Review:
`review-a2-retained-passive-solved-a1-continuity.md`.
