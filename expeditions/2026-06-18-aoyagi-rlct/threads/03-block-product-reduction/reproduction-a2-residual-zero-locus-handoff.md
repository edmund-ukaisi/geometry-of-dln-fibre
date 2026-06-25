# Reproduction - A2 residual zero-locus handoff

Status: formalised and xhigh checked.

## Source Anchor

The p.13 local finite-integral bridge consumes a residual positivity input:

```text
0 < residualSquareSum(x)  for almost every x on the source stratum.
```

This slice replaces that direct positivity hypothesis by a more geometric
null-zero-locus hypothesis.  It does not prove the zero locus is null, and it
does not prove residual negative-power integrability.

## Calculation

Let `f : α -> R` be nonnegative everywhere.  If

```text
μ {x | f x = 0} = 0,
```

then `0 < f x` for `μ`-almost every `x`.

Indeed, the exceptional set for positivity is

```text
{x | not (0 < f x)}.
```

Since `0 <= f x` for every `x`, any point in this exceptional set has
`f x = 0`.  Hence the exceptional set is contained in the null zero locus, so
it is null.

For the Aoyagi residual block,

```text
f(x) =
  aoyagiCoordinateSquareSum
    (paperEndpointFixedBaseResidualBlockCoordinateMap ... x).
```

The repo already proves coordinate square-sums are nonnegative.  Therefore the
same argument gives residual positivity a.e. from nullity of the residual
zero-locus under `μ.restrict source`.

## Restriction Plumbing

The existing local finite-integral bridge shrinks from a source stratum `S` to
`U ∩ S`.  If the residual zero locus is null on `S`, then residual positivity
is first obtained on `S`, and the existing monotonicity helper transfers both
positivity and residual negative-power integrability to the smaller source.

Thus the new combined helper consumes:

```text
source' subset source,
zero residual locus is null on source,
residual negative-power integral is finite on source,
```

and returns the residual positivity/integrability pair on `source'`.

## Lean Landing

Lean adds the generic measure lemma in `LocalMeasureHandoff.lean`:

```text
ae_pos_of_forall_nonneg_of_measure_zero_eq_zero
```

Lean adds the Aoyagi residual specializations in
`RegularSuspensionLocalMeasure.lean`:

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.residualSquareSum_pos_ae_of_zero_set_null
PaperEndpointFixedBaseRegularCoordinateSourceData.residualSourceHypotheses_mono_of_zero_set_null
```

## Nonclaims

- No proof that the residual zero locus is null.
- No proof of residual negative-power integrability.
- No construction of a source chart or product chart.
- No Jacobian/density transport.
- No original DLN loss comparison.
- No normal-crossing production, pole order, or RLCT extraction.
