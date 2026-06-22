# Reproduction - Normal-crossing ratio chart counts

Date: 2026-06-22.

Status: A0 finite definitional rewrite.

## Source Boundary

Aoyagi PDF pp. 5-6 gives the normal-crossing finite formula after charts have
been supplied.  The exponent is the minimum active ratio `(h+1)/(2k)`, and the
order is the maximum chartwise number of active coordinates attaining that
minimum.

This slice adds a source-facing finite count at a specified ratio `q`.  It
does not construct charts or prove that any displayed source count is correct.

## Definitions

For supplied finite exponent data `D`, define:

```text
coordsInChartAtRatio q c
  = { j | 0 < lossExp c j and ratioAt (c,j) = q }

countInChartAtRatio q c
  = #(coordsInChartAtRatio q c).
```

The existing minimum-coordinate set is:

```text
minCoordsInChart c
  = { j | 0 < lossExp c j and ratioAt (c,j) = D.exponentMinimum }.
```

## Rewrite

If `D.exponentMinimum = q`, then for each chart `c`:

```text
minCoordsInChart c = coordsInChartAtRatio q c.
```

This is extensional: a coordinate `j` is in the left-hand set exactly when it
has positive loss exponent and `ratioAt (c,j) = D.exponentMinimum`; after
rewriting `D.exponentMinimum` as `q`, this is exactly membership in
`coordsInChartAtRatio q c`.

Taking cardinalities gives:

```text
minCountInChart c = countInChartAtRatio q c.
```

## Order Certificate

If `D.exponentMinimum = ratio`, and a chart `c` satisfies:

```text
countInChartAtRatio ratio c = N,
forall c', countInChartAtRatio ratio c' <= N,
```

then the previous finite maximum certificate applies after rewriting every
`minCountInChart c'` to `countInChartAtRatio ratio c'`:

```text
D.exponentOrder = N.
```

## Lean Names

```text
AoyagiNormalCrossingExponentData.coordsInChartAtRatio
AoyagiNormalCrossingExponentData.countInChartAtRatio
AoyagiNormalCrossingExponentData.minCoordsInChart_eq_coordsInChartAtRatio_of_exponentMinimum_eq
AoyagiNormalCrossingExponentData.minCountInChart_eq_countInChartAtRatio_of_exponentMinimum_eq
AoyagiNormalCrossingExponentData.exponentOrder_eq_of_countInChartAtRatio_eq_of_forall_le
```

## Nonclaims

This does not prove normal-crossing chart production, active-ratio
inequalities, chart-count upper bounds, unit nonvanishing, Jacobian/prior
exponent correctness, pole order, normal crossings, or RLCT extraction.

## Kill Conditions

- `countInChartAtRatio q c` is only a count at a candidate ratio.  It becomes
  a minimum-coordinate count only after `D.exponentMinimum = q` is supplied or
  proved.
- The order certificate is still a maximum over chartwise counts, not a sum
  over charts.
