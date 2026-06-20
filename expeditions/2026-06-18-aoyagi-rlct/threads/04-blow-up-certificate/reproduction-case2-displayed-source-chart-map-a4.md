# A4 Case 2 Displayed Source-Chart Map

Status: reproduced the source-coordinate displayed top-left Case 2 chart map.

## Source Situation

Aoyagi's displayed Case 2 chart selects the top-left residual-block entry

```text
d_(J+1,J+1) = u_(S,J+1).
```

The residual rows are

```text
J+1 <= i <= M(S),
```

where `M(S)` is the prefix minimum. The residual columns are

```text
J+1 <= j <= M^(S+1),
```

where `M^(S+1)` is the actual active width. The continuation condition

```text
J+1 <= M(S+1) = min(M(S), M^(S+1))
```

puts `(J+1,J+1)` in both ranges.

## Reproduction

Let

```text
I = {i | J+1 <= i <= M(S)}
K = {j | J+1 <= j <= M^(S+1)}.
```

The displayed selected-entry chart is the finite substitution

```text
d_(J+1,J+1) = u,
d_ij         = u*rho_ij      for (i,j) != (J+1,J+1).
```

Equivalently, after normalising the pivot,

```text
D_src = u*A,
A_(J+1,J+1) = 1.
```

The source-coordinate map is therefore

```text
chart(p) = selectedEntryChartMap (J+1,J+1) u residual p,
norm(p)  = selectedEntryNormalizedMap (J+1,J+1) residual p.
```

Restricting to the residual block gives

```text
Sub(i,j) = chart(i,j),
Norm(i,j) = norm(i,j).
```

The existing displayed block API uses subtype indices. The only bookkeeping
bridge needed is:

```text
(i.val,j.val) = (J+1,J+1)
  iff
(i,j) = (displayedPivotRow, displayedPivotCol).
```

This proves:

```text
Norm = case2DisplayedNormalizedMatrix (case2SourceResidualBlock residual),
Sub  = case2DisplayedSubstitutionMatrix u (case2SourceResidualBlock residual),
Sub  = u * Norm.
```

The diagonal source-variable transport then follows from the existing displayed
block theorem:

```text
(diag(weight) * Sub)^pivotFirst
  =
diag_pivotFirst(u*weight) * pivotFirst(Norm).
```

For a source following factor `C`, the transported following factor is the
source-coordinate version of Aoyagi's `Q^-1 C`:

```text
Ctr = Q^-1(Norm) * C^pivotFirst.
```

The displayed supplied boundary can therefore restate its existing
source-coordinate `Q/P` identity entirely in these source-chart names.

## Scope / Caveats

- This is only the displayed top-left Case 2 source-coordinate chart map.
- It proves source map restriction to the existing displayed block API.
- It does not prove chart coverage, non-top-left source-displayed formulas, or
  arbitrary-pivot source-order formulas.
- It does not prove recurrence or exponent post-data are chart-produced.
- It does not compute a Jacobian or prove coordinate regularity.
- It does not prove normal crossings, RLCT extraction, termination, or a full
  transition invariant.
- The corrected exponent update remains the prefix-minimum certificate; the
  printed Case 2 vector mismatch remains separate.
