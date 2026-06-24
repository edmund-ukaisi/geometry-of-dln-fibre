# Reproduction - A2 chart-local suffix-state field continuity

Date: 2026-06-24.

Status: pen-and-paper reproduction for a focused topology slice.

## Question

The deterministic product-reduction suffix state carries fields

```text
L, B, Ctop, D.
```

`ChartTopology.lean` already proves continuity of the accumulated upper block
`B` through the one-step update and through the whole suffix recursion.  The
next A2 product-reduction gap is field regularity for the other deterministic
multiplier blocks, especially `L`, `Ctop`, and `D`, because the pointwise
triangular block-diagonalization already exposes these blocks.

## Source Anchors

Aoyagi PDF pp. 11-13 performs the product reduction by recursive block
elimination on determinant charts.  The proof uses deterministic multiplier
blocks and residual lower-right blocks.  The Lean formalisation currently
records these as chart-local matrix functions, not analytic maps.

This slice only proves topological continuity of the deterministic fields on
the selected determinant chart.  It does not prove analytic regularity,
exact-rank openness, source-rank-stratum openness, regular-suspension
construction, normal crossings, pole order, or RLCT.

## One-step Calculation

For a current suffix state `S` and edge `E_p`, define

```text
M = fromBlocks(1, S.B, 0, 1) * E_p.
```

The deterministic update is

```text
B'    = topLeft(M)^(-1) * upperRight(M),
Ctop' = S.Ctop * topLeft(M),
D'    = S.D * schurResidualBlock(M),
L'    = fromBlocks(1, 0,
          -(S.D * lowerLeft(M) * (S.Ctop * topLeft(M))^(-1)), 1) * S.L.
```

If `E_p` and the old fields are continuous at `x0`, then `M` is continuous at
`x0`.  The projections `topLeft`, `upperRight`, `lowerLeft`, and `lowerRight`
are continuous linear coordinate projections on matrix entries.

The selected determinant-chart hypothesis says

```text
IsUnit det(topLeft(M x0)).
```

Over a normed field, matrix inversion is continuous at determinant-unit
matrices.  Therefore `topLeft(M x)^(-1)` is continuous at `x0`, and so `B'`
is continuous.

If the induction also carries

```text
IsUnit det(S.Ctop x0),
```

then

```text
det(S.Ctop x0 * topLeft(M x0))
  = det(S.Ctop x0) * det(topLeft(M x0))
```

is a unit.  Thus `(S.Ctop * topLeft(M))^(-1)` is continuous at `x0`.  Since
matrix addition, negation, multiplication, and block assembly are continuous,
`L'`, `Ctop'`, and `D'` are continuous at `x0`.  The same determinant
calculation also gives the next induction invariant:

```text
IsUnit det(Ctop' x0).
```

## Suffix Recursion

The terminal state at the right endpoint has

```text
L = 1, B = 0, Ctop = 1, D = 1,
```

so all fields are constant and `det(Ctop)=1` is a unit.  Descending induction
over `i <= j` applies the one-step continuity result at each edge `p`, using
the existing recursive determinant-chart hypothesis at the basepoint:

```text
identityCornerDetChart
  (ChartLocalSuffixState.transformedEdge (E x0) p
    (ChartLocalSuffixState.suffixState (E x0) j p.succ hpj)).
```

The result should be a bundled theorem: for every suffix state
`suffixState (E x) j i hij`, the basepoint `Ctop.det` is a unit and all four
fields are continuous at `x0`.

## Guardrails

This slice must not:

- assert exact-rank strata are open;
- claim analytic/regular maps from continuity;
- construct the product-reduction local source neighborhood;
- prove regular-suspension or ideal transport;
- infer normal crossings, pole order, or RLCT.
