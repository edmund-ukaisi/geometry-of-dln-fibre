# Reproduction - A0 normal-crossing exponent interface

Source: Aoyagi 2023 PDF pp. 5-6 only.

## Source calculation

Aoyagi applies Hironaka's theorem to a Kullback function and writes, on each
local chart with coordinates `u = (u_1, ..., u_d)`,

```text
K(pi(u)) = unit(u) * product_j u_j^(2 k_j),
pi'(u) phi(pi(u)) = unit'(u) * product_j u_j^(h_j).
```

The units and the existence of the finite chart cover are analytic data.  The
finite calculation after those hypotheses are supplied is:

```text
lambda = min_chart min_{j : k_{chart,j} > 0} (h_{chart,j}+1)/(2 k_{chart,j}),
theta  = max_chart Card { j : k_{chart,j} > 0 and
                           (h_{chart,j}+1)/(2 k_{chart,j}) = lambda }.
```

Coordinates with `k_j = 0` do not impose a finite integrability bound in the
one-variable factor and cannot be included in the denominator.  They are
ignored before the finite minimum is taken.

## Pen-and-paper check

For a single active coordinate, the local factor has the form

```text
|u_j|^(-2 c k_j) * |u_j|^(h_j).
```

The one-variable integral near zero is finite exactly below the threshold

```text
h_j - 2 c k_j > -1,
```

which gives

```text
c < (h_j + 1)/(2 k_j)
```

when `k_j > 0`.  A product chart is finite when all active coordinate
thresholds are respected, so the chart threshold is the minimum of those
ratios.  A finite chart cover takes the worst chart, hence the minimum over
charts.  At the global threshold, the pole order is the number of coordinates
in a single chart attaining the global threshold; the final order is the
maximum of this chartwise count over the finite cover.

## Lean representation

`AoyagiNormalCrossingExponentData` records:

- finite chart and coordinate index sets;
- natural loss exponents `k`;
- natural Jacobian/prior exponents `h`;
- a nonempty active coordinate set `k > 0`.

The PDF text says the displayed exponents are "non-positive integers", but the
monomial form and the threshold calculation use the usual nonnegative order
convention.  Lean stores these exponents as natural numbers.  If a later
analytic certificate needs a signed exponent presentation, it should pass
through a separate adapter with explicit nonnegativity hypotheses.

`activePairs` filters out zero-loss-exponent coordinates before any minimum.
`activeRatios` images active pairs under `(h+1)/(2*k)`.
`exponentMinimum` is the finite minimum of `activeRatios`.
`minCoordsInChart` counts active coordinates in one chart whose ratio is the
global minimum.
`exponentOrder` is the maximum of these chartwise counts.

`AoyagiNormalCrossingExtractionHypothesis D lambda theta` is the explicit
cited-boundary assumption saying that the analytic normal-crossing extraction
theorem identifies the external `lambda` and `theta` with this finite
arithmetic.  The Lean module proves the finite minima/count infrastructure, not
the analytic theorem.

## Nonclaims

This slice does not prove Hironaka resolution, construct analytic charts,
prove nonvanishing of units, prove prior hypotheses, prove Aoyagi Lemma 1,
prove regular-coordinate additivity, prove Theorem 4, identify any RLCT, or
show that Aoyagi's blow-up recursion supplies normal-crossing data.

## Kill conditions

- A zero-loss exponent coordinate is included in the ratio minimum.
- `theta` is summed across charts instead of maximized chartwise.
- A chart-local minimum is counted even when it is not equal to the global
  minimum.
- The Lean structure is used as if it proved the analytic extraction theorem.
