# Reproduction - A0 normal-crossing chart-certificate spine

Status: reproduced and formalised; independent review pending.

Source: Aoyagi 2023 PDF pp. 5-6.

## Source Anchor

Definition 1 defines the log canonical threshold by local integrability and
the zeta-function pole order.  After applying Hironaka's theorem to the
Kullback function, Aoyagi writes local coordinates `u=(u_1,...,u_d)` with

```text
K(pi(u)) = u_1^(2 k_1) ... u_d^(2 k_d),
pi'(u) phi(pi(u)) = u_1^(h_1) ... u_d^(h_d),
```

and then gives the finite formulas

```text
lambda = min_U min_j (h_j + 1)/(2 k_j),
theta  = max_U Card {j : (h_j + 1)/(2 k_j) = lambda}.
```

The PDF suppresses units in the displayed monomial forms.  The standard
normal-crossing certificate includes nonvanishing unit factors multiplying
these monomials; the finite ratios are unchanged by units.

The source text says the exponents are "non-positive integers".  The displayed
monomial powers and the finite threshold calculation use nonnegative order
exponents.  Lean keeps the existing natural-number convention and treats the
analytic sign convention as part of the cited analytic presentation, not as a
finite arithmetic theorem.

## Pen-And-Paper Reproduction

For one chart `c`, a source-facing certificate must remember:

```text
chart points u in U_c,
chart map pi_c(u),
coordinates u_j,
K(pi_c(u)) = unit_K(c,u) * product_j u_j^(2 k_cj),
pi'_c(u) phi(pi_c(u))
  = unit_J(c,u) * product_j u_j^(h_cj).
```

The unit factors must be nonvanishing.  In algebraic Lean over a commutative
monoid, "nonvanishing unit" is represented by `IsUnit` for the displayed unit
factor.  This is only a placeholder for the analytic nonvanishing condition;
the analytic theorem applying to real or complex charts remains cited.

The finite part obtained by forgetting chart maps, coordinates, and units is
exactly the existing exponent data:

```text
numCharts,
numCoords,
lossExp(c,j) = k_cj,
jacobianPriorExp(c,j) = h_cj,
exists (c,j), 0 < k_cj.
```

The active-coordinate condition prevents division by zero in
`(h+1)/(2*k)`.  Coordinates with `k=0` are ignored before taking the finite
minimum.

## Lean Shape

The new structure
`AoyagiNormalCrossingChartCertificate Param R` records:

- finite chart and coordinate counts;
- a chart-point type for each finite chart, with a nonempty witness;
- chart maps and chart coordinates;
- loss and combined Jacobian-prior functions;
- loss and Jacobian-prior unit factors;
- exponent arrays;
- monomial identities for loss and Jacobian-prior;
- unit witnesses for both unit factors;
- a nonempty active loss-exponent witness.

The projection
`AoyagiNormalCrossingChartCertificate.exponentData` forgets the chart-level
data and returns the existing `AoyagiNormalCrossingExponentData`.

The chart-level `ExtractionHypothesis` is a wrapper around the existing
`AoyagiNormalCrossingExtractionHypothesis C.exponentData lambda theta`.  It is
still the cited analytic boundary; it does not prove that the chart
certificate satisfies the hypotheses of the analytic theorem.

The A6 wrapper `AoyagiTheorem2SuppliedChartFinalBoundary` packages a chart
certificate, chart-level extraction hypothesis, selected-width provenance, and
finite exponent formula equalities, then projects to the existing supplied
final boundary.

## Not Proved

No Hironaka theorem, analytic chart construction, properness, chart coverage,
coordinate validity, analytic nonvanishing theorem, change of variables,
integrability threshold theorem, zeta-pole statement, ideal-generator
comparison, prior-independence theorem, source construction of exponent data,
finite exponent formula equality, Lemma 5 count, pole order without A0, or
RLCT extraction is proved.

## Kill Conditions

- The chart certificate is used as if it proved the analytic extraction
  theorem.
- The unit fields are interpreted as a proof of analytic nonvanishing for real
  or complex functions.
- The chart-point nonempty field is treated as chart coverage.
- The projected exponent data is used after changing the meaning of `lossExp`
  from `k` to `2*k`.
