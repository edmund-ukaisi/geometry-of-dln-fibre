# Draft cited interface - normal-crossing extraction

Status: controller draft from `scout-report.md`, not yet a Lean statement.

Source: Aoyagi PDF pp. 5-6. This is the only analytic theorem the operator has
allowed as a Lean citation.

## Intended cited boundary

The cited interface should say only:

Given a finite normal-crossing chart presentation of the transformed
sum-of-squares loss, with monomial exponents for the loss and monomial exponents
for the Jacobian/weight factor, the RLCT and pole order are computed by the
standard exponent formula.

In Aoyagi's notation on a chart:

```text
K(pi(u)) = unit(u) * product_j u_j^(2 k_j),
pi'(u) phi(pi(u)) = unit'(u) * product_j u_j^(h_j),
lambda = min_j (h_j + 1) / (2 k_j),
theta = card of variables attaining the minimum on the worst chart.
```

For a finite chart cover, `lambda` is the minimum over charts and variables, and
`theta` is the maximum attaining-cardinality among charts that realise the
global minimum. Coordinates with `k_j = 0` must be explicitly ignored or assigned
infinite ratio; they cannot enter the denominator.

## Lean-facing shape

Do not define an RLCT theorem named after Aoyagi's final formula at this layer.
Use a named hypothesis/interface, for example:

```text
NormalCrossingExtractionData -> rlct = exponentMinimum
                              ∧ rlctOrder = exponentOrder
```

or keep it as an explicit assumption in the final theorem:

```text
(hNC : NormalCrossingExtraction ncData lambda theta)
```

The exact Lean representation should wait until A4 supplies the finite
normal-crossing certificate data. The interface must mention all analytic inputs:
resolution charts, nonvanishing unit factors, Jacobian/weight exponents,
positivity/nonvanishing of the prior near the base point, and finite chart cover.

## Explicit non-boundaries

These are not included in the allowed citation unless the operator expands the
scope:

- Aoyagi Lemma 1's ideal-generator comparison/equality on PDF p. 5.
- Aoyagi Theorem 4's deepest-singular-point comparison on PDF p. 14.
- Local analytic coordinate invariance not already packaged into the precise
  normal-crossing extraction statement.
- Regular-coordinate additivity for post-Theorem-3 RLCT reductions, unless the
  final interface is deliberately broadened and reviewed.

## Kill-conditions

- If the final Aoyagi theorem needs global deepest-point comparison, Theorem 4
  must be proved in a restricted form, avoided by a local theorem, or surfaced as
  a scope conflict.
- If a reduction step replaces generators of an ideal before normal-crossing
  data exists, it cannot be justified by the cited normal-crossing extractor
  alone.
- If a chart's minimum is not global across the finite cover, its local `theta`
  is not the final pole order.
