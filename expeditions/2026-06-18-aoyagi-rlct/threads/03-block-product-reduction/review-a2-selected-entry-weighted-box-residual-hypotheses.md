# Review - A2 selected-entry weighted-box residual hypotheses

Date: 2026-06-28.

Reviewer: xhigh `Maxwell the 3rd`.

Verdict: PASS.

## Findings

No scoped correctness issues found.

The Lean theorem statement stays within the selected-entry weighted signed-box
model: it defines the product signed-box measure, weights it by
`ofReal (sourceDensity pivot y)`, and proves only residual a.e. positivity plus
finite negative-power `lintegral`.  It does not claim retained-passive source
transport, source pushforward, or original DLN prior transport.

The hypotheses are correctly scoped.  `pivot : center` rules out an empty
center.  Singleton centers reduce the critical inequality to `2 * t < 1`,
which is the expected one-dimensional condition.  Positive radii are explicit,
the pivot/non-pivot exponent split matches the pen-and-paper calculation, and
the finite-product null-coordinate step uses the existing signed-box
a.e.-nonzero-coordinate lemma.

The `withDensity` and `ofReal_mul` step is sound.  The proof first obtains
finiteness for `ofReal (residual^(-t) * sourceDensity)` under the unweighted
signed-box measure, rewrites the weighted integral as multiplication by the
density, and uses `ofReal_mul'` with a.e. nonnegativity of the source density.

The reproduction and statement card state the correct arithmetic boundary:

```text
(|center|-1) - 2*t > -1,
```

equivalently

```text
2*t < |center|,
```

formalized as

```text
2 * t < ((center.erase pivot.1).card : R) + 1.
```

Lean hygiene/import risk is low: no new imports were added, the local
`set_option` is scoped to the theorem, and the focused module elaborates.

## Residual Risk

This result remains only the elementary selected-entry signed-box measure
calculation.  It is not a retained-passive source-production bridge and does
not prove RLCT extraction.
