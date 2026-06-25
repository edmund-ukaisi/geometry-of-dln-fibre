# Review - A2 positive-box monomial integrability

Date: 2026-06-25.

Reviewer: xhigh `Lorentz the 4th`.

## Verdict

No high or medium findings.

The Lean slice is correctly scoped as positive-box product-factor
integrability: one-dimensional `x^p` on `(0,R)`, finite product via
`Measure.pi`, and the Aoyagi exponent corollary from `2*t*k_i<h_i+1`.
The notes avoid endpoint, signed-box, density/prior, chart-cover,
normal-crossing, pole-order, and RLCT claims.

## Low Finding

The future residual/density comparison target was described too tersely in the
roadmap text.  It must not be copied forward as a theorem statement without
the missing hypotheses: `c>0`, a suitable finite nonnegative density constant,
the sign condition on `t`, a.e. positivity where negative powers are used,
measurability or lower-integral comparison assumptions, and the signed-box to
positive-box decomposition/comparison.

Action: the reproduction note and priorities text now record this caveat next
to the future-target sketch.

## Verification

The reviewer checked:

```text
lake env lean DLNFibre/DLN/Aoyagi/MonomialChartIntegrability.lean
lake env lean DLNFibre.lean
```

Both passed in the review environment.  The reviewer also confirmed that
`RegularSuspensionIntegrability.lean` has no current diff and was not polluted
with monomial/positive-box terminology.
