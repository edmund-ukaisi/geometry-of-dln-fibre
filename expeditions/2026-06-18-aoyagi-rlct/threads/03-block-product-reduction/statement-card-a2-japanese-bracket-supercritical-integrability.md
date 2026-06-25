# Statement Card - A2 Japanese-bracket supercritical integrability

Date: 2026-06-25.

## Claim

Let `E` be a finite-dimensional real normed space with additive Haar measure
`mu`.

If

```text
finrank_R(E) / 2 < s,
```

then

```text
(1 + ||x||^2)^(-s)
```

is integrable, and

```text
∫⁻ x, ENNReal.ofReal ((1 + ||x||^2)^(-s)) dmu
```

is finite.

If additionally `a > 0`, then

```text
∫⁻ x, ENNReal.ofReal ((a + ||x||^2)^(-s)) dmu
```

is finite.

## Lean Artifact

File:

```text
lean/DLNFibre/DLN/Aoyagi/RegularSuspensionIntegrability.lean
```

Theorems:

```text
DLNFibre.DLN.Aoyagi.integrable_one_add_norm_sq_rpow_neg
DLNFibre.DLN.Aoyagi.lintegral_ofReal_one_add_norm_sq_rpow_neg_lt_top
DLNFibre.DLN.Aoyagi.lintegral_ofReal_norm_sq_add_pos_rpow_neg_lt_top
```

## Proof Ingredients

- Mathlib `integrable_rpow_neg_one_add_norm_sq`;
- the arithmetic equivalence `finrank/2 < s` implies `finrank < 2s`;
- nonnegative `ENNReal.ofReal` lower-integral handoff from real integrability;
- fixed-parameter comparison using `c = min(a,1)`;
- `Real.rpow_le_rpow_of_nonpos` and `Real.mul_rpow`.

## Nonclaims

- No sharp `a^(finrank/2-s)` bound.
- No product theorem with a base function `a(y)` approaching zero.
- No regular-variable `+ dim(E)/2` threshold shift.
- No endpoint theorem.
- No lower/divergence theorem.
- No uniform asymptotic in `a`.
- No bounded-density or prior theorem.
- No Aoyagi p.13 analytic chart/Jacobian construction.
- No normal-crossing construction, pole order, or RLCT.
