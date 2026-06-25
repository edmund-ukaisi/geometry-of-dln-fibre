# Statement Card - A2 product below-critical integrability

Date: 2026-06-24.

## Claim

Let `X` be a measurable space with finite measure `mu`.  Let `E` be a
nontrivial finite-dimensional real normed space with additive Haar measure
`nu`, and let `d = finrank_R(E)`.

If

```text
R > 0,
a(x) >= 0 for mu-a.e. x,
s >= 0,
2s < d,
```

then

```text
∫_{X x E} ENNReal.ofReal
  (1_{ball(0,R)}(u) * (a(x)+||u||^2)^(-s))
  d(mu x nu)
```

is finite.

## Lean Artifact

File:

```text
lean/DLNFibre/DLN/Aoyagi/RegularSuspensionIntegrability.lean
```

Theorem:

```text
DLNFibre.DLN.Aoyagi.lintegral_ofReal_add_norm_sq_rpow_neg_indicator_ball_prod_lt_top
```

## Proof Ingredients

- a.e. nonnegativity of the base term;
- `Measure.ae_ne` on the additive Haar regular factor;
- a.e. domination by the `a = 0` regular-ball integrand;
- the already proved open-ball radial finite-side theorem;
- `lintegral_prod_mul` and finiteness of the base measure.

## Nonclaims

- No regular-variable `+ dim(E)/2` threshold shift.
- No theorem for `s >= dim(E)/2`.
- No endpoint theorem.
- No lower/divergence theorem.
- No uniform asymptotic in `a`.
- No bounded-density or prior theorem.
- No Aoyagi p.13 analytic chart/Jacobian construction.
- No normal-crossing construction, pole order, or RLCT.
