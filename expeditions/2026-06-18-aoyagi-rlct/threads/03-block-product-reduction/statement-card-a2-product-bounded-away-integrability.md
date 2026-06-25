# Statement Card - A2 product bounded-away integrability

Date: 2026-06-25.

## Claim

Let `X` be a measurable space with finite measure `mu`.  Let `E` be a
nontrivial finite-dimensional real normed space with additive Haar measure
`nu`.

In Lean this is stated with the typeclass assumptions

```text
[MeasurableSpace X],
[NormedAddCommGroup E],
[NormedSpace R E],
[MeasurableSpace E],
[BorelSpace E],
[FiniteDimensional R E],
[Nontrivial E],
[IsFiniteMeasure mu],
[nu.IsAddHaarMeasure].
```

If

```text
epsilon > 0,
a(x) >= epsilon for mu-a.e. x,
s >= 0,
```

then, for every real `R`,

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
DLNFibre.DLN.Aoyagi.lintegral_ofReal_add_norm_sq_rpow_neg_indicator_ball_prod_lt_top_of_ae_pos_le
```

## Proof Ingredients

- a.e. lower bound `epsilon <= a(x)`;
- monotonicity of `t^(-s)` for `s >= 0`;
- finiteness of Haar measure on metric balls in finite-dimensional real
  normed spaces;
- `lintegral_indicator_const`;
- `lintegral_prod_mul` and finiteness of the base measure.

## Review

Review:

```text
review-a2-product-bounded-away-integrability.md
```

## Nonclaims

- No regular-variable `+ dim(E)/2` threshold shift.
- No singular-base theorem where `a(x)` approaches zero.
- No endpoint theorem.
- No lower/divergence theorem.
- No uniform asymptotic in `a`.
- No bounded-density or prior theorem.
- No Aoyagi p.13 analytic chart/Jacobian construction.
- No normal-crossing construction, pole order, or RLCT.
