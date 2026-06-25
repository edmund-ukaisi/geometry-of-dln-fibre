# Reproduction - A2 positive-box monomial integrability

Date: 2026-06-25.

Status: pen-and-paper reproduction and Lean formalisation for the positive-box
monomial factor theorem.

## Scope

This slice proves the elementary finite-side integrability theorem for products
of one-dimensional monomial factors on a positive box.  It is the base
integrability layer needed before a later residual/density comparison theorem.

It is independent of the quiver paper.  It does not use Aoyagi Lemma 1,
Aoyagi Theorem 4, regular-coordinate additivity, normal-crossing extraction,
or any RLCT theorem.

## Calculation

First fix `R>0` and a real exponent `p`.  Mathlib's one-dimensional improper
integrability theorem gives

```text
IntegrableOn (x |-> x^p) (0,R) volume  iff  -1 < p.
```

Thus, if `-1<p`,

```text
∫⁻_{x in (0,R)} ofReal(x^p) < infinity.
```

Lean obtains this lower-integral statement from Bochner integrability by the
general inequality

```text
∫⁻ ofReal(f) <= ∫⁻ ||f||_e,
```

and `hasFiniteIntegral_iff_enorm`.

Now let `i` range over a finite type.  On the product measure

```text
mu = Measure.pi (i |-> volume.restrict (0,R_i)),
```

set

```text
f_i(x_i) = x_i^(p_i).
```

If every `R_i>0` and every `p_i>-1`, the one-dimensional step gives
`Integrable f_i` for every `i`.  Mathlib's finite product theorem gives

```text
Integrable (x |-> prod_i f_i(x_i)) mu.
```

Applying the same `ofReal <= enorm` lower-integral handoff gives

```text
∫⁻ x, ofReal(prod_i x_i^(p_i)) dmu < infinity.
```

For the Aoyagi exponent form, take

```text
p_i = h_i - 2*t*k_i.
```

The strict inequality

```text
2*t*k_i < h_i + 1
```

is equivalent to

```text
-1 < h_i - 2*t*k_i.
```

Therefore

```text
∫⁻ x, ofReal(prod_i x_i^(h_i - 2*t*k_i)) dmu < infinity.
```

## Lean Shape

Lean proves these theorems in

```text
lean/DLNFibre/DLN/Aoyagi/MonomialChartIntegrability.lean
```

```text
lintegral_ofReal_rpow_restrict_Ioo_lt_top
lintegral_ofReal_monomialFactor_restrict_Ioo_lt_top
lintegral_ofReal_fintype_rpow_positiveBox_lt_top
lintegral_ofReal_fintype_monomialFactor_positiveBox_lt_top
```

The module is imported by `lean/DLNFibre.lean`.

## Role In The Aoyagi Route

This is the product-factor integrability part of the monomial chart criterion.
The next comparison theorem should combine it with explicit a.e. hypotheses of
the form

```text
loss(z) >= c * prod_i |z_i|^(2*k_i),
density(z) <= C * prod_i |z_i|^(h_i).
```

That future theorem will need to state its hypotheses explicitly, including
`c>0`, a finite nonnegative density constant `C`, the sign condition on `t`,
a.e. positivity where negative powers are used, the needed measurability or
lower-integral comparison assumptions, and a decomposition or comparison from
signed/absolute-value boxes to the positive boxes proved here.

This slice only proves the positive-coordinate model
`prod_i x_i^(h_i-2*t*k_i)` on `prod_i (0,R_i)`.

## Nonclaims

- No residual-loss lower-bound theorem.
- No density or prior upper-bound theorem.
- No signed-box `|x_i|` theorem.
- No endpoint theorem at `2*t*k_i = h_i+1`.
- No divergent-side theorem or threshold equality.
- No finite chart cover theorem.
- No Aoyagi p.13 analytic chart/Jacobian construction.
- No Aoyagi Lemma 1, Aoyagi Theorem 4, or regular-coordinate additivity.
- No normal-crossing construction, pole order, or RLCT extraction.
