# Reproduction - A2 positive-box monomial domination

Date: 2026-06-25.

Status: pen-and-paper reproduction and Lean formalisation for a direct
domination corollary of positive-box monomial integrability.

## Scope

This slice proves that an arbitrary real-valued integrand has finite
`ENNReal.ofReal` lower integral on a positive monomial box if it is a.e.
bounded above by a finite nonnegative constant times the already-integrable
monomial product.

It is independent of the quiver paper and does not use Aoyagi Lemma 1,
Aoyagi Theorem 4, regular-coordinate additivity, normal-crossing extraction,
or any RLCT theorem.

## Calculation

Let

```text
mu = Measure.pi (i |-> volume.restrict (0,R_i)),
g(x) = prod_i x_i^(p_i).
```

Assume every `R_i>0`, every `p_i>-1`, and `A>=0`.  The previous positive-box
theorem gives

```text
∫⁻ x, ofReal(g(x)) dmu < infinity.
```

If an integrand `f` satisfies, for `mu`-a.e. `x`,

```text
f(x) <= A * g(x),
```

then monotonicity of `ofReal` gives

```text
ofReal(f(x)) <= ofReal(A*g(x)).
```

Since `A>=0`,

```text
ofReal(A*g(x)) = ofReal(A) * ofReal(g(x)).
```

Therefore

```text
∫⁻ ofReal(f)
  <= ofReal(A) * ∫⁻ ofReal(g)
  < infinity.
```

For Aoyagi's exponent form, take

```text
p_i = h_i - 2*t*k_i.
```

The strict inequalities `2*t*k_i<h_i+1` give `p_i>-1`, so the same domination
argument applies to

```text
g(x)=prod_i x_i^(h_i-2*t*k_i).
```

## Lean Shape

Lean proves these theorems in

```text
lean/DLNFibre/DLN/Aoyagi/MonomialChartIntegrability.lean
```

```text
lintegral_ofReal_le_const_mul_fintype_rpow_positiveBox_lt_top
lintegral_ofReal_le_const_mul_fintype_monomialFactor_positiveBox_lt_top
```

The hypotheses are deliberately direct: the caller supplies the a.e. upper
bound by the monomial majorant.  This theorem does not derive that bound from
separate residual-loss and density estimates.

## Role In The Aoyagi Route

This is the finite-side handoff that a later residual/density theorem should
feed after proving the correct pointwise or a.e. domination.  That later
theorem still has to account for `c>0`, the density constant, sign and
measurability hypotheses, a.e. positivity where negative powers are used, and
the signed-box or absolute-value reduction.

## Nonclaims

- No residual-loss lower-bound theorem.
- No density or prior upper-bound theorem.
- No derivation from `loss >= c*prod |x_i|^(2*k_i)`.
- No signed-box or absolute-value monomial theorem.
- No endpoint theorem at `2*t*k_i = h_i+1`.
- No divergent-side theorem or threshold equality.
- No finite chart cover theorem.
- No Aoyagi p.13 analytic chart/Jacobian construction.
- No Aoyagi Lemma 1, Aoyagi Theorem 4, or regular-coordinate additivity.
- No normal-crossing construction, pole order, or RLCT extraction.
