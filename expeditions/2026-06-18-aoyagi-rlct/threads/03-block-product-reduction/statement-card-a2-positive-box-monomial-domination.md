# Statement Card - A2 positive-box monomial domination

Date: 2026-06-25.

## Claim

Let

```text
mu = Measure.pi (i |-> volume.restrict (0,R_i)).
```

If `R_i>0`, `p_i>-1`, `A>=0`, and

```text
f(x) <= A * prod_i x_i^(p_i)
```

for `mu`-a.e. `x`, then

```text
∫⁻ x, ofReal(f(x)) dmu < infinity.
```

In Aoyagi's exponent notation, the same holds for
`p_i=h_i-2*t*k_i` under the strict inequalities

```text
2*t*k_i < h_i + 1.
```

## Lean Artifact

File:

```text
lean/DLNFibre/DLN/Aoyagi/MonomialChartIntegrability.lean
```

Theorems:

```text
DLNFibre.DLN.Aoyagi.lintegral_ofReal_le_const_mul_fintype_rpow_positiveBox_lt_top
DLNFibre.DLN.Aoyagi.lintegral_ofReal_le_const_mul_fintype_monomialFactor_positiveBox_lt_top
```

## Proof Ingredients

- `lintegral_ofReal_fintype_rpow_positiveBox_lt_top`;
- `lintegral_mono_ae`;
- `ENNReal.ofReal_le_ofReal`;
- `ENNReal.ofReal_mul` using `A>=0`;
- `lintegral_const_mul'`;
- `ENNReal.mul_lt_top`.

## Nonclaims

- No residual-loss lower-bound theorem.
- No density or prior upper-bound theorem.
- No derivation from separate loss and density estimates.
- No signed-box or absolute-value monomial theorem.
- No endpoint theorem, divergent-side theorem, or threshold equality.
- No finite chart cover theorem.
- No Aoyagi p.13 analytic chart/Jacobian construction.
- No Aoyagi Lemma 1, Aoyagi Theorem 4, or regular-coordinate additivity.
- No normal-crossing construction, pole order, or RLCT.
