# Statement Card - A2 positive-box monomial integrability

Date: 2026-06-25.

## Claim

For a finite index type `i`, radii `R_i>0`, and exponents `p_i>-1`,

```text
∫⁻ x : i -> R, ofReal(prod_i x_i^(p_i))
  d Measure.pi (i |-> volume.restrict (0,R_i))
<
infinity.
```

In Aoyagi's exponent notation, if `h_i,k_i : Nat` and

```text
2*t*k_i < h_i + 1
```

for every `i`, then

```text
∫⁻ x, ofReal(prod_i x_i^(h_i - 2*t*k_i)) < infinity
```

on the same positive box.

## Lean Artifact

File:

```text
lean/DLNFibre/DLN/Aoyagi/MonomialChartIntegrability.lean
```

Theorems:

```text
DLNFibre.DLN.Aoyagi.lintegral_ofReal_rpow_restrict_Ioo_lt_top
DLNFibre.DLN.Aoyagi.lintegral_ofReal_monomialFactor_restrict_Ioo_lt_top
DLNFibre.DLN.Aoyagi.lintegral_ofReal_fintype_rpow_positiveBox_lt_top
DLNFibre.DLN.Aoyagi.lintegral_ofReal_fintype_monomialFactor_positiveBox_lt_top
```

Aggregator import:

```text
lean/DLNFibre.lean
```

## Proof Ingredients

- `intervalIntegral.integrableOn_Ioo_rpow_iff`;
- `MeasureTheory.Integrable.fintype_prod`;
- `lintegral_ofReal_le_lintegral_enorm`;
- `hasFiniteIntegral_iff_enorm`;
- arithmetic conversion from `2*t*k < h+1` to `-1 < h-2*t*k`.

## Nonclaims

- No residual-loss lower-bound theorem.
- No density or prior upper-bound theorem.
- No signed-box or absolute-value monomial theorem.
- No endpoint theorem, divergent-side theorem, or threshold equality.
- No finite chart cover theorem.
- No Aoyagi p.13 analytic chart/Jacobian construction.
- No Aoyagi Lemma 1, Aoyagi Theorem 4, or regular-coordinate additivity.
- No normal-crossing construction, pole order, or RLCT.
