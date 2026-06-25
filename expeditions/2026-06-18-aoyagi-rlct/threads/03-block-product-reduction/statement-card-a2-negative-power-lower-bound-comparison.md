# Statement Card - A2 negative-power lower-bound comparison

Date: 2026-06-25.

## Claim

Let `a,b : alpha -> ℝ`, let `mu` be a measure, and let `c,t : ℝ`.  If

```text
c > 0,
t >= 0,
a(x) > 0       for mu-a.e. x,
c*a(x) <= b(x) for mu-a.e. x,
∫⁻ x, ENNReal.ofReal(a(x)^(-t)) dmu < infinity,
```

then

```text
∫⁻ x, ENNReal.ofReal(b(x)^(-t)) dmu < infinity.
```

## Lean Artifact

File:

```text
lean/DLNFibre/DLN/Aoyagi/RegularSuspensionIntegrability.lean
```

Theorem:

```text
DLNFibre.DLN.Aoyagi.lintegral_ofReal_rpow_neg_lt_top_of_ae_pos_of_ae_const_mul_le
```

## Proof Ingredients

- Monotonicity of negative real powers on positive bases:
  `Real.rpow_le_rpow_of_nonpos`;
- multiplicativity of real powers on nonnegative factors:
  `Real.mul_rpow`;
- `ENNReal.ofReal_mul` for the nonnegative constant factor;
- `lintegral_mono_ae`;
- `lintegral_const_mul'`;
- `ENNReal.mul_lt_top`.

## Nonclaims

- No construction of the lower bound for Aoyagi's residual product map.
- No monomial negative-power integrability theorem.
- No finite chart cover theorem.
- No density or prior transport theorem.
- No endpoint theorem, divergent-side theorem, or threshold equality.
- No Aoyagi p.13 analytic chart/Jacobian construction.
- No Aoyagi Lemma 1, Aoyagi Theorem 4, or regular-coordinate additivity.
- No normal-crossing construction, pole order, or RLCT.
