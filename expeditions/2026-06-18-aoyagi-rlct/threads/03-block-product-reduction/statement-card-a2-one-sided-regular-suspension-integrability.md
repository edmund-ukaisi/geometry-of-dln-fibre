# Statement Card - A2 one-sided regular-suspension integrability

Date: 2026-06-24.

## Claim

For ENNReal-valued losses `a` and `q`, exponent `s >= 0`, and product measure
`mu.prod nu`,

```text
∫ (a x + q y)^(-s) d(mu.prod nu)
  <= ∫ (a x)^(-s) d(mu.prod nu).
```

If `nu` is finite and `∫ (a x)^(-s) dmu < infinity`, then the left-hand
product integral is finite.  The same finite-preservation statement holds for
restricted measures `mu.restrict u` and `nu.restrict t` when `nu t < infinity`.

## Lean Artifacts

File:

```text
lean/DLNFibre/DLN/Aoyagi/RegularSuspensionIntegrability.lean
```

Theorems:

```text
DLNFibre.DLN.Aoyagi.lintegral_rpow_neg_add_right_le_prod_fst
DLNFibre.DLN.Aoyagi.lintegral_rpow_neg_add_right_lt_top_of_lintegral_rpow_neg_lt_top
DLNFibre.DLN.Aoyagi.lintegral_rpow_neg_add_right_restrict_lt_top_of_lintegral_rpow_neg_restrict_lt_top
```

## Inputs

- `s >= 0`;
- `AEMeasurable a mu` for the finite-product preservation theorem;
- finite extra measure `nu`, or finite restricted extra measure `nu t`;
- finite base integral of `a^(-s)`.

No measurability of `q` is needed for the one-sided estimate, since the proof
does not evaluate the left integral by Fubini; it only compares it with a
separable right-hand integrand.

## Proof Ingredients

- `ENNReal.rpow_neg`;
- monotonicity of `ENNReal.rpow` for nonnegative exponents;
- inverse order reversal in `ENNReal`;
- `lintegral_mono`;
- `lintegral_prod_mul`;
- `isFiniteMeasure_restrict`.

## Nonclaims

- This is not the `+ k/2` threshold shift.
- This is not a regular-coordinate/Fubini additivity theorem.
- This is not Aoyagi Lemma 1 or Theorem 4.
- This is not normal-crossing-to-RLCT extraction.
- This does not construct Aoyagi's p. 13 analytic chart or density bounds.
