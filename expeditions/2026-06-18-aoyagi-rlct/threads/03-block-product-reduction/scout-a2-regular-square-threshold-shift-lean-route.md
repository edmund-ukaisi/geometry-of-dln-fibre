# Scout - A2 regular-square threshold-shift Lean route

Date: 2026-06-25.

Scout: xhigh `Ohm the 4th`.

Status: route probe; no Lean edits by the scout.

## Target

The true regular-square theorem should control the fiber integral

```text
∫_{ball(0,R)} (a + ||u||^2)^(-s) du
```

for `a > 0` in the supercritical regime

```text
finrank_R(E) / 2 < s.
```

The expected bound is by a finite constant times

```text
a^(finrank_R(E)/2 - s).
```

This is the missing analytic input for proving that adding `dim(E)` regular
square variables shifts a local power-integrability threshold by `dim(E)/2`.

## Proposed Mathlib Route

Use scaling plus the Japanese-bracket integrability theorem, rather than
building a new polar-coordinate evaluation from scratch.

Useful APIs:

- `integrable_rpow_neg_one_add_norm_sq` in
  `Mathlib/Analysis/SpecialFunctions/JapaneseBracket.lean`;
- `Measure.integral_comp_smul`,
  `Measure.integral_comp_smul_of_nonneg`,
  `Measure.setIntegral_comp_smul_of_pos`,
  `integrable_comp_smul_iff`, and `Integrable.comp_smul` in
  `Mathlib/MeasureTheory/Measure/Haar/NormedSpace.lean`;
- `lintegral_prod`, `lintegral_lintegral`, and `lintegral_prod_mul` in
  `Mathlib/MeasureTheory/Measure/Prod.lean`;
- real-power algebra lemmas around `Real.rpow_add`, `Real.rpow_mul`,
  `Real.mul_rpow`, and `Real.rpow_le_rpow_of_nonpos`.

## Recommended Slices

1. Prove global model finiteness:

```text
∫⁻ v, ENNReal.ofReal ((1 + ||v||^2)^(-s)) < infinity
```

under `finrank_R(E)/2 < s`.

2. Prove the fixed-positive-parameter fiber bound:

```text
∫⁻ u in ball(0,R), ENNReal.ofReal ((a + ||u||^2)^(-s))
  <= C * ENNReal.ofReal (a^(finrank_R(E)/2 - s)).
```

3. Use the fiber bound in a product theorem over a base measure with
`a(x) > 0` a.e. and

```text
∫⁻ x, ENNReal.ofReal ((a x)^(finrank_R(E)/2 - s)) dmu < infinity.
```

## Risks

The main risk is bookkeeping, not missing analysis: the proof needs careful
real-power algebra around `sqrt(a)`, `a^(finrank/2)`, and
`(a * (1 + ||v||^2))^(-s)`.  Keep `a > 0`; do not state this route at
`a = 0`.

## Boundary

This route is independent of the normal-crossing-to-RLCT extraction theorem.
It should not mention normal-crossing certificates.  It proves threshold-level
integrability control, not pole-order preservation by itself.
