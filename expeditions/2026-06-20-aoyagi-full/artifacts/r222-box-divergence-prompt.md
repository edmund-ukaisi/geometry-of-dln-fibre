# Consultation: ε-uniform multivariate monomial divergence (Lean 4 / Mathlib v4.29)

## Goal lemma

I need to PROVE (Lean, sorry-free) the ε-uniform divergence atom for the RLCT ≤-direction:

```
theorem monomialIntegrand_lintegral_box_eq_top (d : ℕ) (k h : Fin d → ℕ) (hk : ∃ j, k j ≠ 0)
    (c' : ℝ) (hc' : monomialThreshold d k h ≤ ENNReal.ofReal c') (hc'0 : 0 < c') {ε : ℝ} (hε : 0 < ε) :
    ∫⁻ u in Set.univ.pi (fun _ : Fin d => Set.Icc (0:ℝ) ε),
        ENNReal.ofReal (|monomialIntegrand d k h c' u|) = ⊤
```

where
```
monomialIntegrand d k h c u := (∏ j, |u j| ^ (h j)) * (∏ j, |u j| ^ (2 * k j)) ^ (-c)   -- ℝ-valued
monomialThreshold d k h := sSup { c : ℝ≥0∞ | ∃ c':NNReal, c = c' ∧ IntegrableOn (monomialIntegrand d k h c') (unitBox d) }
unitBox d := Set.univ.pi (fun _ => Set.Icc (0:ℝ) 1)
axisRatio h k := (h+1)/(2k)  (in ℝ≥0∞; = ⊤ if k=0)
-- S2 AXIOM available: monomialThreshold d k h = ⨅ j, axisRatio (h j) (k j)
```

On the box `[0,ε]^d` (all u_j ≥ 0), `|u_j| = u_j` and the integrand is the product of one-variable
rpows: `∏_j u_j^{h_j - 2 k_j c'}`. Integrable iff every axis `h_j - 2k_j c' > -1`, i.e.
`c' < (h_j+1)/(2k_j)` for each binding axis. Diverges (integral = ⊤) iff SOME axis has
`c' ≥ (h_j+1)/(2k_j) = axisRatio`, which holds since `c' ≥ monomialThreshold = ⨅ axisRatio`.

## Reusable Mathlib-side machinery I ALREADY have (proven, in Case111Bridge)

```
abs_rpow_integrableOn_Icc_symm_iff (s ε : ℝ) (hε : 0 < ε) :
    IntegrableOn (fun x : ℝ => |x| ^ s) (Icc (-ε) ε) volume ↔ -1 < s
abs_rpow_integrableOn_Ioo_iff (s ε : ℝ) (hε : 0 < ε) :
    IntegrableOn (fun x : ℝ => |x| ^ s) (Ioo (0:ℝ) ε) volume ↔ -1 < s
```
(the per-axis ε-independent test, both directions; built on `intervalIntegral.integrableOn_Ioo_rpow_iff`).
For the (1,1,1) case I did the 2-variable product version `prodBoxSymm_rpow_integrableOn_iff` by Tonelli
(`Integrable.mul_prod` / `prod_right_ae` slicing).

## The questions

**Q1 — divergence (= ⊤), not just non-integrability.** The ≤-localization lemma I built consumes
`∫⁻ ... = ⊤` (an ENNReal lintegral equals top), NOT `¬ IntegrableOn`. For a NONNEGATIVE measurable
integrand `g`, `∫⁻ ofReal(g) = ⊤ ↔ ¬ IntegrableOn g` (since `IntegrableOn g ↔ ∫⁻ ofReal g < ⊤` for g ≥ 0,
via `hasFiniteIntegral_iff_ofReal`). Is that the right bridge, and is it cleaner to:
  (a) prove `¬ IntegrableOn (monomialIntegrand ...) box` and convert to `= ⊤`, OR
  (b) work directly with the lintegral and a Tonelli product `lintegral_prod` / `lintegral_eq_prod`?
Which avoids the `0^{neg} = 0` / `⊤` artifacts better?

**Q2 — the multivariate factoring + one binding axis.** The integrand on `[0,ε]^d` is
`∏_j u_j^{h_j - 2k_j c'}`. To show non-integrability from ONE divergent axis `j₀` (where
`h_{j₀} - 2k_{j₀} c' ≤ -1`), the standard Tonelli argument: integrating out the OTHER `d-1` axes over
`[0,ε]` gives a positive finite constant `× ∫_{[0,ε]} u_{j₀}^{h_{j₀}-2k_{j₀}c'}`, and the j₀-factor
diverges. In Lean with `Fin d` (not a fixed small d), is the cleanest route:
  (a) `MeasureTheory.lintegral_pi` / a Fubini-over-`Fin d` product formula `∫⁻_{pi box} ∏ f_j = ∏ ∫⁻ f_j`
      (does Mathlib have `lintegral_finset_prod` / `lintegral_pi_pi` for the pi-measure of a product of
      single-variable nonneg functions?), then "a product of ℝ≥0∞ is ⊤ if one factor is ⊤ and the rest
      are positive" — what's the cleanest ENNReal `Finset.prod_eq_top` lemma?
  (b) or reduce to 2 variables (j₀ vs the rest as a single block) via `MeasurableEquiv.piSplitAt` /
      `piFinSuccAbove` and reuse the 2-D `prodBoxSymm`-style slicing?
Be concrete about the Mathlib v4.29 lemma names for "lintegral of a pi-product of single-var functions
factors as the product of the per-axis lintegrals" and "ENNReal Finset.prod = ⊤ iff some factor ⊤ (others ≠ 0)".

**Q3 — do I even need the FULL `= ⨅ monomialThreshold` cover form, or can I bound more cheaply?**
The end goal (controller's cover-form): `rlctAtOn myF222 0 = ⨅_i monomialThreshold (d i)(k i)(h i)`.
The ≥-direction uses per-leaf integrability below threshold (already have the down-set lemmas); the
≤-direction uses THIS box-divergence atom fed into `rlctAtOn_le_of_box_diverges`. For the ≤, I need:
for `c' > ⨅_i threshold_i`, SOME leaf diverges on every box. Since `⨅` is the min over leaves, `c' > ⨅`
means `c' > threshold_{i₀}` for the minimizing leaf i₀. So I need divergence at the leaf achieving the
min, on the box = chart-preimage of `cubeBox`. Question: is it sound/cleanest to prove the box-divergence
atom at the level of the SINGLE binding leaf's monomial (so I only ever need ONE leaf to diverge), and
is `c' ≥ threshold` (= `≥`, the S2 ⨅) the right hypothesis, or do I need strict `>`? (The threshold is a
sSup generically NOT attained, so at `c' = threshold` the integral already diverges — `≥` should be
right, but confirm against the `0^{neg}` convention at `c'` exactly at the boundary.)

Please give: (a) the cleanest Lean proof skeleton for `monomialIntegrand_lintegral_box_eq_top` (the
Tonelli-product + one-binding-axis route), with concrete v4.29 lemma names; (b) flag any soundness
subtlety in the `≥ threshold ⟹ diverges` boundary (Q3) and the `= ⊤ ↔ ¬Integrable` bridge (Q1).
