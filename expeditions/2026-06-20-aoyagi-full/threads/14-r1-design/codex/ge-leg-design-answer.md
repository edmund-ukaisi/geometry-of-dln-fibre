1. **Q1: CLEANER-A.** Use `g5_flat_cover` on the bounded target box with clipped chart domains, then bound each RHS term by a rectangle integral. Since `g5` already packages the change-of-variables determinant, cover, null sets, and finite sum, the subadditive route mostly re-proves weaker versions of that infrastructure.

2. **Q2: RECTANGLE-OK.** The clipped preimage is not a rectangle, but it is contained in one: the constraints `|y₀ * x_j| ≤ r` only shrink the domain. So use
   `V_p ∩ φ_p ⁻¹' Ω \ Z_p ⊆ {|y₀| ≤ R} ×ˢ {|x_j| ≤ 1} ×ˢ Bbox`.
   Then apply monotonicity of nonnegative set integrals. This part is sound; the coupling is not a wall.

3. **Q3: WALL, as stated.** Shrinking the target neighborhood makes `y₀` and spectator `B` small, but it does **not** make the active-rest ratios `x_j = A_j / A_p` small. Any open neighborhood of `A = 0` contains directions with ratios near `1`. Thus `core_admissible_of_lt` near the single core point `0` does not imply integrability on the full ratio box `[-1,1]^(mk-1) × smallBbox`. You need a new uniform/core-box lemma over the compact exceptional chart, or a finite projective cover proving admissibility at all relevant ratio points.

4. **Q4: ABSTRACT.** Build one abstract finite-chart domination lemma, but keep the DLN-specific rectangle/core-box facts outside it. The abstract lemma should assume the clipped-domain-to-rectangle containment and per-rectangle pullback integrability. That isolates the measure theory from the missing geometric input in Q3.

5. **Q5: WALL.** The GE assembly is sound only after adding the missing full core-box integrability input. Q2 is assembly; Q3 is the real gap.

Ordered lemma statements:

```lean
lemma chart_cover_integrableOn_of_rect_dom
  (hcover : g5_flat_cover hypotheses for Ω and clipped chart domains C p)
  (hsub : ∀ p, C p ⊆ R p)
  (hint : ∀ p, IntegrableOn pullbackDensity (R p) volume) :
  IntegrableOn targetDensity Ω volume
```

Rests on `g5_flat_cover`, finite-sum finiteness, `setLIntegral_mono_set` / `IntegrableOn.mono_set`.

```lean
lemma pivot_clipped_preimage_subset_rect
  (hΩ : Ω is a bounded coordinate box around 0) :
  chartDomOn p ∩ φ_p ⁻¹' Ω \ Z_p ⊆
    Iy R ×ˢ Vz_fullRatio S
```

Rests on `argmaxCellOn` bounds, `φ_p` coordinate formulas, elementary `abs_mul` inequalities.

```lean
lemma core_integrableOn_fullRatioBox_of_lt
  (hc : c' < rlctAtOn core 0) :
  IntegrableOn (fun z => |core z| ^ (-c')) Vz_fullRatio volume
```

This is **not** from the listed pieces. It needs new machinery: uniform integrability over the ratio compact set, or a finite cover of the exceptional divisor.

FLAGS: Q2 coupling is harmless by enlargement. Q3 active-rest shrinking is false. The missing input is full-ratio core-box integrability, not more change-of-variables machinery.