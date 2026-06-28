1. **Q1:** Yes, inner joint-recognition is subsumed by the abstract IH, after translating `M22 ↦ Sc` and enlarging boxes. Caveat: when `c' ≤ 2`, the shifted exponent `c' - 2` is not positive, so close by the subcritical/bounded-volume peel case, not IH.

2. **Q2:** Clean order is:
   ```lean
   ∫ Sc,Sbot (∫ Stop (topSq Stop + w Sc Sbot)^(-c'))
     ≤ ∫ Sc,Sbot C * (w Sc Sbot)^(-(c' - 2))
   ```
   then recognize the outer integral as `SchurCore 4 (r-1) (c'-2) T'` and invoke `SchurLowerIH`, only in the `2 < c'` branch.

   Obligations: measurable `matBox`/chart cells, measurable block projections, measurable Schur-complement translation, measurable `topSq` and `w := frobSq (Sc ⬝ Sbot)`, pivot/determinant hypotheses holding a.e., product/restricted measures sigma-finite, bounded boxes finite measure. Tonelli is nonnegative `lintegral`; likely names: `MeasureTheory.lintegral_lintegral_swap` (INFERRED), `lintegral_mono_ae` (INFERRED).

3. **Q3:** Yes. Enter through the lower comparison
   ```lean
   c₀ * (top + w) ≤ frobSq (R ⬝ S)
   ```
   so inverse powers flip:
   ```lean
   frobSq (R ⬝ S)^(-c') ≤ c₀^(-c') * (top + w)^(-c')
   ```
   using `0 < c'`. The `|R| ≤ 1` hypothesis holds on the argmax chart: after normalizing by the pivot, every ratio has absolute value `≤ 1`. The zero-pivot locus is the all-zero `Δ` locus and should be discharged a.e. If your generic chart only records `≤ T`, add the ratio-bound lemma.

4. **Q4 dependency list:**

   ```lean
   lemma matToFlat_equiv_box {r T} : ... -- mirror/new boilerplate
   ```

   ```lean
   lemma argmaxCellOn_angular_abs_le_one {N i x} : x ∈ argmaxCellOn i → x i ≠ 0 → |x k / x i| ≤ 1 -- mirror
   ```

   ```lean
   lemma schur_pivotAxis_pullout_lt_top {r c T} : c < (r*r:ℝ)/2 → ... -- mirror/general
   ```

   ```lean
   lemma schurSplit_integrand_le_general {r c R S} : ... -- mirror over general N2b
   ```

   ```lean
   lemma schur_topBlock_morse_peel {r c R Sbot} : 2 < c → ... ≤ C * w^(-(c-2)) -- new wrapper
   ```

   ```lean
   lemma schur_topBlock_subcritical_lt_top {r c R Sbot} : c ≤ 2 → ... < ⊤ -- new
   ```

   ```lean
   lemma schur_residual_translate_to_core {r c T} : ... ≤ SchurCore 4 (r-1) c T' -- new
   ```

   ```lean
   lemma schur_matBox_chart_lt_top {r i c T} : ... → chartIntegral r i c T < ⊤ -- mirror, riskiest
   ```

   ```lean
   theorem schurRecStep_four : SchurRecStep 4 schurLambda -- final assembly
   ```

   Riskiest lemma: `schur_matBox_chart_lt_top`, because it composes flattening, blow-up Jacobian, a.e. chart hypotheses, Tonelli order, split, peel, translation, and IH recognition.