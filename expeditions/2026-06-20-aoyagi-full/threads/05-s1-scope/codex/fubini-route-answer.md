**Verdict:** the card is wrong if it calls the full equality “light”. The smooth-block value is light and already essentially done; the smooth-block-plus-core equality is not. You can avoid the false finite-radius Beta identity, but the non-integrability half still needs a real comparison theorem.

**Cheapest Routes**

1. **One-sided lower bound: joint RLCT `≥ n/2 + λ_core`**
   This proves integrability for every `c < n/2 + λ_core`.

   Key idea: choose `a < n/2`, `b < λ_core`, `a + b = c`, then compare
   `(‖x‖² + G y)^(-c) ≤ ‖x‖^(-2a) * (G y)^(-b)` a.e.

   Confident Mathlib/local lemmas:
   `MeasureTheory.Integrable.mul_prod`, `Measure.prod_restrict`, `IntegrableOn.mono_set`, `integrableOn_congr_fun`, local `radial_ball_iff`, local `smoothBlockND_admissible_iff`.

   New sublemmas: about 4-6.
   Hardest sub-step: making the comparison a.e. because Lean’s `Real.rpow` has `0^negative = 0`, so the pointwise inequality fails on zero sets. For normal-crossing monomials the bad zero sets are null; for arbitrary measurable `G` this is false.

   This route **avoids radial asymptotics entirely**, but only proves one inequality.

2. **Full equality for explicit normal-crossing monomial core**
   This is the cheapest honest full-threshold route.

   Use the upper comparison above, plus the lower “cusp” comparison:
   on `‖x‖² ≤ G y`,
   `(‖x‖² + G y)^(-c) ≥ const * (G y)^(-c)`,
   and the `x`-ball has volume `≈ (G y)^(n/2)`, so joint integrability forces core integrability with exponent `c - n/2`.

   Confident Mathlib lemmas:
   `MeasureTheory.lintegral_prod`, `MeasureTheory.integrable_prod_iff'`, `Measure.addHaar_ball_of_pos`, `EuclideanSpace.volume_ball`, `intervalIntegral.integrableOn_Ioo_rpow_iff`, `MeasureTheory.Integrable.mul_prod`.

   New sublemmas: about 10-15 for a clean reusable theorem.
   Hardest sub-step: formalising the lower cusp estimate as an implication
   `IntegrableOn joint c → IntegrableOn core (c - n/2)`, using nonnegative `lintegral` bounds and ball-volume scaling.

   This **does not need** a separately stated near-zero asymptotic for
   `g(s) = ∫ (‖x‖²+s)^(-c) dx`, but it proves the same lower-bound content locally.

3. **Parametric radial bound route**
   Prove directly:
   for `c > n/2`,
   `C₁ * s^(n/2-c) ≤ ∫_{‖x‖<ε} (‖x‖²+s)^(-c) dx ≤ C₂ * s^(n/2-c)`
   near `s = 0`.

   Confident Mathlib lemmas:
   `MeasureTheory.integrable_fun_norm_addHaar`, `intervalIntegral.integrableOn_Ioo_rpow_iff`, `MeasureTheory.lintegral_prod`, `Measure.addHaar_ball_of_pos`.

   New sublemmas: likely 15-25.
   Hardest sub-step: parametric measurability and bounding the radial integral after splitting at `√s`.

   This is heavier than route 2. It is not necessary for the theorem, though it is mathematically clean.

4. **General analytic disjoint additivity**
   Statement: RLCT of a sum in disjoint analytic variable blocks is the sum of RLCTs.

   This is the conceptual theorem, but in Lean it is heavy: Laplace/Mellin/Tauberian-style infrastructure, or a serious analytic citation. Not Mathlib-light.

5. **Exact Beta integral**
   Do not use this route. The finite-`ε` identity is false. The whole-space identity is irrelevant to the neighbourhood definition of `rlctAt`.

**Important Name Corrections**

Confident in Mathlib v4.29:

- `MeasureTheory.integrable_fun_norm_addHaar`
- `intervalIntegral.integrableOn_Ioo_rpow_iff`
- `MeasureTheory.integrable_prod_iff`
- `MeasureTheory.integrable_prod_iff'`
- `MeasureTheory.Integrable.mul_prod`
- `MeasureTheory.Integrable.prod_right_ae`
- `Measure.prod_restrict`
- `MeasureTheory.lintegral_prod`
- `Measure.addHaar_ball_of_pos`
- `EuclideanSpace.volume_ball`

I did **not** find `integrableOn_prod_iff` by that exact name. The working pattern is:
`rw [IntegrableOn, ← Measure.prod_restrict]`, then use `integrable_prod_iff` / `integrable_prod_iff'`.

**Asymptotics?**

The cleanest full route does **not** need a named asymptotic theorem for the radial integral. But it does need a lower comparison equivalent in strength to the lower half of that asymptotic. There is no magic Fubini-only proof of the divergence direction.

Upper/integrability direction: genuinely light.

Lower/non-integrability direction: real work.

**Statement Hygiene**

Do not state this for merely `G ≥ 0`, measurable, `G ≢ 0`. That is false under the current Lean `Real.rpow` convention. If `G` vanishes on a positive-measure set near `0` but is not identically zero, `rlctAtOn G 0` can become `⊤`, while the joint function still sees the smooth block and has finite threshold `n/2`.

Also, Jacobian exponents `h_j` belong in `weightedThreshold`, not plain `rlctAt G`, unless the weight is explicitly part of the integrand.

**Honest Light Deliverable**

A genuinely light L2-consumable theorem is the one-sided regular contribution:

`c < n/2 + λ_core → c is joint-admissible`.

Together with the already-proven `smoothBlockND_rlct`, this is useful and axiom-clean. The full equality should be marked heavy unless you restrict to explicit normal-crossing monomial cores and budget for the cusp lower-bound build.