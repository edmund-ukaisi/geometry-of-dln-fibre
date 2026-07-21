## 1. Verdict

The architecture is sound and the locked theorem is correctly stated for the checked-in `Chart`/`Resolution` records. Leg B genuinely closes through Pieces 2 and 3; no additional geometric field is needed.

Two implementation caveats:

- The actual `Chart` does contain `hFmeas : ∀ i, Measurable (F i)` at [ProductResolution.lean](/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/agent-a34130c87db24f302/lean/DLNFibre/Core/Aoyagi/ProductResolution.lean:70). Your abbreviated field list omitted it. Without this or an equivalent local measurability hypothesis, your stated measurability argument would have a gap.
- The current `exists_unit_sumSqFam_monomial` API exposes only `ContinuousAt U 0` and `0 < U 0` [MonomialRLCT.lean](/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/agent-a34130c87db24f302/lean/DLNFibre/Core/Aoyagi/MonomialRLCT.lean:370). Piece 2 needs the readily provable stronger facts `Continuous U` and `∀ u, 1 ≤ U u`. The existing polynomial witness already has both; this is an API refactor, not a missing assumption.

I recommend proving the stronger set identity directly:
\[
\operatorname{localAdmissibleExponents}(K,x_0)= [0,R),
\qquad R=\min_c T_c.
\]
Leg A gives `⊆`; Leg B gives `⊇`. Then `csSup_Ico` finishes both sides. This avoids most `BddAbove`/`csSup_le_csSup` plumbing.

## 2. Single riskiest step

Piece 2 is the riskiest and most load-bearing step: origin-threshold information alone does not imply integrability at every point of `dom`.

It is nevertheless engineering, not new mathematics. The key refactor is:

- strengthen the collapse-unit API globally;
- reuse the existing a.e.-off-axes factorization;
- establish local integrability at arbitrary `p`.

The present box lemmas are also `private`; either put Piece 2 in `MonomialRLCT.lean` or expose the needed symmetric-box lemma.

## 3. Piece 1

Correct and buildable, provided the helper assumes `s ⊆ nbhd` or directly assumes `InjOn g (s \ excep)`.

Confirmed Mathlib v4.29 names:

- `lintegral_image_eq_lintegral_abs_det_fderiv_mul`
- `integrableOn_image_iff_integrableOn_abs_det_fderiv_smul`
- `addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero`
- `AnalyticOnNhd.differentiableOn`
- `AnalyticAt.hasStrictFDerivAt`
- `integrableOn_congr_set_ae`
- `Measure.restrict_congr_set`

Take `t := s \ excep`. Then:

- `t` is measurable.
- `hg_inj` restricts to `t`.
- At `u ∈ t`, use analytic-at-`u`, then
  `hasStrictFDerivAt.hasFDerivAt.hasFDerivWithinAt`; this gives the required derivative as the global `fderiv`.
- `s ∩ excep` is null, and differentiability is needed only on `s ∩ excep`; the named null-image lemma explicitly permits nonmeasurable null sets.
- `g '' s =ᵐ g '' t` because the difference is contained in `g '' (s ∩ excep)`.
- Likewise `s =ᵐ t`.

No injectivity involving points inside `excep` is needed.

For the atlas theorem, the integrability equivalence theorem is cleaner than repeatedly converting through `lintegral`: remove the null sets, apply the injective equivalence, then restore them by `integrableOn_congr_set_ae`.

## 4. Piece 2

A box centered at `p` is cleaner than translation, but there is an even simpler route: use a sufficiently large symmetric box centered at `0` containing `p`.

Because `c < T`, the existing `hexp_iff` gives
\[
-1 < \beta_d=h_d-2e_{k_0d}c
\]
for every `d`, including nonbinding axes. For nonbinding axes, `e k₀ d = 0`, so `β_d=h_d≥0`.

Thus the existing symmetric-box theorem makes the pure product integrable on every sufficiently large origin-centered box. Restrict it to a neighborhood of `p`. This avoids:

- a coordinate-dependent box theorem;
- separate “interval avoiding zero” lemmas;
- translation and shifted factors `|v_d+p_d|^{β_d}`.

Measurability needs care:

- `ContinuousAt unit p` alone does not imply measurable-on-a-neighborhood.
- Your global `Measurable unit`, polynomial/measurable `U`, and eventual equality for `W` are enough.
- `W` need not be globally measurable: on the chosen neighborhood, use eventual equality with the measurable model exactly as the existing origin proof does.
- For charts, construct the measurable extension of `|unit|` once per chart, as the existing chart proof already does.

## 5. Nonnegative integrands

Yes, this needs explicit handling. Finiteness of
`∫⁻ ENNReal.ofReal f`
does not by itself produce `IntegrableOn f`; `AEStronglyMeasurable` is also required.

Confirmed Mathlib tools include:

- `IntegrableOn.setLIntegral_lt_top`
- `hasFiniteIntegral_iff_ofReal`
- `lintegral_ofReal_ne_top_iff_integrable`
- `ENNReal.ofReal_mul`

Here the required measurability and nonnegativity are available for both `negPow K c` and `jacWeightFn * negPow …`. Still, using `integrableOn_image_iff_integrableOn_abs_det_fderiv_smul` avoids most of this bookkeeping.

Piece 3 is then direct using confirmed:

- `IntegrableAtFilter.filter_mono`
- `LocallyIntegrableOn.integrableOn_isCompact`
- `integrableOn_finite_iUnion`

Finally use `hcover` to prove
`U =ᵐ U ∩ ⋃ c, g_c '' dom_c`, followed by `IntegrableOn.congr_set_ae`. Measurability of `U` is not required.

## 6. Size estimate

With the large-origin-box simplification:

- Piece 1: 70–120 lines
- Piece 2 plus stronger `U` API: 130–210
- Piece 3: 10–25
- Per-chart set form/Step 0: 100–180
- Leg A: 50–90
- Leg B and finite-cover glue: 120–200
- Final set/supremum wiring: 30–60

Total: roughly 550–850 lines. So 600–900 is realistic. The centered-at-`p` generalized-box route likely adds another 100–200 lines.