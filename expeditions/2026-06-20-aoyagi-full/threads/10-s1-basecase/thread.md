# Thread 10 — S1 base case: the (1,1,1) `rlctAt` bridge + λ-axiom-elimination probe

- **Seat:** `fm-2` (formaliser, Lean). MAIN checkout, `expedition/aoyagi-full`. Controller green-gates.
- **Goal:** prove `case111_rlct_eq_monomialThreshold` sorry-free (`rlctAt = monomialThreshold` for the
  `(1,1,1)` monomial) → first FULL end-to-end (`case111_rlct` sorry-free; 10 → 9 sorry). PROBE: is the
  threshold-half of `monomial_rlct` provable in general (→ λ becomes axiom-free)?

## Feasibility read (Codex unavailable in sandbox — first-principles + Mathlib-verified)

Every load-bearing Mathlib lemma VERIFIED to exist + compose (spikes in /tmp, all green):

- **Single-var iff (the analytic heart):** `intervalIntegral.integrableOn_Ioo_rpow_iff (ht : 0 < t) :`
  `IntegrableOn (fun x ↦ x ^ s) (Ioo 0 t) ↔ -1 < s`. For `s = -2c`: integrable ⟺ `c < 1/2`. ✓
- **Icc↔Ioo:** `integrableOn_Icc_iff_integrableOn_Ioo` (endpoints null). ✓
- **Product (forward):** `MeasureTheory.Integrable.mul_prod (hf hg) :`
  `Integrable (fun z ↦ f z.1 * g z.2) (μ.prod ν)`; restricted via `IntegrableOn` + `Measure.prod_restrict`
  (`(μ.restrict s).prod (ν.restrict t) = (μ.prod ν).restrict (s ×ˢ t)`). ✓ (spike green)
- **Product (reverse / divergence):** `integrable_prod_iff'` ⇒ a.e.-slice integrability; slice back to the
  single-var iff to forbid `c ≥ 1/2`. (API present; assembly pending.)
- **pi(Fin 2)↔prod:** `measurePreserving_finTwoArrow (volume : Measure ℝ) :`
  `MeasurePreserving finTwoArrow (Measure.pi fun _ ↦ volume) (volume.prod volume)`; `volume` on
  `Fin 2 → ℝ` is defeq the pi measure (spike green). Transfer `IntegrableOn` via
  `MeasurePreserving.integrableOn_comp_preimage` (`e ⁻¹' (Icc×Icc) = unitBox 2`). ✓
- **abs on the box:** on `[0,1]`, `|x| = x`, so `monomialIntegrand 2 (1,1) (0,0) c u = |u0|^{-2c}|u1|^{-2c}`
  collapses to the rpow product (spike green: `unfold monomialIntegrand; simp [Fin.prod_univ_two]`).

**Verdict: the box-side `monomialThreshold = 1/2` is provable axiom-free.** ⇒ the threshold-half of
`monomial_rlct` is NOT an irreducible citation for normal-crossing data — it is Fubini + the Mathlib
rpow iff, per axis. The GENERAL threshold-half (`rlctAt(monomial) = ⨅ⱼ (hⱼ+1)/(2kⱼ)`) should follow the
same recipe at `d` axes (`Fin d` pi↔iterated-prod, `Finset.prod` of per-axis integrals, the binding axis
sets the min) — no analytic wall foreseen; the obstruction is Lean labour (n-ary Fubini bookkeeping), not
mathematics. **Recommendation: eliminate the λ-citation** (keep `monomial_rlct` order-half seamed for θ).

## The `rlctAt` side (the genuine S1 content even here)

`rlctAt` uses `∃ U ∈ 𝓝 0`. Two directions:
- `c < 1/2` admissible: exhibit `U = box`; a closed box `Icc (-ε) ε ^ 2` is a `𝓝 0`; integrable there
  (forward product, with `|x|` now genuinely two-sided — symmetrize via `|x|^a` even/`Icc`-split).
- `c ≥ 1/2` not admissible: EVERY `U ∈ 𝓝 0` contains a small box where it diverges (slice argument).

This is "baby S1.1": germ-locality made concrete. Plan: prove `rlctAt = 1/2` and `monomialThreshold = 1/2`
separately, bridge by transitivity (avoids a direct `𝓝 ↔ box` set-equality).

## Status (DELIVERED)

**Probe: ANSWERED YES — λ-citation eliminated for the threshold path.** `Validate/Case111Bridge.lean`
(new, sorry-free, axiom-free):
- `prodBox_rpow_integrableOn_iff` — `x^{−2c}·y^{−2c}` integrable on `[0,1]²` ⟺ `c < 1/2` (both
  directions; forward `Integrable.mul_prod`, reverse a.e.-slice).
- `unitBox_monomialIntegrand_integrableOn_iff` — lifted to the `Fin 2` box via `finTwoArrow`.
- `monomialThreshold_case111 : monomialThreshold 2 (1,1) (0,0) = 1/2`, **`#print axioms` = standard
  only** (no `monomial_rlct`).

`Case111.lean` refactored: `case111_monomialThreshold` now routes through `monomialThreshold_case111`
⇒ **axiom-free** (was `[…, monomial_rlct]`). Knock-on: `case111_rlct` axioms dropped `monomial_rlct`,
now `[propext, sorryAx, Classical.choice, Quot.sound]` — so closing the one remaining bridge `sorry`
makes the headline **fully axiom-free** (beyond the one-citation target).

**General threshold-half feasibility:** the recipe (per-axis rpow iff + n-ary Fubini, binding axis sets
the `⨅`) carries to general `(d, k, h)` with no foreseen analytic wall — the cost is Lean labour
(`Fin d` pi↔iterated-prod bookkeeping, the `kⱼ=0` unit axes). **Recommend eliminating the λ-citation**
(keep `monomial_rlct`'s order-half seamed for θ). The controller may re-engage `pp` for the general
n-ary-Fubini blueprint if/when prioritised.

## NOT done: the `rlctAt` bridge `sorry` (10 → 9 NOT achieved)

`case111_rlct_eq_monomialThreshold` remains a (now-sharpened) `sorry`. The RHS is axiom-free `1/2`, so
the gap is `rlctAt = 1/2` directly. Verified-feasible but a genuine multi-hundred-line build — the real
baby-S1.1 — with three pieces (all confirmed reachable, none an analytic wall):
1. a **measure-preserving** equiv `Params (1,1,1) ≃ᵐ (Fin 2 → ℝ)` — `Matrix (Fin 1)(Fin 1) ℝ ≃ᵐ ℝ`
   needs unfolding the `Matrix` `def` (bare `funUnique` compose hits the wrapper) + the m.p. proof,
   then compose with `finTwoArrow`;
2. **two-sided** `|x|^{−2c}` integrability on `[-ε,ε]` (the nbhd crosses 0; box `[0,1]` was one-sided)
   — split `Icc (-ε) ε` by evenness, no Mathlib lemma off-the-shelf;
3. the `∃ U ∈ 𝓝 0` quantifier — box witness for `c<1/2`, divergence over every nbhd for `c≥1/2`
   (`IntegrableOn.mono_set` + the reverse iff).
Left as a named `sorry` rather than forced (brief: "do NOT force"); the threshold-side win is banked.
