<task>
Lean 4 + Mathlib v4.29. I need the CLEANEST proof route for an RLCT-invariance ("peel") lemma for a
fiber-translation homeomorphism (a "shear"), and I'm choosing between two infrastructure routes.

## Setup

`M := (Fin nReg → ℝ) × ((Fin nM → ℝ) × (Fin nG → ℝ))` (a finite product of ℝ, so finite-dim real
normed space with Haar/Lebesgue `volume`). Slots: `.1` = reg, `.2.1` = core, `.2.2` = spec.

I have a self-homeomorphism `coreAbsorb : M ≃ₜ M`, the additive fiber-shear
`coreAbsorb q = (q.1, (q.2.1 + shift (q.1, q.2.2), q.2.2))` for a continuous
`shift : (Fin nReg → ℝ) × (Fin nG → ℝ) → (Fin nM → ℝ)`. It fixes reg (.1) and spec (.2.2), shifts core
(.2.1) by a function of (reg, spec). It fixes 0 (when `shift (0,0) = 0`).

GOAL (the "coreAbsorb_rlct" peel): for `G : M → ℝ`, `G q = (∑ i, q.1 i ^ 2) + coreF (q.2.1)` (a fixed
function depending only on reg and core), prove
    rlctAtOn (fun q => G (coreAbsorb q)) 0 = rlctAtOn G 0.
(`rlctAtOn F wstar` = the real-log-canonical-threshold germ at `wstar`: sSup of admissible `c` s.t.
`|F|^(-c)` is locally integrable near `wstar`. It is invariant under measure-preserving homeomorphisms
fixing the basepoint, and under bounded-unit-Jacobian homeomorphisms.)

I have TWO peel lemmas available:
- (MP peel) `rlctAtOn_comp_homeomorph (e : M ≃ₜ M') (he : MeasurePreserving e volume volume)
   (hemb : MeasurableEmbedding e) (F) (w0) : rlctAtOn (F ∘ e) w0 = rlctAtOn F (e w0)`.
   Needs `coreAbsorb` MEASURE-PRESERVING.
- (bounded-unit peel) `rlctAtOn_boundedUnit_homeomorph (F)(wstar)(π : M ≃ₜ M)(Dπ : M → (M →L[ℝ] M))
   (hfix : π wstar = wstar)(hderiv : ∀ x, HasFDerivAt π (Dπ x) x)(hdetmeas)(hbdd : ∃U∈𝓝 wstar,∃a b,
   0<a ∧ ∀w∈U, a≤|（Dπ w).det| ≤ b) : rlctAtOn (F∘π) wstar = rlctAtOn F wstar`.
   Needs `coreAbsorb` differentiable EVERYWHERE with bounded-unit det near wstar.

The fiber-shear has Jacobian = a block-unipotent matrix (identity diagonal, the shift's derivative
off-diagonal), so `det = 1` everywhere — IF `shift` is differentiable. As a measure transform it is
volume-preserving (det = 1).

## QUESTION

Which route is cleanest in Mathlib v4.29, and what is the proof?

ROUTE A (MP peel): prove `MeasurePreserving coreAbsorb volume volume` for the fiber-shear directly.
 - Is there a Mathlib lemma for the measure-preservation of `(x, y) ↦ (x, y + f x)` (a skew/shear
   translation) on a product measure? I found `measurePreserving_prod_mul` (the group
   `(x,y)↦(x,x*y)`) but that's the group-action form, not an arbitrary `f`. Is there a
   `MeasurePreserving` for the ADDITIVE fiber-shift `(x,y) ↦ (x, y + f x)` (Fubini + translation
   invariance of the inner Lebesgue measure)? Name it, or give the ~5-line Fubini construction
   (`Measure.prod` + `measurePreserving_add_right` per fiber + `MeasurePreserving.prod`-style).
   NOTE: my shift depends on (reg, spec) = `(.1, .2.2)`, NOT a single factor — the shear is on the
   MIDDLE slot of a triple `reg × (core × spec)`, shifting `core` by `f(reg, spec)`. Does that
   complicate the Fubini (need to reassociate `reg × (core × spec) ≃ (reg × spec) × core`, shear the
   `core` factor over `(reg × spec)`, MP via the reassoc + the 2-factor skew)?

ROUTE B (bounded-unit peel): require `shift` to be `C¹` (`ContDiff ℝ 1`), prove `HasFDerivAt coreAbsorb
 (Dπ x) x` everywhere with `Dπ x` the block-unipotent CLM, and `det (Dπ x) = 1` (so hbdd trivial
 a=b=1). How hard is the `HasFDerivAt` of the fiber-shear + computing `det` of the block-unipotent
 ContinuousLinearMap = 1 in Mathlib? (det of `id + nilpotent`-ish, or `ContinuousLinearMap.det` of a
 lower-triangular block map.)

Rank the two routes by Mathlib-friction (line count + lemma availability). For the winner, give the
exact lemma names (v4.29) + a proof skeleton. Key sub-question for ROUTE A: the exact Mathlib name (if
any) for additive-skew measure-preservation, or confirm it must be hand-built from Fubini + translation.
</task>

<output_contract>
1. WINNER: Route A (MP) or Route B (bounded-unit), one line + why (friction).
2. For the winner: the exact Mathlib v4.29 lemma chain + a proof skeleton (≤25 lines), with the
   reassociation handling (reg × (core × spec) → shear the core over reg×spec).
3. The key missing-or-present lemma: does Mathlib have additive-skew/fiber-shift MeasurePreserving
   (Route A) or do I hand-build it? / det of a block-unipotent CLM = 1 (Route B)?
4. Any gotcha (the triple-product middle-slot shear; det of CLM vs Matrix; volume on `Fin n → ℝ`).
Keep under ~450 words.
</output_contract>

<grounding_rules>
Flag any lemma name you are not sure exists in Mathlib v4.29 (the project hit `toPartialHomeomorph` →
`toOpenPartialHomeomorph` renames, and `Basis` = `Module.Basis`). Distinguish a lemma you KNOW is in
Mathlib from one you'd EXPECT. If Route A needs a hand-built Fubini shear-MP, say so explicitly (don't
claim a lemma that may not exist).
</grounding_rules>
