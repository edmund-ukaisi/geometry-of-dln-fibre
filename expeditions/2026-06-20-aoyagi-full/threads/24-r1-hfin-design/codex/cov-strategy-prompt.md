<task>
Lean 4 + Mathlib v4.29. I must close ONE `sorry`, the `cov` field of a structure, a
genuine change-of-variables for a Lebesgue (lintegral) integral.

SETUP (all the named lemmas below are ALREADY PROVED, sorry-free, in my repo):

- `Params M334 = (s : Fin 2) → Matrix (Fin (M s.castSucc)) (Fin (M s.succ)) ℝ` for `M = ![3,3,4]`.
  Concretely it is `Matrix (Fin 3) (Fin 3) ℝ × Matrix (Fin 3) (Fin 4) ℝ` as a nested Pi.
- `paramsEquivFlat M334 : Params M334 ≃ᵐ (Fin 21 → ℝ)` is a MeasurableEquiv built as
  `(piCurry …).symm.trans ((piCurry …).symm.trans (arrowCongr' (Fintype.equivFin (FlatIdx M334)) (refl ℝ)))`.
  It is a coordinate RESHAPE + REINDEX — ℝ-LINEAR as a function, but packaged only as a
  `MeasurableEquiv` (+ proven homeomorphism). It is `measurePreserving_paramsEquivFlat`
  (MeasurePreserving for the product Lebesgue volumes), `continuous_paramsEquivFlat`,
  `continuous_paramsEquivFlat_symm`.
- `chartParams334 : (Fin 21 → ℝ) → Params M334` is a POLYNOMIAL matrix map (entries are
  monomials in the 21 coords), continuous.
- `phi334 u := paramsEquivFlat M334 (chartParams334 u)`, so `phi334 : (Fin 21 → ℝ) → (Fin 21 → ℝ)`.
- `phi334_injOn` : `Set.InjOn phi334 {u | u 0 ≠ 0 ∧ u 1 ≠ 0}` (PROVED).
- The honest Jacobian determinant of `phi334` is `det Dφ = −(u 0)^7·(u 1)^2` (sympy-exact),
  whose abs equals the bundle weight `|u 0|^7·|u 1|^2`.

GOAL (`cov`): for all measurable `V ⊆ (Fin 21 → ℝ)` and all `g : (Fin 21 → ℝ) → ℝ≥0∞`,
    ∫⁻ x in phi334 '' (V \ {x | x 0 = 0}), g x
      = ∫⁻ u in V \ {x | x 0 = 0}, ENNReal.ofReal (|u 0|^7 · |u 1|^2) · g (phi334 u).

The Mathlib tool is `lintegral_image_eq_lintegral_abs_det_fderiv_mul`:
  for measurable `s`, `(∀ x ∈ s, HasFDerivWithinAt f (f' x) s x)`, `InjOn f s`, `g`,
    ∫⁻ x in f '' s, g x = ∫⁻ x in s, ENNReal.ofReal |(f' x).det| · g (f x).
It needs the WITHIN-derivative `f' x : (Fin 21 → ℝ) →L[ℝ] (Fin 21 → ℝ)` AS A ContinuousLinearMap,
with computable `ContinuousLinearMap.det`.

THE BLOCKER: to get `HasFDerivWithinAt phi334 (Dφ u) s u` with `(Dφ u).det = ±(u 0)^7·(u 1)^2`,
I must differentiate `phi334 = paramsEquivFlat ∘ chartParams334`. The inner is polynomial
(differentiable, fderiv = a CLM with a matrix). The outer `paramsEquivFlat` is LINEAR but
only packaged as a MeasurableEquiv — no `ContinuousLinearEquiv`/fderiv/det lemma exists.

WHAT MATHLIB HAS for building the linear iso:
- `LinearEquiv.piCurry`, `LinearEquiv.piCongrLeft`, `LinearEquiv.funCongrLeft`,
  `LinearEquiv.arrowCongr` — all share the SAME underlying `Equiv` as the `MeasurableEquiv`
  pieces (`Equiv.piCurry`, `Equiv.arrowCongr'`).
- I can probably build `paramsEquivFlatₗ : Params M334 ≃ₗ[ℝ] (Fin 21 → ℝ)` (and CLE) whose
  `toFun` is DEFEQ (or provably equal) to `paramsEquivFlat M334`.
- Banked `pivotBlowupOn`/`pivotBlowupOnDeriv` infra (flat `Fin N → ℝ`): a pivot-blowup with
  proved `HasFDerivWithinAt`, `det = (x p)^(card−1)`, `InjOn`. The (2,2,2) sibling chart was
  built ENTIRELY in flat coordinates as a composition of these (NO paramsEquivFlat in the way),
  so its cov was a clean chain of `lintegral_image_eq_lintegral_abs_det_fderiv_mul`.

CANDIDATE ROUTES I am weighing:

(A) PEEL THE OUTER REINDEX BY MEASURE-PRESERVATION, not fderiv. Since paramsEquivFlat is a
    measure-preserving measurable EMBEDDING (it's an equiv), `MeasurePreserving.setLIntegral_comp_emb`
    gives `∫⁻_{E '' s} f = ∫⁻_s f∘E`. But the c-o-v lemma needs a SINGLE space E→E; chartParams334
    maps `(Fin 21→ℝ) → Params M334` (different spaces). Does the det/fderiv of a map between
    DIFFERENT finite-dim spaces even make sense for this lemma? I think NOT — the lemma is `f : E → E`.

(B) BUILD `paramsEquivFlatₗ` as a `ContinuousLinearEquiv` `(Params M334) ≃L[ℝ] (Fin 21 → ℝ)`,
    prove `(paramsEquivFlatₗ : … → …) = paramsEquivFlat M334` (funext / the shared Equiv), then
    `fderiv phi334 u = paramsEquivFlatₗ.toContinuousLinearMap ∘L (fderiv chartParams334 u)`, and
    `det` of the composite = det of the round-trip CLM. Compute that det = ±(u 0)^7·(u 1)^2.

(C) DEFINE A PURELY-FLAT chart `psiFlat : (Fin 21→ℝ) → (Fin 21→ℝ)` as a composition of
    `pivotBlowupOn` + linear shear/substitution maps (mirroring the (2,2,2) sibling), prove
    `psiFlat = phi334` (or that they agree on the relevant set), and inherit the clean flat cov.
    BUT this risks re-deriving the validated chart and the agreement proof may be as hard.

QUESTIONS:
1. Rank routes (A)/(B)/(C) by total Mathlib-friction to a sorry-free `cov`. Is (A) genuinely
   dead (det between different spaces), or is there a clean reduction where after peeling E by
   measure-preservation the REMAINING c-o-v is `chartParams334` viewed through E.symm, i.e. a
   self-map `E.symm ∘ ... `? Spell out the cleanest decomposition if so.
2. For route (B): what is the cleanest way in Mathlib v4.29 to get the det of the composite CLM
   `E_lin ∘L D(chartParams334)` as a self-map of `Fin 21 → ℝ`? `ContinuousLinearMap.det` is
   defined via `LinearMap.det`; is there a `det_comp` / multiplicativity I can use across the
   space-change, and how do I actually COMPUTE the resulting 21×21 det without a `Matrix.det`
   blow-up (which times out)? Can I factor `chartParams334` itself as pivotBlowup ∘ shear ∘
   b-subst in FLAT coords so the det multiplies as `u0^7 · 1 · u1^2`?
3. Is there a SHORTCUT: since I only need `|det| = |u0|^7·|u1|^2`, and paramsEquivFlat is
   measure-preserving (|det of its linear part| = 1), can I AVOID computing the reindex det
   explicitly — e.g. is `|det (E_lin ∘L D)| = |det_in_some_basis (D)|` where the reindex
   contributes a ±1 I can pin via `volume_preserving`/`abs_det = 1` rather than an explicit
   permutation-sign computation?
4. The honest answer I most need: is closing this `cov` realistically a 1-day (≤200 line) job
   in Mathlib v4.29, or is it a multi-file infrastructure build (the "cost driver 2" my lead
   flagged)? If the latter, what is the SMALLEST honest partial result (e.g. the linear-iso
   lemma alone) worth banking, and where exactly will I hit the wall?
</task>

<output_contract>
1. A ranked verdict on routes (A)/(B)/(C): cheapest-first, one paragraph each on WHY, naming the
   precise Mathlib lemmas/instances each needs in v4.29 and the single biggest risk.
2. For the winning route: a concrete step list (≤8 steps) with the exact lemma names to chase,
   and the det-computation plan that AVOIDS a 21×21 Matrix.det.
3. A direct answer to Q3 (the |det|=1 reindex shortcut): yes/no + the lemma if yes.
4. A blunt effort estimate (line count / file count) and the smallest bankable partial if it
   overruns. No hedging.
</output_contract>

<grounding_rules>
Flag clearly when you are INFERRING a Mathlib lemma exists vs KNOWING its exact v4.29 name/signature.
Mathlib v4.29 may differ from your memory — mark any lemma name you are not certain of as
"verify name". Do not invent lemma signatures with false confidence. If a route depends on a
lemma you cannot confirm exists, say so and give the fallback.
</grounding_rules>
