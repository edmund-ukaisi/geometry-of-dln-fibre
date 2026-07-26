<task>
Lean 4 + Mathlib v4.29. I must prove ONE theorem (statement is LOCKED, cannot change). It is a disjoint-block Tonelli integrability result for an over-vanishing RLCT engine. I want your review of my proof SKELETON and the cleanest Mathlib idioms for the two hardest sub-steps (the two coordinate-subtype reindexings and the a.e. product-factorization carried through a measure-preserving equiv). I have already verified every lemma name below EXISTS in the local Mathlib.

## The locked theorem (must prove exactly this)

```
open MeasureTheory Set Filter Topology RLCT
variable {D : ℕ}

-- monoSumSqGerm a Z u = (∏ d, (u d)^(a d))^2 * ∑ j ∈ Z, (u j)^2
-- jacWeight jac u = ∏ d, |u d|^(jac d)              (h d : ℕ, so |u d|^(jac d) is Monoid.npow)
-- negPow K c u = (K u) ^ (-c)                        (Real.rpow, so (K u)^(-c))
-- monomialThreshold a jac hbind = (bindingAxes a).inf' hbind (fun d => (jac d + 1 : ℝ)/(2 * a d))
-- bindingAxes a = univ.filter (fun d => 0 < a d)

theorem monoSumSq_integrableAtFilter_of_lt
    {a jac : Fin D → ℕ} {Z : Finset (Fin D)} {W unit : (Fin D → ℝ) → ℝ} {p : Fin D → ℝ} {cc : ℝ}
    (hbind : (bindingAxes a).Nonempty) (hZne : Z.Nonempty)
    (hZa : ∀ j ∈ Z, a j = 0) (hZjac : ∀ j ∈ Z, jac j = 0)
    (hc0 : 0 ≤ cc)
    (hthr : cc < monomialThreshold a jac hbind) (hsos : 2 * cc < (Z.card : ℝ))
    (hunit : ContinuousAt unit p) (hunit0 : unit p ≠ 0) (hunitmeas : Measurable unit)
    (hW : ∀ᶠ u in 𝓝 p, W u = jacWeight jac u * unit u) :
    IntegrableAtFilter (fun u ↦ W u * negPow (monoSumSqGerm a Z) cc u) (𝓝 p)
```

## Math content (verified correct, do not re-derive)

Near p, integrand = jacWeight jac u * unit u * ((∏ u_d^{a_d})^2 * ∑_{j∈Z} u_j^2)^{-cc}.
Split rpow (both bases ≥ 0): = unit·[jacWeight jac·((∏u_d^{a_d})^2)^{-cc}]·(∑_{j∈Z}u_j^2)^{-cc}.
Set mono u := jacWeight jac u · ((∏ u_d^{a_d})^2)^{-cc}. Off coordinate hyperplanes
mono u = ∏_{d:Fin D} |u_d|^{ev d} with ev d := jac_d − 2·a_d·cc. Because a_j=0 AND jac_j=0 for j∈Z,
ev j = 0, so the Z-coordinate factors are |u_j|^0 = 1: mono depends only on Zᶜ coords.
- Zᶜ block (pure power ∏_{d∈Zᶜ}|u_d|^{ev d}): ev d > −1 for ALL d (from cc < monomialThreshold via
  the existing lemma `monomial_forall_neg_one_lt_iff_lt_threshold`), so finite box lintegral.
- Z block ((∑_{j∈Z}u_j^2)^{-cc} = ‖·‖^{-2cc}): finite iff 2cc < |Z| = card Z (hsos).
The unit COUPLES the blocks (does not factor); bound it by |unit| ≤ Mub = |unit p|+1 on a nbhd of p
(ContinuousAt), exactly mirroring an existing proof.

## Mirror proof already in the file (I will follow its domination spine)

`monomialSumSq_integrableAtFilter_of_lt` (MonomialRLCT.lean ~777-896): builds an origin-centred
symmetric box `box = univ.pi (fun _ => Ioo (-R) R)` with R = (∑|p_d|)+1 (so p ∈ box, box ∈ 𝓝 p),
proves `hbig : ∫⁻ u in box, ofReal (mono u) < ⊤` via `MonomialBox.prodRpow_boxSymm_lt_top`, gets
`IntegrableOn mono B` on a ball B ⊆ box, then `refine (hmono_intB.const_mul Mub).mono' ?meas ?bound`
to dominate the actual integrand. My case adds the (∑z²)^{-cc} factor, so my dominating function is
g u := mono u · (∑_{j∈Z}u_j^2)^{-cc} and I must show `∫⁻ u in box, ofReal (g u) < ⊤`.

## Confirmed-present Mathlib substrate (exact names)

- MeasurableEquiv.piEquivPiSubtypeProd (π) (p) : (∀ i, π i) ≃ᵐ (∀ i:Subtype p, π i)×(∀ i:{i//¬p i}, π i)
- measurePreserving_piEquivPiSubtypeProd (μ) (p) : MeasurePreserving that equiv (Measure.pi μ) (prod)
- Equiv.preimage_piEquivPiSubtypeProd_symm_pi p s : (equiv).symm ⁻¹' (pi univ s) = (pi univ ..) ×ˢ (pi univ ..)
- MeasurableEquiv.piCongrLeft (f : δ ≃ δ') ; measurePreserving_piCongrLeft (f) ;
  volume_measurePreserving_piCongrLeft ; piCongrLeft_apply_apply, piCongrLeft_symm_apply
- Measure.prod_restrict (s t) : (μ.restrict s).prod (ν.restrict t) = (μ.prod ν).restrict (s ×ˢ t)
- Integrable.mul_prod (hf : Integrable f μ)(hg : Integrable g ν): Integrable (fun z=>f z.1*g z.2)(μ.prod ν)
- lintegral_prod_mul (hf hg AEMeasurable): ∫⁻ f z.1*g z.2 ∂μ.prod ν = (∫⁻ f ∂μ)*(∫⁻ g ∂ν)
- MeasurePreserving.integrableOn_comp_preimage (h₁)(h₂ emb): IntegrableOn (f∘e)(e⁻¹'s) μ ↔ IntegrableOn f s ν
- integrableOn_map_equiv (e:α≃ᵐβ): IntegrableOn f s (μ.map e) ↔ IntegrableOn (f∘e)(e⁻¹'s) μ
- RLCT.integrableOn_ball_norm_rpow_iff {m}{R}(hR:0<R){s}(hs:s<0):
    IntegrableOn (fun x:EuclideanSpace ℝ (Fin (m+1))=>‖x‖^s)(Metric.ball 0 R) volume ↔ -(m+1:ℝ)<s
- RLCT.sumSq_ofLp (x:EuclideanSpace ℝ (Fin C)): sumSq C (WithLp.ofLp x) = ‖x‖^2   (sumSq C y = ∑ (y i)^2)
- PiLp.volume_preserving_ofLp (ι) : MeasurePreserving (WithLp.ofLp) ... ; MeasurableEquiv.toLp
- MonomialBox.prodRpow_boxSymm_lt_top {D}(hε:0<ε)(e:Fin D→ℝ)(he:∀ j,-1<e j):
    ∫⁻ u in univ.pi (fun _:Fin D=>Ioo (-ε) ε), ofReal (∏ j,|u j|^(e j)) < ⊤   (I will un-private this)
- ENNReal.mul_lt_top, hasFiniteIntegral_iff_ofReal, Real.mul_rpow, Real.finset_prod_rpow

## My planned skeleton (please critique / correct / simplify)

Domination target: produce ball B ∈ 𝓝 p, show IntegrableOn (integrand) B via
`(hg_intB.const_mul Mub).mono' hmeas hbound` where hg_intB : IntegrableOn g B, g u = mono u·(∑_{j∈Z}u_j²)^{-cc}.
Get IntegrableOn g box from `∫⁻ box ofReal g < ⊤` + g≥0 + g measurable, then .mono_set to B.

CRUX: `∫⁻ u in box, ofReal (g u) < ⊤`.
Step 1. a.e. on box: g u = Fsub((e u).1) · Gsub((e u).2), where
   e := MeasurableEquiv.piEquivPiSubtypeProd (fun _:Fin D=>ℝ) (·∈Z),
   Fsub : ({i//i∈Z}→ℝ)→ℝ := fun y => (∑ i, (y i)^2)^{-cc},
   Gsub : ({i//¬i∈Z}→ℝ)→ℝ := fun w => ∏ d, |w d|^(ev ↑d).
   (a.e. because mono = ∏_{Fin D}|u_d|^{ev d} off hyperplanes, and Z-factors are 1.)
Step 2. transport ∫⁻ box ofReal(Fsub∘.1 · Gsub∘.2) via measurePreserving e; box preimage splits as
   boxZ ×ˢ boxZᶜ; use Measure.prod_restrict + lintegral_prod_mul to get (∫⁻ boxZ ofReal Fsub)·(∫⁻ boxZᶜ ofReal Gsub).
Step 3a. ∫⁻ boxZᶜ ofReal Gsub < ⊤: reindex {i//¬i∈Z}→Fin(Zᶜ.card) via piCongrLeft, apply prodRpow_boxSymm_lt_top.
Step 3b. ∫⁻ boxZ ofReal Fsub < ⊤: reindex {i//i∈Z}→Fin(Z.card) via piCongrLeft, then ofLp to EuclideanSpace,
   boxZ ⊆ ℓ²-ball 0 (R·√card), apply integrableOn_ball_norm_rpow_iff (cc>0; handle cc=0 separately as constant).

## Questions (answer each, concretely)

1. Is Step 2 cleaner done at the Integrable level (Integrable.mul_prod + MeasurePreserving.integrableOn_comp_preimage
   + Measure.prod_restrict) instead of the ∫⁻ level? Give the single cleanest transport chain for
   "IntegrableOn g box" from "IntegrableOn Fsub boxZ" and "IntegrableOn Gsub boxZᶜ", including how to
   discharge the a.e. g = Fsub·Gsub∘e equality (I only need it a.e. on box) — what is the exact idiom to
   combine `.mono'`/`.congr` with the transport so I don't fight the a.e. set.
3. For Step 3b, is there a way to AVOID the double transport (subtype→Fin→EuclideanSpace)? e.g. can I use
   `EuclideanSpace ℝ {i//i∈Z}` directly and a Fintype-general ball threshold? Is `integrableOn_ball_norm_rpow_iff`
   easily reprovable/generalizable to `EuclideanSpace ℝ ι` [Fintype ι] [Nonempty ι], or is reindexing to Fin cheaper?
4. Cheapest idiom for the piCongrLeft box preimage + product reindex: I need
   `∫⁻ boxZᶜ ofReal(∏_{d:{i//¬i∈Z}}|w d|^{ev↑d}) = ∫⁻ (Fin-box) ofReal(∏_{i':Fin n}|v i'|^{ev↑(φ i')})`.
   Which transport lemma (setLIntegral_comp_preimage_emb vs map_apply vs lintegral_map) is least painful, and
   how to show the box preimage equals the Fin box (piCongrLeft permutes a constant box).
5. Any landmine: SFinite/SigmaFinite instances on subtype pi spaces, `Measure.pi (fun _=>volume) = volume`
   defeq on `{i//i∈Z}→ℝ`, DecidablePred (·∈Z), or the `Fin (m+1)` shape requirement of the ball lemma
   (Z nonempty ⟹ card = m+1). Flag anything that will bite.

Prioritize: the ONE cleanest end-to-end chain for the crux (∫⁻ box ofReal g < ⊤ OR IntegrableOn g box),
and whether Integrable-level or ∫⁻-level is less transport-painful.
</task>

<output_contract>
Answer questions 1-5 in order, each ≤ 12 lines, concrete Lean idioms (lemma names + the shape of the
rewrite/apply), not prose. Then a final "RECOMMENDED SKELETON" section: the crux as a numbered sequence
of ≤ 15 Lean steps (tactic-level), naming the exact lemma at each step. Flag any lemma you are UNSURE
exists vs. that I listed as confirmed. Distinguish "this will typecheck" (confident) from "likely, verify".
</output_contract>

<grounding_rules>
Only the lemmas I listed under "confirmed-present substrate" are known to exist. If you propose any OTHER
lemma, mark it [UNVERIFIED] and give a fallback built only from confirmed lemmas. Do not invent Mathlib
API. If a step needs a lemma that likely does not exist, say so and give the from-scratch construction.
</grounding_rules>
