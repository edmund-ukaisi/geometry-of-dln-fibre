<task>
Design-review a Lean construction: an explicit local diffeomorphism Ψ on flat coordinates feeding a
banked RLCT-invariance lemma. I have Ψ and the composition identity verified exactly (sympy/numpy);
I need a ruthless check of the SMOOTHNESS/domain hypotheses and the cleanest formulation, plus an honest
tide estimate. Try to find a hole in the smoothness story.
</task>

<setup>
L=2 DLN, deepest point wstar (all per-layer reads → 0 there). Chart `split : (Fin (flatDim H)→ℝ) ≃ₜ
DeepestSplit` is a homeomorphism; `DeepestSplit = (reg) × (core × spec)`. Per-layer reads X_s,Y_s,Z_s
(reg/spec) and cores T_s (core slot), s=0,1. M_s = H_s − r reduced widths.

Two functions on flat coords x:
  Score(x) = ‖Rcore‖²_F,  Rcore = S0·(1−K)·S1   (banked LDU `rcore_schur_factor_of_corner_split`),
    S_s = T_s − Z_s·(1+X_s)⁻¹·Y_s (per-layer Schur cores),  K = Z1·P00⁻¹·Y0  (P00 = full-product (1,1)
    block + 1, → I at wstar; depends only on reg/spec reads).
  coreΦ(x) = deepestCoreF(coreAbsorb(split x)).2.1 = ‖∏ S_s‖²_F = ‖S0·S1‖²_F   (per-layer product;
    `deepestCoreF := dlnLoss(deepestM)`, banked `deepestCoreF_coreAbsorb_eq_prodSchur` gives the = ‖∏S‖²).
  (Both have Sreg_E added in the actual goal; Sreg_E is unchanged by Ψ — see below.)

GOAL LEMMA (to feed banked `rlctAtOn_comp_localDiffeo`):
  rlctAtOn(Sreg_E + coreΦ) wstar = rlctAtOn(Sreg_E + Score) wstar.

`rlctAtOn_comp_localDiffeo (F) (wstar) (f) (e : M ≃L[ℝ] M)` needs: `ContDiff ℝ ⊤ f` (GLOBAL),
`HasStrictFDerivAt f (e:M→L M) wstar`, `f wstar = wstar`; concludes `rlctAtOn(F∘f) wstar = rlctAtOn F wstar`.
Its docstring notes "ContDiff ⊤ is a CONVENIENCE above the germ minimum — ContDiffAt/HasStrictFDerivAt at
wstar would suffice — but the producer's maps are globally smooth anyway."

MY Ψ (verified: coreΦ∘Ψ = Score exactly, all shapes r,M; Ψ'(wstar)=id exactly; Ψ(wstar)=wstar):
  Ψ acts ONLY on the last-layer core block, fixing reg/spec/T0:
     T1 ↦ T1' = (1−K)·T1 + K·Z1·(1+X1)⁻¹·Y1,   K = Z1·P00⁻¹·Y0.
  Then the absorbed last-layer core S1' = T1' − Z1(1+X1)⁻¹Y1 = (1−K)·S1, so ∏(absorbed) = S0·(1−K)·S1 =
  Rcore, hence coreΦ(Ψ x) = ‖Rcore‖² = Score. K depends only on reg/spec (NOT on core T) ⟹ Ψ is
  TRIANGULAR (fixes reg/spec, affine in the core slot). On flat coords Ψ = split⁻¹ ∘ (core-action) ∘ split.

The HOLE I'm worried about: Ψ involves matrix inverses P00⁻¹ and (1+X1)⁻¹, which are smooth only where
P00, 1+X1 are invertible (a NBHD of wstar, not global). `rlctAtOn_comp_localDiffeo` wants `ContDiff ⊤ f`
GLOBALLY.
</setup>

<questions>
1. SMOOTHNESS: is the global-ContDiff⊤ requirement a real obstruction? Options: (a) cutoff-bump Ψ
   (multiply the K-correction by a `ContDiffBump` χ=1 near wstar, like the banked `schurCutoffShift =
   χ·schurShiftRaw`), giving a GLOBAL ContDiff⊤ map that equals honest Ψ on the inner ball — but then is
   Ψ still a diffeo with Ψ'(wstar)=id? (the cutoff is 1 near wstar so the germ is unchanged); (b) prove a
   `ContDiffAt`-only variant of `rlctAtOn_comp_localDiffeo` (its docstring says ContDiffAt suffices); (c)
   something cleaner. Which is the least-work, soundest route? Does the cutoff version still satisfy ALL
   three antecedents (ContDiff ⊤ global ✓, HasStrictFDerivAt at wstar = id ✓ since χ=1 near wstar, fix ✓)?
2. Is acting on T1 (the last-layer core) the cleanest, or is there a simpler Ψ? (e.g. acting on the
   reduced-product directly, or a different slot.) The constraint: Ψ must fix Sreg_E and turn ∏S into Rcore.
3. The composition identity coreΦ∘Ψ = Score: I verified it numerically. The Lean proof chain: Ψ's core
   action gives absorbed S1' = (1−K)S1 (algebra: T1' − Z1(1+X1)⁻¹Y1 = (1−K)(T1 − Z1(1+X1)⁻¹Y1) since
   T1' = (1−K)T1 + K·Z1(1+X1)⁻¹Y1), then ∏ = S0·(1−K)·S1 = Rcore by the banked LDU. Is this chain
   complete/correct, or is there a gap (e.g. does deepestCoreF see the product in the order S0·S1, and does
   coreAbsorb's shift interact with my T1-replacement)?
4. FDERIV: Ψ'(wstar) = id because the K-correction is O(read³) near wstar (K=O(read²), times T1/Z1Y1
   =O(read)). So HasStrictFDerivAt Ψ id wstar. Confirm this is the right e:≃L (the identity ≃L), and that
   the cutoff (if used) doesn't break it.
5. HONEST TIDE ESTIMATE: another agent says multi-tide. What's the heaviest sub-piece? Candidates: (i) the
   cutoff-bump global smoothness + its strict-fderiv-at-wstar = id (mirrors banked schurCutoffShift work);
   (ii) the composition identity through split/coreAbsorb/paramsEquivFlat (lots of defeq plumbing); (iii)
   transporting Ψ from DeepestSplit to flat coords (split is a homeo, not linear — does ContDiff transport?
   split is only ≃ₜ, NOT a diffeo a priori!). Flag (iii) — is `split` smooth? If split is only a
   homeomorphism (not C⊤), then Ψ = split⁻¹∘…∘split may NOT be ContDiff even if the core-action is. THIS
   could be the real heavy piece. Assess.
</questions>

<output_contract>
- Separate FACT from INFERENCE. Rank the sub-pieces by difficulty with a tide estimate.
- The KEY deliverables: (a) is the cutoff route sound for all three antecedents? (b) is `split`'s
  smoothness a hidden obstruction (Ψ on flat coords needs split to be a diffeo, not just a homeo)? (c) the
  cleanest Ψ + the complete composition-identity chain.
- If `split` smoothness is the blocker, say so loudly and propose the route (work in DeepestSplit coords
  throughout / is split actually a diffeo by construction?).
</output_contract>

<grounding_rules>
- coreΦ∘Ψ = Score verified exactly (machine precision, all r,M shapes). Ψ'(wstar)=id, Ψ(wstar)=wstar
  verified exactly. The question is the Lean SMOOTHNESS/transport story, not the algebra.
- `split` is typed `≃ₜ` (homeomorphism). Whether it is also ContDiff/a diffeo is the load-bearing unknown.
- Banked: `rcore_schur_factor_of_corner_split` (LDU), `deepestCoreF_coreAbsorb_eq_prodSchur`,
  `coreShearHomeo` + its strict-fderiv-at-0=id (`hasStrictFDerivAt_coreShearHomeo_symm_zero`),
  `schurCutoffShift` (the χ-cutoff pattern + its ContDiff + strict-fderiv-0 = banked),
  `rlctAtOn_comp_localDiffeo`.
</grounding_rules>
