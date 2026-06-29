<task>
I am formalising in Lean 4 / Mathlib v4.29 the L=2 "gauge-slice diffeo bridge" for a deep-linear-network
RLCT computation. I must DEFINE a reparametrization map `psiL2` on flat coordinates and prove it is a
local diffeo at a base point `wstar`, with an eventual composition identity. I need a sanity check on the
DEFINITION SHAPE and the BUILD ORDER before sinking effort, because a wrong def wastes all downstream work.

CONTEXT (the math, verified ~1e-17 by an upstream sympy/numpy cert):
The joint (T1,Y1) action Ψ on the gauge-split coordinates is, with A_s = I + readX s (per-layer pivot),
all "reads" being matrix blocks that VANISH at wstar (origin of the split):
  K   := Z1 · ⅟P00 · Y0
  W   := I + Z1·A1⁻¹·A0⁻¹·Y0
  S1  := T1 − Z1·A1⁻¹·Y1
  T1' := W⁻¹·[ (I−K)·S1 + Z1·A1⁻¹·Y1 + Z1·A1⁻¹·A0⁻¹·Y0·T1 ]
  Y1' := Y1 + A0⁻¹·Y0·(T1 − T1')
Everything else (X0,X1,Z0,Z1,Y0,T0, spectators) is FIXED. Note T1−T1' = O(read³), Y1'−Y1 = O(read⁴),
K = O(read²), W−I = O(read²), S1 = O(read). At wstar all reads = 0, so T1'=T1, Y1'=Y1 (Ψ fixes wstar).

THE LEAN ENCODING (immovable — banked, I cannot change these):
- `split : (Fin n → ℝ) ≃ₜ DeepestSplit` is a SMOOTH AFFINE chart: `split w = deepestSplitCLE (w − wstar)`,
  with `deepestSplitCLE` a ContinuousLinearEquiv. `DeepestSplit = Reg × (Core × Spec)` (a product of
  three `Fin _ → ℝ` function spaces). I have `contDiff_deepestSplit`, `hasStrictFDerivAt_deepestSplit`
  (deriv = deepestSplitCLE), and the same for `.symm`.
- The Core slot `q.2.1 : Fin (flatDim M) → ℝ` decodes to per-layer cores via `paramsEquivFlat M`:
  `(paramsEquivFlat M).symm q.2.1 s` is the layer-s core matrix block. Last layer = `lastLayer hL`.
- The (Reg, Spec) slots `(q.1, q.2.2)` feed `regGaugeSlotEquiv` to give `RegGaugeIdx → ℝ`, off which
  `readX/readY/readZ (q.1,q.2.2) s` read the per-layer X/Y/Z blocks. I have read-after-write lenses:
  `readY_regGaugeSlotEquiv_symm_update_ne` (a Function.update at one Y-tag fixes all other reads).
- BANKED smoothness pattern: `contDiff_contDiffBump_smul (χ : ContDiffBump 0) (raw) (hraw : ∀ x ∈ tsupport χ, ContDiffAt ⊤ raw x) : ContDiff ⊤ (fun x => χ x • raw x)`.
  And `unitSet = {p | ∀ s, det(1 + readX p s) ≠ 0}` is OPEN, contains 0; `cutoffBump` is a ContDiffBump
  at 0 with tsupport ⊆ unitSet. Matrix-inverse-entry smoothness where det≠0 is banked
  (`contDiffAt_matrix_inv_entry_of_det_ne_zero`, `contDiffAt_matrix_mul_entry`).
- BANKED fderiv pattern: `hasStrictFDerivAt_coreShearHomeo_symm_zero` shows an additive core-shear
  `(reg,core,spec) ↦ (reg, core − shift(reg,spec), spec)` with `shift` having strict deriv 0 at 0 has
  strict deriv = id at 0.
- The final assembly is `rlctAtOn_diffeo_bridge_of (Φscore Φcore wstar Psi e) (hcontdiff)(hderiv)(hfix)(hcomp)`
  needing: ContDiff ⊤ Psi; HasStrictFDerivAt Psi (e:=id CLE) wstar; Psi wstar = wstar;
  Φcore ∘ Psi =ᶠ[𝓝 wstar] Φscore.

MY PROPOSED DEFINITION:
  psiSplitCorr (q : DeepestSplit) : DeepestSplit -- a function producing the joint (ΔT1, ΔY1) edit
     := writes Core slot' = paramsEquivFlat M (Function.update (decode core) lastLayer T1'), where
        T1' uses W⁻¹,⅟P00 of the reads of (q.1,q.2.2); and Reg/Spec slot via regGaugeSlotEquiv.symm
        (Function.update (encode) lastY-tag Y1'). i.e. Ψ_split q = (reg', (core', spec')).
  psiSplitL2 q := (1 - χ(q)) • q + χ(q) • Ψ_split q   -- additive cutoff blend (χ = cutoffBump-type on DeepestSplit)
  psiRawL2 w := split.symm (Ψ_split (split w))    -- raw, no cutoff
  psiL2 w    := split.symm (psiSplitL2 (split w)) -- cutoff version

QUESTIONS (rank + answer each, concise):
1. Is the additive-blend cutoff `(1−χ)•q + χ•Ψ_split q` the right shape, OR should I cut off only the
   CORRECTION `q + χ•(Ψ_split q − q)` (so that off-support it is exactly `id`, and `Ψ_split q − q` is the
   thing that is O(read³) hence has deriv 0 at 0)? Which makes S4 (deriv=id at wstar) and S2 (ContDiff)
   cleanest given the banked `contDiff_contDiffBump_smul` + `hasStrictFDerivAt_coreShearHomeo_symm_zero`?
2. The cutoff bump on DeepestSplit: I need a ContDiffBump at 0 on the FULL `DeepestSplit` (Reg×(Core×Spec)),
   but `unitSet`/`cutoffBump` are banked only on `(Reg × Spec)` (the reads don't touch Core). Cleanest way
   to get a full-DeepestSplit bump whose support is inside {reads invertible}: compose the banked
   (Reg×Spec) bump with the projection `(reg,core,spec) ↦ (reg,spec)`? Or build a fresh ContDiffBump at 0
   on DeepestSplit and intersect support with the preimage of unitSet? Note χ must be ContDiff and =1 near 0.
3. For S4 (HasStrictFDerivAt psiL2 (id) wstar): with the "cut off the correction" form, the correction
   `χ•(Ψ_split·−·)` should have deriv 0 at 0 because `Ψ_split·−·` is O(read³)=o(‖·‖). Is proving
   "HasStrictFDerivAt (correction) 0 at 0" via `hasStrictFDerivAt_iff_isLittleO`/the o(‖h‖) route viable,
   or is there a cleaner compositional route (each of T1'−T1, Y1'−Y1 is a product where ≥1 factor is a
   read that vanishes-to-deriv-0)? The reads themselves are LINEAR in w (coordinate projections), so
   their deriv is NOT 0 — only PRODUCTS of ≥2 reads have deriv 0. Flag the trap.
4. Build order to MAXIMISE landed lemmas if S6 (comp-identity through the LDU) turns out to be 2+ tides:
   which of S2(ContDiff)/S4(fderiv)/S3(fixpoint) can land WITHOUT the comp-identity, and does the def shape
   above let them land independently?
5. Any structural reason this whole route is wrong / a simpler Ψ exists that the upstream cert missed?
</task>

<output_contract>
Answer Q1–Q5 in order, each ≤8 sentences. For Q1 and Q2 give the concrete recommended Lean def shape
(pseudocode is fine). Flag any trap explicitly as "TRAP:". End with a one-line GO / RECONSIDER verdict
on the proposed def.
</output_contract>

<grounding_rules>
You may reason from standard Mathlib v4.29 API and the banked lemmas I listed. Mark anything you are
INFERRING about Mathlib lemma availability (vs certain) as "[infer]". Do not invent lemma names as if
they certainly exist.
</grounding_rules>
