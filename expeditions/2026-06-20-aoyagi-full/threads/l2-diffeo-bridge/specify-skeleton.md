# SPECIFY — `deepest_diffeo_bridge_L2` (the L=2 gauge-slice diffeo bridge)

Skeleton + sub-lemma signatures, for controller approval BEFORE filling. Builds from the g146
design certs (`../31-pin2-comparability/h2-diffeo-bridge-cert.md`,
`h2-joint-psi-cert.md`). L=2 ONLY; does NOT touch 3289.

## Target

The bare `sorry` at `DeepestGaugeConstruction.lean:2915` is the body of
`deepest_diffeo_bridge_L2` (header 2853): for the joint `(T1,Y1)` Ψ at `L=2`,
`rlctAtOn Φscore wstar = rlctAtOn Φcore wstar`, where
`Φscore x = ∑(regStraighten(split x)).1² + Score x`,
`Φcore x = ∑(regStraighten(split x)).1² + deepestCoreF H r (coreAbsorb (split x)).2.1`.

## Module placement

NEW module `DeepestDiffeoBridgeL2.lean` (imports `DeepestGaugeConstruction` + my
`DeepestLeadingBlock`). The bridge CONTENT is built here as `deepest_diffeo_bridge_L2_impl`
with the IDENTICAL signature to `deepest_diffeo_bridge_L2`. The controller then replaces
2915's `sorry` with `exact DeepestDiffeoBridgeL2.deepest_diffeo_bridge_L2_impl H r B …`
(single-writer producer — I do not edit it). The `_impl` lemma is independently
`#print axioms`-verifiable.

OPEN QUESTION for controller: alternatively, do you want the bridge body filled IN PLACE at
2915 (you paste my proof term)? The `_impl` route keeps the producer single-writer and gives
independent axiom-verification; I default to it unless you prefer in-place.

## The Ψ (from the design cert, verified exact ~1e-17)

Act on the last-layer core `T1` AND last-layer reg read `Y1`; fix everything else:

    K   := Z1 · ⅟P00 · Y0                         (M1×M1, = O(read²))
    W   := I_{M1} + Z1·A1⁻¹·A0⁻¹·Y0               (M1×M1 unit near wstar)
    S1  := T1 − Z1·A1⁻¹·Y1
    T1' := W⁻¹·[ (I−K)·S1 + Z1·A1⁻¹·Y1 + Z1·A1⁻¹·A0⁻¹·Y0·T1 ]
    Y1' := Y1 + A0⁻¹·Y0·(T1 − T1')

`A0 = 1+X0`, `A1 = 1+X1` (the per-layer reg reads, units near wstar). `A0⁻¹` is where my KC1
`deepestPoint_leadingBlock_isUnit` / the regular-block invertibility supplies `[Invertible A0]`.

## Skeleton (sub-lemmas, sorry-each, in dependency order)

### S0 — the raw Ψ map on flat coords (def, no proof)
`psiRawL2 : (Fin (flatDim H) → ℝ) → (Fin (flatDim H) → ℝ)` — `split⁻¹ ∘ (joint (T1,Y1) action on
DeepestSplit) ∘ split`. The action reads the core/reg slots of `DeepestSplit H r (deepestNGauge H r)`,
applies the closed form, writes back. Built via the `DeepestPsiLens` read-lenses + `Function.update`.
RISK: the slot-encoding bookkeeping (which `DeepestSplit` fields are T1/Y1/Z1/A_s) — the cert §(2)
names them via `framedParamsPivot` blocks; I confirm the exact field maps in-build against
`DeepestPsiLens` (`readX/readY/readZ_regGaugeSlotEquiv_symm`).

### S1 — the cutoff Ψ (def, no proof): `psiL2 := wstar + χ·(psiRawL2 − wstar)`
Reuse the banked `cutoffBump`/`schurCutoffShift` pattern (`DeepestSchurShift:270/310`): χ a
`ContDiffBump`, χ=1 on a ball ⊂ the common invertibility locus `U_inv = {det A0,det A1,det W,det P00 ≠ 0}`,
`tsupport χ ⊂ U_inv`. `psiL2 = psiRawL2` on χ=1, `= id` off `tsupport χ`.

### S2 — `psiL2_contDiff : ContDiff ℝ ⊤ psiL2`   [HEAVIEST]
The two NEW composite-inverse smoothness lemmas (`W⁻¹`, `⅟P00`) ContDiff-on-`U_inv` via
`contDiffAt_matrix_inv_entry_of_det_ne_zero` (banked) + `ContDiff.mul` of the banked per-layer
`(1+X_s)⁻¹` (`DeepestSchurSmooth:117`); then χ-cutoff to global (the `contDiff_schurCutoffShift`
pattern, `:208`). Consumes: `split` smoothness `contDiff_deepestSplit` (BANKED).

### S3 — `psiL2_fixpoint : psiL2 wstar = wstar`
At wstar all reads → 0 ⟹ K=0, S1=0, the (T1,Y1)-correction = 0; χ(wstar)=1. Light.

### S4 — `psiL2_hasStrictFDerivAt : HasStrictFDerivAt psiL2 (ContinuousLinearMap.id ℝ _) wstar`
The correction is O(read³) ⟹ D(psiRawL2 − id)(wstar) = 0; χ=1 near wstar; `split` deriv is the
`≃L` L, conjugates to id. Mirror `hasStrictFDerivAt_coreShearHomeo_symm_zero` (BANKED) +
`hasStrictFDerivAt_deepestSplit` (BANKED). Moderate.

### S5 — `e2_regPreserve : deepestEFull H r hr hL J Pf Qf ∘ (Ψ_split) = deepestEFull …`   [my KC1 brick]
The EXACT `A0·A0⁻¹=I` cancel (cert §(b), ~tens LoC). P00,P10 are T1,Y1-free (fixed by `rfl`/`congr`);
P01'−P01 = A0(Y1'−Y1)+Y0(T1'−T1) = Y0(T1−T1')+Y0(T1'−T1) = 0 via `[Invertible A0]` (my brick) +
`Matrix.mul_inv_cancel`/`mul_add`. Packs through `deepestEFull`'s `regResidualPack` (the
P00/P01/P10 block-read).

### S6 — `comp_identity : (fun x => Φcore (psiL2 x)) =ᶠ[nhds wstar] Φscore`   [composition plumbing]
On the inner ball (χ=1): the reg term `∑(regStraighten(split x)).1²` is `deepestEFull`-based and
FIXED by S5; the core term `coreΦ(Ψx) = frobSq(S0·(I−K)·S1) = Score(x)` via banked
`deepestCoreF_coreAbsorb_eq_prodSchur` (`:1945`) + the LDU `rcore_schur_factor_of_corner_split`
(`DeepestBlockDecomp:208`). The fiddly part: threading the joint action through
`split`/`coreAbsorb`/`paramsEquivFlat`/`framedParamsPivot` encodings (cert §(2) steps 1-6).

### FINAL — `deepest_diffeo_bridge_L2_impl` (the signature-matching assembly)
`rw [← rlctAtOn_germ_local _ _ wstar (comp_identity …)]` then
`exact rlctAtOn_comp_localDiffeo Φcore wstar psiL2 (.id ℝ _) (S2) (S4) (S3)`
— i.e. EXACTLY the banked `rlctAtOn_diffeo_bridge_of` body (S2/S4/S3/S6 are its four antecedents).

## Banked dependencies (all re-verified present)
- `rlctAtOn_comp_localDiffeo` / `rlctAtOn_diffeo_bridge_of` / `rlctAtOn_germ_local` — abstract bridge.
- `contDiff_deepestSplit` / `hasStrictFDerivAt_deepestSplit` (+symm) — split smooth-affine (DONE).
- `cutoffBump` / `schurCutoffShift` / `contDiff_schurCutoffShift` / `hasStrictFDerivAt_schurCutoffShift_zero` — cutoff.
- `contDiffAt_matrix_inv_entry_of_det_ne_zero` — matrix-inverse smoothness; `DeepestSchurSmooth:117` per-layer (1+X)⁻¹.
- `deepestCoreF_coreAbsorb_eq_prodSchur` (:1945) + `rcore_schur_factor_of_corner_split` (DeepestBlockDecomp:208) — composition.
- `hasStrictFDerivAt_coreShearHomeo_symm_zero` — fderiv-id pattern.
- `DeepestPsiLens` (readX/Y/Z lenses) — the slot read/write.
- `deepestEFull` / `regResidualPack` / `framedParamsPivot_coreZero` — the reg-block read.
- `deepestPoint_leadingBlock_isUnit` (MINE) — `[Invertible A0]` for S5.

## Difficulty ranking (revised, split-promotion DONE)
S2 (composite-inverse cutoff smoothness) > S6 (composition encoding-plumbing) > S4 (fderiv) >
S0/S1 (Ψ defs + slot bookkeeping) > S5 (E2, easy via my brick) > S3 (fixpoint). ~2 tides.

## Risks (honest)
- S0/S6 slot-encoding bookkeeping: which `DeepestSplit` fields ↔ T1/Y1/Z1/A_s. The cert names them
  via `framedParamsPivot` + `DeepestPsiLens`; if the field map is more tangled than the cert's clean
  closed form, S6 balloons. MITIGATION: confirm the field map FIRST (a `#check`/`example` probe against
  `DeepestPsiLens` lenses) before committing to S0's def.
- S2 the `⅟P00` / `W⁻¹` composite-inverse ContDiff: the per-layer is banked; these EXTEND it (product-
  pivot (1,1)-block + the W composite). If `contDiffAt_matrix_inv` doesn't compose cleanly over the
  product-block at v4.29, S2 is the wall — would consult Codex.
- The product-order convention (`prod = S0·S1` vs `S1·S0`) — confirm `prodAux` fold vs LDU `S0·(…)·S1`
  in-build (cert flags it, low risk at L=2 two-factor).

## What I send the controller now
This skeleton + the OPEN QUESTION (_impl vs in-place). On approval I write the Lean skeleton
(defs + 6 sub-lemma signatures, sorry-each, typechecking against the banked interface) and send THAT
diff before filling. Then fill S3→S5→S4→S2→S6→FINAL (light-first to de-risk the assembly early),
diff-gated per soundness-region sub-lemma (esp. S5/S6).
