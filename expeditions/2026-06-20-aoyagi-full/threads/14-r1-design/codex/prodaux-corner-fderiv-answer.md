   Updating ssh://git@github.com/AI-Safety-Institute/aisi-inspect-tools (HEAD)
    Updated ssh://git@github.com/AI-Safety-Institute/aisi-inspect-tools (fa7351f6ef4773f536ee4975c3251325eb9c44df)
Reading additional input from stdin...
OpenAI Codex v0.142.0
--------
workdir: /home/ubuntu/workspace/deriv-spec
model: gpt-5.5
provider: openai-aisi
approval: untrusted
sandbox: read-only
reasoning effort: xhigh
reasoning summaries: none
session id: 019ef5a0-c1f7-7cd0-9896-ea1a59ab88dd
--------
user
Lean 4 + Mathlib v4.29 formalisation. I need the explicit strict-derivative VALUE of the entries of a chain matrix product, evaluated at a base point where every layer is the idempotent "corner" matrix.

SETUP (all banked, sorry-free):
- `Params H := ∀ s : Fin L, Matrix (Fin (H s.castSucc)) (Fin (H s.succ)) ℝ`.
- `prodAux H A : (k:ℕ) → (hk : k < L+1) → Matrix (Fin (H 0)) (Fin (H ⟨k,hk⟩)) ℝ`, with
  `prodAux 0 = 1`, `prodAux (k+1) = prodAux k * (cast layer ⟨k,hkL⟩)` (dependent Fin casts e1/e2).
- `prod H A := prodAux H A L (Nat.lt_succ_self L)`.
- `framedParamsReg H r hr hL p : Params H`, each layer = `reindex e.symm e'.symm (fromBlocks (1+X_s) Y_s Z_s 0)` where X_s=readX p s etc (linear in p, =0 at p=0).
- At p=0 (gauge slot 0): `prodAux_framedParamsReg_zero_aux`: for 1≤k≤L, `prodAux (framedParamsReg 0) k = reindex e0.symm ek.symm (fromBlocks 1 0 0 0)` (the corner).
- Banked: `hasStrictFDerivAt_prodAux_entry` proves EXISTENCE of a strict derivative D for each entry `fun y => prodAux (g y) k i j` (opaque D, built by Leibniz HasStrictFDerivAt.sum/.mul induction), but NOT the explicit value.
- `corner_reindex_mul`: corner * corner = corner (idempotent under the chain, reindexed).

GOAL: the reg-slice `r0 ↦ deepestEPivot (r0,0)` (each output coord is a block entry (P11-1)/P12/P21 of `P=reindex(prod(framedParamsReg(r0,0)))`) has strict derivative `id` at 0. The math: dP|_0 = Σ_s corner·δC_s·corner. corner·δC_s·corner keeps only: (0,0)-block X_s for all s, (0,1)-block Y_s for the LAST layer, (1,0)-block Z_s for the FIRST layer. With gauge=0 the reg-coords route X to first layer, Y to last, Z to first (via regBoundaryToRegGauge∘regPivotFinEquiv shared with regResidualPack=regPivotFinEquiv), so each coord's derivative = the matching r0 projection.

QUESTION: what is the cleanest Lean route to get the EXPLICIT derivative value (the corner-sandwich sum), given only the EXISTENCE lemma + the corner idempotent base? Options I see:
(A) Prove a NEW explicit-value Leibniz lemma `prodAux_corner_fderiv`: by induction, the strict derivative of `prodAux(framedParamsReg(r0,0)) k i j` at 0 is `Σ_{s<k} (corner_{0..s})·(δlayer_s)·(corner_{s+1..k})` — but this needs naming the running-corner-prefixes and is heavy.
(B) Bypass the explicit Σ: prove directly that the COORDINATE function `r0 ↦ (block entry of reindex prod) i` has derivative `proj i`, by showing the function equals `r0 ↦ r0 i + (higher order)` — i.e. find a clean `HasStrictFDerivAt` via the structure without naming the full Σ.
(C) Something using `HasFDerivAt.congr_fderiv` / uniqueness: we KNOW a derivative D exists (existence lemma); separately compute that the FUNCTION agrees to first order with the linear `proj i` — e.g. via `hasStrictFDerivAt_iff_isLittleO` and bounding the remainder.

Which is least Lean-painful at v4.29? Give the concrete lemma statement(s) + tactic skeleton for the recommended route. Be concrete about avoiding the dependent-Fin cast blowup in the prodAux induction. Mathlib v4.29 names only.
codex
I’ll inspect the local Lean/mathlib APIs and the existing formalization shape first, because the practical answer depends on the exact names and how much notation/cast machinery is already banked.
exec
/bin/bash -lc 'rg -n "hasStrictFDerivAt_iff_isLittleO|HasStrictFDerivAt|congr_fderiv|unique.*fderiv|isLittleO" $(pwd)/.lake/packages/mathlib/Mathlib $(pwd)/.lake/packages/mathlib/Mathlib.lean' in /home/ubuntu/workspace/deriv-spec
2026-06-23T17:57:08.568955Z ERROR codex_app_server::bespoke_event_handling: request failed with client error: JSONRPCErrorError { code: -32000, data: None, message: "command execution approval is not supported in exec mode for thread `019ef5a0-c1f7-7cd0-9896-ea1a59ab88dd`" }
 exited 1:
2026-06-23T17:57:08.569602Z ERROR codex_core::tools::router: error=exec_command failed for `/bin/bash -lc 'rg -n "hasStrictFDerivAt_iff_isLittleO|HasStrictFDerivAt|congr_fderiv|unique.*fderiv|isLittleO" $(pwd)/.lake/packages/mathlib/Mathlib $(pwd)/.lake/packages/mathlib/Mathlib.lean'`: CreateProcess { message: "Rejected(\"rejected by user\")" }
exec
/bin/bash -lc "rg --files . | rg '("'^|/)CLAUDE'"\\.md"'$|lake-manifest'"\\.json|lakefile|Deriv|Dln|Fibre|Formal|Lean|\\.lean"'$'"'" in /home/ubuntu/workspace/deriv-spec
 succeeded in 0ms:
./CLAUDE.md
./lean/DLNFibre.lean
./lean/lake-manifest.json
./lean/lakefile.toml
./lean/CLAUDE.md
./lean/DLNFibre/Core/SmoothPointRegular.lean
./lean/DLNFibre/Core/OrbitImageDim.lean
./lean/DLNFibre/Core/BoxMoveGeneral.lean
./lean/DLNFibre/Core/Barcode.lean
./lean/DLNFibre/Core/CThetaQIP.lean
./lean/DLNFibre/Core/MatrixKaehler.lean
./lean/DLNFibre/Core/IntegralDimension.lean
./lean/DLNFibre/Core/Gabriel.lean
./lean/DLNFibre/Core/OrbitVariety.lean
./lean/DLNFibre/Core/NullstellensatzCodim.lean
./lean/DLNFibre/Core/RankLocusClosed.lean
./lean/DLNFibre/Core/CTheta.lean
./lean/DLNFibre/Core/AffineDomainDimension.lean
./lean/DLNFibre/Core/CThetaQIPConverse.lean
./lean/DLNFibre/Core/OrbitCodim.lean
./lean/DLNFibre/Core/BaseChange.lean
./lean/DLNFibre/Core/CThetaDropM.lean
./lean/DLNFibre/Core/FlatQuasiFiniteHeight.lean
./lean/DLNFibre/Core/IntervalModule.lean
./lean/DLNFibre/Core/PolynomialDimension.lean
./lean/DLNFibre/Core/SmoothLocalRelativeDimension.lean
./lean/DLNFibre/Core/OrbitKostant.lean
./lean/DLNFibre/Core/OrbitClosure.lean
./lean/DLNFibre/Core/VoigtDischarge.lean
./lean/DLNFibre/Core/OrbitLinearCodim.lean
./lean/DLNFibre/Core/CThetaExplicit.lean
./lean/DLNFibre/Core/Submult.lean
./lean/DLNFibre/Core/JacobianTrdeg.lean
./lean/DLNFibre/Core/BoxMoveDegeneration.lean
./lean/DLNFibre/Core/Basic.lean
./lean/DLNFibre/Core/BoxMoveGeneration.lean
./lean/DLNFibre/Core/CThetaValue.lean
./lean/DLNFibre/Core/PolynomialCurveLimit.lean
./lean/DLNFibre/Core/CThetaThetaBridge.lean
./lean/DLNFibre/Core/OrbitSmooth.lean
./lean/DLNFibre/Core/OrbitDifferentialRank.lean
./lean/DLNFibre/Core/CThetaGeometric.lean
./lean/DLNFibre/Core/DeformationExt.lean
./lean/DLNFibre/Core/AffineNoetherRank.lean
./lean/DLNFibre/Core/NoetherMonicPositioning.lean
./lean/DLNFibre/Core/OrbitTangentCotangent.lean
./lean/DLNFibre/Core/OrbitDifferential.lean
./lean/DLNFibre/Core/Setup.lean
./lean/DLNFibre/Core/MeasureTheory/PolynomialZeroSet.lean
./lean/DLNFibre/Core/OrbitPullbackDim.lean
./lean/DLNFibre/Core/Orbit.lean
./lean/DLNFibre/DLN/Basic.lean
./lean/DLNFibre/Core/Matrix/RankNormalForm.lean
./lean/DLNFibre/Core/RankPattern.lean
./lean/DLNFibre/Core/CotangentJacobian.lean
./expeditions/2026-06-18-voigt-discharge/threads/33-A1-kahler-trdeg-api/probes/KahlerTrdegProbe.lean
./expeditions/2026-06-18-voigt-discharge/threads/33-A1-kahler-trdeg-api/probes/RingKrullTrdegProbe.lean
./lean/DLNFibre/DLN/RLCT/BGEngine.lean
./lean/DLNFibre/DLN/RLCT/Foundations/S1Cover.lean
./lean/DLNFibre/DLN/RLCT/Foundations/S1Additive.lean
./lean/DLNFibre/DLN/RLCT/Foundations/S1Spectator.lean
./lean/DLNFibre/DLN/RLCT/Foundations/ParamsFlat.lean
./lean/DLNFibre/DLN/RLCT/Foundations/S1G5.lean
./lean/DLNFibre/DLN/RLCT/Foundations/S1Fubini.lean
./lean/DLNFibre/DLN/RLCT/Foundations/S1SmoothBlock.lean
./lean/DLNFibre/DLN/RLCT/Foundations/Loss.lean
./lean/DLNFibre/DLN/RLCT/Foundations/Lambda.lean
./lean/DLNFibre/DLN/RLCT/Foundations/S1ProductMin.lean
./lean/DLNFibre/DLN/RLCT/Foundations/DeepestSplitHaar.lean
./lean/DLNFibre/DLN/RLCT/Foundations/S1NonMPTransport.lean
./lean/DLNFibre/DLN/RLCT/Foundations/S1Transport.lean
./lean/DLNFibre/DLN/RLCT/Foundations/S1G5Charts.lean
./lean/DLNFibre/DLN/RLCT/Foundations/Rlct.lean
./lean/DLNFibre/DLN/RLCT/Foundations/CoreShearMP.lean
./lean/DLNFibre/DLN/RLCT/Foundations/ParamsFlat222.lean
./lean/DLNFibre/DLN/RLCT/Foundations/S1Local.lean
./lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeBlocks.lean
./lean/DLNFibre/DLN/RLCT/Validate/Case111.lean
./lean/DLNFibre/DLN/RLCT/Validate/DeepestSplitReindex.lean
./lean/DLNFibre/DLN/RLCT/Validate/DeepestNormalFormWiring.lean
./lean/DLNFibre/DLN/RLCT/Validate/DeepestFramedProduct.lean
./lean/DLNFibre/DLN/RLCT/Validate/Case222CoverGE.lean
./lean/DLNFibre/DLN/RLCT/Validate/DeepestRegAbsorbIFT.lean
./lean/DLNFibre/DLN/RLCT/Validate/DeepestTelescoping.lean
./lean/DLNFibre/DLN/RLCT/Validate/Case222CoverGETail.lean
./lean/DLNFibre/DLN/RLCT/Validate/Case222Resolution.lean
./lean/DLNFibre/DLN/RLCT/Validate/GeneralR1Recursion.lean
./lean/DLNFibre/DLN/RLCT/Validate/Case212.lean
./lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeConstruction.lean
./lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeDiffeo.lean
./lean/DLNFibre/DLN/RLCT/Validate/DeepestSchurShift.lean
./lean/DLNFibre/DLN/RLCT/Validate/ResolutionAtlas.lean
./lean/DLNFibre/DLN/RLCT/Validate/Case222Block.lean
./lean/DLNFibre/DLN/RLCT/Validate/Case222Value.lean
./lean/DLNFibre/DLN/RLCT/Validate/Case222Lemma2.lean
./lean/DLNFibre/DLN/RLCT/Validate/Case222Rlct.lean
./lean/DLNFibre/DLN/RLCT/Validate/DeepestFrame.lean
./lean/DLNFibre/DLN/RLCT/Validate/Case222Cover.lean
./lean/DLNFibre/DLN/RLCT/Validate/Case111Bridge.lean
./lean/DLNFibre/DLN/RLCT/Validate/DeepestCoreNonvanishing.lean
./lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeChart.lean
./lean/DLNFibre/DLN/RLCT/Validate/Case222Algebra.lean
./lean/DLNFibre/DLN/RLCT/Validate/DeepestMinRlct.lean
./lean/DLNFibre/DLN/RLCT/AxCheck.lean
./lean/DLNFibre/DLN/RLCT/Skeleton.lean

exec
/bin/bash -lc 'rg -n "hasStrictFDerivAt_prodAux_entry|prodAux_framedParamsReg_zero_aux|corner_reindex_mul|deepestEPivot|framedParamsReg|regBoundaryToRegGauge|regResidualPack|regPivotFinEquiv" -S .' in /home/ubuntu/workspace/deriv-spec
 succeeded in 0ms:
./lean/DLNFibre/DLN/RLCT/Validate/DeepestSplitReindex.lean:213:by construction (g213/#91). `regResidualPack` (in `DeepestGaugeConstruction`) and `regGaugeIdxSplit`
./lean/DLNFibre/DLN/RLCT/Validate/DeepestSplitReindex.lean:214:(below) both factor through the SAME `regPivotFinEquiv`, so they cancel. -/
./lean/DLNFibre/DLN/RLCT/Validate/DeepestSplitReindex.lean:217:sandwich: `(r×r) ⊕ ((r×M_L) ⊕ (M_0×r))`, the sum type `regResidualPack` targets, of card `deepestNReg`. -/
./lean/DLNFibre/DLN/RLCT/Validate/DeepestSplitReindex.lean:221:/-- **The card match** — `card BoundaryPivotIdx = deepestNReg` (the arithmetic `regResidualPack` proves:
./lean/DLNFibre/DLN/RLCT/Validate/DeepestSplitReindex.lean:238:noncomputable def regPivotFinEquiv (H : Fin (L + 1) → ℕ) (r : ℕ)
./lean/DLNFibre/DLN/RLCT/Validate/DeepestSplitReindex.lean:269:def regBoundaryToRegGauge (H : Fin (L + 1) → ℕ) (r : ℕ) (hL : 1 ≤ L) :
./lean/DLNFibre/DLN/RLCT/Validate/DeepestSplitReindex.lean:276:/-- A LEFT INVERSE of `regBoundaryToRegGauge` (total on `RegGaugeIdx`, inverting on the image). -/
./lean/DLNFibre/DLN/RLCT/Validate/DeepestSplitReindex.lean:287:/-- **`regBoundaryToRegGauge` is INJECTIVE** (the no-collapse fact) — via the left inverse `regGaugeDecode`
./lean/DLNFibre/DLN/RLCT/Validate/DeepestSplitReindex.lean:290:theorem regBoundaryToRegGauge_injective (H : Fin (L + 1) → ℕ) (r : ℕ) (hL : 1 ≤ L) :
./lean/DLNFibre/DLN/RLCT/Validate/DeepestSplitReindex.lean:291:    Function.Injective (regBoundaryToRegGauge H r hL) := by
./lean/DLNFibre/DLN/RLCT/Validate/DeepestSplitReindex.lean:300:  · rw [regBoundaryToRegGauge, regGaugeDecode, dif_pos hY]
./lean/DLNFibre/DLN/RLCT/Validate/DeepestSplitReindex.lean:302:  · rw [regBoundaryToRegGauge, regGaugeDecode, dif_pos hZ]
./lean/DLNFibre/DLN/RLCT/Validate/DeepestSplitReindex.lean:330:  ⟨regBoundaryToRegGauge H r hL, regBoundaryToRegGauge_injective H r hL⟩
./lean/DLNFibre/DLN/RLCT/Validate/DeepestSplitReindex.lean:356:`Fin nReg` (reg) half routes onto the boundary generators via `regBoundaryToRegGauge ∘ regPivotFinEquiv`
./lean/DLNFibre/DLN/RLCT/Validate/DeepestSplitReindex.lean:358:complement (its enumeration opaque — only the REG half needs the boundary alignment). So `regResidualPack
./lean/DLNFibre/DLN/RLCT/Validate/DeepestSplitReindex.lean:359::= regPivotFinEquiv` and this split's reg-half SHARE `regPivotFinEquiv`, hence cancel (reg-block = id). -/
./lean/DLNFibre/DLN/RLCT/Validate/DeepestSplitReindex.lean:366:  -- (the SHARED `regPivotFinEquiv`), gauge-half `≃ Fin nGauge` (opaque enum on the complement).
./lean/DLNFibre/DLN/RLCT/Validate/DeepestSplitReindex.lean:370:      (regPivotFinEquiv H r hr).symm
./lean/DLNFibre/DLN/RLCT/Validate/DeepestFramedProduct.lean:115:/-- **The `T = 0` framed reconstruction** (the `deepestEPivot` reconstruction half). Reconstructs the
./lean/DLNFibre/DLN/RLCT/Validate/DeepestFramedProduct.lean:117:(the core is `coreAbsorb`'s domain — `deepestEPivot` is the regular residual of `∏C|_{T=0}`, the
./lean/DLNFibre/DLN/RLCT/Validate/DeepestFramedProduct.lean:121:noncomputable def framedParamsReg (H : Fin (L + 1) → ℕ) (r : ℕ)
./lean/DLNFibre/DLN/RLCT/Validate/DeepestFramedProduct.lean:129:/-- At the origin gauge slot, `framedParamsReg` is the **block-normal identity chain**: every layer is
./lean/DLNFibre/DLN/RLCT/Validate/DeepestFramedProduct.lean:131:fact for `deepestEPivot`'s `_base` (the residual of `∏ blockdiag[I_r,0]` is `0`). -/
./lean/DLNFibre/DLN/RLCT/Validate/DeepestFramedProduct.lean:132:theorem framedParamsReg_zero (H : Fin (L + 1) → ℕ) (r : ℕ)
./lean/DLNFibre/DLN/RLCT/Validate/DeepestFramedProduct.lean:134:    framedParamsReg H r hr hL 0 s
./lean/DLNFibre/DLN/RLCT/Validate/DeepestFramedProduct.lean:138:  simp only [framedParamsReg, framedLayer, readX_zero H r hr hL s, readY_zero H r hr hL s,
./lean/DLNFibre/DLN/RLCT/Validate/DeepestFramedProduct.lean:141:/-- Each `framedParamsReg` layer ENTRY is `ContDiff ⊤` in the `(reg, gauge)` slots: the entry is a
./lean/DLNFibre/DLN/RLCT/Validate/DeepestFramedProduct.lean:144:theorem contDiff_framedParamsReg_entry (H : Fin (L + 1) → ℕ) (r : ℕ)
./lean/DLNFibre/DLN/RLCT/Validate/DeepestFramedProduct.lean:147:    ContDiff ℝ (⊤ : ℕ∞) (fun p => framedParamsReg H r hr hL p s i j) := by
./lean/DLNFibre/DLN/RLCT/Validate/DeepestFramedProduct.lean:149:  have hentry : (fun p => framedParamsReg H r hr hL p s i j)
./lean/DLNFibre/DLN/RLCT/Validate/DeepestFramedProduct.lean:155:    simp only [framedParamsReg, framedLayer, Matrix.reindex_apply, Matrix.submatrix_apply,
./lean/DLNFibre/DLN/RLCT/Validate/DeepestFramedProduct.lean:189:/-! ## `ContDiff` of the layer product (the `deepestEPivot._contdiff` infrastructure)
./lean/DLNFibre/DLN/RLCT/Validate/DeepestFramedProduct.lean:191:`deepestEPivot` is `pack ∘ residual ∘ reindex ∘ prod ∘ framedParamsReg`; its `ContDiff ⊤` reduces to
./lean/DLNFibre/DLN/RLCT/Validate/DeepestFramedProduct.lean:192:`ContDiff ⊤ (fun x => prod H (g x))` for `g = framedParamsReg` (each layer affine in the slots, so
./lean/DLNFibre/DLN/RLCT/Validate/DeepestFramedProduct.lean:256:theorem hasStrictFDerivAt_prodAux_entry {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
./lean/DLNFibre/DLN/RLCT/Validate/DeepestFramedProduct.lean:308:/-- **`HasStrictFDerivAt` of the full layer-product entries** (`hasStrictFDerivAt_prodAux_entry` at
./lean/DLNFibre/DLN/RLCT/Validate/DeepestFramedProduct.lean:310:entry does. The `_deriv` input — `deepestEPivot` is a constant-linear post-composition of these. -/
./lean/DLNFibre/DLN/RLCT/Validate/DeepestFramedProduct.lean:318:  hasStrictFDerivAt_prodAux_entry H g x g' hg L (Nat.lt_succ_self L) i j
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/fold2-deriv-statement-card.md:1:# Statement card — #82 FOLD2: `deepestEPivot_deriv` (the shear-CLE derivative)
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/fold2-deriv-statement-card.md:3:> **Claim.** `deepestEPivot`'s strict derivative at `0` is bundled with an invertible CLE `e` equal to
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/fold2-deriv-statement-card.md:7:> - **Lean:** `DLNFibre.DLN.RLCT.deepestEPivot_deriv`
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/fold2-deriv-statement-card.md:12:>   `HasStrictFDerivAt deepestEPivot D_E 0 ∧ (e : →L) = regStraightenTotalCLM D_E`
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/fold2-deriv-statement-card.md:17:>   - `D_E := fderiv ℝ deepestEPivot 0`, `hsd : HasStrictFDerivAt deepestEPivot D_E 0` via
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/fold2-deriv-statement-card.md:18:>     `(deepestEPivot_contdiff).hasStrictFDerivAt` (free from `_contdiff`).
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/fold2-deriv-statement-card.md:21:>   - that reg-block `= id` by `deepestEPivot_regSlice_fderiv_id` (the ONE obligation, see below).
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/fold2-deriv-statement-card.md:26:>   - `hasStrictFDerivAt_prodAux_entry` / `hasStrictFDerivAt_prod_entry`
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/fold2-deriv-statement-card.md:35:>   `deepestEPivot_regSlice_fderiv_id :`
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/fold2-deriv-statement-card.md:36:>   `HasStrictFDerivAt (fun r0 : Reg => deepestEPivot H r hr hL (r0, 0)) (ContinuousLinearMap.id ℝ Reg) 0`
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/fold2-deriv-statement-card.md:38:>   `dP|_0 = Σ_s corner·δC_s·corner` (corners idempotent, `prodAux_framedParamsReg_zero` banked) keeps,
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/fold2-deriv-statement-card.md:42:>   - **Named wall (Codex + g239):** the opaque `regResidualPack` / `regGaugeSlotEquiv` packing — the
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/pin1-regabsorb-statement-card.md:51:>   The shared pivot map `DLNFibre.DLN.RLCT.deepestEPivot` + its three props (`deepestEPivot_contdiff`,
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/pin1-regabsorb-statement-card.md:52:>   `deepestEPivot_deriv`, `deepestEPivot_base`) are `sorry` — the concrete nonlinear straightened
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/pin1-regabsorb-statement-card.md:56:>   E_pivot-form confirmation before the `deepestEPivot` def + props are filled.
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/pin1-regabsorb-statement-card.md:58:> - **Status.** PIN 1's analytic machinery sorry-free; the shared `deepestEPivot` (def + 3 props)
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/pin1-regabsorb-statement-card.md:70:  props — its correctness does not depend on the concrete residual form. So pinning `deepestEPivot`
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/pin1-regabsorb-statement-card.md:71:  later cannot reopen the PIN-1 peel; only the three `deepestEPivot_*` props remain.
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/deriv-alignment-sandwich-tactic-cert.md:3:For cobuild's in-place close of `deepestEPivot_regSlice_fderiv_id` AFTER the def-change (regResidualPack
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/deriv-alignment-sandwich-tactic-cert.md:4::= regPivotFinEquiv, regGaugeIdxSplit's reg-half := regBoundaryToRegGauge ∘ regPivotFinEquiv). The
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/deriv-alignment-sandwich-tactic-cert.md:5:strict-deriv is FREE (`ContDiff.hasStrictFDerivAt` on `deepestEPivot_contdiff`); the content is the VALUE
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/deriv-alignment-sandwich-tactic-cert.md:10:    theorem deepestEPivot_regSlice_fderiv_id … :
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/deriv-alignment-sandwich-tactic-cert.md:11:      HasStrictFDerivAt (fun r0 : Fin (deepestNReg H r) → ℝ => deepestEPivot H r hr hL (r0, 0))
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/deriv-alignment-sandwich-tactic-cert.md:23:    -- goal: HasStrictFDerivAt (fun r0 => deepestEPivot (r0,0) i) (proj i) 0
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/deriv-alignment-sandwich-tactic-cert.md:26:For each output coord `i : Fin nReg`, `regResidualPack i = regPivotFinEquiv i ∈ BoundaryPivotIdx` (now
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/deriv-alignment-sandwich-tactic-cert.md:28:on the boundary arm (`rcases regPivotFinEquiv i with ⟨a,b⟩ | ⟨a,b⟩ | ⟨a,b⟩`):
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/deriv-alignment-sandwich-tactic-cert.md:31:Output coord = `(P.toBlocks₁₁ − 1) a b` where `P = reindex (prod (framedParamsReg (r0,0)))`. By the #91
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/deriv-alignment-sandwich-tactic-cert.md:33:image is `X_first` (the injective routing — `regBoundaryToRegGauge_injective`), so `Σ_s δX_s = δX_first`,
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/deriv-alignment-sandwich-tactic-cert.md:34:and `δX_first a b = (the reg coord regPivotFinEquiv.symm (inl (a,b)))` — i.e. `= proj i`. KEY identity:
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/deriv-alignment-sandwich-tactic-cert.md:35:`(framedParamsReg (r0,0)) reads readX_first (r0) a b = regGaugeSlotEquiv (r0,0) ⟨0, inl(inl(a,b))⟩`,
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/deriv-alignment-sandwich-tactic-cert.md:36:and post-def-change `regGaugeSlotEquiv (r0,0) ⟨0,inl(inl(a,b))⟩ = r0 (regPivotFinEquiv.symm (inl(a,b)))`
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/deriv-alignment-sandwich-tactic-cert.md:37:(= `r0 i`) BY CONSTRUCTION (the reg-half routes via regBoundaryToRegGauge ∘ regPivotFinEquiv, so the
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/deriv-alignment-sandwich-tactic-cert.md:46:    -- d(prod (framedParamsReg (r0,0)))|_0 = Σ_s (corner prefix) · δC_s · (corner suffix), and the
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/deriv-alignment-sandwich-tactic-cert.md:49:      HasFDerivAt (fun r0 => (reindex (prod (framedParamsReg (r0,0)))) i j)
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/deriv-alignment-sandwich-tactic-cert.md:54:1. `prod_framedParamsReg_zero` (banked): at r0=0, `prod (framedParamsReg 0) = reindex (fromBlocks 1 0 0 0)`
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/deriv-alignment-sandwich-tactic-cert.md:56:2. The product derivative at 0 (Leibniz, cobuild's `hasStrictFDerivAt_prodAux_entry` VALUE, or a direct
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/deriv-alignment-sandwich-tactic-cert.md:58:   AT r0=0 are the idempotent corner (by `prodAux_framedParamsReg_zero_aux` — the partial products at 0
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/deriv-alignment-sandwich-tactic-cert.md:62:   only for the FIRST. The `fromBlocks_multiply` / `corner_reindex_mul` kernels (banked in
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/deriv-alignment-sandwich-tactic-cert.md:72:      regGaugeSlotEquiv (r0, 0) (regBoundaryToRegGauge (regPivotFinEquiv i))
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/deriv-alignment-sandwich-tactic-cert.md:75:This should be `rfl`/`simp [regGaugeSlotEquiv, regGaugeIdxSplit, regBoundaryToRegGauge, regPivotFinEquiv,
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/deriv-alignment-sandwich-tactic-cert.md:76:Equiv.symm_apply_apply]` ONCE regGaugeIdxSplit's reg-half is `regBoundaryToRegGauge ∘ regPivotFinEquiv`
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/deriv-alignment-sandwich-tactic-cert.md:78:"cancel by symm_apply_apply" — the WHOLE POINT of using ONE shared regPivotFinEquiv for both defs. If it
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/deriv-alignment-sandwich-tactic-cert.md:84:- `prod_framedParamsReg_zero`, `prodAux_framedParamsReg_zero_aux`, `corner_reindex_mul`,
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/deriv-alignment-sandwich-tactic-cert.md:87:- `hasStrictFDerivAt_prodAux_entry` (cobuild @2bf7065) — IF a Leibniz value is wanted; else direct induction.
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/deriv-alignment-sandwich-tactic-cert.md:90:  `regPivotFinEquiv i` and `regBoundaryToRegGauge` REDUCE (the property the opaque Fintype.equivFin lacked).
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/deriv-alignment-sandwich-tactic-cert.md:93:- The `Fin.last` cast in `regBoundaryToRegGauge` (Y_last layer-tag) — the `(Fin.last Lm).succ =
./lean/DLNFibre/DLN/RLCT/Validate/DeepestTelescoping.lean:89:theorem corner_reindex_mul {a b c r : ℕ}
./lean/DLNFibre/DLN/RLCT/Validate/DeepestTelescoping.lean:131:the block-normal corner `reindex (fromBlocks 1 0 0 0)` (`framedParamsReg_zero`), and the corner is
./lean/DLNFibre/DLN/RLCT/Validate/DeepestTelescoping.lean:133:(at width `H 0 × H ⟨k⟩`). Proven by `prodAux_succ` + `framedParamsReg_zero` + `fromBlocks_multiply`
./lean/DLNFibre/DLN/RLCT/Validate/DeepestTelescoping.lean:135:theorem prodAux_framedParamsReg_zero_aux (H : Fin (L + 1) → ℕ) (r : ℕ)
./lean/DLNFibre/DLN/RLCT/Validate/DeepestTelescoping.lean:138:      prodAux H (framedParamsReg H r hr hL 0) k hk
./lean/DLNFibre/DLN/RLCT/Validate/DeepestTelescoping.lean:155:      -- IS the corner at the running widths (`framedParamsReg_zero` then `cases e1; cases e2` collapses the
./lean/DLNFibre/DLN/RLCT/Validate/DeepestTelescoping.lean:157:      -- the Eq.mpr-cast layer = the corner at the running widths (PROBE-proven: `framedParamsReg_zero`
./lean/DLNFibre/DLN/RLCT/Validate/DeepestTelescoping.lean:159:      have hlayer : ((by rw [e1, e2]; exact framedParamsReg H r hr hL 0 ⟨k, hkL⟩ :
./lean/DLNFibre/DLN/RLCT/Validate/DeepestTelescoping.lean:164:        rw [framedParamsReg_zero H r hr hL ⟨k, hkL⟩]; cases e1; cases e2; rfl
./lean/DLNFibre/DLN/RLCT/Validate/DeepestTelescoping.lean:165:      have hstep : prodAux H (framedParamsReg H r hr hL 0) (k + 1) hk
./lean/DLNFibre/DLN/RLCT/Validate/DeepestTelescoping.lean:166:          = prodAux H (framedParamsReg H r hr hL 0) k hk' *
./lean/DLNFibre/DLN/RLCT/Validate/DeepestTelescoping.lean:170:        show prodAux H (framedParamsReg H r hr hL 0) k hk' *
./lean/DLNFibre/DLN/RLCT/Validate/DeepestTelescoping.lean:171:            ((by rw [e1, e2]; exact framedParamsReg H r hr hL 0 ⟨k, hkL⟩ :
./lean/DLNFibre/DLN/RLCT/Validate/DeepestTelescoping.lean:173:        exact congrArg (prodAux H (framedParamsReg H r hr hL 0) k hk' * ·) hlayer
./lean/DLNFibre/DLN/RLCT/Validate/DeepestTelescoping.lean:180:        exact corner_reindex_mul (rThresholdSplit r (H 0) (hr 0))
./lean/DLNFibre/DLN/RLCT/Validate/DeepestTelescoping.lean:184:/-- **The idempotent fold at `0` — `prod` form** (`#123` (1), the `deepestEPivot_base` input). The full
./lean/DLNFibre/DLN/RLCT/Validate/DeepestTelescoping.lean:185:gauge-sliced product at the deepest gauge slot is the block-normal corner: `prod (framedParamsReg 0) =
./lean/DLNFibre/DLN/RLCT/Validate/DeepestTelescoping.lean:188:theorem prodAux_framedParamsReg_zero (H : Fin (L + 1) → ℕ) (r : ℕ)
./lean/DLNFibre/DLN/RLCT/Validate/DeepestTelescoping.lean:190:    prod H (framedParamsReg H r hr hL 0)
./lean/DLNFibre/DLN/RLCT/Validate/DeepestTelescoping.lean:194:  have h := prodAux_framedParamsReg_zero_aux H r hr hL L (Nat.lt_succ_self L) hL
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/deriv-120-wiring-spec.md:1:# #82-deriv wiring-spec — the #120 explicit-pack refactor that makes `deepestEPivot_regSlice_fderiv_id` provable
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/deriv-120-wiring-spec.md:4:obligation of `deepestEPivot_deriv` is
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/deriv-120-wiring-spec.md:6:    deepestEPivot_regSlice_fderiv_id :
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/deriv-120-wiring-spec.md:7:      HasStrictFDerivAt (fun r0 => deepestEPivot H r hr hL (r0, 0))
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/deriv-120-wiring-spec.md:11:`regResidualPack` and `regGaugeIdxSplit`). This spec is the value-preserving transparency refactor that
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/deriv-120-wiring-spec.md:22:    d[r0 ↦ deepestEPivot(r0,0)]|₀  =  regResidualPack-CLM ∘ (idempotent sandwich) ∘ regGaugeSlotRead|_reg
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/deriv-120-wiring-spec.md:39:Then `regResidualPack` packs `(δX_first, δY_last, δZ_first)` back to `Fin nReg` IDENTICALLY ⟹ reg-block
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/deriv-120-wiring-spec.md:45:{⟨0, inr⟩}`, and `regResidualPack` must use the matching enumeration. The interior X_s (s≠0), Y_s
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/deriv-120-wiring-spec.md:55:(`= deepestNReg`-cardinality, the residual-block sum type `regResidualPack` already targets). The
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/deriv-120-wiring-spec.md:58:    regBoundaryToRegGauge : BoundaryPivotIdx H r ↪ RegGaugeIdx H r
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/deriv-120-wiring-spec.md:65:because `regBoundaryToRegGauge` routes each `BoundaryPivotIdx` coord to a DISTINCT `RegGaugeIdx` entry:
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/deriv-120-wiring-spec.md:72:reg image is `X_first`). **Bake `injective_regBoundaryToRegGauge` into the alignment lemma's hypotheses**
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/deriv-120-wiring-spec.md:76:The gauge half is `RegGaugeIdx \ image(regBoundaryToRegGauge)` (the interior/non-boundary X/Y/Z). The
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/deriv-120-wiring-spec.md:80:  the `inl`/reg half is `regBoundaryToRegGauge`'s image, `inr`/gauge half the complement. Concretely:
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/deriv-120-wiring-spec.md:83:- **`regResidualPack`** (`DeepestGaugeConstruction.lean:357`): `Fin nReg ≃ BoundaryPivotIdx` the EXACT
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/deriv-120-wiring-spec.md:84:  INVERSE of the reg-half `Fin`-enumeration used in `regGaugeIdxSplit`. So `regResidualPack` and
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/deriv-120-wiring-spec.md:87:Cleanest Lean realization: define ONE `regPivotFinEquiv : Fin (deepestNReg H r) ≃ BoundaryPivotIdx H r`
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/deriv-120-wiring-spec.md:90:  - `regResidualPack := regPivotFinEquiv`
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/deriv-120-wiring-spec.md:91:  - `regGaugeIdxSplit`'s reg half := `regBoundaryToRegGauge ∘ regPivotFinEquiv`
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/deriv-120-wiring-spec.md:92:so the composite `regResidualPack ∘ (sandwich picks boundary) ∘ (regGaugeIdxSplit|_reg read) = id` holds
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/deriv-120-wiring-spec.md:93:definitionally / by `regPivotFinEquiv.symm_apply_apply`.
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/deriv-120-wiring-spec.md:97:    theorem deepestEPivot_regSlice_fderiv_id … :
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/deriv-120-wiring-spec.md:98:      HasStrictFDerivAt (fun r0 => deepestEPivot H r hr hL (r0,0))
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/deriv-120-wiring-spec.md:103:`d(P)|₀ = Σ_s corner·δC_s·corner`; (b) the idempotent-sandwich collapse (`prodAux_framedParamsReg_zero` +
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/deriv-120-wiring-spec.md:105:interior reads vanish, so `Σ_s δX_s = δX_first`, `δY_L = δY_last`, `δZ_1 = δZ_first`, each `= regPivotFinEquiv`'s
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/deriv-120-wiring-spec.md:106:reg-coord (via the explicit `regBoundaryToRegGauge` enumeration); (d) `regResidualPack = regPivotFinEquiv`
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/deriv-120-wiring-spec.md:108:`ContDiff.hasStrictFDerivAt` on `deepestEPivot_contdiff` (my finding) — only the plain `HasFDerivAt`
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/deriv-120-wiring-spec.md:113:    theorem regResidualPack_regGaugeIdxSplit_reg_cancel … :
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/deriv-120-wiring-spec.md:114:      ∀ i : Fin nReg, regGaugeSlotRead-of (regResidualPack.symm-pivot i) = (the i-th reg basis read)
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/deriv-120-wiring-spec.md:116:(the explicit form depends on the final `regPivotFinEquiv`; pin in the drop-in.)
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/deriv-120-wiring-spec.md:120:`regResidualPack` uses (all in the single-writer `DeepestGaugeConstruction.lean`):
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/deriv-120-wiring-spec.md:121:- `deepestEPivot` def (:382) — `match regResidualPack … with` (value: which block each `Fin nReg` coord
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/deriv-120-wiring-spec.md:122:  reads). CHANGING `regResidualPack`'s value CHANGES `deepestEPivot`'s value → ripples to ALL #80 lemmas
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/deriv-120-wiring-spec.md:123:  that reference `deepestEPivot`'s value (the `hregval` identification in `deepest_loss_squeeze`).
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/deriv-120-wiring-spec.md:124:- `deepestEPivot_contdiff` (:407,412) — `rcases regResidualPack` then per-arm `ContDiff`. Equiv-agnostic
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/deriv-120-wiring-spec.md:126:- `deepestEPivot_base` (:496) — `rcases regResidualPack` then per-arm `fromBlocks 1 0 0 0` residual = 0.
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/deriv-120-wiring-spec.md:132:  is which X/Y/Z) → ripples to `readX/Y/Z` VALUES → `framedParamsReg`/`deepestEPivot` VALUES.
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/deriv-120-wiring-spec.md:139:**The genuine ripple** (the value-changing edges): `deepestEPivot`'s value (via both `regResidualPack` and
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/deriv-120-wiring-spec.md:141:(`(regStraighten q).1 = deepestEPivot (q.1, q.2.2)`). Since the squeeze takes `hregval` as a HYPOTHESIS
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/deriv-120-wiring-spec.md:143:INSULATED IF it uses `deepestEPivot` only through `hregval` + `deepestEPivot_base` (value at 0 = 0, which
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/deriv-120-wiring-spec.md:145:`deepestEPivot`/`regResidualPack` to a CONCRETE per-coordinate value anywhere? If yes → those steps
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/deriv-120-wiring-spec.md:152:1. `BoundaryPivotIdx` + `regPivotFinEquiv` (explicit enumeration) — DeepestSplitReindex.lean, ~40-60 LoC.
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/deriv-120-wiring-spec.md:153:2. `regBoundaryToRegGauge` + the partition `regGaugeIdxSplit` (semantic) — replace :235, ~50-80 LoC,
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/deriv-120-wiring-spec.md:155:3. `regResidualPack := regPivotFinEquiv` — replace :357, re-prove `_contdiff`/`_base` (equiv-agnostic).
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/deriv-120-wiring-spec.md:156:4. `deepestEPivot_regSlice_fderiv_id` — the #91 sandwich + the by-construction cancel, ~150-200 LoC
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/deriv-120-wiring-spec.md:160:**GATING RECOMMENDATION**: this is the exact-index-bijection design — the `regPivotFinEquiv` enumeration
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/deriv-120-wiring-spec.md:161:+ the `regBoundaryToRegGauge` map + the sandwich-collapse correspondence. Getting the enumeration wrong
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/deriv-120-wiring-spec.md:164:`regBoundaryToRegGauge` routing + the per-coordinate `Σ_s δX_s = δX_first` collapse, sympy/sage-checked at
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/deriv-120-wiring-spec.md:170:`regResidualPack` already proves (`DeepestGaugeConstruction.lean:362-371`: `r·r + r·(H_L−r) + (H₀−r)·r =
./lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeConstruction.lean:342:/-! ## The shared pivot map `deepestEPivot` (the PIN1↔PIN2 coupling object)
./lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeConstruction.lean:344:The reg-straightening's reg-output is `deepestEPivot` — the genuine nonlinear straightened residual
./lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeConstruction.lean:345:reading the reg + spectator slots, with `dE(0) = id` (typed `HasStrictFDerivAt deepestEPivot (fst) 0`).
./lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeConstruction.lean:347:concrete value (`(deepestEPivot (split w).reg, (split w).spec)` ≍ the loss residual `E`). So this is
./lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeConstruction.lean:354:`:= regPivotFinEquiv` (the TRANSPARENT `finProdFinEquiv`/`finSumFinEquiv` enumeration in
./lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeConstruction.lean:356:`regBoundaryToRegGauge ∘ regPivotFinEquiv`), so the two cancel and the gauge-zero reg-slice derivative is
./lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeConstruction.lean:358:noncomputable def regResidualPack (H : Fin (L + 1) → ℕ) (r : ℕ)
./lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeConstruction.lean:362:  regPivotFinEquiv H r hr
./lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeConstruction.lean:365:`Fin nReg → ℝ` via `regResidualPack`. `P = ∏ (framedParamsReg p)` reindexed to `r ⊕ M` block shape;
./lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeConstruction.lean:367:noncomputable def deepestEPivot (H : Fin (L + 1) → ℕ) (r : ℕ)
./lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeConstruction.lean:372:      (hr (Fin.last L))) (prod H (framedParamsReg H r hr hL p))
./lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeConstruction.lean:373:    fun i => match regResidualPack H r hr i with
./lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeConstruction.lean:378:theorem deepestEPivot_contdiff (H : Fin (L + 1) → ℕ) (r : ℕ)
./lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeConstruction.lean:380:    ContDiff ℝ (⊤ : ℕ∞) (deepestEPivot H r hr hL) := by
./lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeConstruction.lean:381:  -- Each layer entry of `framedParamsReg` is `ContDiff` (`contDiff_framedParamsReg_entry`), so each
./lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeConstruction.lean:382:  -- entry of `prod H (framedParamsReg ·)` is `ContDiff` (`contDiff_prod_entry`).
./lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeConstruction.lean:384:      ContDiff ℝ (⊤ : ℕ∞) (fun p => framedParamsReg H r hr hL p s a b) :=
./lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeConstruction.lean:385:    contDiff_framedParamsReg_entry H r hr hL
./lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeConstruction.lean:387:      ContDiff ℝ (⊤ : ℕ∞) (fun p => prod H (framedParamsReg H r hr hL p) a b) :=
./lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeConstruction.lean:388:    fun a b => contDiff_prod_entry H (framedParamsReg H r hr hL) hlayer a b
./lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeConstruction.lean:389:  -- `deepestEPivot p` is a `Fin nReg → ℝ` whose each coordinate is (a `prod`-entry, reindexed) − const.
./lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeConstruction.lean:393:  have hcoord : (fun p => deepestEPivot H r hr hL p i)
./lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeConstruction.lean:397:          (prod H (framedParamsReg H r hr hL p))
./lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeConstruction.lean:398:        match regResidualPack H r hr i with
./lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeConstruction.lean:403:  rcases regResidualPack H r hr i with ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩
./lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeConstruction.lean:414:/-- **`deepestEPivot`'s reg-block derivative at `0` is the IDENTITY** (the #91 analytic crux,
./lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeConstruction.lean:415:g213-pin1-de0). Restricted to the regular slice `r ↦ deepestEPivot (r, 0)`, the strict derivative at
./lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeConstruction.lean:419:packaging) is banked. **OBLIGATION:** the `regResidualPack` ↔ `(X_first, Y_last, Z_first)` pivot-coord
./lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeConstruction.lean:421:theorem deepestEPivot_regSlice_fderiv_id (H : Fin (L + 1) → ℕ) (r : ℕ)
./lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeConstruction.lean:424:        deepestEPivot H r hr hL (r0, 0))
./lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeConstruction.lean:426:  -- #120 (deriv-fm): the opaque-pack wall is DISSOLVED — `regResidualPack := regPivotFinEquiv` and
./lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeConstruction.lean:427:  -- `regGaugeIdxSplit`'s reg-half route via `regBoundaryToRegGauge ∘ regPivotFinEquiv` (the SHARED
./lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeConstruction.lean:428:  -- `regPivotFinEquiv`), so the reg-coords ARE the boundary pivots (X_first/Y_last/Z_first) by
./lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeConstruction.lean:434:  -- Per-coordinate: `HasStrictFDerivAt (fun r0 => deepestEPivot (r0,0) i) (proj i) 0`. The #91
./lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeConstruction.lean:435:  -- idempotent-sandwich: `d(prod(framedParamsReg (r0,0)))|_0 = Σ_s corner·δC_s·corner` keeps the
./lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeConstruction.lean:436:  -- surviving boundary block at coord `i`; the SHARED `regPivotFinEquiv` cancel identifies it with `r0 i`.
./lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeConstruction.lean:442:/-- **`deepestEPivot`'s derivative at `0` is the invertible SHEAR** (#120-corrected: NOT `fst`). By #91
./lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeConstruction.lean:446:on `DeepestSplit`, det 1, invertible). Bundled: `∃ D_E (e : ≃L), HasStrictFDerivAt deepestEPivot D_E 0
./lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeConstruction.lean:448:identity `deepestEPivot_regSlice_fderiv_id` (the #91 crux), and the generic shear-CLE
./lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeConstruction.lean:450:theorem deepestEPivot_deriv (H : Fin (L + 1) → ℕ) (r : ℕ)
./lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeConstruction.lean:455:      HasStrictFDerivAt (deepestEPivot H r hr hL) D_E 0 ∧
./lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeConstruction.lean:458:  -- `D_E := fderiv ℝ deepestEPivot 0` (free from `_contdiff`); its reg-block is `id` (the #91 fact),
./lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeConstruction.lean:460:  set D_E := fderiv ℝ (deepestEPivot H r hr hL) 0 with hD_E
./lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeConstruction.lean:461:  have hsd : HasStrictFDerivAt (deepestEPivot H r hr hL) D_E 0 :=
./lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeConstruction.lean:462:    (deepestEPivot_contdiff H r hr hL).hasStrictFDerivAt (by simp)
./lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeConstruction.lean:463:  -- The reg-block: `D_E.comp regInCLM = id`. The reg-slice `r ↦ deepestEPivot (r,0)` has strict
./lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeConstruction.lean:473:      deepestEPivot H r hr hL (r0, 0)) (D_E.comp regInCLM) 0 := by
./lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeConstruction.lean:474:    have hsd0 : HasStrictFDerivAt (deepestEPivot H r hr hL) D_E
./lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeConstruction.lean:481:    have h2 := (deepestEPivot_regSlice_fderiv_id H r hr hL).hasFDerivAt.fderiv
./lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeConstruction.lean:487:theorem deepestEPivot_base (H : Fin (L + 1) → ℕ) (r : ℕ)
./lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeConstruction.lean:489:    deepestEPivot H r hr hL 0 = 0 := by
./lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeConstruction.lean:490:  -- At the origin slot, `∏(framedParamsReg 0)` is the reindexed corner `fromBlocks 1 0 0 0`
./lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeConstruction.lean:491:  -- (`prod_framedParamsReg_zero`); the outer `reindex` in `P` cancels it, so `P = fromBlocks 1 0 0 0`.
./lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeConstruction.lean:495:        (hr (Fin.last L))) (prod H (framedParamsReg H r hr hL 0)))
./lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeConstruction.lean:497:    rw [prodAux_framedParamsReg_zero H r hr hL, ← Matrix.reindex_symm,
./lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeConstruction.lean:500:  simp only [deepestEPivot, hP, Pi.zero_apply]
./lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeConstruction.lean:501:  rcases regResidualPack H r hr i with ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ <;>
./lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeConstruction.lean:512:`deepestEPivot`; `hcoreabs`: `coreAbsorb` is the cutoff Schur shear) — without them the maps are
./lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeConstruction.lean:522:      (regStraighten q).1 = deepestEPivot H r hr hL (q.1, q.2.2))
./lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeConstruction.lean:541:  -- `deepestEPivot` = the E-residual) and `‖Rcore‖² = deepestCoreF (coreAbsorb(split w)).2.1` (`hcoreabs`
./lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeConstruction.lean:598:  -- The reg-output is the shared `deepestEPivot` (the PIN1↔PIN2 coupling object); its three analytic
./lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeConstruction.lean:600:  obtain ⟨D_E, eShear, hEp_deriv, he_shear⟩ := deepestEPivot_deriv H r hr hL
./lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeConstruction.lean:604:      (deepestEPivot H r hr hL) (deepestEPivot_contdiff H r hr hL)
./lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeConstruction.lean:605:      D_E hEp_deriv eShear he_shear (deepestEPivot_base H r hr hL)
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/fold2-deriv-route-prompt.md:5:THE OBLIGATION (`deepestEPivot_deriv`, in DLNFibre.DLN.RLCT):
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/fold2-deriv-route-prompt.md:7:    HasStrictFDerivAt deepestEPivot D_E 0 ∧ (e : DeepestSplit →L DeepestSplit) = regStraightenTotalCLM D_E
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/fold2-deriv-route-prompt.md:11:- deepestEPivot : (Reg × Gauge) → Reg. Concretely:
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/fold2-deriv-route-prompt.md:12:    deepestEPivot p = (fun i => match regResidualPack i with
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/fold2-deriv-route-prompt.md:16:  where P = reindex eIn eOut (prod H (framedParamsReg p))  [reindex/eIn/eOut are FIXED Equivs,
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/fold2-deriv-route-prompt.md:17:  constant in p]. So deepestEPivot is: pack ∘ (block-projections − const) ∘ reindex ∘ (prod ∘ framedParamsReg).
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/fold2-deriv-route-prompt.md:18:  The ONLY p-dependence is in prod H (framedParamsReg p). reindex, toBlocks, −1, pack are all CONSTANT-LINEAR.
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/fold2-deriv-route-prompt.md:19:- framedParamsReg p : each layer s = reindex (fromBlocks (1+X_s) Y_s Z_s 0), where (X_s,Y_s,Z_s) =
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/fold2-deriv-route-prompt.md:28:- hasStrictFDerivAt_prodAux_entry : ∀ entry, ∃ D, HasStrictFDerivAt (fun y => prodAux H (g y) k hk i j) D x
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/fold2-deriv-route-prompt.md:31:- prodAux_framedParamsReg_zero : prod H (framedParamsReg 0) = reindex (corner = fromBlocks 1 0 0 0)
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/fold2-deriv-route-prompt.md:33:- fromBlocks_blockdiag_idem (corner·corner = corner), corner_reindex_mul.
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/fold2-deriv-route-prompt.md:34:- deepestEPivot_contdiff : ContDiff ⊤ deepestEPivot (so HasStrictFDerivAt deepestEPivot (fderiv ℝ … 0) 0 is FREE).
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/fold2-deriv-route-prompt.md:42:THE GAP: my hasStrictFDerivAt_prodAux_entry gives ∃ D (opaque). I need the EXPLICIT D_E (or at least
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/fold2-deriv-route-prompt.md:48:(B) Set D_E := fderiv ℝ deepestEPivot 0 (free from ContDiff), then prove its reg→reg block = id by a
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/fold2-deriv-route-prompt.md:49:    SEPARATE direct computation of fderiv (fun r => deepestEPivot (r, 0)) 0 = id (avoiding the full
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/fold2-deriv-route-prompt.md:52:    an explicitly-constructed N), prove HasStrictFDerivAt deepestEPivot (the reg-component of e) 0 by
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/fold2-deriv-route-prompt.md:53:    showing deepestEPivot agrees to first order with that linear map (via a direct littleo / the
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:23:- `framedParamsReg H r hr hL p : Params H`, each layer = `reindex e.symm e'.symm (fromBlocks (1+X_s) Y_s Z_s 0)` where X_s=readX p s etc (linear in p, =0 at p=0).
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:24:- At p=0 (gauge slot 0): `prodAux_framedParamsReg_zero_aux`: for 1≤k≤L, `prodAux (framedParamsReg 0) k = reindex e0.symm ek.symm (fromBlocks 1 0 0 0)` (the corner).
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:25:- Banked: `hasStrictFDerivAt_prodAux_entry` proves EXISTENCE of a strict derivative D for each entry `fun y => prodAux (g y) k i j` (opaque D, built by Leibniz HasStrictFDerivAt.sum/.mul induction), but NOT the explicit value.
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:26:- `corner_reindex_mul`: corner * corner = corner (idempotent under the chain, reindexed).
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:28:GOAL: the reg-slice `r0 ↦ deepestEPivot (r0,0)` (each output coord is a block entry (P11-1)/P12/P21 of `P=reindex(prod(framedParamsReg(r0,0)))`) has strict derivative `id` at 0. The math: dP|_0 = Σ_s corner·δC_s·corner. corner·δC_s·corner keeps only: (0,0)-block X_s for all s, (0,1)-block Y_s for the LAST layer, (1,0)-block Z_s for the FIRST layer. With gauge=0 the reg-coords route X to first layer, Y to last, Z to first (via regBoundaryToRegGauge∘regPivotFinEquiv shared with regResidualPack=regPivotFinEquiv), so each coord's derivative = the matching r0 projection.
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md:31:(A) Prove a NEW explicit-value Leibniz lemma `prodAux_corner_fderiv`: by induction, the strict derivative of `prodAux(framedParamsReg(r0,0)) k i j` at 0 is `Σ_{s<k} (corner_{0..s})·(δlayer_s)·(corner_{s+1..k})` — but this needs naming the running-corner-prefixes and is heavy.
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/fold2-deriv-route-answer.md:3:1. **B**. Set `D_E := fderiv ℝ deepestEPivot 0`; prove only the reg-slice derivative is `id`; package invertibility by `clmShearEquiv`.  
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/fold2-deriv-route-answer.md:4:   Biggest risk: the reg-slice coordinate simp may hit the `regGaugeIdxSplit`/`regResidualPack` packing wall.
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/fold2-deriv-route-answer.md:19:let E := deepestEPivot H r hr hL
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/fold2-deriv-route-answer.md:23:  (deepestEPivot_contdiff H r hr hL).hasStrictFDerivAt (by simp)
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/fold2-deriv-route-answer.md:44:lemma deepestEPivot_regSlice_hasStrictFDerivAt_id :
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/fold2-deriv-route-answer.md:46:    (fun r0 : Reg => deepestEPivot H r hr hL (r0, 0))
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/fold2-deriv-route-answer.md:50:Prove this coordinatewise by `hasStrictFDerivAt_pi''`. For each packed coordinate, unfold `deepestEPivot`, `framedParamsReg`, `framedLayer`, then use the gauge-zero slice facts for reads:
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/fold2-deriv-route-answer.md:84:      -- packed residual of prod H (framedParamsReg (r0,0))
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/fold2-deriv-route-answer.md:92:lemma fderiv_deepestEPivot_regBlock :
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/fold2-deriv-route-answer.md:95:  have hid := deepestEPivot_regSlice_hasStrictFDerivAt_id H r hr hL
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/fold2-deriv-route-answer.md:113:The wall is `deepestEPivot_regSlice_hasStrictFDerivAt_id`, specifically making `regResidualPack` and `regGaugeIdxSplit` expose that the regular coordinates are exactly `(X_first, Y_last, Z_first)`. Fallback: do A only for the reg-slice, not full `(reg,gauge)`: name a restricted Leibniz derivative for `fun r => prod H (framedParamsReg (r,0))`; collapse it to `id`; still keep `D_E := fderiv` for the full map.
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/fold1-prodaux-zero-statement-card.md:1:# Statement card — #123 FOLD1: the idempotent `prodAux`-at-0 fold + `deepestEPivot_base`
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/fold1-prodaux-zero-statement-card.md:3:> **Claim.** At the origin gauge slot, the framed (T=0) layer product `∏(framedParamsReg 0)` is the
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/fold1-prodaux-zero-statement-card.md:5:> `deepestEPivot 0 = 0`. This is FOLD1 (value) of the #123 `prodAux` fold family — the cast-wall break
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/fold1-prodaux-zero-statement-card.md:6:> that gated `deepestEPivot_base`.
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/fold1-prodaux-zero-statement-card.md:9:>   - `DLNFibre.DLN.RLCT.prodAux_framedParamsReg_zero_aux` and
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/fold1-prodaux-zero-statement-card.md:10:>     `DLNFibre.DLN.RLCT.prodAux_framedParamsReg_zero` (crux2's single-writer
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/fold1-prodaux-zero-statement-card.md:12:>   - `DLNFibre.DLN.RLCT.deepestEPivot_base`
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/fold1-prodaux-zero-statement-card.md:15:> - **Gloss.** Every layer of `framedParamsReg H r hr hL 0` is, at the origin, the block-normal corner
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/fold1-prodaux-zero-statement-card.md:17:>   (`framedParamsReg_zero`). The corner is idempotent under the chain product, so the running product
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/fold1-prodaux-zero-statement-card.md:18:>   through `k ≥ 1` layers is again the corner at width `H 0 × H ⟨k⟩` (`prodAux_framedParamsReg_zero_aux`),
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/fold1-prodaux-zero-statement-card.md:19:>   and at `k = L` this is `∏ = reindex(corner)` (`prodAux_framedParamsReg_zero`). The pivot residual
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/fold1-prodaux-zero-statement-card.md:20:>   `deepestEPivot p` reads the `(P11−I, P12, P21)` blocks of `reindex(∏)` — for `p = 0`, the outer
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/fold1-prodaux-zero-statement-card.md:27:>   matrix-VALUE rewrite of `framedParamsReg_zero` under the fold. TWO independent cracks:
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/fold1-prodaux-zero-statement-card.md:32:>     (the `prodAux 0 = 1` head), `k ≥ 1` → `rw [ih]` + `corner_reindex_mul` (the idempotent
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/fold1-prodaux-zero-statement-card.md:38:>   `prodAux_framedParamsReg_zero_aux`, `prodAux_framedParamsReg_zero`, `deepestEPivot_base` — all
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/fold1-prodaux-zero-statement-card.md:42:>   `prodAux_succ_layer` (the kernel), `corner_reindex_mul` (`submatrix_mul_equiv` + `fromBlocks_multiply`).
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/fold1-prodaux-zero-statement-card.md:45:>   - `deepestEPivot_deriv` (#82): the `HasStrictFDerivAt` Leibniz derivative + shear — analytic, OPEN.
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/sub34-gate-status.md:13:- `prodAux_framedParamsReg_zero_aux` + `prodAux_framedParamsReg_zero` (crux2's file, axiom-clean).
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/sub34-gate-status.md:14:- **`deepestEPivot_base` PROVED** (cobuild, `DeepestGaugeConstruction.lean`, clean-three) — consumes the
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/sub34-gate-status.md:15:  prod-level corollary; `deepestEPivot 0 = 0` via the reindex-cancellation to `fromBlocks 1 0 0 0`.
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/sub34-gate-status.md:19:- **`deepestEPivot_deriv` (FOLD2, #82):** ASSEMBLY COMPLETE @da45d78 — `_deriv` is PROVEN modulo ONE
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/sub34-gate-status.md:20:  named sorry. BANKED clean-three: `hasStrictFDerivAt_prodAux_entry`/`_prod_entry` (the L-fold product
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/sub34-gate-status.md:22:  Codex Route D), `regInCLM` (reg-slice embedding). The packaging closes: `D_E := fderiv ℝ deepestEPivot 0`
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/sub34-gate-status.md:25:  remaining obligation, now fully isolated: `deepestEPivot_regSlice_fderiv_id :
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/sub34-gate-status.md:26:  HasStrictFDerivAt (fun r0 => deepestEPivot (r0,0)) id 0` — the #91 idempotent-sandwich (gauge-zero
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/sub34-gate-status.md:27:  slice → (0,0) X-pivot = reg-input). Named wall (Codex): the `regResidualPack` ↔ `(X_first,Y_last,Z_first)`
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/sub34-gate-status.md:33:  (`hregval : (regStraighten q).1 = deepestEPivot (q.1,q.2.2)`; `hcoreabs : coreAbsorb = deepestCoreAbsorb`);
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/sub34-gate-status.md:61:    clean-three, the `deepestEPivot` gap honestly isolated. Statement card:
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/sub34-gate-status.md:68:## The single remaining gate: the shared `deepestEPivot` form (#115) + PIN 2 (#80)
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/sub34-gate-status.md:70:`deepestEPivot` (def + 3 props `_contdiff`/`_deriv`/`_base`, `DeepestGaugeConstruction.lean:313-331`)
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/sub34-gate-status.md:80:  via `fullProduct_loss_squeeze` + `core_comparability_squeeze`. Needs the concrete `deepestEPivot`
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/sub34-gate-status.md:81:  value (so `(regStraightenOf deepestEPivot (split w)).1 = E`). The telescoping `prod H A = P0·∏C·QL`
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/sub34-gate-status.md:93:## `deepestEPivot` def + infra (BANKED, sorry-free) + the props
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/sub34-gate-status.md:95:- `deepestEPivot` CONCRETE def + `regResidualPack` @20ad514; `framedParamsReg` (T=0) + `_zero` @2f3508e;
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/sub34-gate-status.md:97:  + `contDiff_framedParamsReg_entry` @ecd8d6f.
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/sub34-gate-status.md:98:- **`deepestEPivot_contdiff` PROVED** (sorry-free) @11899a7: `contDiff_pi` over the `Fin nReg` output,
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/sub34-gate-status.md:110:`e` with `(e:→L) = regStraightenTotalCLM D_E`; `deepestEPivot_deriv` bundled `∃ D_E e, … ∧ (e:→L)=…`.
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/sub34-gate-status.md:113:## The remaining `deepestEPivot` props
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/sub34-gate-status.md:115:- **`_base`** (`deepestEPivot 0 = 0`): **DONE** (clean-three) via `prodAux_framedParamsReg_zero` (the
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/sub34-gate-status.md:118:- **`_deriv`** (the bundled shear): the concrete shear `D_E` + `HasStrictFDerivAt deepestEPivot D_E 0`
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/sub34-gate-status.md:137:`dlnLoss_block_squeeze`, the #95-(I) frames, `deepestEPivot_contdiff` — all GREEN on my branch), the
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/sub34-gate-status.md:149:`deepestCoreAbsorb` + PIN 1 `regStraightenOf deepestEPivot` + PIN 2 `deepest_loss_squeeze`. Open
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/sub34-gate-status.md:150:sorries: `deepestEPivot` (def + 3 props, blocked on the layout obstruction) and `deepest_loss_squeeze`
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/sub34-gate-status.md:152:matrix squeeze are banked sorry-free; the gate is the `deepestEPivot` coordinate convention.

codex
The repo already has notes around this exact derivative gate, plus the banked product-at-zero and existence lemmas. I’m narrowing this to the smallest lemma boundary that avoids redoing the whole product derivative.
exec
/bin/bash -lc "sed -n '1,220p' CLAUDE.md" in /home/ubuntu/workspace/deriv-spec
 succeeded in 0ms:
# geometry-of-dln-fibre

AI-assisted math-research + Lean-formalisation harness for **digesting and formalising** the paper
*"Geometry of the fibers of the multiplication map of deep linear neural networks"* (Simon Pepin
Lehalleur & Richárd Rimányi, 2024; `paper-sources/lehalleur-rimanyi-2024-geometry-of-dln-fibre/`).
Orientation is in [`README.md`](README.md); this file is the disposition and the working discipline.
The process harness (disposition + policies + roles + skills + the markdown→Lean pipeline) is ported
from the `ai-research-assistant` harness and is **domain-agnostic** — see [`TEMPLATE.md`](TEMPLATE.md)
to instantiate it for another paper.

## Disposition

The work here is research. Not coding, not ticking off a support ticket, not shipping a product. 
The stance: 
- careful, conscientious, objective as a scientist.
- meticulous in calculation as Euler, bold as Grothendieck. 
- methodical as Sherlock Holmes. Observe before theorising. Distinguish data from interpretation. 
- update like a Bayesian; do not collapse to the mode. 


- **Resist the move-fast-and-ship-it instinct.** Stackable, solid progress is the goal; the trap is
  *visible* progress raced ahead of it — a clean doc or confident headline that travels far while leaving
  holes behind. When you reach for a confident headline, that is the moment to look for the confound. Each
  layer should be solid and hole-free before the next stands on it.
- **Fill the layer — completion is your strength.** *The sea rises inexorably, but not in spikes*
  ([`docs/policies/bedrock.md`](docs/policies/bedrock.md)): within a boundary already staked, close the holes
  — the generality a statement promised, the cases it already claims, fidelity to the definition and the
  underlying spirit it invokes — rather than defer them. Such hardening is high-value, and it is where your
  **comparative advantage** lies: your bottleneck is scoping, taste, and direction, not the patient completion
  of well-scoped work — so do not treat that completion capacity, which is *abundant*, as if it were *scarce*.
  **Just do it!** Don't file it as a "chore" (an *unprobed* difficulty claim, not a defer). Surface to move the
  *boundary* — but an **earned** taste-judgment that a gap is the *right* extension is itself direction:
  **Just Do It** if within reach, else **roadmap** it; only a *bare, unargued* extension waits for the operator.
- **Name results for what they are.** A result's name and statement denote exactly what is proven — no more;
  reaching for an impressive name (or "done") is the visible-progress instinct in disguise. Separate Proved /
  Assumed / Cited / Deferred. See [`docs/policies/precision.md`](docs/policies/precision.md). (Here the
  recurring trap: a `rlct_…`-named result that in fact proves only a *codimension* — the `rlct = ½·codim`
  reading needs the cited analytic bound.)
- **Build to bedrock.** A sorry-free build defeats *technical* slop; it never defeats *conceptual* slop —
  "technically correct but subtly wrong, not The Way." **Bedrock is the rock the rising sea rises over**: build
  the theory so the next result can stand on it without re-opening it. Where short feedback loops fail, **beauty
  is the instrument** — a vacuous, mis-scoped, or overclaiming result is *ugly*, and the ugliness is
  information. The **controller holds this taste and judges against it**; a green build is necessary, never
  sufficient. See [`docs/policies/bedrock.md`](docs/policies/bedrock.md).
- **Caveats live next to claims, not in footnotes.** An assumed hypothesis or a cited interface goes in the
  same paragraph as any claim that depends on it.
- **Write to figure out the truth, not to persuade.** Concise and fact-based.
- **Elementary, precisely.** Build explanations up from precise but simple well-chunked objects, established locally in the
  document. "Elementary" does not mean imprecise or dumbed-down or toy analogies: every step stays
  mathematically precise. Introduce the objects you use before you use them; prefer a chain of small exact
  statements over one dense one. Resist over-naming things to do chunking. Reach for an analogy only when it is exact and load-bearing. See
  [`docs/policies/writing-style.md`](docs/policies/writing-style.md).

## Writing and communication discipline (object-level focus)
In writing or in communication, focus on object-level. Resist meta-level pull. 
Remove authorial self-reassurance: `honestly`, `fundamentally`, `this is the whole point`, `this is loadbearing`, `of course`, `simply`, `just`, and selling phrasing.
The full list and the review function that enforces it are in [`docs/policies/review.md`](docs/policies/review.md).

## How research runs here

- **Expeditions** ([`docs/policies/expedition.md`](docs/policies/expedition.md)) are the unit: a central
  question, a controller delegating to thread teammates (explore / formalisation / infra), reviewers, and a
  synthesis at close. Run on the Agent Teams substrate (`CLAUDE_CODE_EXPERIMENTAL_AGENT_TEAMS=1`); launch with
  cwd = this repo root.
- **Pipeline: markdown → Lean.** Theory develops in markdown (`theory/`, expedition notes). A stable claim is
  formalised in Lean (`lean/`, library `DLNFibre`). The reader-facing digest/expositions live in
  `docs/expositions/`.
  - *Scholium* is a **viewer** (renders these markdown docs with KaTeX + callouts), not an editor; write to its
    conventions in [`docs/policies/scholium-writing-format.md`](docs/policies/scholium-writing-format.md). The
    recurring trap: display math `$$…$$` needs a **blank line before and after**, fences on their own lines
    (indented inside `!!!`/`???` callouts) — packed against text it falls through to markdown and the `_`
    subscripts render as emphasis. A second trap: **fenced code does not render inside a callout** — use an
    indented code block (8-space indent) there; top-level fenced code is fine.
- **Claims** carry kill-conditions; new claims are stress-tested, established/cited results verified against
  source ([`docs/policies/claims.md`](docs/policies/claims.md)).
- **Codex** is the independent second model for strategy and review
  ([`docs/policies/codex-consultation.md`](docs/policies/codex-consultation.md)).

## Team structure

Roles are documented under [`.agent-team/roles/`](.agent-team/roles/):
- `controller` — this lead session: meta-planning, delegation, integration.
- `scout` — explore / reconnaissance threads: map the terrain (Mathlib, the paper, possibility spaces), compute / derive / claims.
- `pen-and-paper` — a specialised `scout`: design-space math adjudicating a truth-value (`witness` / `obstruction` seats), exact algebra, decorrelated Codex; hands a certificate to the formaliser. No Lean.
- `formaliser` — formalisation (tide) threads.
- `reviewer` — controller-spawned independent audit (soundness / fidelity).
- `hardener` — independent principles / taste reviewer (precision, bedrock).

If dispatched into a role, read its role file and agent definition first.

## Branch discipline

- **One remote: `origin = git@github.com:edmund-ukaisi/geometry-of-dln-fibre.git`.** All work lives here.
- **`dev` is the integration branch.** Feature and expedition branches branch off `dev` and PR back into
  `dev`. `master` is the **release** branch — promoted from `dev` deliberately by the operator, never pushed
  to directly.
- Use a **feature branch** for any non-trivial unit of work; you can push here; don't commit to `dev` or `master` directly. One
  expedition runs on one branch (`expedition/<slug>`); PR at close behind signal-and-wait.
- **Pushing feature/expedition branches to `origin` is pre-authorized** (operator standing instruction,
  2026-06-12) — push freely to bank and share work. **Opening/merging PRs and the `dev → master` promotion
  remain operator-gated** (signal-and-wait); the operator performs those. Always confirm the push target is
  `origin`, never a non-`origin` remote.

## Memory

Persistent context lives **in-repo**: this file, the policies in `docs/policies/`, the expedition docs
(`synthesis.md` / statement cards / `thread.md`), `ROADMAP.md`, and `lean/CLAUDE.md`. Save conventions and
decisions there.

**Do NOT write to global Claude memory (`~/.claude/**/memory/`).** It pollutes other workspaces and is
invisible to collaborators reading the repo. This binds the controller **and every teammate** — the harness
may prompt you to save a memory there; do not. If a teammate writes one, the controller deletes it and
re-homes the content in-repo. (Agent-Teams *runtime* state under `~/.claude/teams/` and `~/.claude/tasks/` is
fine — that's the substrate, not persistent context.)

## The destination, plainly

We want, in honest Lean, the paper's results about the **fibres of matrix multiplication** for deep linear
networks:

- the space $\operatorname{Rep}_{\underline d}$ of composable matrix tuples, the multiplication map
  $\operatorname{mult}$, the zero-product / rank-$r$ loci, and the fibres $\operatorname{mult}^{-1}(B)$;
- via the **type-A quiver** translation (orbits ↔ Kostant partitions ↔ rank patterns, Gabriel, orbit-closure
  order, the `Ext` codimension): the codimension $C$ and the number $\theta$ of top-dimensional components,
  in the paper's three forms (Poincaré series, a quadratic integer program, an explicit formula), and the
  surprising **permutation invariance** of $(C,\theta)$;
- the payoff: the real log-canonical threshold of the square-Frobenius loss is $C/2$ — DLNs are "mildly
  singular". The geometric codimension is the new content; the `rlct ≤ ½·codim` direction is **Cited**
  (Aoyagi / Watanabe).

The reusable **engine** (everything before "the payoff") is network-free and lives in `DLNFibre.Core`; the
DLN/RLCT **application** lives in `DLNFibre.DLN`. See [`ROADMAP.md`](ROADMAP.md) for the formalisation ladder.

## Pointers

- [`README.md`](README.md) — orientation, how to launch an expedition, Lean build.
- [`ROADMAP.md`](ROADMAP.md) — the result-map + the Core/DLN formalisation-target ladder.
- [`docs/policies/`](docs/policies/) — expedition, claims, review, precision, bedrock, codex-consultation, statement-cards, writing-style (+ the reader-facing exposition trio).
- [`docs/expositions/`](docs/expositions/) — the curated reader-facing digest (starts with `paper-digest/high-level-overview.md`).
- [`.claude/skills/`](.claude/skills/) — lean-formalisation, local-codex-consult.
- [`lean/CLAUDE.md`](lean/CLAUDE.md) — Lean build + Mathlib conventions; the Core/DLN split.
- [`theory/`](theory/) — markdown theory workspace.
- [`TEMPLATE.md`](TEMPLATE.md) — how to instantiate this harness for a new paper.

exec
/bin/bash -lc "sed -n '1,220p' lean/DLNFibre/DLN/RLCT/Validate/DeepestTelescoping.lean" in /home/ubuntu/workspace/deriv-spec
 succeeded in 0ms:
import DLNFibre.DLN.RLCT.Foundations.Loss
import DLNFibre.DLN.RLCT.Validate.DeepestFramedProduct

/-!
# `DLNFibre.DLN.RLCT.Validate.DeepestTelescoping` — the PIN2 endpoint-frame telescoping

The cast-heavy `prodAux` induction behind PIN2's frame bridge:
`∏C = P₀ · (∏A) · Q_{L-1}` when each layer is framed `C s = P s · A s · Q s` and the interior
interfaces cancel (`Q s · P (s+1) = 1`). Stated with EXISTENTIAL endpoints (cobuild's banked
statement-shape, `@eee22a1`) to dodge the `H 0` vs `H ⟨0,_⟩.castSucc` definitional mismatch.

**STATUS (crux2 2026-06-23): the cast mechanics are DE-RISKED, the induction is the XL-cast — DEFERRED
to a fresh-session-with-Codex (HEq-induction design), per controller's 3-attempt discipline.** Two
findings shape the eventual proof:
- (PROBE 1, BUILDS) the running-width identifications `H ⟨k,hk⟩` and `H (⟨k,hkL⟩.castSucc)` are
  DEFINITIONALLY `rfl` (Fin proof-irrelevance + `castSucc ⟨k,_⟩` reduction). So the index VALUES agree
  freely — the obstacle is purely the elaborator's `HMul` instance synthesis, NOT a real value-mismatch.
- (`prodAux_succ` SHAPE, typechecks) the `k+1` fold IS the running product times the layer transported
  by `Matrix.reindex (finCongr ·) (finCongr ·)` (the explicit form of the def's `rw [e1,e2]`). This is
  the right unfold; its `rfl`-discharge needs an entry-chase through `reindex_apply` vs the def's `Eq.mpr`
  cast — the bridge that wants Codex's design (3-attempt cap hit on the entry-chase).
The `endpoint_telescoping` statement-SHAPE is cobuild's (`@eee22a1`); it typechecks (signature GREEN).
The remaining work is the prefix-fold induction with interface-cancellation in the reindexed types.
-/

open Matrix
namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-- **DE-RISK PROBE 1 (BUILDS `rfl`).** The two running-width identifications are definitionally equal —
the index values agree freely; only `HMul` instance synthesis (not a value-mismatch) is the obstacle. -/
example (H : Fin (L + 1) → ℕ) (k : ℕ) (hk : k + 1 < L + 1) :
    H (⟨k, Nat.lt_of_succ_lt hk⟩ : Fin (L + 1))
      = H ((⟨k, Nat.lt_of_succ_lt_succ hk⟩ : Fin L).castSucc) := rfl

/-- **`prodAux` recursion, reindex-explicit** (statement TYPECHECKS; proof is the deferred entry-chase).
The `k+1` fold is the running product times the `k`-th layer, transported to the running-width type by
`Matrix.reindex (finCongr ·) (finCongr ·)` — the explicit form of the def's `rw [e1,e2]; exact A …`. -/
theorem prodAux_succ (H : Fin (L + 1) → ℕ) (A : Params H) (k : ℕ) (hk : k + 1 < L + 1)
    (e1 : H (⟨k, Nat.lt_of_succ_lt hk⟩ : Fin (L+1))
        = H ((⟨k, Nat.lt_of_succ_lt_succ hk⟩ : Fin L).castSucc))
    (e2 : H (⟨k + 1, hk⟩ : Fin (L+1))
        = H ((⟨k, Nat.lt_of_succ_lt_succ hk⟩ : Fin L).succ)) :
    prodAux H A (k + 1) hk
      = (prodAux H A k (Nat.lt_of_succ_lt hk)) *
          (Matrix.reindex (finCongr e1.symm) (finCongr e2.symm) (A ⟨k, Nat.lt_of_succ_lt_succ hk⟩)) := by
  obtain rfl : e1 = rfl := Subsingleton.elim _ _
  obtain rfl : e2 = rfl := Subsingleton.elim _ _
  rfl

/-- **SHARED step-cast helper** (#123, the family kernel). If the `k`-th layer of `A` is the reindexed
block `Matrix.reindex eC.symm eS.symm M` at the running widths, then the `prodAux` succ-step is the clean
product `prodAux k * reindex eC.symm eS.symm M` — the def's `Eq.mpr` cast is collapsed by the index-level
`cases e1; cases e2` idiom (the `contDiff_prodAux_entry` precedent). All three folds (value / deriv /
telescope) apply this then their own block-composition. `eC, eS` are the threshold splits at `H ⟨k,hk'⟩`,
`H ⟨k+1,hk⟩`. -/
theorem prodAux_succ_layer (H : Fin (L + 1) → ℕ) (A : Params H) (k : ℕ) (hk : k + 1 < L + 1)
    {p q : ℕ} (eC : Fin (H (⟨k, Nat.lt_of_succ_lt hk⟩ : Fin (L+1))) ≃ Fin p ⊕ Fin q)
    {p' q' : ℕ} (eS : Fin (H (⟨k + 1, hk⟩ : Fin (L+1))) ≃ Fin p' ⊕ Fin q')
    (M : Matrix (Fin p ⊕ Fin q) (Fin p' ⊕ Fin q') ℝ)
    (hlayer : A (⟨k, Nat.lt_of_succ_lt_succ hk⟩ : Fin L)
      = (by rw [show (⟨k, Nat.lt_of_succ_lt_succ hk⟩ : Fin L).castSucc
                = (⟨k, Nat.lt_of_succ_lt hk⟩ : Fin (L+1)) from by apply Fin.ext; simp [Fin.castSucc],
              show (⟨k, Nat.lt_of_succ_lt_succ hk⟩ : Fin L).succ
                = (⟨k + 1, hk⟩ : Fin (L+1)) from by apply Fin.ext; simp [Fin.succ]]
            exact Matrix.reindex eC.symm eS.symm M :
          Matrix (Fin (H (⟨k, Nat.lt_of_succ_lt_succ hk⟩ : Fin L).castSucc))
            (Fin (H (⟨k, Nat.lt_of_succ_lt_succ hk⟩ : Fin L).succ)) ℝ)) :
    prodAux H A (k + 1) hk
      = prodAux H A k (Nat.lt_of_succ_lt hk) * Matrix.reindex eC.symm eS.symm M := by
  have hkL : k < L := Nat.lt_of_succ_lt_succ hk
  have hk' : k < L + 1 := Nat.lt_of_succ_lt hk
  have e1 : (⟨k, hk'⟩ : Fin (L + 1)) = (⟨k, hkL⟩ : Fin L).castSucc := by
    apply Fin.ext; simp [Fin.castSucc]
  have e2 : (⟨k + 1, hk⟩ : Fin (L + 1)) = (⟨k, hkL⟩ : Fin L).succ := by
    apply Fin.ext; simp [Fin.succ]
  show prodAux H A k hk' *
      ((by rw [e1, e2]; exact A ⟨k, hkL⟩ :
        Matrix (Fin (H ⟨k, hk'⟩)) (Fin (H ⟨k + 1, hk⟩)) ℝ)) = _
  refine congrArg (prodAux H A k hk' * ·) ?_
  rw [hlayer]; cases e1; cases e2; rfl

/-- **The corner-block idempotent product** (reindex form). The block-normal corner `fromBlocks 1 0 0 0`
is idempotent under the chain product, and reindexing along a shared middle interface `eB` cancels:
`reindex eA.symm eB.symm corner * reindex eB.symm eC.symm corner = reindex eA.symm eC.symm corner`.
Via `reindex_apply` (→ `submatrix`), `submatrix_mul_equiv` (the `eB.symm` interface), `fromBlocks_multiply`
(`[1,0;0,0]·[1,0;0,0] = [1,0;0,0]`). -/
theorem corner_reindex_mul {a b c r : ℕ}
    (eA : Fin a ≃ Fin r ⊕ Fin (a - r)) (eB : Fin b ≃ Fin r ⊕ Fin (b - r))
    (eC : Fin c ≃ Fin r ⊕ Fin (c - r)) :
    (Matrix.reindex eA.symm eB.symm (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℝ) 0 0 0))
        * (Matrix.reindex eB.symm eC.symm (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℝ) 0 0 0))
      = Matrix.reindex eA.symm eC.symm (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℝ) 0 0 0) := by
  simp only [Matrix.reindex_apply, Equiv.symm_symm]
  rw [Matrix.submatrix_mul_equiv (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℝ) 0 0 0)
      (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℝ) 0 0 0) eA eB eC]
  congr 1
  rw [Matrix.fromBlocks_multiply]
  simp

/-- **Reindex distributes over a left endpoint-frame product** (the FOLD3 general-layer kernel). For a
SQUARE row-frame `P : Matrix m m ℝ` and a general layer `A : Matrix m n ℝ`, reindexing the product
`P * A` along `(eC, eS)` factors as `(reindex eC eC P) * (reindex eC eS A)` — the frame `P` rides on the
row-index alone, so its reindex is the diagonal `(eC, eC)` and the shared middle interface `eC.symm`
cancels (`submatrix_mul_equiv`). This is the boundary-frame extraction the `endpoint_telescoping` base
step needs (`reindex (C ⟨0⟩) = (cast P₀) · reindex (A ⟨0⟩)` when `C ⟨0⟩ = P₀ · A ⟨0⟩`). Generic over the
index types — `m, n` any Fintypes, `eC, eS` any reindex equivs. -/
theorem reindex_mul_distrib_left {m n m' n' : Type*} [Fintype m] [Fintype n]
    [Fintype m'] [Fintype n']
    (P : Matrix m m ℝ) (A : Matrix m n ℝ) (eC : m ≃ m') (eS : n ≃ n') :
    Matrix.reindex eC eS (P * A)
      = Matrix.reindex eC eC P * Matrix.reindex eC eS A := by
  simp only [Matrix.reindex_apply, Equiv.symm_symm]
  rw [Matrix.submatrix_mul_equiv P A eC.symm eC.symm eS.symm]

/-- **Reindex distributes over a right endpoint-frame product** (the FOLD3 boundary-`Q` kernel). For a
general layer `A : Matrix m n ℝ` and a SQUARE column-frame `Q : Matrix n n ℝ`, reindexing `A * Q` along
`(eC, eS)` factors as `(reindex eC eS A) * (reindex eS eS Q)` — `Q` rides on the column-index, so the
shared middle interface `eS.symm` cancels. The boundary-right-frame extraction the `endpoint_telescoping`
final step needs (`reindex (C ⟨Lm⟩) = reindex (A ⟨Lm⟩) · (cast Q_Lm)` when `C ⟨Lm⟩ = A ⟨Lm⟩ · Q_Lm`). -/
theorem reindex_mul_distrib_right {m n m' n' : Type*} [Fintype m] [Fintype n]
    [Fintype m'] [Fintype n']
    (A : Matrix m n ℝ) (Q : Matrix n n ℝ) (eC : m ≃ m') (eS : n ≃ n') :
    Matrix.reindex eC eS (A * Q)
      = Matrix.reindex eC eS A * Matrix.reindex eS eS Q := by
  simp only [Matrix.reindex_apply, Equiv.symm_symm]
  rw [Matrix.submatrix_mul_equiv A Q eC.symm eS.symm eS.symm]

/-- **The idempotent fold at `0`** (`prodAux` form, `1 ≤ k`). At the deepest gauge slot, every layer is
the block-normal corner `reindex (fromBlocks 1 0 0 0)` (`framedParamsReg_zero`), and the corner is
idempotent under the chain product, so the running product through `k ≥ 1` layers is again the corner
(at width `H 0 × H ⟨k⟩`). Proven by `prodAux_succ` + `framedParamsReg_zero` + `fromBlocks_multiply`
(the `[1,0;0,0]·[1,0;0,0] = [1,0;0,0]` corner idempotent) + `submatrix_mul_equiv` (interface cancel). -/
theorem prodAux_framedParamsReg_zero_aux (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) :
    ∀ (k : ℕ) (hk : k < L + 1), 1 ≤ k →
      prodAux H (framedParamsReg H r hr hL 0) k hk
        = Matrix.reindex (rThresholdSplit r (H 0) (hr 0)).symm
            (rThresholdSplit r (H ⟨k, hk⟩) (hr ⟨k, hk⟩)).symm
            (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℝ) 0 0 0) := by
  intro k
  induction k with
  | zero => intro _ hk0; exact absurd hk0 (by norm_num)
  | succ k ih =>
      intro hk _
      have hkL : k < L := Nat.lt_of_succ_lt_succ hk
      have hk' : k < L + 1 := Nat.lt_of_succ_lt hk
      -- INDEX-level equalities (the `prodAux` def's own, `Fin.ext`).
      have e1 : (⟨k, hk'⟩ : Fin (L + 1)) = (⟨k, hkL⟩ : Fin L).castSucc := by
        apply Fin.ext; simp [Fin.castSucc]
      have e2 : (⟨k + 1, hk⟩ : Fin (L + 1)) = (⟨k, hkL⟩ : Fin L).succ := by
        apply Fin.ext; simp [Fin.succ]
      -- `prodAux (k+1)` unfolds (def at Loss.lean) to `prodAux k * (Eq.mpr-cast layer)`, and that layer
      -- IS the corner at the running widths (`framedParamsReg_zero` then `cases e1; cases e2` collapses the
      -- two `Eq.mpr` casts to `rfl`). Rewrite the whole succ-step in one `rw [hstep]`.
      -- the Eq.mpr-cast layer = the corner at the running widths (PROBE-proven: `framedParamsReg_zero`
      -- then `cases e1; cases e2` collapses the two `Eq.mpr` casts to `rfl`).
      have hlayer : ((by rw [e1, e2]; exact framedParamsReg H r hr hL 0 ⟨k, hkL⟩ :
            Matrix (Fin (H ⟨k, hk'⟩)) (Fin (H ⟨k + 1, hk⟩)) ℝ))
          = Matrix.reindex (rThresholdSplit r (H ⟨k, hk'⟩) (hr ⟨k, hk'⟩)).symm
              (rThresholdSplit r (H ⟨k + 1, hk⟩) (hr ⟨k + 1, hk⟩)).symm
              (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℝ) 0 0 0) := by
        rw [framedParamsReg_zero H r hr hL ⟨k, hkL⟩]; cases e1; cases e2; rfl
      have hstep : prodAux H (framedParamsReg H r hr hL 0) (k + 1) hk
          = prodAux H (framedParamsReg H r hr hL 0) k hk' *
              Matrix.reindex (rThresholdSplit r (H ⟨k, hk'⟩) (hr ⟨k, hk'⟩)).symm
                (rThresholdSplit r (H ⟨k + 1, hk⟩) (hr ⟨k + 1, hk⟩)).symm
                (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℝ) 0 0 0) := by
        show prodAux H (framedParamsReg H r hr hL 0) k hk' *
            ((by rw [e1, e2]; exact framedParamsReg H r hr hL 0 ⟨k, hkL⟩ :
              Matrix (Fin (H ⟨k, hk'⟩)) (Fin (H ⟨k + 1, hk⟩)) ℝ)) = _
        exact congrArg (prodAux H (framedParamsReg H r hr hL 0) k hk' * ·) hlayer
      rw [hstep]
      rcases Nat.eq_zero_or_pos k with hk0 | hkpos
      · subst hk0
        -- accumulator is `prodAux 0 = 1`; `1 * corner = corner` (`prodAux 0` reduces, then `one_mul`).
        exact Matrix.one_mul _
      · rw [ih hk' hkpos]
        exact corner_reindex_mul (rThresholdSplit r (H 0) (hr 0))
          (rThresholdSplit r (H ⟨k, hk'⟩) (hr ⟨k, hk'⟩))
          (rThresholdSplit r (H ⟨k + 1, hk⟩) (hr ⟨k + 1, hk⟩))

/-- **The idempotent fold at `0` — `prod` form** (`#123` (1), the `deepestEPivot_base` input). The full
gauge-sliced product at the deepest gauge slot is the block-normal corner: `prod (framedParamsReg 0) =
reindex (fromBlocks 1 0 0 0)` (at width `H 0 × H (last)`). `prod = prodAux L`; specialize the `aux`
fold at `k = L` (`1 ≤ L`). The `Fin.last L = ⟨L, _⟩` index form aligns by `Fin.ext`. -/
theorem prodAux_framedParamsReg_zero (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) :
    prod H (framedParamsReg H r hr hL 0)
      = Matrix.reindex (rThresholdSplit r (H 0) (hr 0)).symm
          (rThresholdSplit r (H (Fin.last L)) (hr (Fin.last L))).symm
          (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℝ) 0 0 0) := by
  have h := prodAux_framedParamsReg_zero_aux H r hr hL L (Nat.lt_succ_self L) hL
  rw [prod]
  rw [h]
  -- `⟨L, _⟩ = Fin.last L` (Fin.ext); the two corner index-forms agree.
  congr 1

/-- **PIN2 endpoint-frame telescoping** (existential endpoints, cobuild's banked shape). If every layer
of `C` is the framed layer `C s = P s · A s · Q s` with `P s, Q s` units, and the interior interfaces
collapse (`Q s = I`, `P ⟨s+1⟩ = I` for adjacent layers — the #95-(I) frame-triviality), then the full
products relate by endpoint conjugation: `∃ P₀ Q_L units, ∏C = P₀ · (∏A) · Q_L`. The endpoints are typed
where `prod` lives (`Fin (H 0)`, `Fin (H (last))`), dodging the layer-index cast. -/
theorem endpoint_telescoping (H : Fin (L + 1) → ℕ) (hL : 1 ≤ L) (A C : Params H)
    (P : (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Q : (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ)
    (hframe : ∀ s : Fin L, C s = P s * A s * Q s)
    (hinterface : ∀ (s : Fin L) (hs : (s : ℕ) + 1 < L),
      Q s = (1 : Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ) ∧
        P ⟨(s : ℕ) + 1, by omega⟩ = (1 : Matrix _ _ ℝ)) :
    ∃ (P0 : Matrix (Fin (H 0)) (Fin (H 0)) ℝ)
      (QL : Matrix (Fin (H (Fin.last L))) (Fin (H (Fin.last L))) ℝ),
      prod H C = P0 * prod H A * QL := by
  -- ALL interior frames are identity (`hinterface`). `P s = 1` for `1 ≤ s` (interior-left + boundary), and
  -- `Q s = 1` for `s ≤ Lm-1` (interior-right). So `C 0 = P 0 · A 0`, `C s = A s` (1 ≤ s ≤ Lm-1),
  -- `C Lm = A Lm · Q Lm`. Then `∏C = P 0 · ∏A · Q Lm` (P 0 rides at fixed width `Fin (H 0)`).
  obtain ⟨Lm, rfl⟩ : ∃ Lm, L = Lm + 1 := ⟨L - 1, by omega⟩
  -- `P s = 1` for `1 ≤ (s:ℕ)`: from `hinterface (s-1)`'s `P ((s-1)+1) = P s = 1`.
  have hPid : ∀ s : Fin (Lm + 1), 1 ≤ (s : ℕ) →

exec
/bin/bash -lc "sed -n '300,490p' lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeConstruction.lean" in /home/ubuntu/workspace/deriv-spec
 succeeded in 0ms:
  exact hkey

/-- **The concrete core absorption** (PIN 0, Route A peel). `coreAbsorb = coreShearHomeo` with the
globally-continuous **cutoff Schur shift** `schurCutoffShift` (`= χ·(−Z_s(I+X_s)⁻¹Y_s)`, the honest
Schur correction times the gauge-slot bump; globally continuous via `continuous_of_tsupport`, equal to
the honest correction on the inner ball). The shift slot type is fixed to `deepestNGauge H r` (the
spectator count the assembly uses). Concrete (not existential) so PIN 2's `loss_squeeze` sees the same
definitional map — Codex-confirmed Option A for the PIN0↔PIN2 coupling. -/
noncomputable def deepestCoreAbsorb (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) :
    DeepestSplit H r (deepestNGauge H r) ≃ₜ DeepestSplit H r (deepestNGauge H r) :=
  coreShearHomeo (schurCutoffShift H r hr hL) (continuous_schurCutoffShift H r hr hL)

/-- `deepestCoreAbsorb` is MEASURE-PRESERVING (the det-1 cutoff-Schur shear — `measurePreserving_coreShear`).
Threaded into PIN 1's `regAbsorb_rlct` (`rlctAtOn_regAbsorb_reduce` needs `coreAbsorb` MP for the
`coreAbsorb.symm` conjugation that strips it from the core term). -/
theorem deepestCoreAbsorb_mp (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) :
    MeasurePreserving (deepestCoreAbsorb H r hr hL) volume volume :=
  measurePreserving_coreShear (deepestNReg H r) (flatDim (deepestM H r)) (deepestNGauge H r)
    (schurCutoffShift H r hr hL) (continuous_schurCutoffShift H r hr hL)

/-- **PIN 0 — the core absorption obligations**. `deepestCoreAbsorb` fixes reg+spec+origin and its
`coreAbsorb_rlct` peel holds — all four via the shift-agnostic, MEASURE-PRESERVING
`coreShear_satisfies_coreAbsorb` (`rlctAtOn_comp_homeomorph` on the det-1 shear). The concrete shift
is `schurCutoffShift`, continuous and vanishing at the origin. -/
theorem deepest_coreAbsorb_exists (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) :
    (deepestCoreAbsorb H r hr hL) 0 = 0 ∧
      (∀ q : DeepestSplit H r (deepestNGauge H r), (deepestCoreAbsorb H r hr hL q).1 = q.1) ∧
      (∀ q : DeepestSplit H r (deepestNGauge H r), (deepestCoreAbsorb H r hr hL q).2.2 = q.2.2) ∧
      rlctAtOn
          (fun q : DeepestSplit H r (deepestNGauge H r) =>
            (∑ i, q.1 i ^ 2) + deepestCoreF H r (deepestCoreAbsorb H r hr hL q).2.1)
          (0 : DeepestSplit H r (deepestNGauge H r))
        = rlctAtOn
            (fun q : DeepestSplit H r (deepestNGauge H r) =>
              (∑ i, q.1 i ^ 2) + deepestCoreF H r q.2.1)
            (0 : DeepestSplit H r (deepestNGauge H r)) :=
  coreShear_satisfies_coreAbsorb H r (deepestNGauge H r) (schurCutoffShift H r hr hL)
    (continuous_schurCutoffShift H r hr hL) (schurCutoffShift_zero H r hr hL)

/-! ## The shared pivot map `deepestEPivot` (the PIN1↔PIN2 coupling object)

The reg-straightening's reg-output is `deepestEPivot` — the genuine nonlinear straightened residual
reading the reg + spectator slots, with `dE(0) = id` (typed `HasStrictFDerivAt deepestEPivot (fst) 0`).
PIN 1 needs ONLY that derivative fact (the IFT/peel is form-agnostic); PIN 2's squeeze needs its
concrete value (`(deepestEPivot (split w).reg, (split w).spec)` ≍ the loss residual `E`). So this is
the SHARED coupling object — defined once, consumed by both pins. Its three properties (`ContDiff ⊤`,
`HasStrictFDerivAt (fst) 0`, `0 ↦ 0`) are the residual gauge-geometry obligation: the product-residual
expansion `∏(I+X_s) − I` read off the gauge slots, certified `dE(0) = id` (pp2 #91, general L). -/

/-- The pack equivalence `Fin nReg ≃ (r×r) ⊕ ((r×M_L) ⊕ (M_0×r))` — the THREE regular residual blocks
`(P11−I, P12, P21)` of `∏C` flatten into the `nReg = r(H_0+H_L−r)` reg coordinates. **#120 explicit:**
`:= regPivotFinEquiv` (the TRANSPARENT `finProdFinEquiv`/`finSumFinEquiv` enumeration in
`DeepestSplitReindex`), SHARED with `regGaugeIdxSplit`'s reg-half (which routes via
`regBoundaryToRegGauge ∘ regPivotFinEquiv`), so the two cancel and the gauge-zero reg-slice derivative is
`id` by construction. `_base`/`_contdiff` need only that it is a coordinate bijection (it is, an `Equiv`). -/
noncomputable def regResidualPack (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) :
    Fin (deepestNReg H r)
      ≃ (Fin r × Fin r) ⊕ ((Fin r × Fin (H (Fin.last L) - r)) ⊕ (Fin (H 0 - r) × Fin r)) :=
  regPivotFinEquiv H r hr

/-- The regular residual blocks `(P11 − I, P12, P21)` of the framed product `∏C|_{T=0}`, packed into
`Fin nReg → ℝ` via `regResidualPack`. `P = ∏ (framedParamsReg p)` reindexed to `r ⊕ M` block shape;
`P11 = toBlocks₁₁`, `P12 = toBlocks₁₂`, `P21 = toBlocks₂₁`; the residual is `(P11−1, P12, P21)`. -/
noncomputable def deepestEPivot (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) :
    (Fin (deepestNReg H r) → ℝ) × (Fin (deepestNGauge H r) → ℝ) → (Fin (deepestNReg H r) → ℝ) :=
  fun p =>
    let P := Matrix.reindex (rThresholdSplit r (H 0) (hr 0)) (rThresholdSplit r (H (Fin.last L))
      (hr (Fin.last L))) (prod H (framedParamsReg H r hr hL p))
    fun i => match regResidualPack H r hr i with
      | Sum.inl (a, b) => (P.toBlocks₁₁ - 1) a b
      | Sum.inr (Sum.inl (a, b)) => P.toBlocks₁₂ a b
      | Sum.inr (Sum.inr (a, b)) => P.toBlocks₂₁ a b

theorem deepestEPivot_contdiff (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) :
    ContDiff ℝ (⊤ : ℕ∞) (deepestEPivot H r hr hL) := by
  -- Each layer entry of `framedParamsReg` is `ContDiff` (`contDiff_framedParamsReg_entry`), so each
  -- entry of `prod H (framedParamsReg ·)` is `ContDiff` (`contDiff_prod_entry`).
  have hlayer : ∀ (s : Fin L) (a : Fin (H s.castSucc)) (b : Fin (H s.succ)),
      ContDiff ℝ (⊤ : ℕ∞) (fun p => framedParamsReg H r hr hL p s a b) :=
    contDiff_framedParamsReg_entry H r hr hL
  have hprod : ∀ (a : Fin (H 0)) (b : Fin (H (Fin.last L))),
      ContDiff ℝ (⊤ : ℕ∞) (fun p => prod H (framedParamsReg H r hr hL p) a b) :=
    fun a b => contDiff_prod_entry H (framedParamsReg H r hr hL) hlayer a b
  -- `deepestEPivot p` is a `Fin nReg → ℝ` whose each coordinate is (a `prod`-entry, reindexed) − const.
  refine contDiff_pi.2 (fun i => ?_)
  -- The `i`-coordinate selects one match-arm (independent of `p`); rewrite to that arm, then it is a
  -- reindexed `prod`-entry (minus the constant `1` on the `inl` arm).
  have hcoord : (fun p => deepestEPivot H r hr hL p i)
      = fun p =>
        let P := Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
          (rThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)))
          (prod H (framedParamsReg H r hr hL p))
        match regResidualPack H r hr i with
        | Sum.inl (a, b) => (P.toBlocks₁₁ - 1) a b
        | Sum.inr (Sum.inl (a, b)) => P.toBlocks₁₂ a b
        | Sum.inr (Sum.inr (a, b)) => P.toBlocks₂₁ a b := rfl
  rw [hcoord]
  rcases regResidualPack H r hr i with ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩
  · simp only [Matrix.toBlocks₁₁, Matrix.sub_apply, Matrix.of_apply, Matrix.reindex_apply,
      Matrix.submatrix_apply, Equiv.symm_symm]
    exact (hprod _ _).sub contDiff_const
  · simp only [Matrix.toBlocks₁₂, Matrix.of_apply, Matrix.reindex_apply, Matrix.submatrix_apply,
      Equiv.symm_symm]
    exact hprod _ _
  · simp only [Matrix.toBlocks₂₁, Matrix.of_apply, Matrix.reindex_apply, Matrix.submatrix_apply,
      Equiv.symm_symm]
    exact hprod _ _

/-- **`deepestEPivot`'s reg-block derivative at `0` is the IDENTITY** (the #91 analytic crux,
g213-pin1-de0). Restricted to the regular slice `r ↦ deepestEPivot (r, 0)`, the strict derivative at
`0` is `id` — the idempotent-sandwich `dP|_0 = Σ_s corner·δC_s·corner` with the gauge slot held at `0`
keeps ONLY the `(0,0)`-block `X`-pivot (which equals the reg-input on the pivot coords). This is the
single analytic obligation of `_deriv`; everything else (the product strict-derivative, the shear-CLE
packaging) is banked. **OBLIGATION:** the `regResidualPack` ↔ `(X_first, Y_last, Z_first)` pivot-coord
correspondence at the gauge-zero slice (the #91 transcription / pp2 coordinate cert). -/
theorem deepestEPivot_regSlice_fderiv_id (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) :
    HasStrictFDerivAt (fun r0 : Fin (deepestNReg H r) → ℝ =>
        deepestEPivot H r hr hL (r0, 0))
      (ContinuousLinearMap.id ℝ (Fin (deepestNReg H r) → ℝ)) 0 := by
  -- #120 (deriv-fm): the opaque-pack wall is DISSOLVED — `regResidualPack := regPivotFinEquiv` and
  -- `regGaugeIdxSplit`'s reg-half route via `regBoundaryToRegGauge ∘ regPivotFinEquiv` (the SHARED
  -- `regPivotFinEquiv`), so the reg-coords ARE the boundary pivots (X_first/Y_last/Z_first) by
  -- construction. Coordinate-wise (`hasStrictFDerivAt_pi'`): each output coord `i`'s derivative is the
  -- `i`-th projection.
  rw [show (ContinuousLinearMap.id ℝ (Fin (deepestNReg H r) → ℝ))
      = ContinuousLinearMap.pi (fun i => ContinuousLinearMap.proj i) from by ext x i; rfl]
  refine hasStrictFDerivAt_pi.2 (fun i => ?_)
  -- Per-coordinate: `HasStrictFDerivAt (fun r0 => deepestEPivot (r0,0) i) (proj i) 0`. The #91
  -- idempotent-sandwich: `d(prod(framedParamsReg (r0,0)))|_0 = Σ_s corner·δC_s·corner` keeps the
  -- surviving boundary block at coord `i`; the SHARED `regPivotFinEquiv` cancel identifies it with `r0 i`.
  -- REMAINING ANALYTIC ATOM (the #91 transcription, per deriv-alignment-sandwich-tactic-cert.md): the
  -- per-coordinate product-derivative value + the cancel. Skeleton validated (shape typechecks); the
  -- atom is the patient analytic fill (the Leibniz sandwich VALUE through `prodAux` + the cancel).
  sorry

/-- **`deepestEPivot`'s derivative at `0` is the invertible SHEAR** (#120-corrected: NOT `fst`). By #91
(`d(P−B)|_0 = (Σ_s X_s, Y_L, Z_1)`, idempotent sandwich), the reg-residual's derivative reads the
reg-X + sums the gauge-X's into reg while keeping the gauge free — the unitriangular shear
`D_E = [[I, Σ],[0, I]]` on `reg×gauge → reg` (its total `regStraightenTotalCLM D_E` is `[[I,Σ],[0,I]]`
on `DeepestSplit`, det 1, invertible). Bundled: `∃ D_E (e : ≃L), HasStrictFDerivAt deepestEPivot D_E 0
∧ (e : →L) = regStraightenTotalCLM D_E`. ASSEMBLED from `_contdiff` (→ `D_E := fderiv`), the reg-block
identity `deepestEPivot_regSlice_fderiv_id` (the #91 crux), and the generic shear-CLE
`regStraightenTotalCLM_equiv_of_regBlock_id`. -/
theorem deepestEPivot_deriv (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) :
    ∃ (D_E : ((Fin (deepestNReg H r) → ℝ) × (Fin (deepestNGauge H r) → ℝ)) →L[ℝ]
        (Fin (deepestNReg H r) → ℝ))
      (e : DeepestSplit H r (deepestNGauge H r) ≃L[ℝ] DeepestSplit H r (deepestNGauge H r)),
      HasStrictFDerivAt (deepestEPivot H r hr hL) D_E 0 ∧
      (e : DeepestSplit H r (deepestNGauge H r) →L[ℝ] DeepestSplit H r (deepestNGauge H r))
        = regStraightenTotalCLM D_E := by
  -- `D_E := fderiv ℝ deepestEPivot 0` (free from `_contdiff`); its reg-block is `id` (the #91 fact),
  -- so `regStraightenTotalCLM D_E` is the invertible shear (`regStraightenTotalCLM_equiv_of_regBlock_id`).
  set D_E := fderiv ℝ (deepestEPivot H r hr hL) 0 with hD_E
  have hsd : HasStrictFDerivAt (deepestEPivot H r hr hL) D_E 0 :=
    (deepestEPivot_contdiff H r hr hL).hasStrictFDerivAt (by simp)
  -- The reg-block: `D_E.comp regInCLM = id`. The reg-slice `r ↦ deepestEPivot (r,0)` has strict
  -- derivative `D_E.comp regInCLM` (chain rule) AND `id` (#91), so they agree.
  have hregIn : HasStrictFDerivAt (fun r0 : Fin (deepestNReg H r) → ℝ => ((r0, 0) :
      (Fin (deepestNReg H r) → ℝ) × (Fin (deepestNGauge H r) → ℝ)))
      (regInCLM : (Fin (deepestNReg H r) → ℝ) →L[ℝ]
        (Fin (deepestNReg H r) → ℝ) × (Fin (deepestNGauge H r) → ℝ)) 0 := by
    have := (regInCLM : (Fin (deepestNReg H r) → ℝ) →L[ℝ]
      (Fin (deepestNReg H r) → ℝ) × (Fin (deepestNGauge H r) → ℝ)).hasStrictFDerivAt (x := 0)
    simpa [regInCLM] using this
  have hcomp : HasStrictFDerivAt (fun r0 : Fin (deepestNReg H r) → ℝ =>
      deepestEPivot H r hr hL (r0, 0)) (D_E.comp regInCLM) 0 := by
    have hsd0 : HasStrictFDerivAt (deepestEPivot H r hr hL) D_E
        (((0 : Fin (deepestNReg H r) → ℝ), (0 : Fin (deepestNGauge H r) → ℝ))) := hsd
    exact hsd0.comp (x := (0 : Fin (deepestNReg H r) → ℝ)) hregIn
  have hblock : D_E.comp (regInCLM : (Fin (deepestNReg H r) → ℝ) →L[ℝ]
      (Fin (deepestNReg H r) → ℝ) × (Fin (deepestNGauge H r) → ℝ))
      = ContinuousLinearMap.id ℝ (Fin (deepestNReg H r) → ℝ) := by
    have h1 := hcomp.hasFDerivAt.fderiv
    have h2 := (deepestEPivot_regSlice_fderiv_id H r hr hL).hasFDerivAt.fderiv
    rw [← h1, ← h2]
  obtain ⟨e, he⟩ := regStraightenTotalCLM_equiv_of_regBlock_id (C := Fin (flatDim (deepestM H r)) → ℝ)
    D_E hblock
  exact ⟨D_E, e, hsd, he⟩

theorem deepestEPivot_base (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) :
    deepestEPivot H r hr hL 0 = 0 := by
  -- At the origin slot, `∏(framedParamsReg 0)` is the reindexed corner `fromBlocks 1 0 0 0`

exec
/bin/bash -lc "sed -n '230,340p' lean/DLNFibre/DLN/RLCT/Validate/DeepestFramedProduct.lean" in /home/ubuntu/workspace/deriv-spec
 succeeded in 0ms:
                  Matrix (Fin (H ⟨k, hk'⟩)) (Fin (H ⟨k + 1, hk⟩)) ℝ) m j) := by
        funext x; rfl
      rw [hentry]
      refine ContDiff.sum (fun m _ => ?_)
      refine (ih hk' i m).mul ?_
      -- The cast `⟨k,hk'⟩ = ⟨k,hkL⟩.castSucc` is `Fin.mk` proof-irrelevance (defeq), so the cast layer
      -- entry IS `g x ⟨k,hkL⟩ m j` up to the `eq_mpr/cast` normal form; `ContDiff` by `hg`.
      have := hg ⟨k, hkL⟩
      simp only [e1, e2, eq_mpr_eq_cast, cast_eq] at this ⊢
      exact this _ _

/-- **`ContDiff` of the full layer-product entries** (`contDiff_prodAux_entry` at `k = L`). -/
theorem contDiff_prod_entry {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (H : Fin (L + 1) → ℕ) (g : X → Params H)
    (hg : ∀ (s : Fin L) (i : Fin (H s.castSucc)) (j : Fin (H s.succ)),
      ContDiff ℝ (⊤ : ℕ∞) (fun x => g x s i j))
    (i : Fin (H 0)) (j : Fin (H (Fin.last L))) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => prod H (g x) i j) :=
  contDiff_prodAux_entry H g hg L (Nat.lt_succ_self L) i j

/-- **`HasStrictFDerivAt` of the partial-product ENTRIES** (the `_deriv` infrastructure, entry-wise to
dodge the matrix-norm instance, mirroring `contDiff_prodAux_entry`). If each layer ENTRY has a strict
derivative `g' s i j` at `x`, then each `prodAux` entry has the LEIBNIZ strict derivative
`∑ m, (prodAux k i m) · (layer deriv) + (prodAux k deriv) · (layer i m)` — built by `HasStrictFDerivAt.sum`
of `HasStrictFDerivAt.mul`. The derivative VALUE is the sum-of-products `prodAux'`; the deepest-point
specialization (idempotent sandwich, #91) collapses it to the `(Σ X_s, Y_L, Z_1)` shear. -/
theorem hasStrictFDerivAt_prodAux_entry {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (H : Fin (L + 1) → ℕ) (g : X → Params H) (x : X)
    (g' : ∀ (s : Fin L) (i : Fin (H s.castSucc)) (j : Fin (H s.succ)), X →L[ℝ] ℝ)
    (hg : ∀ (s : Fin L) (i : Fin (H s.castSucc)) (j : Fin (H s.succ)),
      HasStrictFDerivAt (fun y => g y s i j) (g' s i j) x)
    (k : ℕ) (hk : k < L + 1) :
    ∀ (i : Fin (H 0)) (j : Fin (H ⟨k, hk⟩)),
      ∃ D : X →L[ℝ] ℝ, HasStrictFDerivAt (fun y => prodAux H (g y) k hk i j) D x := by
  revert hk
  induction k with
  | zero =>
      intro hk i j
      -- `prodAux 0 = 1`; each entry is constant, derivative `0`.
      refine ⟨0, ?_⟩
      have : (fun y => prodAux H (g y) 0 hk i j)
          = fun _ => (1 : Matrix (Fin (H 0)) (Fin (H 0)) ℝ) i j := rfl
      rw [this]; exact hasStrictFDerivAt_const _ _
  | succ k ih =>
      intro hk i j
      have hk' : k < L + 1 := Nat.lt_of_succ_lt hk
      have hkL : k < L := Nat.lt_of_succ_lt_succ hk
      have e1 : (⟨k, hk'⟩ : Fin (L + 1)) = (⟨k, hkL⟩ : Fin L).castSucc := by
        apply Fin.ext; simp [Fin.castSucc]
      have e2 : (⟨k + 1, hk⟩ : Fin (L + 1)) = (⟨k, hkL⟩ : Fin L).succ := by
        apply Fin.ext; simp [Fin.succ]
      -- `prodAux (k+1) i j = ∑ m, prodAux k i m · (cast layer k) m j`.
      have hentry : (fun y => prodAux H (g y) (k + 1) hk i j)
          = fun y => ∑ m, prodAux H (g y) k hk' i m
              * ((by rw [e1, e2]; exact g y ⟨k, hkL⟩ :
                  Matrix (Fin (H ⟨k, hk'⟩)) (Fin (H ⟨k + 1, hk⟩)) ℝ) m j) := by
        funext y; rfl
      rw [hentry]
      -- Each summand `prodAux k i m * (cast layer) m j` has a strict derivative (product rule).
      -- `HasStrictFDerivAt.sum` over `m`; each summand via `HasStrictFDerivAt.mul` of (ih) and (the
      -- cast-normalised layer entry, `simp [e1,e2,eq_mpr_eq_cast,cast_eq]` to `g · ⟨k,hkL⟩`, then `hg`).
      have hsummand : ∀ m : Fin (H ⟨k, hk'⟩), ∃ D : X →L[ℝ] ℝ,
          HasStrictFDerivAt (fun y => prodAux H (g y) k hk' i m
              * ((by rw [e1, e2]; exact g y ⟨k, hkL⟩ :
                  Matrix (Fin (H ⟨k, hk'⟩)) (Fin (H ⟨k + 1, hk⟩)) ℝ) m j)) D x := by
        intro m
        obtain ⟨Dpre, hDpre⟩ := ih hk' i m
        have hlayer : HasStrictFDerivAt
            (fun y => (by rw [e1, e2]; exact g y ⟨k, hkL⟩ :
                Matrix (Fin (H ⟨k, hk'⟩)) (Fin (H ⟨k + 1, hk⟩)) ℝ) m j)
            (g' ⟨k, hkL⟩ (e1 ▸ m) (e2 ▸ j)) x := by
          have := hg ⟨k, hkL⟩ (e1 ▸ m) (e2 ▸ j)
          simp only [eq_mpr_eq_cast, cast_eq] at this ⊢
          exact this
        exact ⟨_, hDpre.mul hlayer⟩
      choose D hD using hsummand
      exact ⟨∑ m, D m, HasStrictFDerivAt.fun_sum (fun m _ => hD m)⟩

/-- **`HasStrictFDerivAt` of the full layer-product entries** (`hasStrictFDerivAt_prodAux_entry` at
`k = L`): each entry of `fun y => prod H (g y) i j` has a strict derivative at `x`, given each layer
entry does. The `_deriv` input — `deepestEPivot` is a constant-linear post-composition of these. -/
theorem hasStrictFDerivAt_prod_entry {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (H : Fin (L + 1) → ℕ) (g : X → Params H) (x : X)
    (g' : ∀ (s : Fin L) (i : Fin (H s.castSucc)) (j : Fin (H s.succ)), X →L[ℝ] ℝ)
    (hg : ∀ (s : Fin L) (i : Fin (H s.castSucc)) (j : Fin (H s.succ)),
      HasStrictFDerivAt (fun y => g y s i j) (g' s i j) x)
    (i : Fin (H 0)) (j : Fin (H (Fin.last L))) :
    ∃ D : X →L[ℝ] ℝ, HasStrictFDerivAt (fun y => prod H (g y) i j) D x :=
  hasStrictFDerivAt_prodAux_entry H g x g' hg L (Nat.lt_succ_self L) i j

end DLNFibre.DLN.RLCT

exec
/bin/bash -lc "sed -n '1,180p' lean/CLAUDE.md" in /home/ubuntu/workspace/deriv-spec
 succeeded in 0ms:
# Lean conventions (DLNFibre)

## Build
- Fresh shells: `source ~/.elan/env` before any `lake` command.
- Build from this `lean/` directory: `lake build DLNFibre.<Module>`, or `lake build` for the whole library.
- First build on a machine: `lake exe cache get` fetches Mathlib oleans before `lake build`.
- Toolchain: Lean `v4.29.0` (`lean-toolchain`), Mathlib `v4.29.0` (`lakefile.toml`). Matches the `ai-research-assistant` harness one level up, so its v4.29 Mathlib idioms transfer.

## Library shape — engine vs application
- **`DLNFibre.Core.*`** is the network-free **engine** (quiver orbits, Kostant partitions / rank patterns, `Ext` codimension, `(C, θ)`). It **must never import `DLNFibre.DLN`**. The dependency arrows point `DLN → Core → Mathlib`.
- **`DLNFibre.DLN.*`** is the **application** (multiplication-map fibres, the square-Frobenius loss, the RLCT payoff); it depends on `Core`.
- State each result at the specificity its claim needs; lift a piece into shared `Core` API on its **second** use, not in anticipation of one. Good API (characterizations over predicates, weakest hypotheses, name = content) is the `bedrock`/`precision` discipline, not a folder layout.

## Aggregator
- `DLNFibre.lean` is single-writer. Add new module imports at the end; do not reorder existing imports.
- New modules live at `DLNFibre/<Core|DLN>/<Topic>/<File>.lean`; one substantive theorem family per file.

## Sorry gate
- Zero `sorry` / `axiom` / `native_decide` / `#exit` in committed files. Audit with `scripts/sorries` from `lean/` before every commit.
- A `sorry` with a correct statement is a building block; a `sorry` with a wrong statement misleads. Fix wrong statements first.

## Bedrock (the bar above the sorry gate)
A green, sorry-free build is the **floor**: it defeats *technical* slop, never *conceptual* slop —
"technically correct but subtly wrong, not The Way." Build each result as **bedrock**: something the next
theorem stands on without re-opening it. Where there's nothing to check against, **beauty is the guide** — a
vacuous, mis-scoped, or overclaiming theorem is *ugly*. In practice that recurrently means (not exhaustively):
name = content; non-vacuous, with the witness *shown* in-file; the weakest hypotheses that suffice, in usable
form; characterized (an `iff`) over asserted; every *cited*/*assumed* step named (never an `…rlct…`-style
theorem that secretly claims an unproved analytic interface — here the `rlct = ½·codim` reading rests on a
cited bound). The controller judges against this taste and holds precedence — full statement:
[`../docs/policies/bedrock.md`](../docs/policies/bedrock.md).

## Style
- `↦` not `=>` for lambda arrows.
- `decide +kernel`, not `native_decide`. Avoid `@[implemented_by]`, `@[extern]`, `unsafePerformIO`.
- One-line docstrings.
- Name a lemma for what it proves: a kernel/ideal *membership* fact is `…_mem_ker`, not `…_gen` (which reads as an ideal-generation claim).
- Confirm a Mathlib lemma exists before building a proof around it: `scripts/lean-search "..."`, or `rg` over `.lake/packages/mathlib/Mathlib/`.
- Pre-stage uncertain API with `example` blocks that pin lemma names/types; keep them as durable contracts.

## Mathlib gotchas (v4.29 pin)
Toolchain-generic notes that transfer at this pin. Accumulate new, DLN-specific ones here as they are found
(the ReLU programme's proof-specific notes were intentionally not ported — they were about a different theory).

- **`Basis` is `Module.Basis` at the v4.29 pin.** Bare `Basis` is unknown even with full Mathlib imports;
  ascribe `Module.Basis (Fin _) ℝ _` (e.g. from `Pi.basisFun`). Dot-notation (`b.tensorProduct b'`) is
  unaffected. Likely to recur in any `Matrix.rank` / column-span work.
- **`decide +kernel`, never `native_decide`.** Kernel `decide` is axiom-clean; `native_decide` trusts the
  compiler and breaks `#print axioms` hygiene. Kernel-reduction cost is **heartbeat-invisible** (a
  `maxHeartbeats` bump does not speed it), so a heartbeat timeout on a `decide` is not the symptom to chase.
- **Matrix-product identities over `ℤ` by `decide`, then cast.** An `ℝ` matrix-product identity is a
  `Matrix.ext` blow-up (per-entry `simp`, times out at scale). Write the matrices over `ℤ`
  (`DecidableEq` ⟹ `Matrix.mul` decides by kernel reduction, `by decide`), define the `ℝ` ones via
  `· .map (Int.castRingHom ℝ)`, and transfer products with `← Matrix.map_mul` (cast is a ring hom). No `ℝ`
  `Matrix.ext` at all.
- **`Fin`-vector `![…]` + `fin_cases` friction.** `fin_cases i` leaves the index as `⟨k, ⋯⟩` (a `Fin.mk`),
  so `Matrix.cons_val_one`/`_two`/… do not fire on the outer selection. Normalize first with
  `rw [show (⟨k, by omega⟩ : Fin n) = (k : Fin n) from rfl]`, then the `cons_val_*` simp set fires; or prove
  the components as separate `have`s and assemble with `funext i; fin_cases i`.
- **`φ` (U+03C6) as a binder name can hit a lexer reject** (`unexpected token 'φ'; expected identifier`)
  when an editing tool inserts a confusable/variant codepoint. If a `∃ φ …` / `obtain ⟨φ, …⟩` line fails
  to parse despite looking right, rename the binder to ASCII (`phi`) or `ψ`; capital `Φ` (U+03A6) has not
  shown the problem. Cost two build cycles on `NoetherMonicPositioning.lean`.

exec
/bin/bash -lc "sed -n '200,390p' lean/DLNFibre/DLN/RLCT/Validate/DeepestSplitReindex.lean" in /home/ubuntu/workspace/deriv-spec
 succeeded in 0ms:
  have hcard := Fintype.card_congr (roleSplitIdx H r hr)
  rw [Fintype.card_sum] at hcard
  have hfH : Fintype.card (FlatIdx H) = flatDim H := rfl
  have hfM : Fintype.card (FlatIdx (deepestM H r)) = flatDim (deepestM H r) := rfl
  rw [hfH, hfM] at hcard
  have hdim := flatDim_deepest_split H r hr hL
  unfold deepestNGauge
  omega

/-! ## The #120 explicit boundary-pivot packing (deriv-fm, #82-deriv)

The transparent replacement for the opaque `Fintype.equivFin` reg/gauge split: route the reg slot
explicitly onto the boundary generators `(X_first, Y_last, Z_first)`, so the reg-block derivative is `id`
by construction (g213/#91). `regResidualPack` (in `DeepestGaugeConstruction`) and `regGaugeIdxSplit`
(below) both factor through the SAME `regPivotFinEquiv`, so they cancel. -/

/-- **The boundary-pivot index type** — the residual blocks `(P11−I, P12, P21)` surviving the idempotent
sandwich: `(r×r) ⊕ ((r×M_L) ⊕ (M_0×r))`, the sum type `regResidualPack` targets, of card `deepestNReg`. -/
abbrev BoundaryPivotIdx (H : Fin (L + 1) → ℕ) (r : ℕ) : Type :=
  (Fin r × Fin r) ⊕ ((Fin r × Fin (H (Fin.last L) - r)) ⊕ (Fin (H 0 - r) × Fin r))

/-- **The card match** — `card BoundaryPivotIdx = deepestNReg` (the arithmetic `regResidualPack` proves:
`r² + r(H_L−r) + (H_0−r)r = r(H_0+H_L−r)`). -/
theorem card_boundaryPivotIdx (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) :
    Fintype.card (BoundaryPivotIdx H r) = deepestNReg H r := by
  simp only [BoundaryPivotIdx, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
  obtain ⟨a', ha'⟩ := Nat.le.dest (hr 0)
  obtain ⟨b', hb'⟩ := Nat.le.dest (hr (Fin.last L))
  unfold deepestNReg
  rw [← ha', ← hb']
  simp only [Nat.add_sub_cancel_left]
  rw [show r + a' + (r + b') - r = r + (a' + b') by omega]
  ring

/-- **The explicit pivot packing** `Fin (deepestNReg H r) ≃ BoundaryPivotIdx H r` — the TRANSPARENT
`finProdFinEquiv`/`finSumFinEquiv`/`finCongr` enumeration replacing the opaque `Fintype.equivFin`.
Computable (has `_apply` equation lemmas), so the cancellation reduces. -/
noncomputable def regPivotFinEquiv (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) :
    Fin (deepestNReg H r) ≃ BoundaryPivotIdx H r :=
  (finCongr (show deepestNReg H r
      = r * r + (r * (H (Fin.last L) - r) + (H 0 - r) * r) by
        obtain ⟨a', ha'⟩ := Nat.le.dest (hr 0)
        obtain ⟨b', hb'⟩ := Nat.le.dest (hr (Fin.last L))
        unfold deepestNReg
        rw [← ha', ← hb']
        simp only [Nat.add_sub_cancel_left]
        rw [show r + a' + (r + b') - r = r + (a' + b') by omega]
        ring)).trans
    (finSumFinEquiv.symm.trans
      (Equiv.sumCongr finProdFinEquiv.symm
        (finSumFinEquiv.symm.trans
          (Equiv.sumCongr finProdFinEquiv.symm finProdFinEquiv.symm))))

/-- The first layer index `⟨0,_⟩ : Fin L` (`0 < L` from `1 ≤ L`). -/
def firstLayer (hL : 1 ≤ L) : Fin L := ⟨0, by omega⟩

/-- The last layer `⟨L-1,_⟩ : Fin L`; `.succ` is `Fin.last L` (width `H (Fin.last L)`). -/
def lastLayer (hL : 1 ≤ L) : Fin L := ⟨L - 1, by omega⟩

/-- `(lastLayer hL).succ` has the same `H`-width as `Fin.last L` — the Y_last column cast. -/
theorem H_lastLayer_succ (H : Fin (L + 1) → ℕ) (hL : 1 ≤ L) :
    H ((lastLayer hL).succ) = H (Fin.last L) := by
  congr 1; apply Fin.ext; simp [lastLayer, Fin.succ, Fin.last]; omega

/-- **The boundary-generator routing** `BoundaryPivotIdx → RegGaugeIdx` (the reg-half target):
`X_first` ↦ layer-0 (0,0) entry, `Y_last` ↦ last-layer (0,1) entry, `Z_first` ↦ layer-0 (1,0) entry.
INJECTIVE (distinct layer-tag × sum-arm). -/
def regBoundaryToRegGauge (H : Fin (L + 1) → ℕ) (r : ℕ) (hL : 1 ≤ L) :
    BoundaryPivotIdx H r → RegGaugeIdx H r
  | Sum.inl (i, j) => ⟨firstLayer hL, Sum.inl (Sum.inl (i, j))⟩
  | Sum.inr (Sum.inl (i, j)) =>
      ⟨lastLayer hL, Sum.inl (Sum.inr (i, (finCongr (by rw [H_lastLayer_succ H hL])) j))⟩
  | Sum.inr (Sum.inr (i, j)) => ⟨firstLayer hL, Sum.inr (i, j)⟩

/-- A LEFT INVERSE of `regBoundaryToRegGauge` (total on `RegGaugeIdx`, inverting on the image). -/
def regGaugeDecode (H : Fin (L + 1) → ℕ) (r : ℕ) (hL : 1 ≤ L) :
    RegGaugeIdx H r → BoundaryPivotIdx H r
  | ⟨_, Sum.inl (Sum.inl (i, j))⟩ => Sum.inl (i, j)
  | ⟨s, Sum.inl (Sum.inr (i, j))⟩ =>
      if h : H s.succ - r = H (Fin.last L) - r then Sum.inr (Sum.inl (i, (finCongr h) j))
      else Sum.inl (i, i)
  | ⟨s, Sum.inr (i, j)⟩ =>
      if h : H s.castSucc - r = H 0 - r then Sum.inr (Sum.inr ((finCongr h) i, j))
      else Sum.inl (j, j)

/-- **`regBoundaryToRegGauge` is INJECTIVE** (the no-collapse fact) — via the left inverse `regGaugeDecode`
(`decode ∘ route = id`, per arm: X reads back, Y/Z fire their `dif` and the `finCongr` round-trip
collapses). The reg-half read is injective, so the `Σ_s δX_s` sandwich keeps `X_first` alone. -/
theorem regBoundaryToRegGauge_injective (H : Fin (L + 1) → ℕ) (r : ℕ) (hL : 1 ≤ L) :
    Function.Injective (regBoundaryToRegGauge H r hL) := by
  have hY : H (lastLayer hL).succ - r = H (Fin.last L) - r := by rw [H_lastLayer_succ H hL]
  have hZ : H ((firstLayer hL).castSucc) - r = H 0 - r := by
    have hc : (firstLayer hL).castSucc = (0 : Fin (L + 1)) := by
      apply Fin.ext; simp [firstLayer, Fin.castSucc, Fin.castAdd, Fin.castLE]
    rw [hc]
  refine Function.LeftInverse.injective (g := regGaugeDecode H r hL) (fun b => ?_)
  rcases b with ⟨i, j⟩ | ⟨i, j⟩ | ⟨i, j⟩
  · rfl
  · rw [regBoundaryToRegGauge, regGaugeDecode, dif_pos hY]
    exact congrArg (fun x => Sum.inr (Sum.inl (i, x))) (Fin.ext (by simp [finCongr_apply]))
  · rw [regBoundaryToRegGauge, regGaugeDecode, dif_pos hZ]
    exact congrArg (fun x => Sum.inr (Sum.inr (x, j))) (Fin.ext (by simp [finCongr_apply]))

/-- **The role-respecting `Fin`-index equivalence** (the precision-pin core): `Fin (flatDim H) ≃
Fin nReg ⊕ (Fin (flatDim (deepestM H r)) ⊕ Fin nGauge)`, where the MIDDLE summand is the reduced `T`-core
(`= FlatIdx (deepestM)`) and the outer/right are the reg/gauge entries — slots BY ROLE, NOT arbitrary.
Built from `roleSplitIdx` (the role split) + `Fintype.equivFin` on each summand + `card_regGaugeIdx`
(reg-gauge count) + `finSumFinEquiv` (the reg/gauge `Fin`-split) + `sumAssoc`. -/
noncomputable def deepestRoleIndexEquiv (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) :
    Fin (flatDim H)
      ≃ Fin (deepestNReg H r) ⊕ (Fin (flatDim (deepestM H r)) ⊕ Fin (deepestNGauge H r)) := by
  -- `Fin (flatDim H) ≃ FlatIdx H ≃ RegGaugeIdx ⊕ FlatIdx (deepestM)`.
  refine (Fintype.equivFin (FlatIdx H)).symm.trans ((roleSplitIdx H r hr).trans ?_)
  -- RegGaugeIdx ≃ Fin nReg ⊕ Fin nGauge; FlatIdx (deepestM) ≃ Fin (flatDim M).
  have eReg : RegGaugeIdx H r ≃ Fin (deepestNReg H r) ⊕ Fin (deepestNGauge H r) :=
    (Fintype.equivFin (RegGaugeIdx H r)).trans
      ((finCongr (card_regGaugeIdx H r hr hL)).trans finSumFinEquiv.symm)
  have eCore : FlatIdx (deepestM H r) ≃ Fin (flatDim (deepestM H r)) :=
    Fintype.equivFin (FlatIdx (deepestM H r))
  refine (Equiv.sumCongr eReg eCore).trans ?_
  -- (Fin nReg ⊕ Fin nGauge) ⊕ Fin (flatDim M) ≃ Fin nReg ⊕ (Fin (flatDim M) ⊕ Fin nGauge).
  refine (Equiv.sumAssoc _ _ _).trans (Equiv.sumCongr (Equiv.refl _) (Equiv.sumComm _ _))

/-- The boundary-generator EMBEDDING `BoundaryPivotIdx ↪ RegGaugeIdx` (from the routing + its injectivity).
The reg slot's image inside `RegGaugeIdx`. -/
def regBoundaryEmbed (H : Fin (L + 1) → ℕ) (r : ℕ) (hL : 1 ≤ L) :
    BoundaryPivotIdx H r ↪ RegGaugeIdx H r :=
  ⟨regBoundaryToRegGauge H r hL, regBoundaryToRegGauge_injective H r hL⟩

/-- The complement of the boundary image has `Nat.card` = `deepestNGauge` — `card RegGaugeIdx −
card BoundaryPivotIdx = (nReg + nGauge) − nReg = nGauge`. Stated with `Nat.card` to avoid a
statement-level `Fintype ↥…ᶜ` synth; the `Fintype` instances are produced locally via `Fintype.ofFinite`. -/
theorem card_compl_regBoundaryEmbed (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) :
    Nat.card (↥(Set.range (regBoundaryEmbed H r hL))ᶜ) = deepestNGauge H r := by
  classical
  haveI : Fintype (↥(Set.range (regBoundaryEmbed H r hL))) := Fintype.ofFinite _
  haveI : Fintype (↥(Set.range (regBoundaryEmbed H r hL))ᶜ) := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card]
  -- `range(embed) ≃ BoundaryPivotIdx` (ofInjective), so `card (range) = card BoundaryPivotIdx = nReg`.
  have hrange : Fintype.card (↥(Set.range (regBoundaryEmbed H r hL)))
      = Fintype.card (BoundaryPivotIdx H r) :=
    (Fintype.card_congr (Equiv.ofInjective _ (regBoundaryEmbed H r hL).injective)).symm
  -- `card (range) + card (rangeᶜ) = card RegGaugeIdx` via `sumCompl`.
  have htot : Fintype.card (↥(Set.range (regBoundaryEmbed H r hL)))
      + Fintype.card (↥(Set.range (regBoundaryEmbed H r hL))ᶜ) = Fintype.card (RegGaugeIdx H r) := by
    rw [← Fintype.card_sum]
    exact Fintype.card_congr (Equiv.Set.sumCompl _)
  rw [hrange, card_boundaryPivotIdx H r hr, card_regGaugeIdx H r hr hL] at htot
  omega

/-- **The reg-gauge index split** (the `eReg` of `deepestRoleIndexEquiv`, named for reuse):
`RegGaugeIdx H r ≃ Fin (deepestNReg H r) ⊕ Fin (deepestNGauge H r)` — the #120 EXPLICIT split: the
`Fin nReg` (reg) half routes onto the boundary generators via `regBoundaryToRegGauge ∘ regPivotFinEquiv`
(`regBoundaryEmbed`'s image, `≃ BoundaryPivotIdx ≃ Fin nReg`); the `Fin nGauge` (gauge) half is the
complement (its enumeration opaque — only the REG half needs the boundary alignment). So `regResidualPack
:= regPivotFinEquiv` and this split's reg-half SHARE `regPivotFinEquiv`, hence cancel (reg-block = id). -/
noncomputable def regGaugeIdxSplit (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) :
    RegGaugeIdx H r ≃ Fin (deepestNReg H r) ⊕ Fin (deepestNGauge H r) := by
  classical
  haveI : Fintype (↥(Set.range (regBoundaryEmbed H r hL))ᶜ) := Fintype.ofFinite _
  -- `RegGaugeIdx ≃ range(embed) ⊕ range(embed)ᶜ` (sumCompl), reg-half `≃ BoundaryPivotIdx ≃ Fin nReg`
  -- (the SHARED `regPivotFinEquiv`), gauge-half `≃ Fin nGauge` (opaque enum on the complement).
  refine (Equiv.Set.sumCompl (Set.range (regBoundaryEmbed H r hL))).symm.trans ?_
  refine Equiv.sumCongr ?_ ?_
  · exact (Equiv.ofInjective _ (regBoundaryEmbed H r hL).injective).symm.trans
      (regPivotFinEquiv H r hr).symm
  · refine (Fintype.equivFin _).trans (finCongr ?_)
    have := card_compl_regBoundaryEmbed H r hr hL
    rwa [Nat.card_eq_fintype_card] at this

/-- **The reg-gauge SLOT bridge** (crux2 #78, for cobuild-sub34's `gaugeDecode` reshape). The split's
two opaque function-slots recombine to the LEGIBLE per-layer `RegGaugeIdx` coordinate function:
`(Fin nReg → ℝ) × (Fin nGauge → ℝ) ≃ₜ (RegGaugeIdx H r → ℝ)`. The producer reads off the per-layer
`X_s/Y_s/Z_s` matrix blocks from `RegGaugeIdx` (the per-layer `Σ`), so this bridge is the stepping
stone from the split's `Fin nReg ⊕ Fin nGauge` slots to that legible Sigma BEFORE the matrix-block
reshape. `(Homeomorph.sumPiEquivProdPi).symm` (joins the two slots into `Fin nReg ⊕ Fin nGauge → ℝ`)
then `(Homeomorph.piCongrLeft regGaugeIdxSplit).symm` (relabels along the index split). -/
noncomputable def regGaugeSlotEquiv (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) :
    ((Fin (deepestNReg H r) → ℝ) × (Fin (deepestNGauge H r) → ℝ)) ≃ₜ (RegGaugeIdx H r → ℝ) :=
  (Homeomorph.sumPiEquivProdPi (Fin (deepestNReg H r)) (Fin (deepestNGauge H r))
      (fun _ => ℝ)).symm.trans
    (Homeomorph.piCongrLeft (Y := fun _ => ℝ) (regGaugeIdxSplit H r hr hL)).symm

/-- **Obligation (i) — the gauge-slice MP reindex exists** (the `split` field of `DeepestGaugeChart`).
At the deepest point, a measure-preserving homeomorphism

exec
/bin/bash -lc "sed -n '1,190p' lean/DLNFibre/DLN/RLCT/Validate/DeepestFramedProduct.lean" in /home/ubuntu/workspace/deriv-spec
 succeeded in 0ms:
import DLNFibre.DLN.RLCT.Validate.DeepestSchurShift

/-!
# `DLNFibre.DLN.RLCT.Validate.DeepestFramedProduct` — the gauge-sliced framed product `∏C` (#44c)

The shared concrete object both PIN 1 (`Ereg`, the regular residual) and PIN 2 (`loss_squeeze`, the
frame bridge) consume: the **framed product** `∏C_s`, where each layer
`C_s = fromBlocks (1 + X_s) Y_s Z_s T_s` is the gauge-sliced normal-form deviation (the `block_elimination`
frame puts `w0` at `blockdiag[I_r,0]`; the deviation reads the gauge blocks `(X_s, Y_s, Z_s)` off the
reg+spec slots via `gaugeSlotRead`/`regGaugeSlotEquiv` and the reduced `T_s` off the core slot).

Per the #92 producer contract: `∏C` is the CLEAN product of the per-layer normal forms (the interior
`block_elimination` frames are trivial — #77 (iii), interior layers already block-normal — so the
per-layer framing telescopes; only the two boundary frames carry units, absorbed by the endpoint
conjugation `conjugation_frobenius_comparable`). The framed product is `prod H C` for the reconstructed
gauge-sliced tuple `C : Params H` — no new fold; `prod`/`prodAux` are reused.

## Status

SCAFFOLD (decision-independent piece): the per-layer framed reconstruction `framedLayer`
(`fromBlocks` reindexed to a `Params H` layer via `rThresholdSplit`) + the framed tuple `framedParams`.
The `∏C` residual (`Ereg`) extraction + the `dlnLoss = ‖∏C − D‖²` bridge are the coupled pieces
(gated on the #77 (iii) decl-confirm + the `Ereg = E_pivot` (B)-ruling); built once confirmed.
-/

open Matrix
open scoped BigOperators
namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-! ## `ContDiff` of the gauge read (the `regGaugeSlotEquiv` linearity, for `_contdiff`)

`regGaugeSlotEquiv` (crux2 #78) is packaged as a `Homeomorph` (coordinate relabels), so its linearity is
not exposed — but the SAME relabels have `ContinuousLinearEquiv` forms in Mathlib v4.29
(`ContinuousLinearEquiv.{sumPiEquivProdPi, piCongrLeft}`), whose underlying `Homeomorph` IS the one
`regGaugeSlotEquiv` uses (`__ := Homeomorph.…`). So a CLE mirror `regGaugeSlotCLE` coerces to the SAME
function (defeq), giving `ContDiff` of `regGaugeSlotEquiv` (hence of the `readX/Y/Z` entries) via
`ContinuousLinearEquiv.contDiff`. This is a fact ABOUT crux2's def, not a change to it. -/

/-- The `ContinuousLinearEquiv` mirror of `regGaugeSlotEquiv` (same underlying Homeomorph/function). -/
noncomputable def regGaugeSlotCLE (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) :
    ((Fin (deepestNReg H r) → ℝ) × (Fin (deepestNGauge H r) → ℝ)) ≃L[ℝ] (RegGaugeIdx H r → ℝ) :=
  (ContinuousLinearEquiv.sumPiEquivProdPi ℝ (Fin (deepestNReg H r)) (Fin (deepestNGauge H r))
      (fun _ => ℝ)).symm.trans
    (ContinuousLinearEquiv.piCongrLeft ℝ (fun _ => ℝ) (regGaugeIdxSplit H r hr hL)).symm

/-- `regGaugeSlotCLE` and `regGaugeSlotEquiv` coerce to the SAME function (the CLE and Homeomorph share
the underlying relabel). -/
theorem regGaugeSlotCLE_coe (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) :
    (regGaugeSlotCLE H r hr hL : _ → _) = regGaugeSlotEquiv H r hr hL := rfl

/-- The gauge read `regGaugeSlotEquiv` is `ContDiff ⊤` (it is the CLE `regGaugeSlotCLE`). -/
theorem contDiff_regGaugeSlotEquiv (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p => regGaugeSlotEquiv H r hr hL p) := by
  rw [← regGaugeSlotCLE_coe H r hr hL]
  exact (regGaugeSlotCLE H r hr hL).contDiff

/-- Each `readX` entry is `ContDiff ⊤` (a coordinate of the `ContDiff` gauge read). -/
theorem contDiff_readX_entry (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (s : Fin L) (i j : Fin r) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p => readX H r hr hL p s i j) := by
  simp only [readX, Matrix.of_apply]
  exact ContDiff.comp (contDiff_apply (𝕜 := ℝ) (E := ℝ) _) (contDiff_regGaugeSlotEquiv H r hr hL)

/-- Each `readY` entry is `ContDiff ⊤`. -/
theorem contDiff_readY_entry (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (s : Fin L) (i : Fin r)
    (j : Fin (H s.succ - r)) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p => readY H r hr hL p s i j) := by
  simp only [readY, Matrix.of_apply]
  exact ContDiff.comp (contDiff_apply (𝕜 := ℝ) (E := ℝ) _) (contDiff_regGaugeSlotEquiv H r hr hL)

/-- Each `readZ` entry is `ContDiff ⊤`. -/
theorem contDiff_readZ_entry (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (s : Fin L) (i : Fin (H s.castSucc - r))
    (j : Fin r) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p => readZ H r hr hL p s i j) := by
  simp only [readZ, Matrix.of_apply]
  exact ContDiff.comp (contDiff_apply (𝕜 := ℝ) (E := ℝ) _) (contDiff_regGaugeSlotEquiv H r hr hL)

/-- **The per-layer framed normal-form matrix** `C_s = fromBlocks (1 + X_s) Y_s Z_s T_s`, reindexed
from the block split `Fin r ⊕ Fin (H_s − r)` to the layer dimension `Fin (H_s)` (via `rThresholdSplit`),
so it types as a `Params H` layer `Matrix (Fin (H s.castSucc)) (Fin (H s.succ)) ℝ`. The gauge blocks
`(X_s, Y_s, Z_s)` are the regular/spectator gauge entries (off `gaugeSlotRead`); `T_s` is the reduced
core block. -/
noncomputable def framedLayer (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (s : Fin L)
    (X : Matrix (Fin r) (Fin r) ℝ) (Y : Matrix (Fin r) (Fin (H s.succ - r)) ℝ)
    (Z : Matrix (Fin (H s.castSucc - r)) (Fin r) ℝ)
    (T : Matrix (Fin (H s.castSucc - r)) (Fin (H s.succ - r)) ℝ) :
    Matrix (Fin (H s.castSucc)) (Fin (H s.succ)) ℝ :=
  Matrix.reindex (rThresholdSplit r (H s.castSucc) (hr s.castSucc)).symm
    (rThresholdSplit r (H s.succ) (hr s.succ)).symm
    (Matrix.fromBlocks (1 + X) Y Z T)

/-- **The framed parameter tuple** `C : Params H` reconstructed from a `DeepestSplit` point: each layer
is `framedLayer` of the gauge blocks `(X_s, Y_s, Z_s)` (read off the reg+spectator slot via
`readX/readY/readZ`) and the reduced core `T_s` (read off the core slot via `paramsEquivFlat (deepestM)`).
The framed product `∏C = prod H (framedParams q)` is the shared object; `dlnLoss = ‖∏A − B‖²` relates to
`‖∏C − D‖²` through the endpoint conjugation (the #77 (iii) telescoping). Decision-independent (the
product `∏C` is well-defined regardless of (iii)/(B); those affect how it relates to `dlnLoss`/`Ereg`). -/
noncomputable def framedParams (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (q : DeepestSplit H r (deepestNGauge H r)) : Params H :=
  fun s =>
    framedLayer H r hr s
      (readX H r hr hL (q.1, q.2.2) s) (readY H r hr hL (q.1, q.2.2) s)
      (readZ H r hr hL (q.1, q.2.2) s)
      ((paramsEquivFlat (deepestM H r)).symm q.2.1 s)

/-- **The `T = 0` framed reconstruction** (the `deepestEPivot` reconstruction half). Reconstructs the
gauge-sliced layer tuple from the `(reg, gauge)` slots ALONE, with the reduced core block `T_s := 0`
(the core is `coreAbsorb`'s domain — `deepestEPivot` is the regular residual of `∏C|_{T=0}`, the
core-INDEPENDENT pivot part, per the #115/g222 cert). Each layer is `framedLayer` of the read blocks
`(X_s, Y_s, Z_s)` with the `(1,1)` block zeroed. Layout-independent: it does not depend on the final
`Fin nReg` pack convention (the open obstruction), only on the gauge read `readX/Y/Z`. -/
noncomputable def framedParamsReg (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (p : (Fin (deepestNReg H r) → ℝ) × (Fin (deepestNGauge H r) → ℝ)) : Params H :=
  fun s =>
    framedLayer H r hr s
      (readX H r hr hL p s) (readY H r hr hL p s) (readZ H r hr hL p s)
      (0 : Matrix (Fin (H s.castSucc - r)) (Fin (H s.succ - r)) ℝ)

/-- At the origin gauge slot, `framedParamsReg` is the **block-normal identity chain**: every layer is
`framedLayer 0 0 0 0 = reindex (fromBlocks 1 0 0 0)` (the deepest value `blockdiag[I_r, 0]`). The base
fact for `deepestEPivot`'s `_base` (the residual of `∏ blockdiag[I_r,0]` is `0`). -/
theorem framedParamsReg_zero (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (s : Fin L) :
    framedParamsReg H r hr hL 0 s
      = Matrix.reindex (rThresholdSplit r (H s.castSucc) (hr s.castSucc)).symm
          (rThresholdSplit r (H s.succ) (hr s.succ)).symm
          (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℝ) 0 0 0) := by
  simp only [framedParamsReg, framedLayer, readX_zero H r hr hL s, readY_zero H r hr hL s,
    readZ_zero H r hr hL s, add_zero]

/-- Each `framedParamsReg` layer ENTRY is `ContDiff ⊤` in the `(reg, gauge)` slots: the entry is a
`fromBlocks (1+X) Y Z 0` block entry (reindexed), i.e. `1+readX` / `readY` / `readZ` / `0`, each
`ContDiff` (the read entries + `const`). The `_contdiff` layer input to `contDiff_prod_entry`. -/
theorem contDiff_framedParamsReg_entry (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (s : Fin L)
    (i : Fin (H s.castSucc)) (j : Fin (H s.succ)) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p => framedParamsReg H r hr hL p s i j) := by
  -- The entry is `(fromBlocks (1+X) Y Z 0) (e₁.symm i) (e₂.symm j)`; case-split on the sum indices.
  have hentry : (fun p => framedParamsReg H r hr hL p s i j)
      = fun p => Matrix.fromBlocks (1 + readX H r hr hL p s) (readY H r hr hL p s)
          (readZ H r hr hL p s) (0 : Matrix (Fin (H s.castSucc - r)) (Fin (H s.succ - r)) ℝ)
          ((rThresholdSplit r (H s.castSucc) (hr s.castSucc)) i)
          ((rThresholdSplit r (H s.succ) (hr s.succ)) j) := by
    funext p
    simp only [framedParamsReg, framedLayer, Matrix.reindex_apply, Matrix.submatrix_apply,
      Equiv.symm_symm]
  rw [hentry]
  rcases (rThresholdSplit r (H s.castSucc) (hr s.castSucc)) i with a | a <;>
    rcases (rThresholdSplit r (H s.succ) (hr s.succ)) j with b | b <;>
    simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂, Matrix.add_apply, Matrix.one_apply, Matrix.zero_apply]
  · -- (1 + X) entry: `(if a = b then 1 else 0) + readX … a b` — the `if` is a constant in `p`.
    exact contDiff_const.add (contDiff_readX_entry H r hr hL s a b)
  · exact contDiff_readY_entry H r hr hL s a b
  · exact contDiff_readZ_entry H r hr hL s a b
  · exact contDiff_const

/-! ## PIN 2 frame bridge — the telescoping (#80, next chunk)

The geometric bridge `dlnLoss H B (paramsSymm w) ≍ ‖∏(framed C) − D‖²` reduces to: the **endpoint-frame
telescoping** `prod H A = P_0⁻¹ · (prod H C) · Q_{L-1}⁻¹` (under #95-(I): interior frames `= I` via
`deepestPoint_interior_eq_corM`, boundary-inner `= I` via `deepestPoint_layer{0,Last}_*_vanish`, so the
interior interfaces `Q_s⁻¹·P_{s+1}⁻¹ = 1` collapse) → `conjugation_frobenius_comparable` (the endpoint
conjugation, banked) → `fullProduct_loss_squeeze` (the block split, banked) + the gauge-read identities.

**The statement SHAPE is solved** (the cast obstacle): state it with EXISTENTIAL endpoints —
`∃ (P0 : Matrix (Fin (H 0)) (Fin (H 0)) ℝ) (QL : Matrix (Fin (H (Fin.last L))) (Fin (H (Fin.last L))) ℝ),
IsUnit P0 ∧ IsUnit QL ∧ prod H C = P0 * prod H A * QL`, with hypotheses: per-layer frames
`P : (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ`, `Q : … (Fin (H s.succ)) …`,
`hframe : ∀ s, C s = P s * A s * Q s`, `hunit : ∀ s, IsUnit (P s) ∧ IsUnit (Q s)`, and the
INTERFACE-VANISHING conditions `Q s * P s' = 1` for adjacent `s + 1 = s'` (the #95-(I) frame-triviality
makes the interfaces `I`). Existential `P0, QL` are naturally typed where `prod` lives (`H 0`, `H (last)`)
— this DODGES the `H 0` vs `H ⟨0,_⟩.castSucc` cast that breaks an explicit-endpoint statement (probed,
typechecks). The PROOF is the cast-heavy `prodAux` induction: invariant `prodAux H C k = P0 *
prodAux H A k * (frame at k)`, interior interfaces cancelling by the `Q s * P s' = 1` conditions. The
endpoint conjugation + block split are banked (`conjugation_frobenius_comparable`,
`fullProduct_loss_squeeze`); only this induction remains for PIN 2's bridge. -/

/-! ## `ContDiff` of the layer product (the `deepestEPivot._contdiff` infrastructure)


exec
/bin/bash -lc "sed -n '1,170p' lean/DLNFibre/DLN/RLCT/Foundations/Loss.lean" in /home/ubuntu/workspace/deriv-spec
 succeeded in 0ms:
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Real.Basic
import Mathlib.Topology.Constructions

/-!
# `DLNFibre.DLN.RLCT.Foundations.Loss` — the deep-linear-network loss

The parameter space `Params H` of composable real matrix tuples, the multiplication map `prod`,
the square-Frobenius loss `dlnLoss`, and the fibre `optimalSet = mult⁻¹(B)`.

Pure polynomial layer (no measure theory). Faithful to Aoyagi 2023, §0–1 (design-spec §0–1):
the `L`-layer model `Y = (∏_{s=1}^L A⁽ˢ⁾) X + noise`, widths `H : Fin (L+1) → ℕ` with `H⁽¹⁾ = H 0`
the **output** dimension and `H⁽ᴸ⁺¹⁾ = H (last)` the **input** dimension, layer `s` a matrix of size
`H⁽ˢ⁾ × H⁽ˢ⁺¹⁾`. The identity-covariance square-Frobenius loss is RLCT-faithful (`Σ_X` drops out by
the regular whitening change of coordinates; design-spec §0).
-/

namespace DLNFibre.DLN.RLCT

open Matrix

variable {L : ℕ}

/-- A network parameter: a composable tuple of layer matrices, layer `s` of size
`H⁽ˢ⁾ × H⁽ˢ⁺¹⁾ = H s.castSucc × H s.succ`. Definitionally a function space (a `Pi` of `Pi`s),
so it inherits `TopologicalSpace`/`MeasurableSpace`/`MeasureSpace` by `inferInstanceAs`. -/
def Params (H : Fin (L + 1) → ℕ) : Type :=
  ∀ s : Fin L, Matrix (Fin (H s.castSucc)) (Fin (H s.succ)) ℝ

/-- The product of the first `k` layer matrices `A⁽¹⁾·…·A⁽ᵏ⁾`, of size `H 0 × H k`. -/
def prodAux (H : Fin (L + 1) → ℕ) (A : Params H) :
    (k : ℕ) → (hk : k < L + 1) → Matrix (Fin (H 0)) (Fin (H ⟨k, hk⟩)) ℝ
  | 0, _ => (1 : Matrix (Fin (H 0)) (Fin (H 0)) ℝ)
  | k + 1, hk => by
      have hk' : k < L + 1 := Nat.lt_of_succ_lt hk
      have hkL : k < L := Nat.lt_of_succ_lt_succ hk
      refine (prodAux H A k hk') * ?_
      have e1 : (⟨k, hk'⟩ : Fin (L + 1)) = (⟨k, hkL⟩ : Fin L).castSucc := by
        apply Fin.ext; simp [Fin.castSucc]
      have e2 : (⟨k + 1, hk⟩ : Fin (L + 1)) = (⟨k, hkL⟩ : Fin L).succ := by
        apply Fin.ext; simp [Fin.succ]
      rw [e1, e2]; exact A ⟨k, hkL⟩

/-- The multiplication map: the layer product `A⁽¹⁾·A⁽²⁾·…·A⁽ᴸ⁾`, of size
`H⁽¹⁾ × H⁽ᴸ⁺¹⁾ = H 0 × H (last)`. -/
def prod (H : Fin (L + 1) → ℕ) (A : Params H) :
    Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ :=
  prodAux H A L (Nat.lt_succ_self L)

/-- The square-Frobenius loss `‖prod A − B‖²_F = ∑ᵢⱼ ((prod A − B)ᵢⱼ)²`. An honest polynomial in the
entries of `A`, hence real-analytic. Faithful to Aoyagi's Kullback function `K(w)` for the Gaussian
model (design-spec §1). -/
def dlnLoss (H : Fin (L + 1) → ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (A : Params H) : ℝ :=
  ∑ i, ∑ j, ((prod H A - B) i j) ^ 2

/-- The fibre `mult⁻¹(B) = {A | prod A = B}`, the zero-set of `dlnLoss B` (a sum of squares). -/
def optimalSet (H : Fin (L + 1) → ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) : Set (Params H) :=
  { A | prod H A = B }

/-- `optimalSet` is exactly the zero-set of `dlnLoss B`: the loss is a sum of squares, zero iff
`prod A = B`. -/
theorem optimalSet_eq_loss_zero (H : Fin (L + 1) → ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) :
    optimalSet H B = { A | dlnLoss H B A = 0 } := by
  ext A
  simp only [optimalSet, dlnLoss, Set.mem_setOf_eq]
  constructor
  · intro h; simp [h]
  · intro h
    -- a finite sum of squares is zero iff each square is zero
    have hsq : ∀ i, ∀ j, ((prod H A - B) i j) ^ 2 = 0 := by
      have hnn : ∀ i, (0 : ℝ) ≤ ∑ j, ((prod H A - B) i j) ^ 2 := fun i =>
        Finset.sum_nonneg fun j _ => sq_nonneg _
      have hi : ∀ i, ∑ j, ((prod H A - B) i j) ^ 2 = 0 := fun i =>
        (Finset.sum_eq_zero_iff_of_nonneg fun i _ => hnn i).1 h i (Finset.mem_univ i)
      intro i j
      exact (Finset.sum_eq_zero_iff_of_nonneg fun j _ => sq_nonneg _).1 (hi i) j (Finset.mem_univ j)
    funext i j
    have hij : (prod H A - B) i j = 0 := by
      have := hsq i j; nlinarith [this]
    have := sub_eq_zero.1 (by simpa [Matrix.sub_apply] using hij)
    simpa using this

/-- **`dlnLoss` is nonnegative.** A sum of squares: `0 ≤ dlnLoss H B A`. Reusable bedrock — needed
for the sqrt-wrapper `Real.sqrt (dlnLoss …) ^ 2 = dlnLoss …` that feeds `rlct_additive_smooth_block`
(the smooth-block split), and for the homogeneous-core work. -/
theorem dlnLoss_nonneg (H : Fin (L + 1) → ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (A : Params H) :
    0 ≤ dlnLoss H B A :=
  Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _

end DLNFibre.DLN.RLCT

codex
The current file already uses the correct outer packaging pattern: define the full derivative as `fderiv` from `ContDiff`, then use uniqueness only for the reg-block. The unresolved part is not existence; it is a value lemma for the slice/coordinate, and it should be isolated below the product rather than baked into `deepestEPivot_deriv`.
exec
/bin/bash -lc "sed -n '1,180p' expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/prodaux-corner-fderiv-answer.md" in /home/ubuntu/workspace/deriv-spec
 succeeded in 0ms:
   Updating ssh://git@github.com/AI-Safety-Institute/aisi-inspect-tools (HEAD)
    Updated ssh://git@github.com/AI-Safety-Institute/aisi-inspect-tools (fa7351f6ef4773f536ee4975c3251325eb9c44df)
Reading additional input from stdin...
OpenAI Codex v0.142.0
--------
workdir: /home/ubuntu/workspace/deriv-spec
model: gpt-5.5
provider: openai-aisi
approval: untrusted
sandbox: read-only
reasoning effort: xhigh
reasoning summaries: none
session id: 019ef5a0-c1f7-7cd0-9896-ea1a59ab88dd
--------
user
Lean 4 + Mathlib v4.29 formalisation. I need the explicit strict-derivative VALUE of the entries of a chain matrix product, evaluated at a base point where every layer is the idempotent "corner" matrix.

SETUP (all banked, sorry-free):
- `Params H := ∀ s : Fin L, Matrix (Fin (H s.castSucc)) (Fin (H s.succ)) ℝ`.
- `prodAux H A : (k:ℕ) → (hk : k < L+1) → Matrix (Fin (H 0)) (Fin (H ⟨k,hk⟩)) ℝ`, with
  `prodAux 0 = 1`, `prodAux (k+1) = prodAux k * (cast layer ⟨k,hkL⟩)` (dependent Fin casts e1/e2).
- `prod H A := prodAux H A L (Nat.lt_succ_self L)`.
- `framedParamsReg H r hr hL p : Params H`, each layer = `reindex e.symm e'.symm (fromBlocks (1+X_s) Y_s Z_s 0)` where X_s=readX p s etc (linear in p, =0 at p=0).
- At p=0 (gauge slot 0): `prodAux_framedParamsReg_zero_aux`: for 1≤k≤L, `prodAux (framedParamsReg 0) k = reindex e0.symm ek.symm (fromBlocks 1 0 0 0)` (the corner).
- Banked: `hasStrictFDerivAt_prodAux_entry` proves EXISTENCE of a strict derivative D for each entry `fun y => prodAux (g y) k i j` (opaque D, built by Leibniz HasStrictFDerivAt.sum/.mul induction), but NOT the explicit value.
- `corner_reindex_mul`: corner * corner = corner (idempotent under the chain, reindexed).

GOAL: the reg-slice `r0 ↦ deepestEPivot (r0,0)` (each output coord is a block entry (P11-1)/P12/P21 of `P=reindex(prod(framedParamsReg(r0,0)))`) has strict derivative `id` at 0. The math: dP|_0 = Σ_s corner·δC_s·corner. corner·δC_s·corner keeps only: (0,0)-block X_s for all s, (0,1)-block Y_s for the LAST layer, (1,0)-block Z_s for the FIRST layer. With gauge=0 the reg-coords route X to first layer, Y to last, Z to first (via regBoundaryToRegGauge∘regPivotFinEquiv shared with regResidualPack=regPivotFinEquiv), so each coord's derivative = the matching r0 projection.

QUESTION: what is the cleanest Lean route to get the EXPLICIT derivative value (the corner-sandwich sum), given only the EXISTENCE lemma + the corner idempotent base? Options I see:
(A) Prove a NEW explicit-value Leibniz lemma `prodAux_corner_fderiv`: by induction, the strict derivative of `prodAux(framedParamsReg(r0,0)) k i j` at 0 is `Σ_{s<k} (corner_{0..s})·(δlayer_s)·(corner_{s+1..k})` — but this needs naming the running-corner-prefixes and is heavy.
(B) Bypass the explicit Σ: prove directly that the COORDINATE function `r0 ↦ (block entry of reindex prod) i` has derivative `proj i`, by showing the function equals `r0 ↦ r0 i + (higher order)` — i.e. find a clean `HasStrictFDerivAt` via the structure without naming the full Σ.
(C) Something using `HasFDerivAt.congr_fderiv` / uniqueness: we KNOW a derivative D exists (existence lemma); separately compute that the FUNCTION agrees to first order with the linear `proj i` — e.g. via `hasStrictFDerivAt_iff_isLittleO` and bounding the remainder.

Which is least Lean-painful at v4.29? Give the concrete lemma statement(s) + tactic skeleton for the recommended route. Be concrete about avoiding the dependent-Fin cast blowup in the prodAux induction. Mathlib v4.29 names only.
codex
I’ll inspect the local Lean/mathlib APIs and the existing formalization shape first, because the practical answer depends on the exact names and how much notation/cast machinery is already banked.
exec
/bin/bash -lc 'rg -n "hasStrictFDerivAt_iff_isLittleO|HasStrictFDerivAt|congr_fderiv|unique.*fderiv|isLittleO" $(pwd)/.lake/packages/mathlib/Mathlib $(pwd)/.lake/packages/mathlib/Mathlib.lean' in /home/ubuntu/workspace/deriv-spec
2026-06-23T17:57:08.568955Z ERROR codex_app_server::bespoke_event_handling: request failed with client error: JSONRPCErrorError { code: -32000, data: None, message: "command execution approval is not supported in exec mode for thread `019ef5a0-c1f7-7cd0-9896-ea1a59ab88dd`" }
 exited 1:
2026-06-23T17:57:08.569602Z ERROR codex_core::tools::router: error=exec_command failed for `/bin/bash -lc 'rg -n "hasStrictFDerivAt_iff_isLittleO|HasStrictFDerivAt|congr_fderiv|unique.*fderiv|isLittleO" $(pwd)/.lake/packages/mathlib/Mathlib $(pwd)/.lake/packages/mathlib/Mathlib.lean'`: CreateProcess { message: "Rejected(\"rejected by user\")" }
exec
/bin/bash -lc "rg --files . | rg '("'^|/)CLAUDE'"\\.md"'$|lake-manifest'"\\.json|lakefile|Deriv|Dln|Fibre|Formal|Lean|\\.lean"'$'"'" in /home/ubuntu/workspace/deriv-spec
 succeeded in 0ms:
./CLAUDE.md
./lean/DLNFibre.lean
./lean/lake-manifest.json
./lean/lakefile.toml
./lean/CLAUDE.md
./lean/DLNFibre/Core/SmoothPointRegular.lean
./lean/DLNFibre/Core/OrbitImageDim.lean
./lean/DLNFibre/Core/BoxMoveGeneral.lean
./lean/DLNFibre/Core/Barcode.lean
./lean/DLNFibre/Core/CThetaQIP.lean
./lean/DLNFibre/Core/MatrixKaehler.lean
./lean/DLNFibre/Core/IntegralDimension.lean
./lean/DLNFibre/Core/Gabriel.lean
./lean/DLNFibre/Core/OrbitVariety.lean
./lean/DLNFibre/Core/NullstellensatzCodim.lean
./lean/DLNFibre/Core/RankLocusClosed.lean
./lean/DLNFibre/Core/CTheta.lean
./lean/DLNFibre/Core/AffineDomainDimension.lean
./lean/DLNFibre/Core/CThetaQIPConverse.lean
./lean/DLNFibre/Core/OrbitCodim.lean
./lean/DLNFibre/Core/BaseChange.lean
./lean/DLNFibre/Core/CThetaDropM.lean
./lean/DLNFibre/Core/FlatQuasiFiniteHeight.lean
./lean/DLNFibre/Core/IntervalModule.lean
./lean/DLNFibre/Core/PolynomialDimension.lean
./lean/DLNFibre/Core/SmoothLocalRelativeDimension.lean
./lean/DLNFibre/Core/OrbitKostant.lean
./lean/DLNFibre/Core/OrbitClosure.lean
./lean/DLNFibre/Core/VoigtDischarge.lean
./lean/DLNFibre/Core/OrbitLinearCodim.lean
./lean/DLNFibre/Core/CThetaExplicit.lean
./lean/DLNFibre/Core/Submult.lean
./lean/DLNFibre/Core/JacobianTrdeg.lean
./lean/DLNFibre/Core/BoxMoveDegeneration.lean
./lean/DLNFibre/Core/Basic.lean
./lean/DLNFibre/Core/BoxMoveGeneration.lean
./lean/DLNFibre/Core/CThetaValue.lean
./lean/DLNFibre/Core/PolynomialCurveLimit.lean
./lean/DLNFibre/Core/CThetaThetaBridge.lean
./lean/DLNFibre/Core/OrbitSmooth.lean
./lean/DLNFibre/Core/OrbitDifferentialRank.lean
./lean/DLNFibre/Core/CThetaGeometric.lean
./lean/DLNFibre/Core/DeformationExt.lean
./lean/DLNFibre/Core/AffineNoetherRank.lean
./lean/DLNFibre/Core/NoetherMonicPositioning.lean
./lean/DLNFibre/Core/OrbitTangentCotangent.lean
./lean/DLNFibre/Core/OrbitDifferential.lean
./lean/DLNFibre/Core/Setup.lean
./lean/DLNFibre/Core/MeasureTheory/PolynomialZeroSet.lean
./lean/DLNFibre/Core/OrbitPullbackDim.lean
./lean/DLNFibre/Core/Orbit.lean
./lean/DLNFibre/DLN/Basic.lean
./lean/DLNFibre/Core/Matrix/RankNormalForm.lean
./lean/DLNFibre/Core/RankPattern.lean
./lean/DLNFibre/Core/CotangentJacobian.lean
./expeditions/2026-06-18-voigt-discharge/threads/33-A1-kahler-trdeg-api/probes/KahlerTrdegProbe.lean
./expeditions/2026-06-18-voigt-discharge/threads/33-A1-kahler-trdeg-api/probes/RingKrullTrdegProbe.lean
./lean/DLNFibre/DLN/RLCT/BGEngine.lean
./lean/DLNFibre/DLN/RLCT/Foundations/S1Cover.lean
./lean/DLNFibre/DLN/RLCT/Foundations/S1Additive.lean
./lean/DLNFibre/DLN/RLCT/Foundations/S1Spectator.lean
./lean/DLNFibre/DLN/RLCT/Foundations/ParamsFlat.lean
./lean/DLNFibre/DLN/RLCT/Foundations/S1G5.lean
./lean/DLNFibre/DLN/RLCT/Foundations/S1Fubini.lean
./lean/DLNFibre/DLN/RLCT/Foundations/S1SmoothBlock.lean
./lean/DLNFibre/DLN/RLCT/Foundations/Loss.lean
./lean/DLNFibre/DLN/RLCT/Foundations/Lambda.lean
./lean/DLNFibre/DLN/RLCT/Foundations/S1ProductMin.lean
./lean/DLNFibre/DLN/RLCT/Foundations/DeepestSplitHaar.lean
./lean/DLNFibre/DLN/RLCT/Foundations/S1NonMPTransport.lean
./lean/DLNFibre/DLN/RLCT/Foundations/S1Transport.lean
./lean/DLNFibre/DLN/RLCT/Foundations/S1G5Charts.lean
./lean/DLNFibre/DLN/RLCT/Foundations/Rlct.lean
./lean/DLNFibre/DLN/RLCT/Foundations/CoreShearMP.lean
./lean/DLNFibre/DLN/RLCT/Foundations/ParamsFlat222.lean
./lean/DLNFibre/DLN/RLCT/Foundations/S1Local.lean
./lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeBlocks.lean
./lean/DLNFibre/DLN/RLCT/Validate/Case111.lean
./lean/DLNFibre/DLN/RLCT/Validate/DeepestSplitReindex.lean
./lean/DLNFibre/DLN/RLCT/Validate/DeepestNormalFormWiring.lean
./lean/DLNFibre/DLN/RLCT/Validate/DeepestFramedProduct.lean
./lean/DLNFibre/DLN/RLCT/Validate/Case222CoverGE.lean
./lean/DLNFibre/DLN/RLCT/Validate/DeepestRegAbsorbIFT.lean
./lean/DLNFibre/DLN/RLCT/Validate/DeepestTelescoping.lean
./lean/DLNFibre/DLN/RLCT/Validate/Case222CoverGETail.lean
./lean/DLNFibre/DLN/RLCT/Validate/Case222Resolution.lean
./lean/DLNFibre/DLN/RLCT/Validate/GeneralR1Recursion.lean
./lean/DLNFibre/DLN/RLCT/Validate/Case212.lean
./lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeConstruction.lean
./lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeDiffeo.lean
./lean/DLNFibre/DLN/RLCT/Validate/DeepestSchurShift.lean
./lean/DLNFibre/DLN/RLCT/Validate/ResolutionAtlas.lean
./lean/DLNFibre/DLN/RLCT/Validate/Case222Block.lean
./lean/DLNFibre/DLN/RLCT/Validate/Case222Value.lean
./lean/DLNFibre/DLN/RLCT/Validate/Case222Lemma2.lean
./lean/DLNFibre/DLN/RLCT/Validate/Case222Rlct.lean
./lean/DLNFibre/DLN/RLCT/Validate/DeepestFrame.lean
./lean/DLNFibre/DLN/RLCT/Validate/Case222Cover.lean
./lean/DLNFibre/DLN/RLCT/Validate/Case111Bridge.lean
./lean/DLNFibre/DLN/RLCT/Validate/DeepestCoreNonvanishing.lean
./lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeChart.lean
./lean/DLNFibre/DLN/RLCT/Validate/Case222Algebra.lean
./lean/DLNFibre/DLN/RLCT/Validate/DeepestMinRlct.lean
./lean/DLNFibre/DLN/RLCT/AxCheck.lean
./lean/DLNFibre/DLN/RLCT/Skeleton.lean

exec
/bin/bash -lc 'rg -n "hasStrictFDerivAt_prodAux_entry|prodAux_framedParamsReg_zero_aux|corner_reindex_mul|deepestEPivot|framedParamsReg|regBoundaryToRegGauge|regResidualPack|regPivotFinEquiv" -S .' in /home/ubuntu/workspace/deriv-spec
 succeeded in 0ms:
./lean/DLNFibre/DLN/RLCT/Validate/DeepestSplitReindex.lean:213:by construction (g213/#91). `regResidualPack` (in `DeepestGaugeConstruction`) and `regGaugeIdxSplit`
./lean/DLNFibre/DLN/RLCT/Validate/DeepestSplitReindex.lean:214:(below) both factor through the SAME `regPivotFinEquiv`, so they cancel. -/
./lean/DLNFibre/DLN/RLCT/Validate/DeepestSplitReindex.lean:217:sandwich: `(r×r) ⊕ ((r×M_L) ⊕ (M_0×r))`, the sum type `regResidualPack` targets, of card `deepestNReg`. -/
./lean/DLNFibre/DLN/RLCT/Validate/DeepestSplitReindex.lean:221:/-- **The card match** — `card BoundaryPivotIdx = deepestNReg` (the arithmetic `regResidualPack` proves:
./lean/DLNFibre/DLN/RLCT/Validate/DeepestSplitReindex.lean:238:noncomputable def regPivotFinEquiv (H : Fin (L + 1) → ℕ) (r : ℕ)
./lean/DLNFibre/DLN/RLCT/Validate/DeepestSplitReindex.lean:269:def regBoundaryToRegGauge (H : Fin (L + 1) → ℕ) (r : ℕ) (hL : 1 ≤ L) :
./lean/DLNFibre/DLN/RLCT/Validate/DeepestSplitReindex.lean:276:/-- A LEFT INVERSE of `regBoundaryToRegGauge` (total on `RegGaugeIdx`, inverting on the image). -/
./lean/DLNFibre/DLN/RLCT/Validate/DeepestSplitReindex.lean:287:/-- **`regBoundaryToRegGauge` is INJECTIVE** (the no-collapse fact) — via the left inverse `regGaugeDecode`
./lean/DLNFibre/DLN/RLCT/Validate/DeepestSplitReindex.lean:290:theorem regBoundaryToRegGauge_injective (H : Fin (L + 1) → ℕ) (r : ℕ) (hL : 1 ≤ L) :
./lean/DLNFibre/DLN/RLCT/Validate/DeepestSplitReindex.lean:291:    Function.Injective (regBoundaryToRegGauge H r hL) := by
./lean/DLNFibre/DLN/RLCT/Validate/DeepestSplitReindex.lean:300:  · rw [regBoundaryToRegGauge, regGaugeDecode, dif_pos hY]
./lean/DLNFibre/DLN/RLCT/Validate/DeepestSplitReindex.lean:302:  · rw [regBoundaryToRegGauge, regGaugeDecode, dif_pos hZ]
./lean/DLNFibre/DLN/RLCT/Validate/DeepestSplitReindex.lean:330:  ⟨regBoundaryToRegGauge H r hL, regBoundaryToRegGauge_injective H r hL⟩
./lean/DLNFibre/DLN/RLCT/Validate/DeepestSplitReindex.lean:356:`Fin nReg` (reg) half routes onto the boundary generators via `regBoundaryToRegGauge ∘ regPivotFinEquiv`
./lean/DLNFibre/DLN/RLCT/Validate/DeepestSplitReindex.lean:358:complement (its enumeration opaque — only the REG half needs the boundary alignment). So `regResidualPack
./lean/DLNFibre/DLN/RLCT/Validate/DeepestSplitReindex.lean:359::= regPivotFinEquiv` and this split's reg-half SHARE `regPivotFinEquiv`, hence cancel (reg-block = id). -/
./lean/DLNFibre/DLN/RLCT/Validate/DeepestSplitReindex.lean:366:  -- (the SHARED `regPivotFinEquiv`), gauge-half `≃ Fin nGauge` (opaque enum on the complement).
./lean/DLNFibre/DLN/RLCT/Validate/DeepestSplitReindex.lean:370:      (regPivotFinEquiv H r hr).symm
./lean/DLNFibre/DLN/RLCT/Validate/DeepestFramedProduct.lean:115:/-- **The `T = 0` framed reconstruction** (the `deepestEPivot` reconstruction half). Reconstructs the
./lean/DLNFibre/DLN/RLCT/Validate/DeepestFramedProduct.lean:117:(the core is `coreAbsorb`'s domain — `deepestEPivot` is the regular residual of `∏C|_{T=0}`, the
./lean/DLNFibre/DLN/RLCT/Validate/DeepestFramedProduct.lean:121:noncomputable def framedParamsReg (H : Fin (L + 1) → ℕ) (r : ℕ)
./lean/DLNFibre/DLN/RLCT/Validate/DeepestFramedProduct.lean:129:/-- At the origin gauge slot, `framedParamsReg` is the **block-normal identity chain**: every layer is
./lean/DLNFibre/DLN/RLCT/Validate/DeepestFramedProduct.lean:131:fact for `deepestEPivot`'s `_base` (the residual of `∏ blockdiag[I_r,0]` is `0`). -/
./lean/DLNFibre/DLN/RLCT/Validate/DeepestFramedProduct.lean:132:theorem framedParamsReg_zero (H : Fin (L + 1) → ℕ) (r : ℕ)
./lean/DLNFibre/DLN/RLCT/Validate/DeepestFramedProduct.lean:134:    framedParamsReg H r hr hL 0 s
./lean/DLNFibre/DLN/RLCT/Validate/DeepestFramedProduct.lean:138:  simp only [framedParamsReg, framedLayer, readX_zero H r hr hL s, readY_zero H r hr hL s,

exec
/bin/bash -lc "sed -n '1,150p' expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/fold2-deriv-route-answer.md" in /home/ubuntu/workspace/deriv-spec
 succeeded in 0ms:
**Ranking**

1. **B**. Set `D_E := fderiv ℝ deepestEPivot 0`; prove only the reg-slice derivative is `id`; package invertibility by `clmShearEquiv`.  
   Biggest risk: the reg-slice coordinate simp may hit the `regGaugeIdxSplit`/`regResidualPack` packing wall.

2. **A**. Most canonical mathematically, but high Lean cost.  
   Biggest risk: dependent `prodAux` casts plus named Leibniz derivative will spread through every entry.

3. **D = factor out the shear lemma first**: prove a generic `regStraightenTotalCLM_equiv_of_regBlock_id`, then feed it any `D_E` with reg-block `id`. This is useful, but still needs B or A for `hblock`.

4. **C**. Avoid.  
   Biggest risk: direct `littleO` for the whole product is just unnamed Leibniz with worse API support.

**Top Route: B**

Use:

```lean
let E := deepestEPivot H r hr hL
let D_E := fderiv ℝ E (0 : Reg × Gauge)

have hE : HasStrictFDerivAt E D_E 0 :=
  (deepestEPivot_contdiff H r hr hL).hasStrictFDerivAt (by simp)
```

Mathlib names I’m confident exist in v4.29:

- `ContDiff.hasStrictFDerivAt`
- `HasStrictFDerivAt.comp`
- `ContinuousLinearMap.hasStrictFDerivAt`
- `HasStrictFDerivAt.hasFDerivAt`
- `HasFDerivAt.fderiv`
- `hasStrictFDerivAt_pi''`
- `ContinuousLinearMap.id`, `.fst`, `.snd`, `.prod`, `.comp`

State these sublemmas:

```lean
def regInCLM : Reg →L[ℝ] Reg × Gauge :=
  (ContinuousLinearMap.id ℝ Reg).prod 0
```

```lean
lemma deepestEPivot_regSlice_hasStrictFDerivAt_id :
  HasStrictFDerivAt
    (fun r0 : Reg => deepestEPivot H r hr hL (r0, 0))
    (ContinuousLinearMap.id ℝ Reg) 0
```

Prove this coordinatewise by `hasStrictFDerivAt_pi''`. For each packed coordinate, unfold `deepestEPivot`, `framedParamsReg`, `framedLayer`, then use the gauge-zero slice facts for reads:

```lean
readX H r hr hL (r0, 0) s = if s = first then X_from_reg r0 else 0
readY H r hr hL (r0, 0) s = if s = last  then Y_from_reg r0 else 0
readZ H r hr hL (r0, 0) s = if s = first then Z_from_reg r0 else 0
```

Then the idempotent fold collapses because all non-pivot layers are

```lean
Matrix.fromBlocks 1 0 0 0
```

and the only first-order surviving sandwiches are:

```lean
corner * δC_s * corner
```

with block results:

```lean
toBlocks₁₁ : Σ_s X_s  -- gauge-zero slice: only pivot X, so this is X_reg
toBlocks₁₂ : Y_last
toBlocks₂₁ : Z_first
```

The simp/idempotency step should be a reusable lemma, not inline:

```lean
lemma regSlice_linear_part :
  HasStrictFDerivAt
    (fun r0 : Reg =>
      -- packed residual of prod H (framedParamsReg (r0,0))
    )
    (ContinuousLinearMap.id ℝ Reg) 0
```

Then derive the block identity:

```lean
lemma fderiv_deepestEPivot_regBlock :
  D_E.comp regInCLM = ContinuousLinearMap.id ℝ Reg := by
  have hcomp := hE.comp regInCLM.hasStrictFDerivAt
  have hid := deepestEPivot_regSlice_hasStrictFDerivAt_id H r hr hL
  exact (hcomp.hasFDerivAt.fderiv).symm.trans hid.hasFDerivAt.fderiv
```

Finally package invertibility generically:

```lean
lemma regStraightenTotalCLM_equiv_of_regBlock_id
    (D_E : Reg × Gauge →L[ℝ] Reg)
    (hblock : D_E.comp regInCLM = ContinuousLinearMap.id ℝ Reg) :
  ∃ e : DeepestSplit ≃L[ℝ] DeepestSplit,
    (e : DeepestSplit →L[ℝ] DeepestSplit) = regStraightenTotalCLM D_E
```

Define `N := regStraightenTotalCLM D_E - ContinuousLinearMap.id ℝ DeepestSplit`; prove `N.comp N = 0` by `ext q; simp [N, regStraightenTotalCLM, hblock_apply]`; then use `clmShearEquiv N hN`.

**Likely Wall**

The wall is `deepestEPivot_regSlice_hasStrictFDerivAt_id`, specifically making `regResidualPack` and `regGaugeIdxSplit` expose that the regular coordinates are exactly `(X_first, Y_last, Z_first)`. Fallback: do A only for the reg-slice, not full `(reg,gauge)`: name a restricted Leibniz derivative for `fun r => prod H (framedParamsReg (r,0))`; collapse it to `id`; still keep `D_E := fderiv` for the full map.
exec
/bin/bash -lc "rg -n \"hasStrictFDerivAt_pi|HasStrictFDerivAt\\.fun_sum|\\.fderiv|hasStrictFDerivAt_iff_isLittleO|isLittleO\" lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus lean/.lake/packages/mathlib/Mathlib/Topology -S" in /home/ubuntu/workspace/deriv-spec
 succeeded in 0ms:
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/Implicit.lean:143:  rw [φ.hasStrictFDerivAt.hasFDerivAt.fderiv]
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/Implicit.lean:234:  exact this.hasFDerivAt.fderiv
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/Implicit.lean:246:    ((hasStrictFDerivAt_const _ _).prodMk (hasStrictFDerivAt_id _)) |>.hasFDerivAt |>.fderiv]
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/Implicit.lean:253:  exact φ.fderiv_implicitFunction_apply_eq_iff.mp rfl |>.left
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/Implicit.lean:258:  exact φ.fderiv_implicitFunction_apply_eq_iff.mp rfl |>.right
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/WithLp.lean:51:theorem hasStrictFDerivAt_piLp :
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/WithLp.lean:55:  rw [← (PiLp.continuousLinearEquiv p 𝕜 E).comp_hasStrictFDerivAt_iff, hasStrictFDerivAt_pi']
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/WithLp.lean:70:  .of_isLittleO <| (Asymptotics.isLittleO_zero _ _).congr_left fun _ => (sub_self _).symm
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/WithLp.lean:75:  .of_isLittleO <| (Asymptotics.isLittleO_zero _ _).congr_left fun _ => (sub_self _).symm
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Bilinear.lean:47:  simp only [hasStrictFDerivAt_iff_isLittleO]
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Bilinear.lean:48:  simp only [← map_add_left_nhds_zero (p, p), isLittleO_map]
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Bilinear.lean:62:      refine h.toContinuousLinearMap.deriv₂.isBoundedBilinearMap.isBigO_comp.trans_isLittleO ?_
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Bilinear.lean:64:        simpa only [mul_one, isLittleO_norm_right] using this
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Bilinear.lean:65:      refine (isBigO_refl _ _).mul_isLittleO ((isLittleO_one_iff _).2 ?_)
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Bilinear.lean:90:protected theorem IsBoundedBilinearMap.fderiv (h : IsBoundedBilinearMap 𝕜 b) (p : E × F) :
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Bilinear.lean:92:  HasFDerivAt.fderiv (h.hasFDerivAt p)
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Bilinear.lean:94:protected theorem IsBoundedBilinearMap.fderivWithin (h : IsBoundedBilinearMap 𝕜 b) (p : E × F)
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Bilinear.lean:96:  rw [DifferentiableAt.fderivWithin (h.differentiableAt p) hxs]
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Bilinear.lean:97:  exact h.fderiv p
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Bilinear.lean:134:theorem ContinuousLinearMap.fderivWithin_of_bilinear {f : G' → E} {g : G' → F} {x : G'} {s : Set G'}
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Bilinear.lean:139:  (B.hasFDerivWithinAt_of_bilinear hf.hasFDerivWithinAt hg.hasFDerivWithinAt).fderivWithin hs
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Bilinear.lean:141:theorem ContinuousLinearMap.fderiv_of_bilinear {f : G' → E} {g : G' → F} {x : G'}
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Bilinear.lean:145:  (B.hasFDerivAt_of_bilinear hf.hasFDerivAt hg.hasFDerivAt).fderiv
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Equiv.lean:68:  iso.hasFDerivAt.fderiv
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Equiv.lean:71:  iso.toContinuousLinearMap.fderivWithin hxs
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Equiv.lean:130:  · rw [fderiv_comp_fderivWithin x iso.differentiableAt h hxs, iso.fderiv]
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Equiv.lean:140:lemma _root_.fderivWithin_continuousLinearEquiv_comp (L : G ≃L[𝕜] G') (f : E → (F →L[𝕜] G))
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Equiv.lean:147:lemma _root_.fderiv_continuousLinearEquiv_comp (L : G ≃L[𝕜] G') (f : E → (F →L[𝕜] G)) (x : E) :
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Equiv.lean:153:lemma _root_.fderiv_continuousLinearEquiv_comp' (L : G ≃L[𝕜] G') (f : E → (F →L[𝕜] G)) :
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Equiv.lean:219:  · exact (iso.comp_right_hasFDerivWithinAt_iff.2 h.hasFDerivWithinAt).fderivWithin hxs
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Equiv.lean:261:  iso.hasFDerivAt.fderiv
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Equiv.lean:264:  (iso : E ≃L[𝕜] F).fderivWithin hxs
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Equiv.lean:337:  refine .of_isLittleO <| this.trans_isLittleO ?_
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Equiv.lean:339:  refine ((hf.isLittleO.comp_tendsto hg).symm.congr' (hfg.mono ?_) .rfl).trans_isBigO ?_
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Equiv.lean:363:  refine .of_isLittleO <| this.trans_isLittleO ?_
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Equiv.lean:365:  refine ((hf.isLittleO.comp_tendsto hg).symm.congr'
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Equiv.lean:414:  have : (fun z ↦ f z - f x) ~[𝓝[s] x] fun z ↦ f' (z - x) := h.isLittleO.trans_isBigO A
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Add.lean:92:  (h.hasFDerivWithinAt.const_smul c).fderivWithin hxs
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Add.lean:112:  · exact (h.hasFDerivWithinAt.const_smul c).fderivWithin hs
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Add.lean:121:  (h.hasFDerivAt.const_smul c).fderiv
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Add.lean:125:  (h.hasFDerivAt.const_smul c).fderiv
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Add.lean:182:  .of_isLittleO <| (hf.isLittleO.add hg.isLittleO).congr_left fun _ => by
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Add.lean:222:  (hf.hasFDerivWithinAt.add hg.hasFDerivWithinAt).fderivWithin hxs
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Add.lean:232:  (hf.hasFDerivAt.add hg.hasFDerivAt).fderiv
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Add.lean:241:  simp [hasFDerivAtFilter_iff_isLittleOTVS]
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Add.lean:248:  simp [hasStrictFDerivAt_iff_isLittleO]
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Add.lean:390:theorem HasStrictFDerivAt.fun_sum (h : ∀ i ∈ u, HasStrictFDerivAt (A i) (A' i) x) :
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Add.lean:392:  simp only [hasStrictFDerivAt_iff_isLittleO] at *
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Add.lean:399:  convert HasStrictFDerivAt.fun_sum h; simp
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Add.lean:403:  simp only [hasFDerivAtFilter_iff_isLittleO] at *
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Add.lean:475:  (HasFDerivWithinAt.fun_sum fun i hi => (h i hi).hasFDerivWithinAt).fderivWithin hxs
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Add.lean:480:  (HasFDerivWithinAt.sum fun i hi => (h i hi).hasFDerivWithinAt).fderivWithin hxs
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Add.lean:484:  (HasFDerivAt.fun_sum fun i hi => (h i hi).hasFDerivAt).fderiv
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Add.lean:488:  (HasFDerivAt.sum fun i hi => (h i hi).hasFDerivAt).fderiv
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Add.lean:573:  · exact h.hasFDerivWithinAt.neg.fderivWithin hxs
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Add.lean:701:  (hf.hasFDerivWithinAt.sub hg.hasFDerivWithinAt).fderivWithin hxs
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Add.lean:710:  (hf.hasFDerivAt.sub hg.hasFDerivAt).fderiv
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Add.lean:846:  simp [HasFDerivWithinAt, hasFDerivAtFilter_iff_isLittleOTVS, ← this, Function.comp_def]
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Affine.lean:37:  refine .of_isLittleOTVS <| .congr_left (.zero _ _) ?_
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Affine.lean:62:  f.hasFDerivAt.fderiv
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Affine.lean:66:  rw [DifferentiableAt.fderivWithin f.differentiableAt hxs]
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Affine.lean:67:  exact f.fderiv
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Const.lean:40:  .of_isLittleOTVS <| (IsLittleOTVS.zero _ _).congr_left fun _ => by simp
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Const.lean:376:  simp [h.fderiv_eq]
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Const.lean:388:protected theorem HasCompactSupport.fderiv (hf : HasCompactSupport f) :
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Const.lean:392:protected theorem HasCompactSupport.fderiv_apply (hf : HasCompactSupport f) (v : E) :
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Prod.lean:55:  .of_isLittleO <| hf₁.isLittleO.prod_left hf₂.isLittleO
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Prod.lean:103:theorem DifferentiableAt.fderiv_prodMk (hf₁ : DifferentiableAt 𝕜 f₁ x)
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Prod.lean:106:  (hf₁.hasFDerivAt.prodMk hf₂.hasFDerivAt).fderiv
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Prod.lean:108:theorem DifferentiableWithinAt.fderivWithin_prodMk (hf₁ : DifferentiableWithinAt 𝕜 f₁ s x)
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Prod.lean:112:  (hf₁.hasFDerivWithinAt.prodMk hf₂.hasFDerivWithinAt).fderivWithin hxs
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Prod.lean:193:  hasFDerivAt_fst.fderiv
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Prod.lean:197:  h.hasFDerivAt.fst.fderiv
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Prod.lean:201:  hasFDerivWithinAt_fst.fderivWithin hs
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Prod.lean:205:  h.hasFDerivWithinAt.fst.fderivWithin hs
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Prod.lean:286:  hasFDerivAt_snd.fderiv
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Prod.lean:290:  h.hasFDerivAt.snd.fderiv
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Prod.lean:294:  hasFDerivWithinAt_snd.fderivWithin hs
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Prod.lean:298:  h.hasFDerivWithinAt.snd.fderivWithin hs
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Prod.lean:356:  simp [hasFDerivAtFilter_iff_isLittleOTVS, isLittleOTVS_pi]
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Prod.lean:359:theorem hasStrictFDerivAt_pi' :
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Prod.lean:364:theorem hasStrictFDerivAt_pi'' (hφ : ∀ i, HasStrictFDerivAt (fun x => Φ x i) ((proj i).comp Φ') x) :
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Prod.lean:365:    HasStrictFDerivAt Φ Φ' x := hasStrictFDerivAt_pi'.2 hφ
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Prod.lean:372:theorem hasStrictFDerivAt_pi :
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Prod.lean:375:  hasStrictFDerivAt_pi'
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Prod.lean:479:  (hasFDerivWithinAt_pi.2 fun i => (h i).hasFDerivWithinAt).fderivWithin hs
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Prod.lean:483:  (hasFDerivAt_pi.2 fun i => (h i).hasFDerivAt).fderiv
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Symmetric.lean:60:in `Convex.isLittleO_alternate_sum_square`, but the argument is essentially the same. It only works
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Symmetric.lean:113:    apply Filter.EventuallyEq.fderivWithin_eq A
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Symmetric.lean:117:  exact (hf.fderivWithin_right (m := 1) ht le_rfl
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Symmetric.lean:124:      (fderivWithin_eventually_congr_set h).fderivWithin_eq_of_nhds
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Symmetric.lean:230:    (isLittleO_iff.2 fun ε εpos => ?_) (isBigO_const_mul_self ((‖v‖ + ‖w‖) * ‖w‖) _ _)
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Symmetric.lean:233:  rw [hasFDerivWithinAt_iff_isLittleO, isLittleO_iff] at hx
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Symmetric.lean:331:theorem Convex.isLittleO_alternate_sum_square {v w : E} (h4v : x + (4 : ℝ) • v ∈ interior s)
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Symmetric.lean:375:    convert (s_conv.isLittleO_alternate_sum_square hf xs hx h4v h4w).sub
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Symmetric.lean:376:      (s_conv.isLittleO_alternate_sum_square hf xs hx h4w h4v) using 1
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Symmetric.lean:382:    have C := this.smul_isLittleO A
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Symmetric.lean:389:  simpa only [sub_eq_zero] using isLittleO_const_const_iff.1 B
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Symmetric.lean:560:        exact hf.fderiv_right (le_minSmoothness.trans hn)
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Symmetric.lean:598:      ((hu.fderivWithin h'u (m := 1) (le_minSmoothness.trans hm)).fderivWithin h'u
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Measurable.lean:161:    eventually_nhds_iff_ball.1 <| hx.hasFDerivAt.isLittleO.bound <| by positivity
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Measurable.lean:293:    simp only [hasFDerivAt_iff_isLittleO_nhds_zero, isLittleO_iff]
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Measurable.lean:347:  rw [← this.fderiv] at f'K
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Measurable.lean:488:  simp_rw [hasDerivWithinAt_iff_isLittleO, isLittleO_iff] at this
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Measurable.lean:622:    simp only [hasDerivWithinAt_iff_isLittleO, isLittleO_iff]
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Analytic.lean:29:* `AnalyticOnNhd.fderiv` : in a complete space, if a function is analytic on a
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Analytic.lean:31:* `AnalyticOnNhd.fderiv_of_isOpen` : if a function is analytic on a neighborhood of an
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Analytic.lean:33:* `AnalyticOn.fderivWithin` : if a function is analytic on a set of unique differentiability,
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Analytic.lean:88:  refine h.isBigO_image_sub_norm_mul_norm_sub.trans_isLittleO (IsLittleO.of_norm_right ?_)
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Analytic.lean:89:  refine isLittleO_iff_exists_eq_mul.2 ⟨fun y => ‖y - (x, x)‖, ?_, EventuallyEq.rfl⟩
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Analytic.lean:96:  simpa only [hasStrictFDerivAt_iff_isLittleO, Set.insert_eq_of_mem, Set.mem_univ,
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Analytic.lean:102:  rw [hasFDerivWithinAt_iff_isLittleO, isLittleO_iff]
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Analytic.lean:107:  exact this (isLittleO_iff.1 h.hasStrictFDerivWithinAt hc)
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Analytic.lean:132:theorem HasFPowerSeriesWithinAt.fderivWithin_eq
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Analytic.lean:135:  h.hasFDerivWithinAt.fderivWithin hu
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Analytic.lean:137:theorem HasFPowerSeriesAt.fderiv_eq (h : HasFPowerSeriesAt f p x) :
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Analytic.lean:139:  h.hasFDerivAt.fderiv
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Analytic.lean:144:  rw [hp.fderiv_eq]
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Analytic.lean:198:theorem HasFPowerSeriesWithinOnBall.fderivWithin_eq [CompleteSpace F]
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Analytic.lean:203:  (h.hasFDerivWithinAt hy h'y).fderivWithin (hu _ h'y)
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Analytic.lean:205:theorem HasFPowerSeriesOnBall.fderiv_eq [CompleteSpace F] (h : HasFPowerSeriesOnBall f p x r)
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Analytic.lean:208:  (h.hasFDerivAt hy).fderiv
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Analytic.lean:211:protected theorem HasFPowerSeriesOnBall.fderiv [CompleteSpace F]
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Analytic.lean:221:  rw [← h.fderiv_eq, add_sub_cancel]
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Analytic.lean:225:protected theorem HasFPowerSeriesWithinOnBall.fderivWithin [CompleteSpace F]
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Analytic.lean:236:    rw [← h.fderivWithin_eq _ _ hu, add_sub_cancel]
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Analytic.lean:242:`HasFPowerSeriesWithinOnBall.fderivWithin_of_mem_of_analyticOn`. -/
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Analytic.lean:243:protected theorem HasFPowerSeriesWithinOnBall.fderivWithin_of_mem [CompleteSpace F]
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Analytic.lean:248:  convert h.fderivWithin hu
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Analytic.lean:253:protected theorem AnalyticAt.fderiv [CompleteSpace F] (h : AnalyticAt 𝕜 f x) :
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Analytic.lean:256:  exact hp.fderiv.analyticAt
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Analytic.lean:259:`AnalyticOnNhd.fderiv_of_isOpen`, removing the completeness assumption but requiring the set
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Analytic.lean:261:protected theorem AnalyticOnNhd.fderiv [CompleteSpace F] (h : AnalyticOnNhd 𝕜 f s) :
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Analytic.lean:263:  fun y hy ↦ AnalyticAt.fderiv (h y hy)
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Analytic.lean:277:    convert ContinuousLinearMap.comp_analyticOnNhd ?g IH.fderiv
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Analytic.lean:326:  have Z := (this.fderivWithin hu).hasSum h'y (by simpa [edist_zero_right] using hy)
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Analytic.lean:328:    apply HasFDerivWithinAt.fderivWithin _ (hu _ h'y)
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Analytic.lean:342:that `F` is complete, see `HasFPowerSeriesWithinOnBall.fderivWithin_of_mem`. -/
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Analytic.lean:343:protected theorem HasFPowerSeriesWithinOnBall.fderivWithin_of_mem_of_analyticOn
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Analytic.lean:356:protected theorem AnalyticOn.fderivWithin (h : AnalyticOn 𝕜 f s) (hu : UniqueDiffOn 𝕜 s) :
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Analytic.lean:360:  refine ⟨p.derivSeries, r, hr.fderivWithin_of_mem_of_analyticOn h hu hx⟩
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Analytic.lean:374:    apply AnalyticOnNhd.comp_analyticOn _ (IH.fderivWithin hu) (mapsTo_univ _ _)
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Analytic.lean:391:theorem AnalyticOnNhd.fderiv_of_isOpen (h : AnalyticOnNhd 𝕜 f s) (hs : IsOpen s) :
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Analytic.lean:394:  exact (h.fderivWithin hs.uniqueDiffOn).congr (fun x hx ↦ (fderivWithin_of_isOpen hs hx).symm)
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Analytic.lean:408:  have : p 1 = (continuousMultilinearCurryFin1 𝕜 E F).symm i := by simp [← h', hp.fderiv_eq]
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Analytic.lean:443:  (ContinuousLinearMap.apply 𝕜 F (1 : 𝕜)).comp_analyticOnNhd h.fderiv
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Analytic.lean:448:  (ContinuousLinearMap.apply 𝕜 F (1 : 𝕜)).comp_analyticOnNhd (h.fderiv_of_isOpen hs)
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Analytic.lean:491:theorem HasFiniteFPowerSeriesOnBall.fderiv_eq (h : HasFiniteFPowerSeriesOnBall f p x n r)
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Analytic.lean:494:  (h.hasFDerivAt hy).fderiv
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Analytic.lean:497:protected theorem HasFiniteFPowerSeriesOnBall.fderiv
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Analytic.lean:507:  rw [← h.fderiv_eq, add_sub_cancel]
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Analytic.lean:511:This is a variant of `HasFiniteFPowerSeriesOnBall.fderiv` where the degree of `f` is `< n`
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Analytic.lean:513:theorem HasFiniteFPowerSeriesOnBall.fderiv' (h : HasFiniteFPowerSeriesOnBall f p x n r) :
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Analytic.lean:518:    · rw [Filter.EventuallyEq.fderiv_eq (f := fun _ ↦ 0)]
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Analytic.lean:527:    exact h.fderiv
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Analytic.lean:530:theorem CPolynomialOn.fderiv (h : CPolynomialOn 𝕜 f s) :
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Analytic.lean:534:  exact hp.fderiv'.cpolynomialAt
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Analytic.lean:545:    convert ContinuousLinearMap.comp_cpolynomialOn ?g IH.fderiv
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Analytic.lean:558:  (ContinuousLinearMap.apply 𝕜 F (1 : 𝕜)).comp_cpolynomialOn h.fderiv
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Analytic.lean:632:    (hasStrictFDerivAt_pi.2 fun _ ↦ hasStrictFDerivAt_id _)
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Analytic.lean:657:    |>.comp x (hf.prodMk (hasStrictFDerivAt_pi.2 hg))
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Analytic.lean:830:      ← ContinuousLinearMap.smul_apply, ih h.fderiv, iteratedFDeriv_succ_apply_right]
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Analytic.lean:845:      ← ContinuousLinearMap.smul_apply, factorial_smul' _ h.fderiv, iteratedFDeriv_succ_apply_right]
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Pi.lean:36:  (hasFDerivAt_update x y).fderiv
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean:150:      simpa [smul_sub] using h.isLittleOTVS.comp_tendsto tendsto_arg |>.smul_left c
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean:152:  rw [isLittleOTVS_one] at this
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean:196:  .of_isLittleOTVS <| h.isLittleOTVS.mono hst
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean:249:  simp_rw [hasFDerivWithinAt_iff_isLittleOTVS]
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean:250:  apply isLittleOTVS_insert
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean:281:  simp [HasFDerivWithinAt, hasFDerivAtFilter_iff_isLittleOTVS]
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean:319:  .of_isLittleOTVS <| by
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean:320:    simpa only using hf.isLittleOTVS.comp_tendsto (tendsto_id.prodMk_nhds tendsto_const_nhds)
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean:349:  simp only [hasFDerivWithinAt_iff_isLittleOTVS, nhdsWithin_union] at *
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean:365:  rw [← hasFDerivWithinAt_diff_singleton_self, hasFDerivWithinAt_iff_isLittleOTVS, h]
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean:405:protected theorem HasFDerivAt.fderiv
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean:415:  funext fun x => (h x).fderiv
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean:417:protected theorem HasFDerivWithinAt.fderivWithin
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean:473:protected theorem DifferentiableAt.fderivWithin
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean:477:  h.hasFDerivAt.hasFDerivWithinAt.fderivWithin hxs
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean:501:  ((DifferentiableWithinAt.hasFDerivWithinAt h).mono_of_mem_nhdsWithin st).fderivWithin ht
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean:598:  simpa using hf.isLittleOTVS.isBigOTVS.fun_add f'.isBigOTVS_comp
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean:630:    refine h.isBigOTVS_sub |>.comp_tendsto prod_pure.ge |>.trans_isLittleOTVS ?_
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean:631:    rw [isLittleOTVS_one]
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean:633:  rw [isLittleOTVS_one] at this
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean:673:  .of_isLittleOTVS <| (IsLittleOTVS.zero _ _).congr_left <| by simp
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean:718:  HasFDerivAt.fderiv (hasFDerivAt_id x)
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean:727:  rw [DifferentiableAt.fderivWithin differentiableAt_id hxs]
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean:753:  rw [IsEquivalent, ← isLittleOTVS_iff_isLittleO (𝕜 := 𝕜)]
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean:754:  exact hf.isLittleOTVS.trans_isBigOTVS <| f'.isThetaTVS_comp hf' |>.symm.isBigOTVS
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean:807:  rw [hasFDerivAtFilter_iff_isLittleO, ← isLittleO_norm_left, ← isLittleO_norm_right,
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean:808:    isLittleO_iff_tendsto]
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean:822:theorem hasFDerivAt_iff_isLittleO_nhds_zero :
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean:824:  rw [hasFDerivAt_iff_isLittleO, ← map_add_left_nhds_zero x, isLittleO_map]
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean:853:  simp_rw [hasFDerivWithinAt_iff_isLittleO,
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean:855:    h.trans_isLittleO ((isLittleO_pow_sub_sub x₀ hn).mono nhdsWithin_le_nhds)]
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean:888:  have := hf.isLittleO.add_isBigOWith (f'.isBigOWith_comp _ _) hK
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean:909:  filter_upwards [isLittleO_iff.1 (hasFDerivAt_iff_isLittleO_nhds_zero.1 hf) ε0, hlip] with y hy hyC
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean:976:  rw [hasFDerivAt_iff_isLittleO_nhds_zero] at ⊢ hf
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean:978:  simpa using ((L.isBigO_comp _ _).trans_isLittleO this).trans_isBigO (R.isBigO_id _)
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/ContinuousAlternatingMap.lean:51:  · rw [hasStrictFDerivAt_iff_isLittleOTVS] at h ⊢
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/ContinuousAlternatingMap.lean:52:    refine Asymptotics.IsBigOTVS.trans_isLittleOTVS ?_ h
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/ContinuousAlternatingMap.lean:68:        fg.1.fderivCompContinuousLinearMap fg.2 ∘L .snd _ _ _)
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/ContinuousAlternatingMap.lean:74:  have H₃ := hasStrictFDerivAt_pi.mpr fun i : ι ↦ hasStrictFDerivAt_id (𝕜 := 𝕜) fg.2
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/ContinuousAlternatingMap.lean:81:        (f x).fderivCompContinuousLinearMap (g x) ∘L g') x :=
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/ContinuousAlternatingMap.lean:88:        (f x).fderivCompContinuousLinearMap (g x) ∘L g') x := by
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/ContinuousAlternatingMap.lean:96:        (f x).fderivCompContinuousLinearMap (g x) ∘L g') s x := by
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/ContinuousAlternatingMap.lean:105:        (f x).fderivCompContinuousLinearMap (g x) ∘L fderivWithin 𝕜 g s x :=
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/ContinuousAlternatingMap.lean:107:    |>.fderivWithin hs
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/ContinuousAlternatingMap.lean:113:        (f x).fderivCompContinuousLinearMap (g x) ∘L fderiv 𝕜 g x :=
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/ContinuousAlternatingMap.lean:114:  hf.hasFDerivAt.continuousAlternatingMapCompContinuousLinearMap (hg.hasFDerivAt) |>.fderiv
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/ContinuousAlternatingMap.lean:210:    |>.fderivWithin hs
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/ContinuousAlternatingMap.lean:224:  hf.hasFDerivAt.continuousAlternatingMap_apply (fun i ↦ (hg i).hasFDerivAt) |>.fderiv
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean:99:  (hc.hasFDerivWithinAt.smul hf.hasFDerivWithinAt).fderivWithin hxs
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean:105:  (hc.hasFDerivWithinAt.smul hf.hasFDerivWithinAt).fderivWithin hxs
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean:109:  (hc.hasFDerivAt.smul hf.hasFDerivAt).fderiv
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean:113:  (hc.hasFDerivAt.smul hf.hasFDerivAt).fderiv
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean:151:  (hc.hasFDerivWithinAt.smul_const f).fderivWithin hxs
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean:155:  (hc.hasFDerivAt.smul_const f).fderiv
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean:233:  (ha.hasFDerivWithinAt.mul' hb.hasFDerivWithinAt).fderivWithin hxs
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean:239:  (ha.hasFDerivWithinAt.mul' hb.hasFDerivWithinAt).fderivWithin hxs
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean:245:  (hc.hasFDerivWithinAt.mul hd.hasFDerivWithinAt).fderivWithin hxs
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean:251:  (hc.hasFDerivWithinAt.mul hd.hasFDerivWithinAt).fderivWithin hxs
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean:255:  (ha.hasFDerivAt.mul' hb.hasFDerivAt).fderiv
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean:259:  (ha.hasFDerivAt.mul' hb.hasFDerivAt).fderiv
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean:263:  (hc.hasFDerivAt.mul hd.hasFDerivAt).fderiv
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean:267:  (hc.hasFDerivAt.mul hd.hasFDerivAt).fderiv
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean:326:  (ha.hasFDerivWithinAt.mul_const' b).fderivWithin hxs
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean:331:  (hc.hasFDerivWithinAt.mul_const d).fderivWithin hxs
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean:335:  (ha.hasFDerivAt.mul_const' b).fderiv
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean:339:  (hc.hasFDerivAt.mul_const d).fderiv
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean:377:  (ha.hasFDerivWithinAt.const_mul b).fderivWithin hxs
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean:381:  (ha.hasFDerivAt.const_mul b).fderiv
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean:502:    (hasStrictFDerivAt_pi.mpr fun i ↦ h (l.get i) (List.getElem_mem ..)) :) ?_
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean:541:  (HasFDerivAt.list_prod' fun i hi ↦ (h i hi).hasFDerivAt).fderiv
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean:548:  (HasFDerivWithinAt.list_prod' fun i hi ↦ (h i hi).hasFDerivWithinAt).fderivWithin hxs
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean:558:      hasStrictFDerivAt_pi.mpr fun i ↦ h (Subtype.val i) i.prop :)
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean:589:  (HasFDerivAt.multiset_prod fun i hi ↦ (h i hi).hasFDerivAt).fderiv
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean:595:  (HasFDerivWithinAt.multiset_prod fun i hi ↦ (h i hi).hasFDerivWithinAt).fderivWithin hxs
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean:601:    (hasStrictFDerivAt_finset_prod.comp x <| hasStrictFDerivAt_pi.mpr fun i ↦ hg i i.prop)
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean:621:  (HasFDerivAt.finset_prod fun i hi ↦ (hg i hi).hasFDerivAt).fderiv
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean:627:  (HasFDerivWithinAt.finset_prod fun i hi ↦ (hg i hi).hasFDerivWithinAt).fderivWithin hxs
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean:648:    (inverse_add_norm_diff_second_order x).trans_isLittleO (isLittleO_norm_pow_id one_lt_two)
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean:649:  simpa [hasFDerivAt_iff_isLittleO_nhds_zero] using this
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean:666:  (hasFDerivAt_ringInverse x).fderiv
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean:738:  (hasFDerivAt_inv' hx).fderiv
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean:743:  rw [DifferentiableAt.fderivWithin (differentiableAt_inv hx) hxs]
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Congr.lean:107:  simp only [hasFDerivAtFilter_iff_isLittleOTVS]
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Congr.lean:108:  exact isLittleOTVS_congr (h₀.mono fun y hy => by simp_all [Prod.map]) .rfl
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Congr.lean:213:theorem DifferentiableWithinAt.fderivWithin_congr_mono
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Congr.lean:218:  (HasFDerivWithinAt.congr_mono h.hasFDerivWithinAt hs hx h₁).fderivWithin hxt
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Congr.lean:221:theorem Filter.EventuallyEq.fderivWithin_eq (hs : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x) :
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Congr.lean:226:theorem Filter.EventuallyEq.fderivWithin_eq_of_mem (hs : f₁ =ᶠ[𝓝[s] x] f) (hx : x ∈ s) :
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Congr.lean:228:  hs.fderivWithin_eq (mem_of_mem_nhdsWithin hx hs :)
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Congr.lean:230:theorem Filter.EventuallyEq.fderivWithin_eq_of_insert (hs : f₁ =ᶠ[𝓝[insert x s] x] f) :
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Congr.lean:232:  apply Filter.EventuallyEq.fderivWithin_eq (nhdsWithin_mono _ (subset_insert x s) hs)
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Congr.lean:235:theorem Filter.EventuallyEq.fderivWithin' (hs : f₁ =ᶠ[𝓝[s] x] f) (ht : t ⊆ s) :
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Congr.lean:239:      EventuallyEq.fderivWithin_eq (hs.filter_mono <| nhdsWithin_mono _ ht)
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Congr.lean:242:protected theorem Filter.EventuallyEq.fderivWithin (hs : f₁ =ᶠ[𝓝[s] x] f) :
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Congr.lean:244:  hs.fderivWithin' Subset.rfl
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Congr.lean:246:theorem Filter.EventuallyEq.fderivWithin_eq_of_nhds (h : f₁ =ᶠ[𝓝 x] f) :
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Congr.lean:248:  (h.filter_mono nhdsWithin_le_nhds).fderivWithin_eq h.self_of_nhds
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Congr.lean:252:  (hs.eventuallyEq.filter_mono inf_le_right).fderivWithin_eq hx
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Congr.lean:258:theorem Filter.EventuallyEq.fderiv_eq (h : f₁ =ᶠ[𝓝 x] f) : fderiv 𝕜 f₁ x = fderiv 𝕜 f x := by
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Congr.lean:259:  rw [← fderivWithin_univ, ← fderivWithin_univ, h.fderivWithin_eq_of_nhds]
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Congr.lean:261:protected theorem Filter.EventuallyEq.fderiv (h : f₁ =ᶠ[𝓝 x] f) : fderiv 𝕜 f₁ =ᶠ[𝓝 x] fderiv 𝕜 f :=
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Congr.lean:262:  h.eventuallyEq_nhds.mono fun _ h => h.fderiv_eq
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Extend.lean:46:    rw [hasFDerivWithinAt_iff_isLittleO, Asymptotics.isLittleO_iff]
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Extend.lean:76:          rw [DifferentiableAt.fderivWithin _ (op.uniqueDiffOn z z_in)]
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/RestrictScalars.lean:48:  .of_isLittleO h.isLittleO
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/RestrictScalars.lean:86:  exact .of_isLittleO h.isLittleO
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/RestrictScalars.lean:92:  exact .of_isLittleO h.isLittleO
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/RestrictScalars.lean:94:theorem DifferentiableAt.fderiv_restrictScalars (h : DifferentiableAt 𝕜' f x) :
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/RestrictScalars.lean:96:  (h.hasFDerivAt.restrictScalars 𝕜).fderiv
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/RestrictScalars.lean:101:  ((hf.hasFDerivWithinAt.restrictScalars 𝕜).fderivWithin hs).symm
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/ContinuousMultilinearMap.lean:35:is given by `ContinuousMultilinearMap.fderivCompContinuousLinearMap`.
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/ContinuousMultilinearMap.lean:65:        fg.1.fderivCompContinuousLinearMap fg.2 ∘L .snd _ _ _)
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/ContinuousMultilinearMap.lean:75:        (f x).fderivCompContinuousLinearMap (g · x) ∘L .pi g') x :=
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/ContinuousMultilinearMap.lean:77:    |>.comp x (hf.prodMk (hasStrictFDerivAt_pi.2 hg))
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/ContinuousMultilinearMap.lean:83:        (f x).fderivCompContinuousLinearMap (g · x) ∘L .pi g') x := by
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/ContinuousMultilinearMap.lean:91:        (f x).fderivCompContinuousLinearMap (g · x) ∘L .pi g') s x := by
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/ContinuousMultilinearMap.lean:100:        (f x).fderivCompContinuousLinearMap (g · x) ∘L .pi fun i ↦ fderivWithin 𝕜 (g i) s x :=
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/ContinuousMultilinearMap.lean:102:    (fun i ↦ (hg i).hasFDerivWithinAt) |>.fderivWithin hs
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/ContinuousMultilinearMap.lean:108:        (f x).fderivCompContinuousLinearMap (g · x) ∘L .pi fun i ↦ fderiv 𝕜 (g i) x :=
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/ContinuousMultilinearMap.lean:110:    (fun i ↦ (hg i).hasFDerivAt) |>.fderiv
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Defs.lean:107:@[mk_iff hasFDerivAtFilter_iff_isLittleOTVS]
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Defs.lean:109:  of_isLittleOTVS ::
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Defs.lean:110:    isLittleOTVS : (fun p ↦ f p.1 - f p.2 - f' (p.1 - p.2)) =o[𝕜; L] (fun p ↦ p.1 - p.2)
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Defs.lean:178:theorem hasFDerivAt_iff_isLittleOTVS :
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Defs.lean:180:  simp [HasFDerivAt, hasFDerivAtFilter_iff_isLittleOTVS, Function.comp_def]
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Defs.lean:182:alias ⟨HasFDerivAt.isLittleOTVS, HasFDerivAt.of_isLittleOTVS⟩ := hasFDerivAt_iff_isLittleOTVS
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Defs.lean:184:theorem hasFDerivWithinAt_iff_isLittleOTVS :
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Defs.lean:187:  simp [HasFDerivWithinAt, hasFDerivAtFilter_iff_isLittleOTVS, Function.comp_def]
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Defs.lean:189:alias ⟨HasFDerivWithinAt.isLittleOTVS, HasFDerivWithinAt.of_isLittleOTVS⟩ :=
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Defs.lean:190:  hasFDerivWithinAt_iff_isLittleOTVS
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Defs.lean:192:theorem hasStrictFDerivAt_iff_isLittleOTVS :
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Defs.lean:195:  hasFDerivAtFilter_iff_isLittleOTVS ..
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Defs.lean:217:theorem hasFDerivAtFilter_iff_isLittleO {L : Filter (E × E)} :
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Defs.lean:219:  (hasFDerivAtFilter_iff_isLittleOTVS ..).trans isLittleOTVS_iff_isLittleO
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Defs.lean:221:alias ⟨HasFDerivAtFilter.isLittleO, HasFDerivAtFilter.of_isLittleO⟩ :=
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Defs.lean:222:  hasFDerivAtFilter_iff_isLittleO
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Defs.lean:224:theorem hasFDerivAt_iff_isLittleO :
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Defs.lean:226:  hasFDerivAt_iff_isLittleOTVS.trans isLittleOTVS_iff_isLittleO
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Defs.lean:228:alias ⟨HasFDerivAt.isLittleO, HasFDerivAt.of_isLittleO⟩ := hasFDerivAt_iff_isLittleO
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Defs.lean:230:theorem hasFDerivWithinAt_iff_isLittleO :
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Defs.lean:233:  hasFDerivWithinAt_iff_isLittleOTVS.trans isLittleOTVS_iff_isLittleO
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Defs.lean:235:alias ⟨HasFDerivWithinAt.isLittleO, HasFDerivWithinAt.of_isLittleO⟩ :=
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Defs.lean:236:  hasFDerivWithinAt_iff_isLittleO
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Defs.lean:238:theorem hasStrictFDerivAt_iff_isLittleO :
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Defs.lean:241:  (hasStrictFDerivAt_iff_isLittleOTVS ..).trans isLittleOTVS_iff_isLittleO
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Defs.lean:243:alias ⟨HasStrictFDerivAt.isLittleO, HasStrictFDerivAt.of_isLittleO⟩ :=
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Defs.lean:244:  hasStrictFDerivAt_iff_isLittleO
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Comp.lean:52:  refine .of_isLittleOTVS <| calc
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Comp.lean:60:      hg.isLittleOTVS.comp_tendsto hL
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Comp.lean:64:    _ =o[𝕜; L] (fun p ↦ p.1 - p.2) := hf.isLittleOTVS
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Comp.lean:139:  (hg.hasFDerivWithinAt.comp x hf.hasFDerivWithinAt h).fderivWithin hxs
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Comp.lean:181:    h2g.comp h2f).fderivWithin hxs
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Comp.lean:185:  (hg.hasFDerivAt.comp x hf.hasFDerivAt).fderiv
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Comp.lean:195:  (hg.hasFDerivAt.comp_hasFDerivWithinAt x hf.hasFDerivWithinAt).fderivWithin hxs
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Linear.lean:45:  .of_isLittleOTVS <| (IsLittleOTVS.zero _ _).congr_left fun x => by
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Linear.lean:80:  f.hasFDerivAt.fderiv
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Linear.lean:84:  rw [DifferentiableAt.fderivWithin f.differentiableAt hxs]
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Linear.lean:85:  exact f.fderiv
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Linear.lean:125:  HasFDerivAt.fderiv h.hasFDerivAt
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Linear.lean:129:  rw [DifferentiableAt.fderivWithin h.differentiableAt hxs]
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Linear.lean:130:  exact h.fderiv
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Norm.lean:29:* `DifferentiableAt.fderiv_norm_self`: if the norm is differentiable at `x`,
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Norm.lean:156:theorem DifferentiableAt.fderiv_norm_self {x : E} (h : DifferentiableAt ℝ (‖·‖) x) :
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Norm.lean:174:  · simp_rw [(hasFDerivAt_of_subsingleton _ _).fderiv, smul_zero]
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Norm.lean:179:      · rw [(hd.hasFDerivAt.hasFDerivAt_norm_smul ht).fderiv]
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Norm.lean:198:    1 * ‖x‖ = fderiv ℝ (‖·‖) x x := by rw [one_mul, h.fderiv_norm_self]
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Pow.lean:159:  hf.hasFDerivAt.pow' n |>.fderiv
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Pow.lean:175:  hf.hasFDerivWithinAt.pow' n |>.fderivWithin hxs
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Pow.lean:233:  hf.hasFDerivAt.pow n |>.fderiv
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Pow.lean:246:  hf.hasFDerivWithinAt.pow n |>.fderivWithin hxs
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/CompCLM.lean:91:  (hc.hasFDerivWithinAt.clm_comp hd.hasFDerivWithinAt).fderivWithin hxs
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/CompCLM.lean:97:  (hc.hasFDerivAt.clm_comp hd.hasFDerivAt).fderiv
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/CompCLM.lean:141:  (hc.hasFDerivWithinAt.clm_apply hu.hasFDerivWithinAt).fderivWithin hxs
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/CompCLM.lean:145:  (hc.hasFDerivAt.clm_apply hu.hasFDerivAt).fderiv
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/CompCLM.lean:182:  (hc.hasFDerivWithinAt.continuousMultilinear_apply_const u).fderivWithin hxs
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/CompCLM.lean:186:  (hc.hasFDerivAt.continuousMultilinear_apply_const u).fderiv
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/CompCLM.lean:271:  (hc.hasFDerivWithinAt.continuousAlternatingMap_apply_const u).fderivWithin hxs
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/CompCLM.lean:275:  (hc.hasFDerivAt.continuousAlternatingMap_apply_const u).fderiv
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/DifferentialForm/Basic.lean:151:  simp only [extDerivWithin, alternatizeUncurryFin, hs.fderivWithin_eq hx]
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/DifferentialForm/Basic.lean:214:      refine (hω.fderivWithin_right hs ?_ h'x).differentiableWithinAt one_ne_zero
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/DifferentialForm/Basic.lean:217:      this.hasFDerivWithinAt |>.fderivWithin (hs.uniqueDiffWithinAt h'x)
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/DifferentialForm/Basic.lean:249:    (hf.fderivWithin_right hs (le_minSmoothness.trans hr) hxs).differentiableWithinAt one_ne_zero
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/Rademacher.lean:241:  · exact ((g_comp.fderiv ℝ).comp_left rfl).mul_right
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/Rademacher.lean:270:  rw [hasFDerivAt_iff_isLittleO_nhds_zero, isLittleO_iff]
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/Rademacher.lean:283:    exact hasLineDerivAt_iff_isLittleO_nhds_zero.1 (hL v (hqs hv))
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/SmoothSeries.lean:167:  (hasFDerivAt_tsum hu (fun n x => (hf n x).hasFDerivAt) hf' hf0 _).fderiv
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/LineDeriv/Basic.lean:151:theorem hasLineDerivAt_iff_isLittleO_nhds_zero :
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/LineDeriv/Basic.lean:154:  simp only [HasLineDerivAt, hasDerivAt_iff_isLittleO_nhds_zero, zero_add, zero_smul, add_zero]
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/MeanValue.lean:651:lemma isLittleO_pow_succ {x₀ : E} {n : ℕ} (hs : Convex ℝ s) (hx₀s : x₀ ∈ s)
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/MeanValue.lean:654:  rw [Asymptotics.isLittleO_iff] at hf' ⊢
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/MeanValue.lean:672:theorem isLittleO_pow_succ_real {f f' : ℝ → E} {x₀ : ℝ} {n : ℕ} {s : Set ℝ}
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/MeanValue.lean:676:  have h := hs.isLittleO_pow_succ hx₀s hff' ?_ (n := n)
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/MeanValue.lean:677:  · rw [Asymptotics.isLittleO_iff] at h ⊢
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/MeanValue.lean:679:  · rw [Asymptotics.isLittleO_iff] at hf' ⊢
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/MeanValue.lean:807:  rw [hasStrictFDerivAt_iff_isLittleO, isLittleO_iff]
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FormalMultilinearSeries.lean:193:series that sums to the derivative of `p.sum`, see `HasFPowerSeriesOnBall.fderiv`. -/
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Operations.lean:72:      hasFDerivWithinAt_pi.2 fun i => (h i).fderivWithin m hm x hx
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Operations.lean:899:    exact f.analyticAt_symm ha hf.analyticAt hf₀'.fderiv
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Operations.lean:1037:        (h.fderivWithin m hm x hx).restrictScalars 𝕜 :)
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Deriv.lean:83:    (H.fderivWithin_right hs hmn hx) (fun _ _ ↦ trivial)
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/RCLike.lean:159:  obtain ⟨C, hC⟩ := (hf.fderiv 𝕂).exists_bound_of_continuous (h'f.continuous_fderiv hn)
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean:652:      ((Hp.mono ho).fderivWithin m (mod_cast lt_add_one m) x ⟨hx, xo⟩).congr
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean:769:  apply (((h.of_le this).ftaylorSeriesWithin hs).fderivWithin m ?_ x hx).differentiableWithinAt
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean:851:      ((hff' y (ho hy)).mono ho).fderivWithin (hs.inter o_open y hy)
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean:854:  | ω => exact (H.analyticOn.fderivWithin hs).contDiffOn hs (n := ω) x hx
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean:866:  exact (h1 x hx).congr_of_mem (fun y hy => (h2 y hy).fderivWithin (hs y hy)) hx
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean:887:protected theorem ContDiffOn.fderivWithin (hf : ContDiffOn 𝕜 n f s) (hs : UniqueDiffOn 𝕜 s)
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean:891:theorem ContDiffOn.fderiv_of_isOpen (hf : ContDiffOn 𝕜 n f s) (hs : IsOpen s) (hmn : m + 1 ≤ n) :
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean:893:  (hf.fderivWithin hs.uniqueDiffOn hmn).congr fun _ hx => (fderivWithin_of_isOpen hs hx).symm
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/InverseFunctionTheorem/FDeriv.lean:79:  have := hf.isLittleO.def hc
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Bounds.lean:72:          IH _ (hf.of_le (Nat.cast_le.2 (Nat.le_succ n))) (hg.fderivWithin hs In)
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Bounds.lean:90:          IH _ (hf.fderivWithin hs In) (hg.of_le (Nat.cast_le.2 (Nat.le_succ n)))
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Bounds.lean:104:      exact B.fderivWithin_of_bilinear (hf.differentiableOn (by positivity) y hy)
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Bounds.lean:109:        (hf.of_le (Nat.cast_le.2 (Nat.le_succ n))) (hg.fderivWithin hs In)
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Bounds.lean:111:      (B.precompL Du).isBoundedBilinearMap.contDiff.comp₂_contDiffOn (hf.fderivWithin hs In)
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Bounds.lean:378:    · apply hg.fderivWithin ht
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Bounds.lean:420:        apply hg.fderivWithin ht
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Bounds.lean:423:        apply hf.fderivWithin hs
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/LocalExtr/Basic.lean:119:theorem IsLocalMaxOn.fderivWithin_nonpos (h : IsLocalMaxOn f s a)
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/LocalExtr/Basic.lean:135:theorem IsLocalMaxOn.fderivWithin_eq_zero (h : IsLocalMaxOn f s a)
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/LocalExtr/Basic.lean:151:theorem IsLocalMinOn.fderivWithin_nonneg (h : IsLocalMinOn f s a)
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/LocalExtr/Basic.lean:167:theorem IsLocalMinOn.fderivWithin_eq_zero (h : IsLocalMinOn f s a)
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/LocalExtr/Basic.lean:183:theorem IsLocalMin.fderiv_eq_zero (h : IsLocalMin f a) : fderiv ℝ f a = 0 := by
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/LocalExtr/Basic.lean:193:theorem IsLocalMax.fderiv_eq_zero (h : IsLocalMax f a) : fderiv ℝ f a = 0 := by
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/LocalExtr/Basic.lean:203:theorem IsLocalExtr.fderiv_eq_zero (h : IsLocalExtr f a) : fderiv ℝ f a = 0 :=
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/LocalExtr/Basic.lean:204:  h.elim IsLocalMin.fderiv_eq_zero IsLocalMax.fderiv_eq_zero
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Comp.lean:622:theorem ContDiffWithinAt.fderivWithin'' {f : E → F → G} {g : E → F} {t : Set F}
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Comp.lean:634:    exact fun y hy h2y => (hvf' y hy).fderivWithin h2y
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Comp.lean:641:    exact fun y hy h2y => (hvf' y hy).fderivWithin h2y
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Comp.lean:647:/-- A special case of `ContDiffWithinAt.fderivWithin''` where we require that `s ⊆ g⁻¹(t)`. -/
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Comp.lean:648:theorem ContDiffWithinAt.fderivWithin' {f : E → F → G} {g : E → F} {t : Set F}
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Comp.lean:653:  hf.fderivWithin'' hg ht hmn <| mem_of_superset self_mem_nhdsWithin <| image_subset_iff.mpr hst
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Comp.lean:655:/-- A special case of `ContDiffWithinAt.fderivWithin'` where we require that `x₀ ∈ s` and there
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Comp.lean:657:protected theorem ContDiffWithinAt.fderivWithin {f : E → F → G} {g : E → F} {t : Set F}
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Comp.lean:662:  refine hf.fderivWithin' hg ?_ hmn hst
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Comp.lean:667:theorem ContDiffWithinAt.fderivWithin_apply {f : E → F → G} {g k : E → F} {t : Set F}
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Comp.lean:673:    ((hf.fderivWithin hg ht hmn hx₀ hst).prodMk hk)
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Comp.lean:676:theorem ContDiffWithinAt.fderivWithin_right (hf : ContDiffWithinAt 𝕜 n f s x₀)
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Comp.lean:679:  ContDiffWithinAt.fderivWithin
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Comp.lean:684:theorem ContDiffWithinAt.fderivWithin_right_apply
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Comp.lean:689:  ContDiffWithinAt.fderivWithin_apply
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Comp.lean:693:-- TODO: can we make a version of `ContDiffWithinAt.fderivWithin` for iterated derivatives?
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Comp.lean:704:    exact ((hi hmn).fderivWithin_right hs le_rfl hx₀s).continuousLinearMap_comp
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Comp.lean:709:protected theorem ContDiffAt.fderiv {f : E → F → G} {g : E → F}
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Comp.lean:713:  refine (ContDiffWithinAt.fderivWithin hf.contDiffWithinAt hg.contDiffWithinAt uniqueDiffOn_univ
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Comp.lean:718:protected theorem ContDiffAt.fderiv_succ {f : E → F → G} {g : E → F}
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Comp.lean:721:  ContDiffAt.fderiv hf hg (le_refl _)
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Comp.lean:724:theorem ContDiffAt.fderiv_right (hf : ContDiffAt 𝕜 n f x₀) (hmn : m + 1 ≤ n) :
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Comp.lean:726:  ContDiffAt.fderiv (ContDiffAt.comp (x₀, x₀) hf contDiffAt_snd) contDiffAt_id hmn
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Comp.lean:728:theorem ContDiffAt.fderiv_right_succ (hf : ContDiffAt 𝕜 (n + 1) f x₀) :
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Comp.lean:730:  ContDiffAt.fderiv (ContDiffAt.comp (x₀, x₀) hf contDiffAt_snd) contDiffAt_id (le_refl (n + 1))
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Comp.lean:738:protected theorem ContDiff.fderiv {f : E → F → G} {g : E → F}
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Comp.lean:741:  contDiff_iff_contDiffAt.mpr fun _ => hf.contDiffAt.fderiv hg.contDiffAt hnm
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Comp.lean:744:protected theorem ContDiff.fderiv_succ {f : E → F → G} {g : E → F}
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Comp.lean:747:  contDiff_iff_contDiffAt.mpr fun _ => hf.contDiffAt.fderiv hg.contDiffAt (le_refl (n + 1))
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Comp.lean:750:theorem ContDiff.fderiv_right (hf : ContDiff 𝕜 n f) (hmn : m + 1 ≤ n) :
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Comp.lean:752:  contDiff_iff_contDiffAt.mpr fun _x => hf.contDiffAt.fderiv_right hmn
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Comp.lean:764:theorem Continuous.fderiv {f : E → F → G} {g : E → F}
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Comp.lean:767:  (hf.fderiv (contDiff_zero.mpr hg) hn).continuous
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Comp.lean:770:theorem Continuous.fderiv_one {f : E → F → G} {g : E → F}
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Comp.lean:772:    Continuous fun x => _root_.fderiv 𝕜 (f x) (g x) :=
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Comp.lean:773:  (hf.fderiv (contDiff_zero.mpr hg) (le_refl 1)).continuous
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Comp.lean:776:protected theorem Differentiable.fderiv_two {f : E → F → G} {g : E → F}
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Comp.lean:780:    (contDiff_iff_contDiffAt.mpr fun _ => hf.contDiffAt.fderiv hg.contDiffAt (le_refl 2))
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Comp.lean:784:theorem ContDiff.fderiv_apply {f : E → F → G} {g k : E → F}
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Comp.lean:787:  (hf.fderiv hg hnm).clm_apply hk
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Comp.lean:793:  ((hf.fderivWithin hs hmn).comp contDiffOn_fst (prod_subset_preimage_fst _ _)).clm_apply
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Comp.lean:813:  hf.fderivWithin_right (m := 0) hs (by simpa [ENat.one_le_iff_ne_zero_withTop]) hx
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Comp.lean:818:  hf.fderiv_right (m := 0) (by simpa [ENat.one_le_iff_ne_zero_withTop]) |>.continuousAt
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/LagrangeMultipliers.lean:115:  rcases hextr.exists_linear_map_of_hasStrictFDerivAt (hasStrictFDerivAt_pi.2 fun i => hf' i)
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Convolution.lean:83:  have hK' : IsCompact K' := (hcg.fderiv 𝕜).isCompact.neg.add (isCompact_closedBall x₀ 1)
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Convolution.lean:86:      (hcg.fderiv 𝕜).convolution_integrand_bound_right L' (hg.continuous_fderiv one_ne_zero)
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Convolution.lean:119:  rw [convolution_precompR_apply L hf (hcg.fderiv 𝕜) (hg.continuous_fderiv one_ne_zero)]
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Convolution.lean:157:    refine (hasFDerivAt_zero_of_eventually_const 0 ?_).fderiv
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Convolution.lean:314:        exact (A (p, x) hp).fderiv
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Convolution.lean:317:        apply (hasFDerivAt_zero_of_eventually_const (0 : E') _).fderiv
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/VectorField.lean:230:    (hf.fderivWithin_right hs (by decide) hxs).differentiableWithinAt one_ne_zero
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/VectorField.lean:276:  · exact ContDiffWithinAt.clm_apply (hW.fderivWithin_right hs hmn hx)
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/VectorField.lean:278:  · exact ContDiffWithinAt.clm_apply (hV.fderivWithin_right hs hmn hx)
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/VectorField.lean:351:  simp [lieBracketWithin, hV.fderivWithin_congr_mono, hW.fderivWithin_congr_mono, hVs, hVx,
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/VectorField.lean:357:  simp only [lieBracketWithin, hV.fderivWithin_eq hxV, hW.fderivWithin_eq hxW, hxV, hxW]
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/VectorField.lean:371:  filter_upwards [hV.fderivWithin' ht (𝕜 := 𝕜), hW.fderivWithin' ht (𝕜 := 𝕜), hV, hW]
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/VectorField.lean:428:    have := hV.fderivWithin_right_apply (hU.of_le one_le_two) hs le_rfl hx
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/VectorField.lean:435:    exact (hU.fderivWithin_right hs le_rfl hx).differentiableWithinAt one_ne_zero
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/VectorField.lean:554:      (h'f.fderivWithin_right (m := 1) hs le_rfl hx).continuousWithinAt
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/VectorField.lean:563:      h'f.fderivWithin_right (m := 1) hs le_rfl hx
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/VectorField.lean:578:    rw [ContinuousLinearMap.fderivWithin_of_bilinear _ (hN.differentiableWithinAt one_ne_zero)
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/VectorField.lean:584:  simp only [ContinuousLinearMap.comp_neg, eN.fderivWithin_eq e'N]
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/VectorField.lean:633:    apply Filter.EventuallyEq.fderivWithin_eq_of_mem _ hx
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/VectorField.lean:637:    apply Filter.EventuallyEq.fderivWithin_eq_of_mem _ hx
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/FTaylorSeries.lean:152:  refine ⟨fun x hx => ?_, h.fderivWithin, h.cont⟩
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/FTaylorSeries.lean:161:    refine ((hp.fderivWithin m hm x hx).congr' (hpq m hm.le).symm hx).congr_fderiv ?_
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/FTaylorSeries.lean:168:  ⟨fun x hx => h.zero_eq x (hst hx), fun m hm x hx => (h.fderivWithin m hm x (hst hx)).mono hst,
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/FTaylorSeries.lean:173:  ⟨h.zero_eq, fun k hk x hx => h.fderivWithin k (lt_of_lt_of_le hk hmn) x hx, fun k hk =>
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/FTaylorSeries.lean:200:      apply (H m.succ).fderivWithin m (by norm_cast; lia)
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/FTaylorSeries.lean:230:  convert h.fderivWithin _ this x hx
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/FTaylorSeries.lean:268:      h.fderivWithin _ (mod_cast lt_add_one n), h.cont (n + 1) le_rfl⟩
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/FTaylorSeries.lean:274:      · exact h.1.fderivWithin m (mod_cast h')
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/FTaylorSeries.lean:299:    convert H.fderivWithin _ A x hx
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/FTaylorSeries.lean:320:    refine ⟨H.zero_eq, H.fderivWithin 0 (Nat.cast_lt.2 (Nat.succ_pos n)), ?_⟩
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/FTaylorSeries.lean:333:            ((p x).shift m.succ).curryLeft s x := Htaylor.fderivWithin _ A x hx
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/FTaylorSeries.lean:537:    have : fderivWithin 𝕜 _ t =ᶠ[𝓝[s] x] fderivWithin 𝕜 _ t := ihn.fderivWithin' ht
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/FTaylorSeries.lean:583:    rw [(ihn hy).fderivWithin_eq_of_nhds, fderivWithin_congr_set' _ hy]
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/FTaylorSeries.lean:644:      (h.fderivWithin m A x hx).congr (fun y hy => (IH (le_of_lt A) hy).symm)
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/FTaylorSeries.lean:646:    rw [iteratedFDerivWithin_succ_eq_comp_left, Function.comp_apply, this.fderivWithin (hs x hx)]
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/FTaylorSeries.lean:711:lemma HasFTaylorSeriesUpTo.fderiv_eq (h : HasFTaylorSeriesUpTo n f p)
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/FTaylorSeries.lean:713:  h.fderiv m hmn x |>.fderiv
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/FTaylorSeries.lean:723:      exact H.fderivWithin m hm x (mem_univ x)
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/FTaylorSeries.lean:732:      exact H.fderiv m hm x
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/FTaylorSeries.lean:798:    rw [funext <| hf.fderiv_eq (mod_cast hl)]
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/FTaylorSeries.lean:930:    apply Filter.EventuallyEq.fderiv_eq
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/Gradient/Basic.lean:213:theorem hasGradientAtFilter_iff_isLittleO :
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/Gradient/Basic.lean:216:  hasFDerivAtFilter_iff_isLittleO.trans <| by simp [Function.comp_def]
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/Gradient/Basic.lean:218:theorem hasGradientWithinAt_iff_isLittleO :
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/Gradient/Basic.lean:221:  hasGradientAtFilter_iff_isLittleO
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/Gradient/Basic.lean:228:theorem hasGradientAt_iff_isLittleO : HasGradientAt f f' x ↔
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/Gradient/Basic.lean:230:  hasGradientAtFilter_iff_isLittleO
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/Gradient/Basic.lean:249:theorem hasGradientAt_iff_isLittleO_nhds_zero : HasGradientAt f f' x ↔
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/Gradient/Basic.lean:251:  hasFDerivAt_iff_isLittleO_nhds_zero
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/Gradient/Basic.lean:257:lemma HasGradientWithinAt.fderivWithin_apply
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/Gradient/Basic.lean:260:  rw [h.hasFDerivWithinAt.fderivWithin hs, toDual_apply_apply]
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/Gradient/Basic.lean:262:lemma HasGradientAt.fderiv_apply (h : HasGradientAt f f' x) : fderiv 𝕜 f x y = ⟪f', y⟫ := by
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/Gradient/Basic.lean:263:  rw [h.hasFDerivAt.fderiv, toDual_apply_apply]
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/Gradient/Basic.lean:268:  rw [h.hasGradientWithinAt.fderivWithin_apply hs]
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/Gradient/Basic.lean:271:  rw [h.hasGradientAt.fderiv_apply]
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/Gradient/Basic.lean:279:  rw [← inner_conj_symm, h.hasGradientAt.fderiv_apply]
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/Gradient/Basic.lean:323:  rwa [Filter.EventuallyEq.fderiv_eq]
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/RestrictScalars.lean:37:  rw [fderiv_comp_fderivWithin _ (by fun_prop) (h.restrictScalars 𝕜) hs, ContinuousLinearMap.fderiv]
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/RestrictScalars.lean:65:    rw [← (h₁a.fderivWithin' (by tauto)).eq_of_nhdsWithin h₄a,
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiffHolder/Pointwise.lean:241:  contDiffAt := hf.contDiffAt.fderiv_right (mod_cast hl)
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiffHolder/Pointwise.lean:254:    simpa +unfoldPartialApp [iteratedFDeriv_succ_eq_comp_left] using (ihm hl).fderiv l.lt_add_one
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Inv.lean:45:    refine .of_isLittleO <| this.congr' ?_ (Eventually.of_forall fun _ => mul_one _)
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Inv.lean:51:  refine (isBigO_refl (fun p : 𝕜 × 𝕜 => p.1 - p.2) _).mul_isLittleO ((isLittleO_one_iff 𝕜).2 ?_)
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Inv.lean:97:  rw [DifferentiableAt.fderivWithin (differentiableAt_inv x_ne_zero) hxs]
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/Conformal/InnerProduct.lean:39:  simp only [conformalAt_iff', h.fderiv]
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/FaaDiBruno.lean:963:theorem taylorComp_sub_taylorComp_isLittleO
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/FaaDiBruno.lean:978:    .prod_left (Asymptotics.isLittleO_pi.2 fun k ↦ hpf k (by grind))
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/FaaDiBruno.lean:979:      (Asymptotics.isLittleO_pi.2 fun k ↦ hqf k (by grind))
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/FaaDiBruno.lean:1082:        hf.fderivWithin (c.partSize i) ((cp i).trans_lt hm) x hx
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/FaaDiBruno.lean:1084:        t (f x) := hg.fderivWithin c.length (cm.trans_lt hm) (f x) (h hx)
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/Conformal/NormedSpace.lean:76:    rwa [hf.fderiv]
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/Taylor.lean:33:* `taylor_isLittleO`: Taylor's theorem using little-o notation
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/Taylor.lean:239:theorem taylor_isLittleO {f : ℝ → E} {x₀ : ℝ} {n : ℕ} {s : Set ℝ}
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/Taylor.lean:244:    simp only [taylor_within_zero_eval, pow_zero, Asymptotics.isLittleO_one_iff]
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/Taylor.lean:252:    convert Convex.isLittleO_pow_succ_real hs hx₀s ?_ (h (hf.derivWithin hs' le_rfl))
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/Taylor.lean:259:theorem taylor_isLittleO_univ {f : ℝ → E} {x₀ : ℝ} {n : ℕ} (hf : ContDiff ℝ n f) :
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/Taylor.lean:261:  simpa using taylor_isLittleO convex_univ (mem_univ x₀) hf.contDiffOn
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/Taylor.lean:268:  have h_isLittleO := (taylor_isLittleO hs hx₀s hf).norm_norm
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/Taylor.lean:269:  rw [Asymptotics.isLittleO_iff_tendsto] at h_isLittleO
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/Taylor.lean:271:    simpa [norm_smul, div_eq_inv_mul] using h_isLittleO
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Polynomial.lean:144:  (p.hasFDerivAt x).fderiv
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Polynomial.lean:149:  (q.hasFDerivAt_aeval x).fderiv
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Polynomial.lean:153:  (p.hasFDerivWithinAt x).fderivWithin hxs
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Polynomial.lean:157:  (q.hasFDerivWithinAt_aeval x).fderivWithin hxs
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Basic.lean:216:    (fun _ : Fin m => E) F G g).hasFDerivAt.comp_hasFDerivWithinAt x (hf.fderivWithin m hm x hx)
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Basic.lean:388:        ((hf.fderivWithin m hm (g x) hx).comp x g.hasFDerivWithinAt (Subset.refl _))
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Basic.lean:546:        ((hf.fderivWithin m hm x hx).prodMk (hg.fderivWithin m hm x hx))
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Basic.lean:262:theorem hasDerivAtFilter_iff_isLittleO :
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Basic.lean:265:  hasFDerivAtFilter_iff_isLittleO ..
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Basic.lean:272:theorem hasDerivWithinAt_iff_isLittleO :
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Basic.lean:275:  hasFDerivWithinAt_iff_isLittleO
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Basic.lean:277:alias ⟨HasDerivWithinAt.isLittleO, HasDerivWithinAt.of_isLittleO⟩ := hasDerivWithinAt_iff_isLittleO
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Basic.lean:284:theorem hasDerivAt_iff_isLittleO :
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Basic.lean:286:  hasFDerivAt_iff_isLittleO ..
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Basic.lean:288:alias ⟨HasDerivAt.isLittleO, HasDerivAt.of_isLittleO⟩ := hasDerivAt_iff_isLittleO
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Basic.lean:362:theorem hasDerivAt_iff_isLittleO_nhds_zero :
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Basic.lean:364:  hasFDerivAt_iff_isLittleO_nhds_zero
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Basic.lean:479:  rw [h.fderivWithin hxs]
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Basic.lean:623:  rw [hs.fderivWithin_eq hx]
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Basic.lean:646:  rwa [Filter.EventuallyEq.fderiv_eq]

codex
The v4.29 API names that matter are present locally: `hasStrictFDerivAt_pi'`, `hasStrictFDerivAt_pi''`, `hasStrictFDerivAt_pi`, `HasStrictFDerivAt.fun_sum`, `hasStrictFDerivAt_iff_isLittleO`, and the uniqueness route through `.hasFDerivAt.fderiv`. That means you do not need an `isLittleO` proof unless you want to reprove product differentiability from scratch.
exec
/bin/bash -lc "sed -n '340,380p' lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Prod.lean" in /home/ubuntu/workspace/deriv-spec
 succeeded in 0ms:
  and is designed to deduce differentiability of `fun x i ↦ φ i x` from differentiability
  of each `φ i`;
* the version with `'` deals with `Φ : E → Π i, F' i` and `Φ' : E →L[𝕜] Π i, F' i`
  and is designed to deduce differentiability of the components `fun x ↦ Φ x i` from
  differentiability of `Φ`.
-/


variable {ι : Type*} {F' : ι → Type*} [∀ i, NormedAddCommGroup (F' i)]
  [∀ i, NormedSpace 𝕜 (F' i)] {φ : ∀ i, E → F' i} {φ' : ∀ i, E →L[𝕜] F' i} {Φ : E → ∀ i, F' i}
  {Φ' : E →L[𝕜] ∀ i, F' i}

@[simp]
theorem hasFDerivAtFilter_pi' :
    HasFDerivAtFilter Φ Φ' L ↔
      ∀ i, HasFDerivAtFilter (fun x => Φ x i) ((proj i).comp Φ') L := by
  simp [hasFDerivAtFilter_iff_isLittleOTVS, isLittleOTVS_pi]

@[simp]
theorem hasStrictFDerivAt_pi' :
    HasStrictFDerivAt Φ Φ' x ↔ ∀ i, HasStrictFDerivAt (fun x => Φ x i) ((proj i).comp Φ') x :=
  hasFDerivAtFilter_pi'

@[fun_prop]
theorem hasStrictFDerivAt_pi'' (hφ : ∀ i, HasStrictFDerivAt (fun x => Φ x i) ((proj i).comp Φ') x) :
    HasStrictFDerivAt Φ Φ' x := hasStrictFDerivAt_pi'.2 hφ

@[fun_prop]
theorem hasStrictFDerivAt_apply (i : ι) (f : ∀ i, F' i) :
    HasStrictFDerivAt (𝕜 := 𝕜) (fun f : ∀ i, F' i => f i) (proj i) f :=
  (proj (R := 𝕜) (φ := F') i).hasStrictFDerivAt

theorem hasStrictFDerivAt_pi :
    HasStrictFDerivAt (fun x i => φ i x) (ContinuousLinearMap.pi φ') x ↔
      ∀ i, HasStrictFDerivAt (φ i) (φ' i) x :=
  hasStrictFDerivAt_pi'

theorem hasFDerivAtFilter_pi :
    HasFDerivAtFilter (fun x i => φ i x) (ContinuousLinearMap.pi φ') L ↔
      ∀ i, HasFDerivAtFilter (φ i) (φ' i) L :=
  hasFDerivAtFilter_pi'

exec
/bin/bash -lc "sed -n '380,405p' lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Add.lean" in /home/ubuntu/workspace/deriv-spec
 succeeded in 0ms:
end Add

section Sum

/-! ### Derivative of a finite sum of functions -/


variable {ι : Type*} {u : Finset ι} {A : ι → E → F} {A' : ι → E →L[𝕜] F}

@[fun_prop]
theorem HasStrictFDerivAt.fun_sum (h : ∀ i ∈ u, HasStrictFDerivAt (A i) (A' i) x) :
    HasStrictFDerivAt (fun y => ∑ i ∈ u, A i y) (∑ i ∈ u, A' i) x := by
  simp only [hasStrictFDerivAt_iff_isLittleO] at *
  convert IsLittleO.sum h
  simp [Finset.sum_sub_distrib, ContinuousLinearMap.sum_apply]

@[fun_prop]
theorem HasStrictFDerivAt.sum (h : ∀ i ∈ u, HasStrictFDerivAt (A i) (A' i) x) :
    HasStrictFDerivAt (∑ i ∈ u, A i) (∑ i ∈ u, A' i) x := by
  convert HasStrictFDerivAt.fun_sum h; simp

theorem HasFDerivAtFilter.fun_sum (h : ∀ i ∈ u, HasFDerivAtFilter (A i) (A' i) L) :
    HasFDerivAtFilter (fun y => ∑ i ∈ u, A i y) (∑ i ∈ u, A' i) L := by
  simp only [hasFDerivAtFilter_iff_isLittleO] at *
  convert IsLittleO.sum h
  simp [ContinuousLinearMap.sum_apply]

exec
/bin/bash -lc "sed -n '35,55p' lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Bilinear.lean" in /home/ubuntu/workspace/deriv-spec
 succeeded in 0ms:
section BilinearMap

/-! ### Derivative of a bounded bilinear map -/

variable {b : E × F → G} {u : Set (E × F)}

open NormedField

-- TODO: rewrite/golf using analytic functions?
@[fun_prop]
theorem IsBoundedBilinearMap.hasStrictFDerivAt (h : IsBoundedBilinearMap 𝕜 b) (p : E × F) :
    HasStrictFDerivAt b (h.deriv p) p := by
  simp only [hasStrictFDerivAt_iff_isLittleO]
  simp only [← map_add_left_nhds_zero (p, p), isLittleO_map]
  set T := (E × F) × E × F
  calc
    _ = fun x ↦ h.deriv (x.1 - x.2) (x.2.1, x.1.2) := by
      ext ⟨⟨x₁, y₁⟩, ⟨x₂, y₂⟩⟩
      rcases p with ⟨x, y⟩
      simp only [map_sub, deriv_apply, Function.comp_apply, Prod.mk_add_mk, h.add_right, h.add_left,
        Prod.mk_sub_mk, h.map_sub_left, h.map_sub_right, sub_add_sub_cancel]

exec
/bin/bash -lc "rg -n \"alias .*HasStrictFDerivAt.*isLittleO|HasStrictFDerivAt\\.isLittleO|HasStrictFDerivAt\\.of_isLittleO|hasStrictFDerivAt_iff_isLittleO\" lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv -S" in /home/ubuntu/workspace/deriv-spec
 succeeded in 0ms:
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Bilinear.lean:47:  simp only [hasStrictFDerivAt_iff_isLittleO]
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/ContinuousAlternatingMap.lean:51:  · rw [hasStrictFDerivAt_iff_isLittleOTVS] at h ⊢
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Analytic.lean:96:  simpa only [hasStrictFDerivAt_iff_isLittleO, Set.insert_eq_of_mem, Set.mem_univ,
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Add.lean:248:  simp [hasStrictFDerivAt_iff_isLittleO]
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Add.lean:392:  simp only [hasStrictFDerivAt_iff_isLittleO] at *
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Defs.lean:192:theorem hasStrictFDerivAt_iff_isLittleOTVS :
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Defs.lean:238:theorem hasStrictFDerivAt_iff_isLittleO :
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Defs.lean:241:  (hasStrictFDerivAt_iff_isLittleOTVS ..).trans isLittleOTVS_iff_isLittleO
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Defs.lean:243:alias ⟨HasStrictFDerivAt.isLittleO, HasStrictFDerivAt.of_isLittleO⟩ :=
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Defs.lean:244:  hasStrictFDerivAt_iff_isLittleO

exec
/bin/bash -lc "rg -n \"theorem HasStrictFDerivAt\\.mul|protected theorem HasStrictFDerivAt\\.mul|HasStrictFDerivAt.*mul\" lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv -S" in /home/ubuntu/workspace/deriv-spec
 succeeded in 0ms:
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Add.lean:57:theorem HasStrictFDerivAt.const_smul (h : HasStrictFDerivAt f f' x) (c : R) :
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean:59:theorem HasStrictFDerivAt.smul (hc : HasStrictFDerivAt c c' x) (hf : HasStrictFDerivAt f f' x) :
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean:60:    HasStrictFDerivAt (c • f) (c x • f' + c'.smulRight (f x)) x :=
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean:116:theorem HasStrictFDerivAt.smul_const (hc : HasStrictFDerivAt c c' x) (f : F) :
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean:117:    HasStrictFDerivAt (fun y => c y • f) (c'.smulRight f) x := by
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean:170:theorem HasStrictFDerivAt.mul' {x : E} (ha : HasStrictFDerivAt a a' x)
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean:177:theorem HasStrictFDerivAt.mul (hc : HasStrictFDerivAt c c' x) (hd : HasStrictFDerivAt d d' x) :
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean:270:theorem HasStrictFDerivAt.mul_const' (ha : HasStrictFDerivAt a a' x) (b : 𝔸) :
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean:275:theorem HasStrictFDerivAt.mul_const (hc : HasStrictFDerivAt c c' x) (d : 𝔸') :
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean:342:theorem HasStrictFDerivAt.const_mul (ha : HasStrictFDerivAt a a' x) (b : 𝔸) :
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean:551:theorem HasStrictFDerivAt.multiset_prod [DecidableEq ι] {u : Multiset ι} {x : E}
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean:669:    HasStrictFDerivAt Ring.inverse (-mulLeftRight 𝕜 R ↑x⁻¹ ↑x⁻¹) x := by
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean:712:    HasStrictFDerivAt Inv.inv (-mulLeftRight 𝕜 R x⁻¹ x⁻¹) x := by
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Norm.lean:91:theorem HasStrictFDerivAt.hasStrictFDerivAt_norm_smul
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Norm.lean:96:  have h2 : HasStrictFDerivAt (fun y ↦ |t| * ‖y‖) (|t| • f) x := h.const_smul |t|
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Norm.lean:105:theorem HasStrictFDerivAt.hasStrictDerivAt_norm_smul_neg
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Norm.lean:110:theorem HasStrictFDerivAt.hasStrictDerivAt_norm_smul_pos

exec
/bin/bash -lc "rg -n \"def proj|theorem .*proj|ContinuousLinearMap\\.pi|def pi\" lean/.lake/packages/mathlib/Mathlib/Topology/Algebra/Module/Basic.lean lean/.lake/packages/mathlib/Mathlib/Analysis/Normed/Module/Basic.lean lean/.lake/packages/mathlib/Mathlib/LinearAlgebra/Pi.lean -S" in /home/ubuntu/workspace/deriv-spec
 succeeded in 0ms:
lean/.lake/packages/mathlib/Mathlib/LinearAlgebra/Pi.lean:56:def pi (f : (i : ι) → M₂ →ₗ[R] φ i) : M₂ →ₗ[R] (i : ι) → φ i :=
lean/.lake/packages/mathlib/Mathlib/LinearAlgebra/Pi.lean:87:def proj (i : ι) : ((i : ι) → φ i) →ₗ[R] φ i where
lean/.lake/packages/mathlib/Mathlib/LinearAlgebra/Pi.lean:93:theorem coe_proj (i : ι) : ⇑(proj i : ((i : ι) → φ i) →ₗ[R] φ i) = Function.eval i :=
lean/.lake/packages/mathlib/Mathlib/LinearAlgebra/Pi.lean:97:theorem toAddMonoidHom_proj (i : ι) : (proj i).toAddMonoidHom (R := R) = Pi.evalAddMonoidHom φ i :=
lean/.lake/packages/mathlib/Mathlib/LinearAlgebra/Pi.lean:100:theorem proj_apply (i : ι) (b : (i : ι) → φ i) : (proj i : ((i : ι) → φ i) →ₗ[R] φ i) b = b i :=
lean/.lake/packages/mathlib/Mathlib/LinearAlgebra/Pi.lean:104:theorem proj_pi (f : (i : ι) → M₂ →ₗ[R] φ i) (i : ι) : (proj i).comp (pi f) = f i := rfl
lean/.lake/packages/mathlib/Mathlib/LinearAlgebra/Pi.lean:107:theorem pi_proj : pi proj = LinearMap.id (R := R) (M := ∀ i, φ i) := rfl
lean/.lake/packages/mathlib/Mathlib/LinearAlgebra/Pi.lean:110:theorem pi_proj_comp (f : M₂ →ₗ[R] ∀ i, φ i) : pi (proj · ∘ₗ f) = f := rfl
lean/.lake/packages/mathlib/Mathlib/LinearAlgebra/Pi.lean:112:theorem proj_surjective (i : ι) : Surjective (proj i : ((i : ι) → φ i) →ₗ[R] φ i) :=
lean/.lake/packages/mathlib/Mathlib/LinearAlgebra/Pi.lean:115:theorem iInf_ker_proj : (⨅ i, ker (proj i : ((i : ι) → φ i) →ₗ[R] φ i) :
lean/.lake/packages/mathlib/Mathlib/LinearAlgebra/Pi.lean:133:def piMap {ψ : ι → Type*} [∀ i, AddCommMonoid (ψ i)] [∀ i, Module R (ψ i)]
lean/.lake/packages/mathlib/Mathlib/LinearAlgebra/Pi.lean:178:theorem proj_comp_single_same (i : ι) : (proj i).comp (single R φ i) = id :=
lean/.lake/packages/mathlib/Mathlib/LinearAlgebra/Pi.lean:181:theorem proj_comp_single_ne (i j : ι) (h : i ≠ j) : (proj i).comp (single R φ j) = 0 :=
lean/.lake/packages/mathlib/Mathlib/LinearAlgebra/Pi.lean:184:theorem iSup_range_single_le_iInf_ker_proj (I J : Set ι) (h : Disjoint I J) :
lean/.lake/packages/mathlib/Mathlib/LinearAlgebra/Pi.lean:193:theorem iInf_ker_proj_le_iSup_range_single {I : Finset ι} {J : Set ι} (hu : Set.univ ⊆ ↑I ∪ J) :
lean/.lake/packages/mathlib/Mathlib/LinearAlgebra/Pi.lean:209:theorem iSup_range_single_eq_iInf_ker_proj {I J : Set ι} (hd : Disjoint I J)
lean/.lake/packages/mathlib/Mathlib/LinearAlgebra/Pi.lean:350:theorem proj_comp_single (i j : ι) : (proj i).comp (single R φ j) = diag j i := by
lean/.lake/packages/mathlib/Mathlib/LinearAlgebra/Pi.lean:375:def pi (I : Set ι) (p : (i : ι) → Submodule R (φ i)) : Submodule R ((i : ι) → φ i) where
lean/.lake/packages/mathlib/Mathlib/LinearAlgebra/Pi.lean:405:theorem biInf_comap_proj :
lean/.lake/packages/mathlib/Mathlib/LinearAlgebra/Pi.lean:410:theorem iInf_comap_proj :
lean/.lake/packages/mathlib/Mathlib/LinearAlgebra/Pi.lean:465:def piCongrRight (e : (i : ι) → φ i ≃ₗ[R] ψ i) : ((i : ι) → φ i) ≃ₗ[R] (i : ι) → ψ i :=
lean/.lake/packages/mathlib/Mathlib/LinearAlgebra/Pi.lean:495:def piCongrLeft' (e : ι ≃ ι') : ((i' : ι) → φ i') ≃ₗ[R] (i : ι') → φ <| e.symm i :=
lean/.lake/packages/mathlib/Mathlib/LinearAlgebra/Pi.lean:504:def piCongrLeft (e : ι' ≃ ι) : ((i' : ι') → φ (e i')) ≃ₗ[R] (i : ι) → φ i :=
lean/.lake/packages/mathlib/Mathlib/LinearAlgebra/Pi.lean:508:def piCurry {ι : Type*} {κ : ι → Type*} (α : ∀ i, κ i → Type*)
lean/.lake/packages/mathlib/Mathlib/LinearAlgebra/Pi.lean:528:def piOptionEquivProd {ι : Type*} {M : Option ι → Type*} [(i : Option ι) → AddCommMonoid (M i)]
lean/.lake/packages/mathlib/Mathlib/LinearAlgebra/Pi.lean:545:def piRing : ((ι → R) →ₗ[R] M) ≃ₗ[S] ι → M :=
lean/.lake/packages/mathlib/Mathlib/LinearAlgebra/Pi.lean:608:def piFinTwo (M : Fin 2 → Type v)

exec
/bin/bash -lc "rg -n \"theorem .*fderiv.*eq|protected theorem HasFDerivAt\\.fderiv|def fderiv|theorem HasStrictFDerivAt\\.hasFDerivAt|hasFDerivAt.*fderiv\" lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Defs.lean -S" in /home/ubuntu/workspace/deriv-spec
 succeeded in 0ms:
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Defs.lean:149:irreducible_def fderivWithin (f : E → F) (s : Set E) (x : E) : E →L[𝕜] F :=
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Defs.lean:158:irreducible_def fderiv (f : E → F) (x : E) : E →L[𝕜] F :=
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean:317:protected theorem HasStrictFDerivAt.hasFDerivAt (hf : HasStrictFDerivAt f f' x) :
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean:405:protected theorem HasFDerivAt.fderiv
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean:412:theorem fderiv_eq
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean:477:  h.hasFDerivAt.hasFDerivWithinAt.fderivWithin hxs
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean:519:theorem fderivWithin_eq_fderiv

codex
I’m going to give the route as a staged API, not a giant theorem. The important design choice is to compute values by asking Lean for the `fderiv` of a function already proved strictly differentiable, then rewrite that `fderiv` to the explicit formula by uniqueness. That keeps casts local to the existing `prodAux` recursion pattern.
exec
/bin/bash -lc "sed -n '232,246p' lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Defs.lean" in /home/ubuntu/workspace/deriv-spec
exec
/bin/bash -lc "rg -n \"namespace ContinuousLinearMap|def proj|theorem proj_apply|def pi \\(|theorem pi_apply|def prod\" lean/.lake/packages/mathlib/Mathlib/Topology/Algebra/Module -S" in /home/ubuntu/workspace/deriv-spec
exec
/bin/bash -lc "sed -n '160,190p' lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean" in /home/ubuntu/workspace/deriv-spec
 succeeded in 0ms:

/-! ### Derivative of the product of two functions -/

open scoped RightActions


variable {𝔸 𝔸' : Type*} [NormedRing 𝔸] [NormedCommRing 𝔸'] [NormedAlgebra 𝕜 𝔸] [NormedAlgebra 𝕜 𝔸']
  {a b : E → 𝔸} {a' b' : E →L[𝕜] 𝔸} {c d : E → 𝔸'} {c' d' : E →L[𝕜] 𝔸'}

@[to_fun (attr := fun_prop)]
theorem HasStrictFDerivAt.mul' {x : E} (ha : HasStrictFDerivAt a a' x)
    (hb : HasStrictFDerivAt b b' x) :
    HasStrictFDerivAt (a * b) (a x • b' + a' <• b x) x :=
  ((ContinuousLinearMap.mul 𝕜 𝔸).isBoundedBilinearMap.hasStrictFDerivAt (a x, b x)).comp x
    (ha.prodMk hb)

@[to_fun (attr := fun_prop)]
theorem HasStrictFDerivAt.mul (hc : HasStrictFDerivAt c c' x) (hd : HasStrictFDerivAt d d' x) :
    HasStrictFDerivAt (c * d) (c x • d' + d x • c') x := by
  convert hc.mul' hd
  ext z
  apply mul_comm

@[to_fun (attr := fun_prop)]
theorem HasFDerivWithinAt.mul' (ha : HasFDerivWithinAt a a' s x) (hb : HasFDerivWithinAt b b' s x) :
    HasFDerivWithinAt (a * b) (a x • b' + a' <• b x) s x := by
  -- `by exact` to solve unification issues.
  exact ((ContinuousLinearMap.mul 𝕜 𝔸).isBoundedBilinearMap.hasFDerivAt
    (a x, b x)).comp_hasFDerivWithinAt x (ha.prodMk hb)

@[to_fun (attr := fun_prop)]

exec
/bin/bash -lc "sed -n '400,418p' lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean" in /home/ubuntu/workspace/deriv-spec
 succeeded in 0ms:

theorem DifferentiableOn.eventually_differentiableAt (h : DifferentiableOn 𝕜 f s) (hs : s ∈ 𝓝 x) :
    ∀ᶠ y in 𝓝 x, DifferentiableAt 𝕜 f y :=
  (eventually_eventually_nhds.2 hs).mono fun _ => h.differentiableAt

protected theorem HasFDerivAt.fderiv
    [ContinuousAdd E] [ContinuousSMul 𝕜 E] [ContinuousAdd F] [ContinuousSMul 𝕜 F] [T2Space F]
    (h : HasFDerivAt f f' x) :
    fderiv 𝕜 f x = f' := by
  ext
  rw [h.unique h.differentiableAt.hasFDerivAt]

theorem fderiv_eq
    [ContinuousAdd E] [ContinuousSMul 𝕜 E] [ContinuousAdd F] [ContinuousSMul 𝕜 F] [T2Space F]
    {f' : E → E →L[𝕜] F} (h : ∀ x, HasFDerivAt f (f' x) x) : fderiv 𝕜 f = f' :=
  funext fun x => (h x).fderiv

protected theorem HasFDerivWithinAt.fderivWithin
    [ContinuousAdd E] [ContinuousSMul 𝕜 E] [ContinuousAdd F] [ContinuousSMul 𝕜 F] [T2Space F]

 succeeded in 101ms:
 succeeded in 106ms:
web search: 
web search: site:leanprover-community.github.io/mathlib4_docs Mathlib Analysis Calculus FDeriv Prod hasStrictFDerivAt_pi'' v4.29
web search: 
web search: github mathlib4 v4.29.0 HasStrictFDerivAt.fun_sum
web search: 
web search: https://raw.githubusercontent.com/leanprover-community/mathlib4/v4.29.0/Mathlib/Analysis/Calculus/FDeriv/Prod.lean
web search: 
web search: github.com/leanprover-community/mathlib4/blob/v4.29.0/Mathlib/Analysis/Calculus/FDeriv/Prod.lean hasStrictFDerivAt_pi
web search: 
web search: https://github.com/leanprover-community/mathlib4/blob/v4.29.0/Mathlib/Analysis/Calculus/FDeriv/Prod.lean
codex
One place where I would add a named lemma is the packing cancellation, independent of calculus. Once `regGaugeIdxSplit_boundary_apply` is proved, all later `readX/readY/readZ` derivative/value lemmas should reduce with `simp`; without that lemma, every coordinate proof reopens the opaque `Set.range` split.
exec
/bin/bash -lc "rg -n \"sumCompl|ofInjective|Set\\.sumCompl\" lean/.lake/packages/mathlib/Mathlib/Data/Equiv lean/.lake/packages/mathlib/Mathlib/Logic lean/.lake/packages/mathlib/Mathlib/Order -S" in /home/ubuntu/workspace/deriv-spec
 exited 2 in 0ms:
rg: lean/.lake/packages/mathlib/Mathlib/Data/Equiv: No such file or directory (os error 2)
lean/.lake/packages/mathlib/Mathlib/Order/Hom/Set.lean:113:  { Equiv.ofInjective _ f.injective with
lean/.lake/packages/mathlib/Mathlib/Order/Hom/Set.lean:134:  toEquiv := Equiv.ofInjective f h_mono.injective
lean/.lake/packages/mathlib/Mathlib/Order/Hom/Lex.lean:40:  toEquiv := .sumCompl (r · x)
lean/.lake/packages/mathlib/Mathlib/Order/Hom/Lex.lean:49:theorem sumLexComplLeft_apply (a) : sumLexComplLeft r x a = Equiv.sumCompl (r · x) a :=
lean/.lake/packages/mathlib/Mathlib/Order/Hom/Lex.lean:53:theorem sumLexComplLeft_symm_apply (a) : sumLexComplLeft r x a = Equiv.sumCompl (r · x) a :=
lean/.lake/packages/mathlib/Mathlib/Order/Hom/Lex.lean:60:  toEquiv := (Equiv.sumComm _ _).trans <| .sumCompl (r x)
lean/.lake/packages/mathlib/Mathlib/Order/Hom/Lex.lean:69:theorem sumLexComplRight_apply (a) : sumLexComplRight r x a = Equiv.sumCompl (r x) a.swap :=
lean/.lake/packages/mathlib/Mathlib/Order/Hom/Lex.lean:73:theorem sumLexComplRight_symm_apply (a) : sumLexComplRight r x a = Equiv.sumCompl (r x) a.swap :=
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Set.lean:18:* `Equiv.ofInjective`: an injective function is (noncomputably) equivalent to its range.
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Set.lean:293:See also `Equiv.sumCompl`. -/
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Set.lean:294:protected def sumCompl {α} (s : Set α) [DecidablePred (· ∈ s)] : s ⊕ (sᶜ : Set α) ≃ α :=
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Set.lean:295:  Equiv.sumCompl (· ∈ s)
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Set.lean:298:theorem sumCompl_apply_inl {α : Type u} (s : Set α) [DecidablePred (· ∈ s)] (x : s) :
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Set.lean:299:    Equiv.Set.sumCompl s (Sum.inl x) = x :=
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Set.lean:303:theorem sumCompl_apply_inr {α : Type u} (s : Set α) [DecidablePred (· ∈ s)] (x : (sᶜ : Set α)) :
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Set.lean:304:    Equiv.Set.sumCompl s (Sum.inr x) = x :=
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Set.lean:307:theorem sumCompl_symm_apply_of_mem {α : Type u} {s : Set α} [DecidablePred (· ∈ s)] {x : α}
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Set.lean:308:    (hx : x ∈ s) : (Equiv.Set.sumCompl s).symm x = Sum.inl ⟨x, hx⟩ :=
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Set.lean:309:  sumCompl_symm_apply_of_pos hx
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Set.lean:311:theorem sumCompl_symm_apply_of_notMem {α : Type u} {s : Set α} [DecidablePred (· ∈ s)] {x : α}
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Set.lean:312:    (hx : x ∉ s) : (Equiv.Set.sumCompl s).symm x = Sum.inr ⟨x, hx⟩ :=
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Set.lean:313:  sumCompl_symm_apply_of_neg hx
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Set.lean:316:theorem sumCompl_symm_apply {α : Type*} {s : Set α} [DecidablePred (· ∈ s)] (x : s) :
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Set.lean:317:    (Equiv.Set.sumCompl s).symm x = Sum.inl x :=
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Set.lean:318:  sumCompl_symm_apply_pos x
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Set.lean:321:theorem sumCompl_symm_apply_compl {α : Type*} {s : Set α} [DecidablePred (· ∈ s)]
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Set.lean:322:    (x : (sᶜ : Set α)) : (Equiv.Set.sumCompl s).symm x = Sum.inr x :=
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Set.lean:323:  sumCompl_symm_apply_neg x
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Set.lean:390:        α ≃ s ⊕ (sᶜ : Set α) := (Set.sumCompl s).symm
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Set.lean:392:        _ ≃ β := Set.sumCompl t)
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Set.lean:394:      simp only [Sum.map_inl, trans_apply, sumCongr_apply, Set.sumCompl_apply_inl,
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Set.lean:395:        Set.sumCompl_symm_apply, Trans.trans]
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Set.lean:399:    · simp only [Set.sumCompl_symm_apply_of_mem hx, ← e.prop ⟨x, hx⟩, Sum.map_inl, sumCongr_apply,
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Set.lean:400:        trans_apply, Set.sumCompl_apply_inl, Trans.trans]
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Set.lean:401:    · simp only [Set.sumCompl_symm_apply_of_notMem hx, Sum.map_inr, subtypeEquiv_apply,
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Set.lean:402:        Set.sumCompl_apply_inr, trans_apply, sumCongr_apply, Trans.trans]
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Set.lean:405:      simp only [Sum.map_inr, subtypeEquiv_apply, Set.sumCompl_apply_inr, Function.comp_apply,
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Set.lean:407:        Set.sumCompl_symm_apply_compl]
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Set.lean:534:noncomputable def ofInjective {α β} (f : α → β) (hf : Injective f) : α ≃ range f :=
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Set.lean:537:theorem apply_ofInjective_symm {α β} {f : α → β} (hf : Injective f) (b : range f) :
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Set.lean:538:    f ((ofInjective f hf).symm b) = b :=
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Set.lean:539:  Subtype.ext_iff.1 <| (ofInjective f hf).apply_symm_apply b
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Set.lean:542:theorem ofInjective_symm_apply {α β} {f : α → β} (hf : Injective f) (a : α) :
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Set.lean:543:    (ofInjective f hf).symm ⟨f a, ⟨a, rfl⟩⟩ = a := by
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Set.lean:544:  apply (ofInjective f hf).injective
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Set.lean:547:theorem coe_ofInjective_symm {α β} {f : α → β} (hf : Injective f) :
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Set.lean:548:    ((ofInjective f hf).symm : range f → α) = rangeSplitting f := by
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Set.lean:554:theorem self_comp_ofInjective_symm {α β} {f : α → β} (hf : Injective f) :
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Set.lean:555:    f ∘ (ofInjective f hf).symm = Subtype.val :=
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Set.lean:556:  funext fun x => apply_ofInjective_symm hf x
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Set.lean:558:theorem ofLeftInverse_eq_ofInjective {α β : Type*} (f : α → β) (f_inv : Nonempty α → β → α)
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Set.lean:561:      ofInjective f ((isEmpty_or_nonempty α).elim (fun _ _ _ _ => Subsingleton.elim _ _)
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Set.lean:566:theorem ofLeftInverse'_eq_ofInjective {α β : Type*} (f : α → β) (f_inv : β → α)
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Set.lean:567:    (hf : LeftInverse f_inv f) : ofLeftInverse' f f_inv hf = ofInjective f hf.injective := by
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Fintype.lean:40:`Equiv.ofLeftInverse` instead. This is the computable version of `Equiv.ofInjective`.
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Fintype.lean:57:theorem Function.Embedding.toEquivRange_eq_ofInjective :
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Fintype.lean:58:    f.toEquivRange = Equiv.ofInjective f f.injective := by
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Fintype.lean:119:  rw [sumCompl_symm_apply_of_pos hx, Sum.map_inl, sumCompl_apply_inl]
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Fintype.lean:130:  rw [sumCompl_symm_apply_of_neg hx, Sum.map_inr, sumCompl_apply_inr]
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Basic.lean:56:  (sumCompl p).symm.trans ((sumCongr e f).trans (sumCompl q))
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Basic.lean:64:  permCongr (sumCompl p) (sumCongr ep en)
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Basic.lean:549:inverse, or `Equiv.ofInjective` in the general case.
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Sum.lean:253:section sumCompl
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Sum.lean:260:that are not necessarily `IsCompl p q`. See also `Equiv.Set.sumCompl` for a version on sets. -/
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Sum.lean:261:def sumCompl {α : Type*} (p : α → Prop) [DecidablePred p] :
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Sum.lean:274:theorem sumCompl_apply_inl {α} {p : α → Prop} [DecidablePred p] (x : { a // p a }) :
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Sum.lean:275:    sumCompl p (Sum.inl x) = x :=
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Sum.lean:279:theorem sumCompl_apply_inr {α} {p : α → Prop} [DecidablePred p] (x : { a // ¬p a }) :
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Sum.lean:280:    sumCompl p (Sum.inr x) = x :=
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Sum.lean:284:theorem sumCompl_symm_apply_of_pos {α} {p : α → Prop} [DecidablePred p] {a : α} (h : p a) :
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Sum.lean:285:    (sumCompl p).symm a = Sum.inl ⟨a, h⟩ :=
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Sum.lean:289:theorem sumCompl_symm_apply_of_neg {α} {p : α → Prop} [DecidablePred p] {a : α} (h : ¬p a) :
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Sum.lean:290:    (sumCompl p).symm a = Sum.inr ⟨a, h⟩ :=
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Sum.lean:294:alias sumCompl_apply_symm_of_pos := sumCompl_symm_apply_of_pos
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Sum.lean:296:alias sumCompl_apply_symm_of_neg := sumCompl_symm_apply_of_neg
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Sum.lean:299:theorem sumCompl_symm_apply_pos {α} {p : α → Prop} [DecidablePred p] (x : {x // p x}) :
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Sum.lean:300:    (sumCompl p).symm x = Sum.inl x :=
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Sum.lean:301:  sumCompl_symm_apply_of_pos x.2
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Sum.lean:304:theorem sumCompl_symm_apply_neg {α} {p : α → Prop} [DecidablePred p] (x : {x // ¬ p x}) :
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Sum.lean:305:    (sumCompl p).symm x = Sum.inr x :=
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Sum.lean:306:  sumCompl_symm_apply_of_neg x.2
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Sum.lean:308:end sumCompl
lean/.lake/packages/mathlib/Mathlib/Order/Partition/Equipartition.lean:118:  let f := (Equiv.sumCompl _).symm.trans ((el.sumCongr es).trans finSumFinEquiv)
lean/.lake/packages/mathlib/Mathlib/Logic/Embedding/Set.lean:92:See also `Equiv.sumCompl`, for when `IsCompl p q`. -/
lean/.lake/packages/mathlib/Mathlib/Logic/Small/Basic.lean:31:  small_map (Equiv.ofInjective f hf)
lean/.lake/packages/mathlib/Mathlib/Logic/Denumerable.lean:320:    Infinite.of_injective _ (Equiv.ofInjective _ encode_injective).injective
lean/.lake/packages/mathlib/Mathlib/Order/SuccPred/LinearLocallyFinite.lean:371:  toEquiv := Equiv.ofInjective _ injective_toZ
lean/.lake/packages/mathlib/Mathlib/Order/InitialSeg.lean:418:  RelIso.symm ⟨(Equiv.ofInjective f f.injective).trans
lean/.lake/packages/mathlib/Mathlib/Order/InitialSeg.lean:423:  Equiv.apply_ofInjective_symm f.injective _
lean/.lake/packages/mathlib/Mathlib/Order/InitialSeg.lean:427:  Equiv.ofInjective_symm_apply f.injective _

exec
/bin/bash -lc 'rg -n "def ofInjective|theorem ofInjective|ofInjective_apply|sumCompl_apply|sumCompl_symm" lean/.lake/packages/mathlib/Mathlib -S' in /home/ubuntu/workspace/deriv-spec
 succeeded in 182ms:
lean/.lake/packages/mathlib/Mathlib/SetTheory/Cardinal/Arithmetic.lean:864:  refine ⟨h, ?_⟩; rintro ⟨x, hx⟩; simp [h, Set.sumCompl_symm_apply_of_mem, hx]
lean/.lake/packages/mathlib/Mathlib/Algebra/Group/Subgroup/Ker.lean:187:noncomputable def ofInjective {f : G →* N} (hf : Function.Injective f) : G ≃* f.range :=
lean/.lake/packages/mathlib/Mathlib/Algebra/Group/Subgroup/Ker.lean:194:theorem ofInjective_apply {f : G →* N} (hf : Function.Injective f) {x : G} :
lean/.lake/packages/mathlib/Mathlib/Algebra/Lie/Subalgebra.lean:771:noncomputable def ofInjective (f : L₁ →ₗ⁅R⁆ L₂) (h : Function.Injective f) : L₁ ≃ₗ⁅R⁆ f.range :=
lean/.lake/packages/mathlib/Mathlib/Algebra/Lie/Subalgebra.lean:776:theorem ofInjective_apply (f : L₁ →ₗ⁅R⁆ L₂) (h : Function.Injective f) (x : L₁) :
lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Basis.lean:42:    Submodule.restrictScalarsEquiv_apply, LinearEquiv.ofInjective_apply, LinearEquiv.coe_ofEq_apply,
lean/.lake/packages/mathlib/Mathlib/Algebra/Star/NonUnitalSubalgebra.lean:544:noncomputable def ofInjective' (f : F) (hf : Function.Injective f) :
lean/.lake/packages/mathlib/Mathlib/Algebra/Star/NonUnitalSubalgebra.lean:549:theorem ofInjective'_apply (f : F) (hf : Function.Injective f) (x : A) :
lean/.lake/packages/mathlib/Mathlib/RingTheory/Polynomial/Basic.lean:722:          Equiv.Set.sumCompl_apply_inl]
lean/.lake/packages/mathlib/Mathlib/Algebra/Algebra/Subalgebra/Basic.lean:633:noncomputable def ofInjective (f : A →ₐ[R] B) (hf : Function.Injective f) : A ≃ₐ[R] f.range :=
lean/.lake/packages/mathlib/Mathlib/Algebra/Algebra/Subalgebra/Basic.lean:637:theorem ofInjective_apply (f : A →ₐ[R] B) (hf : Function.Injective f) (x : A) :
lean/.lake/packages/mathlib/Mathlib/Algebra/Algebra/Subalgebra/Basic.lean:642:noncomputable def ofInjectiveField {E F : Type*} [DivisionRing E] [Semiring F] [Nontrivial F]
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Set.lean:298:theorem sumCompl_apply_inl {α : Type u} (s : Set α) [DecidablePred (· ∈ s)] (x : s) :
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Set.lean:303:theorem sumCompl_apply_inr {α : Type u} (s : Set α) [DecidablePred (· ∈ s)] (x : (sᶜ : Set α)) :
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Set.lean:307:theorem sumCompl_symm_apply_of_mem {α : Type u} {s : Set α} [DecidablePred (· ∈ s)] {x : α}
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Set.lean:309:  sumCompl_symm_apply_of_pos hx
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Set.lean:311:theorem sumCompl_symm_apply_of_notMem {α : Type u} {s : Set α} [DecidablePred (· ∈ s)] {x : α}
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Set.lean:313:  sumCompl_symm_apply_of_neg hx
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Set.lean:316:theorem sumCompl_symm_apply {α : Type*} {s : Set α} [DecidablePred (· ∈ s)] (x : s) :
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Set.lean:318:  sumCompl_symm_apply_pos x
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Set.lean:321:theorem sumCompl_symm_apply_compl {α : Type*} {s : Set α} [DecidablePred (· ∈ s)]
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Set.lean:323:  sumCompl_symm_apply_neg x
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Set.lean:394:      simp only [Sum.map_inl, trans_apply, sumCongr_apply, Set.sumCompl_apply_inl,
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Set.lean:395:        Set.sumCompl_symm_apply, Trans.trans]
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Set.lean:399:    · simp only [Set.sumCompl_symm_apply_of_mem hx, ← e.prop ⟨x, hx⟩, Sum.map_inl, sumCongr_apply,
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Set.lean:400:        trans_apply, Set.sumCompl_apply_inl, Trans.trans]
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Set.lean:401:    · simp only [Set.sumCompl_symm_apply_of_notMem hx, Sum.map_inr, subtypeEquiv_apply,
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Set.lean:402:        Set.sumCompl_apply_inr, trans_apply, sumCongr_apply, Trans.trans]
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Set.lean:405:      simp only [Sum.map_inr, subtypeEquiv_apply, Set.sumCompl_apply_inr, Function.comp_apply,
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Set.lean:407:        Set.sumCompl_symm_apply_compl]
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Set.lean:534:noncomputable def ofInjective {α β} (f : α → β) (hf : Injective f) : α ≃ range f :=
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Set.lean:542:theorem ofInjective_symm_apply {α β} {f : α → β} (hf : Injective f) (a : α) :
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Fintype.lean:119:  rw [sumCompl_symm_apply_of_pos hx, Sum.map_inl, sumCompl_apply_inl]
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Fintype.lean:130:  rw [sumCompl_symm_apply_of_neg hx, Sum.map_inr, sumCompl_apply_inr]
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Sum.lean:274:theorem sumCompl_apply_inl {α} {p : α → Prop} [DecidablePred p] (x : { a // p a }) :
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Sum.lean:279:theorem sumCompl_apply_inr {α} {p : α → Prop} [DecidablePred p] (x : { a // ¬p a }) :
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Sum.lean:284:theorem sumCompl_symm_apply_of_pos {α} {p : α → Prop} [DecidablePred p] {a : α} (h : p a) :
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Sum.lean:289:theorem sumCompl_symm_apply_of_neg {α} {p : α → Prop} [DecidablePred p] {a : α} (h : ¬p a) :
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Sum.lean:294:alias sumCompl_apply_symm_of_pos := sumCompl_symm_apply_of_pos
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Sum.lean:296:alias sumCompl_apply_symm_of_neg := sumCompl_symm_apply_of_neg
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Sum.lean:299:theorem sumCompl_symm_apply_pos {α} {p : α → Prop} [DecidablePred p] (x : {x // p x}) :
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Sum.lean:301:  sumCompl_symm_apply_of_pos x.2
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Sum.lean:304:theorem sumCompl_symm_apply_neg {α} {p : α → Prop} [DecidablePred p] (x : {x // ¬ p x}) :
lean/.lake/packages/mathlib/Mathlib/Logic/Equiv/Sum.lean:306:  sumCompl_symm_apply_of_neg x.2

exec
/bin/bash -lc "rg -n \"HasStrictFDerivAt\\.congr|HasFDerivAt\\.congr|congr_fderiv\" lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv -S" in /home/ubuntu/workspace/deriv-spec
exec
/bin/bash -lc "rg -n \"congr_fderiv|congr.*fderiv|EventuallyEq\\.fderiv|fderiv_eq_of\" lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus -S" in /home/ubuntu/workspace/deriv-spec
 succeeded in 166ms:
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Congr.lean:114:theorem HasStrictFDerivAt.congr_fderiv (h : HasStrictFDerivAt f f' x) (h' : f' = g') :
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Congr.lean:118:theorem HasFDerivAt.congr_fderiv (h : HasFDerivAt f f' x) (h' : f' = g') : HasFDerivAt f g' x :=
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Congr.lean:121:theorem HasFDerivWithinAt.congr_fderiv (h : HasFDerivWithinAt f f' s x) (h' : f' = g') :
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Congr.lean:125:theorem HasStrictFDerivAt.congr_of_eventuallyEq (h : HasStrictFDerivAt f f' x)
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Congr.lean:174:theorem HasFDerivAt.congr_of_eventuallyEq (h : HasFDerivAt f f' x) (h₁ : f₁ =ᶠ[𝓝 x] f) :
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Pow.lean:57:    refine this.congr_fderiv <| aux _ _ _ _
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Pow.lean:77:    exact this.congr_fderiv <| aux _ _ _ _
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Pow.lean:96:    exact this.congr_fderiv <| aux _ _ _ _
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Pow.lean:206:  h.pow' n |>.congr_fderiv <| aux_sum_eq_pow _
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Pow.lean:215:  h.pow' n |>.congr_fderiv <| aux_sum_eq_pow _
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Pow.lean:224:  h.pow' n |>.congr_fderiv <| aux_sum_eq_pow _
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean:405:    exact .congr_fderiv (.mul' (ContinuousLinearMap.hasStrictFDerivAt _) IH)
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean:413:  hasStrictFDerivAt_list_prod'.congr_fderiv <|
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean:422:  classical exact hasStrictFDerivAt_list_prod'.congr_fderiv <| Eq.symm <|
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean:458:  refine hasStrictFDerivAt_list_prod'.congr_fderiv ?_
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean:501:  refine .congr_fderiv (hasStrictFDerivAt_list_prod_finRange'.comp x
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean:517:  refine .congr_fderiv (hasFDerivAt_list_prod_finRange'.comp x
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean:530:  refine .congr_fderiv (hasFDerivAt_list_prod_finRange'.comp_hasFDerivWithinAt x
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean:556:  exact .congr_fderiv
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean:570:  exact .congr_fderiv
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean:580:  exact .congr_fderiv
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean:600:  simpa [← Finset.prod_attach u] using .congr_fderiv
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean:607:  simpa [← Finset.prod_attach u] using .congr_fderiv
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean:614:  simpa [← Finset.prod_attach u] using .congr_fderiv

 succeeded in 174ms:
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Symmetric.lean:113:    apply Filter.EventuallyEq.fderivWithin_eq A
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Symmetric.lean:124:      (fderivWithin_eventually_congr_set h).fderivWithin_eq_of_nhds
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Analytic.lean:394:  exact (h.fderivWithin hs.uniqueDiffOn).congr (fun x hx ↦ (fderivWithin_of_isOpen hs hx).symm)
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Analytic.lean:518:    · rw [Filter.EventuallyEq.fderiv_eq (f := fun _ ↦ 0)]
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean:405:    exact .congr_fderiv (.mul' (ContinuousLinearMap.hasStrictFDerivAt _) IH)
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean:413:  hasStrictFDerivAt_list_prod'.congr_fderiv <|
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean:422:  classical exact hasStrictFDerivAt_list_prod'.congr_fderiv <| Eq.symm <|
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean:458:  refine hasStrictFDerivAt_list_prod'.congr_fderiv ?_
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean:501:  refine .congr_fderiv (hasStrictFDerivAt_list_prod_finRange'.comp x
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean:517:  refine .congr_fderiv (hasFDerivAt_list_prod_finRange'.comp x
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean:530:  refine .congr_fderiv (hasFDerivAt_list_prod_finRange'.comp_hasFDerivWithinAt x
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean:556:  exact .congr_fderiv
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean:570:  exact .congr_fderiv
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean:580:  exact .congr_fderiv
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean:600:  simpa [← Finset.prod_attach u] using .congr_fderiv
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean:607:  simpa [← Finset.prod_attach u] using .congr_fderiv
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean:614:  simpa [← Finset.prod_attach u] using .congr_fderiv
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Congr.lean:94:theorem fderivWithin_congr_set (h : s =ᶠ[𝓝 x] t) : fderivWithin 𝕜 f s x = fderivWithin 𝕜 f t x :=
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Congr.lean:114:theorem HasStrictFDerivAt.congr_fderiv (h : HasStrictFDerivAt f f' x) (h' : f' = g') :
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Congr.lean:118:theorem HasFDerivAt.congr_fderiv (h : HasFDerivAt f f' x) (h' : f' = g') : HasFDerivAt f g' x :=
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Congr.lean:121:theorem HasFDerivWithinAt.congr_fderiv (h : HasFDerivWithinAt f f' s x) (h' : f' = g') :
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Congr.lean:218:  (HasFDerivWithinAt.congr_mono h.hasFDerivWithinAt hs hx h₁).fderivWithin hxt
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Congr.lean:221:theorem Filter.EventuallyEq.fderivWithin_eq (hs : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x) :
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Congr.lean:226:theorem Filter.EventuallyEq.fderivWithin_eq_of_mem (hs : f₁ =ᶠ[𝓝[s] x] f) (hx : x ∈ s) :
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Congr.lean:230:theorem Filter.EventuallyEq.fderivWithin_eq_of_insert (hs : f₁ =ᶠ[𝓝[insert x s] x] f) :
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Congr.lean:232:  apply Filter.EventuallyEq.fderivWithin_eq (nhdsWithin_mono _ (subset_insert x s) hs)
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Congr.lean:235:theorem Filter.EventuallyEq.fderivWithin' (hs : f₁ =ᶠ[𝓝[s] x] f) (ht : t ⊆ s) :
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Congr.lean:239:      EventuallyEq.fderivWithin_eq (hs.filter_mono <| nhdsWithin_mono _ ht)
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Congr.lean:242:protected theorem Filter.EventuallyEq.fderivWithin (hs : f₁ =ᶠ[𝓝[s] x] f) :
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Congr.lean:246:theorem Filter.EventuallyEq.fderivWithin_eq_of_nhds (h : f₁ =ᶠ[𝓝 x] f) :
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Congr.lean:258:theorem Filter.EventuallyEq.fderiv_eq (h : f₁ =ᶠ[𝓝 x] f) : fderiv 𝕜 f₁ x = fderiv 𝕜 f x := by
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Congr.lean:261:protected theorem Filter.EventuallyEq.fderiv (h : f₁ =ᶠ[𝓝 x] f) : fderiv 𝕜 f₁ =ᶠ[𝓝 x] fderiv 𝕜 f :=
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Pow.lean:57:    refine this.congr_fderiv <| aux _ _ _ _
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Pow.lean:77:    exact this.congr_fderiv <| aux _ _ _ _
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Pow.lean:96:    exact this.congr_fderiv <| aux _ _ _ _
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Pow.lean:206:  h.pow' n |>.congr_fderiv <| aux_sum_eq_pow _
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Pow.lean:215:  h.pow' n |>.congr_fderiv <| aux_sum_eq_pow _
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Pow.lean:224:  h.pow' n |>.congr_fderiv <| aux_sum_eq_pow _
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/Gradient/Basic.lean:323:  rwa [Filter.EventuallyEq.fderiv_eq]
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Basic.lean:603:  h.hasStrictFDerivAt.congr_fderiv <| congr_arg _ h'
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Basic.lean:606:  HasFDerivAt.congr_fderiv h <| congr_arg _ h'
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Basic.lean:610:  HasFDerivWithinAt.congr_fderiv h <| congr_arg _ h'
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Basic.lean:646:  rwa [Filter.EventuallyEq.fderiv_eq]
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Star.lean:56:  · exact DFunLike.congr_fun (fderivWithin_star hxs) _
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Star.lean:60:  DFunLike.congr_fun fderiv_star _
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/FTaylorSeries.lean:161:    refine ((hp.fderivWithin m hm x hx).congr' (hpq m hm.le).symm hx).congr_fderiv ?_
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/FTaylorSeries.lean:930:    apply Filter.EventuallyEq.fderiv_eq
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean:866:  exact (h1 x hx).congr_of_mem (fun y hy => (h2 y hy).fderivWithin (hs y hy)) hx
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean:880:    contDiffOn_congr fun x hx ↦ fderivWithin_of_isOpen hs hx]
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean:893:  (hf.fderivWithin hs.uniqueDiffOn hmn).congr fun _ hx => (fderivWithin_of_isOpen hs hx).symm
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/VectorField.lean:351:  simp [lieBracketWithin, hV.fderivWithin_congr_mono, hW.fderivWithin_congr_mono, hVs, hVx,
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/VectorField.lean:633:    apply Filter.EventuallyEq.fderivWithin_eq_of_mem _ hx
lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/VectorField.lean:637:    apply Filter.EventuallyEq.fderivWithin_eq_of_mem _ hx

codex
`HasStrictFDerivAt.congr_fderiv` and `HasFDerivAt.congr_fderiv` do exist in v4.29, but they are only for replacing the derivative map after you have proved an equality of CLMs. They will not extract the value from an existential derivative by themselves.
exec
/bin/bash -lc "sed -n '108,122p' lean/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Congr.lean" in /home/ubuntu/workspace/deriv-spec
 succeeded in 0ms:
  exact isLittleOTVS_congr (h₀.mono fun y hy => by simp_all [Prod.map]) .rfl

theorem Filter.EventuallyEq.hasStrictFDerivAt_iff (h : f₀ =ᶠ[𝓝 x] f₁) (h' : ∀ y, f₀' y = f₁' y) :
    HasStrictFDerivAt f₀ f₀' x ↔ HasStrictFDerivAt f₁ f₁' x :=
  h.prodMap_nhds h |>.hasFDerivAtFilter_iff h'

theorem HasStrictFDerivAt.congr_fderiv (h : HasStrictFDerivAt f f' x) (h' : f' = g') :
    HasStrictFDerivAt f g' x :=
  h' ▸ h

theorem HasFDerivAt.congr_fderiv (h : HasFDerivAt f f' x) (h' : f' = g') : HasFDerivAt f g' x :=
  h' ▸ h

theorem HasFDerivWithinAt.congr_fderiv (h : HasFDerivWithinAt f f' s x) (h' : f' = g') :
    HasFDerivWithinAt f g' s x :=

exec
/bin/bash -lc "sed -n '185,200p' lean/.lake/packages/mathlib/Mathlib/Topology/Algebra/Module/LinearMapPiProd.lean" in /home/ubuntu/workspace/deriv-spec
exec
/bin/bash -lc "sed -n '35,48p' lean/.lake/packages/mathlib/Mathlib/Topology/Algebra/Module/LinearMapPiProd.lean" in /home/ubuntu/workspace/deriv-spec
 succeeded in 287ms:

theorem pi_comp (f : ∀ i, M →L[R] φ i) (g : M₂ →L[R] M) :
    (pi f).comp g = pi fun i => (f i).comp g :=
  rfl

/-- The projections from a family of topological modules are continuous linear maps. -/
def proj (i : ι) : (∀ i, φ i) →L[R] φ i :=
  ⟨LinearMap.proj i, continuous_apply _⟩

@[simp]
theorem proj_apply (i : ι) (b : ∀ i, φ i) : (proj i : (∀ i, φ i) →L[R] φ i) b = b i :=
  rfl

@[simp]
theorem proj_pi (f : ∀ i, M₂ →L[R] φ i) (i : ι) : (proj i).comp (pi f) = f i := rfl


 succeeded in 176ms:
  {M₂ : Type*} [TopologicalSpace M₂] [AddCommMonoid M₂] [Module R M₂]
  {M₃ : Type*} [TopologicalSpace M₃] [AddCommMonoid M₃] [Module R M₃]
  {M₄ : Type*} [TopologicalSpace M₄] [AddCommMonoid M₄] [Module R M₄]

/-- The Cartesian product of two bounded linear maps, as a bounded linear map. -/
protected def prod (f₁ : M₁ →L[R] M₂) (f₂ : M₁ →L[R] M₃) :
    M₁ →L[R] M₂ × M₃ :=
  ⟨(f₁ : M₁ →ₗ[R] M₂).prod f₂, f₁.2.prodMk f₂.2⟩

@[simp, norm_cast]
theorem coe_prod (f₁ : M₁ →L[R] M₂) (f₂ : M₁ →L[R] M₃) :
    (f₁.prod f₂ : M₁ →ₗ[R] M₂ × M₃) = LinearMap.prod f₁ f₂ :=
  rfl


codex
**Recommendation:** use an **A-lite + uniqueness** route. Do not prove the closed-form `Σ_{s<k} corner · δC_s · corner` as the primary theorem, and do not use `littleO` directly. Instead, expose the recursive derivative that your current existential proof already constructs, then specialize/evaluate it at the corner.

The existential lemma is a dead end for values: uniqueness only says an existing derivative equals another derivative after you prove the other derivative exists.

Core lemma:

```lean
noncomputable def prodAuxEntryDeriv
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (H : Fin (L + 1) → ℕ) (g : X → Params H) (x : X)
    (g' : ∀ s i j, X →L[ℝ] ℝ) :
    (k : ℕ) → (hk : k < L + 1) →
      Fin (H 0) → Fin (H ⟨k, hk⟩) → X →L[ℝ] ℝ
| 0, hk, i, j => 0
| k + 1, hk, i, j => by
    have hk' : k < L + 1 := Nat.lt_of_succ_lt hk
    have hkL : k < L := Nat.lt_of_succ_lt_succ hk
    have e1 : (⟨k, hk'⟩ : Fin (L + 1)) = (⟨k, hkL⟩ : Fin L).castSucc := by
      apply Fin.ext; simp [Fin.castSucc]
    have e2 : (⟨k + 1, hk⟩ : Fin (L + 1)) = (⟨k, hkL⟩ : Fin L).succ := by
      apply Fin.ext; simp [Fin.succ]
    exact ∑ m : Fin (H ⟨k, hk'⟩),
      (prodAux H (g x) k hk' i m) •
          g' ⟨k, hkL⟩ (e1 ▸ m) (e2 ▸ j)
      +
      (((by rw [e1, e2]; exact g x ⟨k, hkL⟩ :
          Matrix (Fin (H ⟨k, hk'⟩)) (Fin (H ⟨k + 1, hk⟩)) ℝ) m j) •
          prodAuxEntryDeriv H g x g' k hk' i m)
```

Then prove the non-existential version by copying the current induction:

```lean
theorem hasStrictFDerivAt_prodAux_entry_explicit
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (H : Fin (L + 1) → ℕ) (g : X → Params H) (x : X)
    (g' : ∀ s i j, X →L[ℝ] ℝ)
    (hg : ∀ s i j, HasStrictFDerivAt (fun y => g y s i j) (g' s i j) x)
    (k : ℕ) (hk : k < L + 1) (i : Fin (H 0)) (j : Fin (H ⟨k, hk⟩)) :
    HasStrictFDerivAt
      (fun y => prodAux H (g y) k hk i j)
      (prodAuxEntryDeriv H g x g' k hk i j) x := by
  revert hk
  induction k with
  | zero =>
      intro hk i j
      simpa [prodAuxEntryDeriv] using
        (hasStrictFDerivAt_const (x := x)
          ((1 : Matrix (Fin (H 0)) (Fin (H 0)) ℝ) i j))
  | succ k ih =>
      intro hk i j
      -- same `hk'`, `hkL`, `e1`, `e2`, `hentry` as your existential lemma
      -- rewrite product entry to a finite sum
      -- each summand: `(ih ...).mul hlayer`
      -- assemble with `HasStrictFDerivAt.fun_sum`
      -- close derivative-map equality with `simp [prodAuxEntryDeriv, add_comm, add_left_comm, add_assoc]`
      ...
```

Then keep the corner computation **below this**, in block-coordinate lemmas, not as a universal prefix/suffix theorem:

```lean
theorem hasStrictFDerivAt_prod_block11_regSlice
    (a b : Fin r) :
    HasStrictFDerivAt
      (fun r0 : Fin (deepestNReg H r) → ℝ =>
        let P := Matrix.reindex
          (rThresholdSplit r (H 0) (hr 0))
          (rThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)))
          (prod H (framedParamsReg H r hr hL (r0, 0)))
        (P.toBlocks₁₁ - 1) a b)
      (ContinuousLinearMap.proj
        ((regPivotFinEquiv H r hr).symm (Sum.inl (a, b)))) 0
```

and analogously:

```lean
hasStrictFDerivAt_prod_block12_regSlice
  -- derivative is proj ((regPivotFinEquiv H r hr).symm (Sum.inr (Sum.inl (a,b))))

hasStrictFDerivAt_prod_block21_regSlice
  -- derivative is proj ((regPivotFinEquiv H r hr).symm (Sum.inr (Sum.inr (a,b))))
```

Add one packing lemma first:

```lean
theorem regGaugeIdxSplit_boundary_apply (b : BoundaryPivotIdx H r) :
    regGaugeIdxSplit H r hr hL (regBoundaryToRegGauge H r hL b)
      = Sum.inl ((regPivotFinEquiv H r hr).symm b) := by
  classical
  simp [regGaugeIdxSplit, regBoundaryEmbed, regBoundaryToRegGauge,
        Equiv.Set.sumCompl_symm_apply_of_mem,
        Equiv.ofInjective_symm_apply]
```

Use it to prove `readX/readY/readZ` slice lemmas: `readX` is nonzero only at `firstLayer`, `readY` only at `lastLayer`, `readZ` only at `firstLayer`.

Final assembly:

```lean
rw [show ContinuousLinearMap.id ℝ (Fin (deepestNReg H r) → ℝ)
    = ContinuousLinearMap.pi (fun i => ContinuousLinearMap.proj i) from by
      ext x i; rfl]
refine hasStrictFDerivAt_pi.2 (fun i => ?_)
rcases hpack : regResidualPack H r hr i with ⟨a,b⟩ | ⟨a,b⟩ | ⟨a,b⟩
· have h := hasStrictFDerivAt_prod_block11_regSlice H r hr hL a b
  have hi : (regPivotFinEquiv H r hr).symm (Sum.inl (a,b)) = i := by
    rw [regResidualPack] at hpack
    rw [← hpack, Equiv.symm_apply_apply]
  simpa [deepestEPivot, hpack, hi] using h
· ...
· ...
```

So: **do not use `hasStrictFDerivAt_iff_isLittleO` for this.** Mathlib v4.29 has it, and also has `HasStrictFDerivAt.congr_fderiv`, but the calculus API route with `HasStrictFDerivAt.mul`, `HasStrictFDerivAt.fun_sum`, `hasStrictFDerivAt_pi`, and `.hasFDerivAt.fderiv` is much less painful. The dependent-Fin casts stay confined to the single `prodAuxEntryDeriv` induction, using the same `e1/e2` pattern already working in your existence lemma.
tokens used
128,863
**Recommendation:** use an **A-lite + uniqueness** route. Do not prove the closed-form `Σ_{s<k} corner · δC_s · corner` as the primary theorem, and do not use `littleO` directly. Instead, expose the recursive derivative that your current existential proof already constructs, then specialize/evaluate it at the corner.

The existential lemma is a dead end for values: uniqueness only says an existing derivative equals another derivative after you prove the other derivative exists.

Core lemma:

```lean
noncomputable def prodAuxEntryDeriv
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (H : Fin (L + 1) → ℕ) (g : X → Params H) (x : X)
    (g' : ∀ s i j, X →L[ℝ] ℝ) :
    (k : ℕ) → (hk : k < L + 1) →
      Fin (H 0) → Fin (H ⟨k, hk⟩) → X →L[ℝ] ℝ
| 0, hk, i, j => 0
| k + 1, hk, i, j => by
    have hk' : k < L + 1 := Nat.lt_of_succ_lt hk
    have hkL : k < L := Nat.lt_of_succ_lt_succ hk
    have e1 : (⟨k, hk'⟩ : Fin (L + 1)) = (⟨k, hkL⟩ : Fin L).castSucc := by
      apply Fin.ext; simp [Fin.castSucc]
    have e2 : (⟨k + 1, hk⟩ : Fin (L + 1)) = (⟨k, hkL⟩ : Fin L).succ := by
      apply Fin.ext; simp [Fin.succ]
    exact ∑ m : Fin (H ⟨k, hk'⟩),
      (prodAux H (g x) k hk' i m) •
          g' ⟨k, hkL⟩ (e1 ▸ m) (e2 ▸ j)
      +
      (((by rw [e1, e2]; exact g x ⟨k, hkL⟩ :
          Matrix (Fin (H ⟨k, hk'⟩)) (Fin (H ⟨k + 1, hk⟩)) ℝ) m j) •
          prodAuxEntryDeriv H g x g' k hk' i m)
```

Then prove the non-existential version by copying the current induction:

```lean
theorem hasStrictFDerivAt_prodAux_entry_explicit
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (H : Fin (L + 1) → ℕ) (g : X → Params H) (x : X)
    (g' : ∀ s i j, X →L[ℝ] ℝ)
    (hg : ∀ s i j, HasStrictFDerivAt (fun y => g y s i j) (g' s i j) x)
    (k : ℕ) (hk : k < L + 1) (i : Fin (H 0)) (j : Fin (H ⟨k, hk⟩)) :
    HasStrictFDerivAt
      (fun y => prodAux H (g y) k hk i j)
      (prodAuxEntryDeriv H g x g' k hk i j) x := by
  revert hk
  induction k with
  | zero =>
      intro hk i j
      simpa [prodAuxEntryDeriv] using
        (hasStrictFDerivAt_const (x := x)
          ((1 : Matrix (Fin (H 0)) (Fin (H 0)) ℝ) i j))
  | succ k ih =>
      intro hk i j
      -- same `hk'`, `hkL`, `e1`, `e2`, `hentry` as your existential lemma
      -- rewrite product entry to a finite sum
      -- each summand: `(ih ...).mul hlayer`
      -- assemble with `HasStrictFDerivAt.fun_sum`
      -- close derivative-map equality with `simp [prodAuxEntryDeriv, add_comm, add_left_comm, add_assoc]`
      ...
```

Then keep the corner computation **below this**, in block-coordinate lemmas, not as a universal prefix/suffix theorem:

```lean
theorem hasStrictFDerivAt_prod_block11_regSlice
    (a b : Fin r) :
    HasStrictFDerivAt
      (fun r0 : Fin (deepestNReg H r) → ℝ =>
        let P := Matrix.reindex
          (rThresholdSplit r (H 0) (hr 0))
          (rThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)))
          (prod H (framedParamsReg H r hr hL (r0, 0)))
        (P.toBlocks₁₁ - 1) a b)
      (ContinuousLinearMap.proj
        ((regPivotFinEquiv H r hr).symm (Sum.inl (a, b)))) 0
```

and analogously:

```lean
hasStrictFDerivAt_prod_block12_regSlice
  -- derivative is proj ((regPivotFinEquiv H r hr).symm (Sum.inr (Sum.inl (a,b))))

hasStrictFDerivAt_prod_block21_regSlice
  -- derivative is proj ((regPivotFinEquiv H r hr).symm (Sum.inr (Sum.inr (a,b))))
```

Add one packing lemma first:

```lean
theorem regGaugeIdxSplit_boundary_apply (b : BoundaryPivotIdx H r) :
    regGaugeIdxSplit H r hr hL (regBoundaryToRegGauge H r hL b)
      = Sum.inl ((regPivotFinEquiv H r hr).symm b) := by
  classical
  simp [regGaugeIdxSplit, regBoundaryEmbed, regBoundaryToRegGauge,
        Equiv.Set.sumCompl_symm_apply_of_mem,
        Equiv.ofInjective_symm_apply]
```

Use it to prove `readX/readY/readZ` slice lemmas: `readX` is nonzero only at `firstLayer`, `readY` only at `lastLayer`, `readZ` only at `firstLayer`.

Final assembly:

```lean
rw [show ContinuousLinearMap.id ℝ (Fin (deepestNReg H r) → ℝ)
    = ContinuousLinearMap.pi (fun i => ContinuousLinearMap.proj i) from by
      ext x i; rfl]
refine hasStrictFDerivAt_pi.2 (fun i => ?_)
rcases hpack : regResidualPack H r hr i with ⟨a,b⟩ | ⟨a,b⟩ | ⟨a,b⟩
· have h := hasStrictFDerivAt_prod_block11_regSlice H r hr hL a b
  have hi : (regPivotFinEquiv H r hr).symm (Sum.inl (a,b)) = i := by
    rw [regResidualPack] at hpack
    rw [← hpack, Equiv.symm_apply_apply]
  simpa [deepestEPivot, hpack, hi] using h
· ...
· ...
```

So: **do not use `hasStrictFDerivAt_iff_isLittleO` for this.** Mathlib v4.29 has it, and also has `HasStrictFDerivAt.congr_fderiv`, but the calculus API route with `HasStrictFDerivAt.mul`, `HasStrictFDerivAt.fun_sum`, `hasStrictFDerivAt_pi`, and `.hasFDerivAt.fderiv` is much less painful. The dependent-Fin casts stay confined to the single `prodAuxEntryDeriv` induction, using the same `e1/e2` pattern already working in your existence lemma.
