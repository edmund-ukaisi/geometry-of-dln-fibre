import DLNFibre.DLN.RLCT.Validate.DeepestSchurSmooth
import DLNFibre.DLN.RLCT.Validate.DeepestSchurShiftConj
import DLNFibre.DLN.RLCT.Validate.DeepestEFullCoreConstant

/-!
# `DLNFibre.DLN.RLCT.Validate.DeepestL2ConjSmooth` — global ⊤-smoothness of the CONJUGATED cutoff Schur shift

The L=2 LINK-2 close (the gauge-reg Θ-peel sandwich, `ScratchL2Link2`) needs the CONJUGATED reg-absorb
peel to feed `deepest_regAbsorb_exists` (PIN-1). That peel's `hTilde` input demands the conjugated
straightening `regStraightenOf2 (deepestEFull ∘ deepestCoreAbsorbConj.symm)` be a LOCAL DIFFEO at `0`,
so `deepestCoreAbsorbConj = coreShearHomeo (schurCutoffShiftConj)` must be GLOBALLY `ContDiff ⊤` (the
`rlctAtOn_comp_localDiffeo` consumer uses global continuity for the absorbed map's global measurability).

This module supplies the smoothness upgrade of `continuous_schurCutoffShiftConj` (which is only
`Continuous`): the conjugated cutoff Schur shift is globally `ContDiff ⊤`. It MIRRORS the bare
`DeepestSchurSmooth` ladder, with the conjugated pivot `deepBlkA_s + readX_s` (invertible on
`unitSetConj`, under `hDA`) in place of the bare `1 + readX_s` (always invertible).

The ladder (bottom-up, conj versions):
  • `contDiffAt_inv_deepBlkA_add_readX_entry`: each `(deepBlkA + readX)⁻¹` entry is `ContDiffAt` on
    `unitSetConj` (the entrywise det/adjugate/inverse route of `DeepestSchurSmooth`);
  • `contDiffAt_schurCorrectionConj_entry` / `contDiffAt_schurShiftRawConj`: the conjugated correction +
    raw shift are `ContDiffAt` on `unitSetConj`;
  • `contDiff_schurCutoffShiftConj`: `χ_conj • schurShiftRawConj` is globally `ContDiff ⊤` (the smooth
    cutoff glue `contDiff_contDiffBump_smul` + `tsupport_cutoffBumpConj_subset_unitSetConj`).

**No strict-derivative-`0` lemma here.** The conjugated shift's derivative at `0` is genuinely NONZERO
(`D(schurCorrectionConj)(0) = −deepBlkZ·deepBlkA⁻¹·D(readY) ≠ 0`, the "atom" the file header flags); the
reg-absorb peel handles this via the value-fold atom `deepestEFull_coreConstant` (D_E annihilates the
core direction), NOT via a `D(shift)(0) = 0` fact. Only the ContDiff⊤ is built here.
-/

open MeasureTheory Matrix
open scoped ENNReal BigOperators Topology Matrix
namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-! ## `schurShiftRawConj` `ContDiffAt` on `unitSetConj`

The conjugated pivot `deepBlkA_s + readX_s` (a constant `deepBlkA_s` plus the entrywise-`ContDiff`
`readX`) has `ContDiffAt` inverse entries where its det `≠ 0`; the conjugated correction is the triple
product `−(deepBlkZ + readZ)·(deepBlkA + readX)⁻¹·(deepBlkY + readY)`. -/

/-- Each entry of the conjugated pivot inverse `(deepBlkA_s + readX p s)⁻¹` is `ContDiffAt p` on
`unitSetConj` (det `≠ 0` there). The `deepBlkA + readX` family is entrywise `ContDiff` (constant
`deepBlkA` + `contDiff_readX_entry`). -/
theorem contDiffAt_inv_deepBlkA_add_readX_entry (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (s : Fin L)
    (p : (Fin (deepestNReg H r) → ℝ) × (Fin (deepestNGauge H r) → ℝ))
    (hp : p ∈ unitSetConj H r B hB hr hL) (i j : Fin r) :
    ContDiffAt ℝ (⊤ : ℕ∞)
      (fun q => ((deepBlkA H r B hB hr hL s + readX H r hr hL q s)⁻¹) i j) p := by
  refine contDiffAt_matrix_inv_entry_of_det_ne_zero
    (A := fun q => deepBlkA H r B hB hr hL s + readX H r hr hL q s) (fun a b => ?_) (hp s) i j
  have : (fun q => (deepBlkA H r B hB hr hL s + readX H r hr hL q s) a b)
      = fun q => (deepBlkA H r B hB hr hL s) a b + readX H r hr hL q s a b := by
    funext q; rw [Matrix.add_apply]
  rw [this]
  exact contDiff_const.add (contDiff_readX_entry H r hr hL s a b)

/-- Each conjugated per-layer correction entry is `ContDiffAt p` on `unitSetConj`: the triple product
`−(deepBlkZ + readZ)·(deepBlkA + readX)⁻¹·(deepBlkY + readY)`, all factors entrywise `ContDiffAt` there. -/
theorem contDiffAt_schurCorrectionConj_entry (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (s : Fin L)
    (p : (Fin (deepestNReg H r) → ℝ) × (Fin (deepestNGauge H r) → ℝ))
    (hp : p ∈ unitSetConj H r B hB hr hL) (i : Fin (H s.castSucc - r)) (j : Fin (H s.succ - r)) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun q => schurCorrectionConj H r B hB hr hL q s i j) p := by
  -- `schurCorrectionConj q s = (−(deepBlkZ + readZ q s))·(deepBlkA + readX q s)⁻¹·(deepBlkY + readY q s)`.
  have hZinv : ∀ (a : Fin (H s.castSucc - r)) (k : Fin r),
      ContDiffAt ℝ (⊤ : ℕ∞)
        (fun q => ((-(deepBlkZ H r B hB hr hL s + readZ H r hr hL q s))
          * (deepBlkA H r B hB hr hL s + readX H r hr hL q s)⁻¹) a k) p := by
    intro a k
    refine contDiffAt_matrix_mul_entry (fun a' k' => ?_)
      (fun k' j' => contDiffAt_inv_deepBlkA_add_readX_entry H r B hB hr hL s p hp k' j') a k
    have : (fun q => (-(deepBlkZ H r B hB hr hL s + readZ H r hr hL q s)) a' k')
        = fun q => -((deepBlkZ H r B hB hr hL s) a' k' + readZ H r hr hL q s a' k') := by
      funext q; rw [Matrix.neg_apply, Matrix.add_apply]
    rw [this]
    exact ((contDiff_const.add (contDiff_readZ_entry H r hr hL s a' k')).neg).contDiffAt
  have hmul := contDiffAt_matrix_mul_entry
    (A := fun q => (-(deepBlkZ H r B hB hr hL s + readZ H r hr hL q s))
      * (deepBlkA H r B hB hr hL s + readX H r hr hL q s)⁻¹)
    (B := fun q => deepBlkY H r B hB hr hL s + readY H r hr hL q s) hZinv
    (fun k' j' => by
      have : (fun q => (deepBlkY H r B hB hr hL s + readY H r hr hL q s) k' j')
          = fun q => (deepBlkY H r B hB hr hL s) k' j' + readY H r hr hL q s k' j' := by
        funext q; rw [Matrix.add_apply]
      rw [this]
      exact (contDiff_const.add (contDiff_readY_entry H r hr hL s k' j')).contDiffAt) i j
  refine hmul.congr_of_eventuallyEq ?_
  filter_upwards with q
  show schurCorrectionConj H r B hB hr hL q s i j
      = ((-(deepBlkZ H r B hB hr hL s + readZ H r hr hL q s))
          * (deepBlkA H r B hB hr hL s + readX H r hr hL q s)⁻¹
          * (deepBlkY H r B hB hr hL s + readY H r hr hL q s)) i j
  rfl

/-- `schurShiftRawConj` is `ContDiffAt p` on `unitSetConj`: `paramsEquivFlatCLE (deepestM)` (a `ContDiff`
CLE) composed with the entrywise-`ContDiffAt` assembled `schurCorrectionConj`. -/
theorem contDiffAt_schurShiftRawConj (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (p : (Fin (deepestNReg H r) → ℝ) × (Fin (deepestNGauge H r) → ℝ))
    (hp : p ∈ unitSetConj H r B hB hr hL) :
    ContDiffAt ℝ (⊤ : ℕ∞) (schurShiftRawConj H r B hB hr hL) p := by
  have hraw : schurShiftRawConj H r B hB hr hL
      = fun q => paramsEquivFlatCLE (deepestM H r) (schurCorrectionConj H r B hB hr hL q) := by
    funext q
    rw [schurShiftRawConj, ← paramsEquivFlatCLE_coe (deepestM H r)]
  rw [hraw]
  refine (paramsEquivFlatCLE (deepestM H r)).contDiff.contDiffAt.comp p ?_
  refine contDiffAt_pi.mpr (fun s => contDiffAt_pi.mpr (fun i => contDiffAt_pi.mpr (fun j => ?_)))
  exact contDiffAt_schurCorrectionConj_entry H r B hB hr hL s p hp i j

/-- **The conjugated cutoff Schur shift is globally `ContDiff ⊤`** (`χ_conj • schurShiftRawConj`). On
`tsupport χ_conj ⊆ unitSetConj` the raw conjugated shift is `ContDiffAt` (`contDiffAt_schurShiftRawConj`);
off it the bump vanishes locally. The smoothness upgrade of `continuous_schurCutoffShiftConj`, demanded
by the conjugated `hTilde` local-diffeo consumer (global, not germ-at-`0`). -/
theorem contDiff_schurCutoffShiftConj (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (hDA : ∀ s : Fin L, IsUnit (deepBlkA H r B hB hr hL s)) :
    ContDiff ℝ (⊤ : ℕ∞) (schurCutoffShiftConj H r B hB hr hL hDA) := by
  have heq : schurCutoffShiftConj H r B hB hr hL hDA
      = fun p => ((cutoffBumpConj H r B hB hr hL hDA) p : ℝ) • schurShiftRawConj H r B hB hr hL p := rfl
  rw [heq]
  refine contDiff_contDiffBump_smul (cutoffBumpConj H r B hB hr hL hDA)
    (schurShiftRawConj H r B hB hr hL) (fun x hx => ?_)
  exact contDiffAt_schurShiftRawConj H r B hB hr hL x
    (tsupport_cutoffBumpConj_subset_unitSetConj H r B hB hr hL hDA hx)

/-! ## The general core-shear-symm strict derivative (arbitrary shift derivative)

`coreShearHomeo shift|>.symm q = (q.1, q.2.1 − shift(q.1, q.2.2), q.2.2)`. With `D(shift)(0) = Dδ`
(ARBITRARY — the conjugated shift's derivative is genuinely nonzero), the strict derivative at `0` is
`(r, c, s) ↦ (r, c − Dδ(r, s), s)`. The general form of `hasStrictFDerivAt_coreShearHomeo_symm_zero`
(which fixes `Dδ = 0` ⟹ derivative `id`). This `S` only moves the CORE slot; its reg/spec components
are the projections. -/

/-- The explicit core-shear-symm derivative CLM `(r, c, s) ↦ (r, c − Dδ(r, s), s)` from a shift
derivative `Dδ : Reg × Spec →L Core`. -/
noncomputable def coreShearSymmCLM {Reg Core Spec : Type*}
    [NormedAddCommGroup Reg] [NormedSpace ℝ Reg]
    [NormedAddCommGroup Core] [NormedSpace ℝ Core]
    [NormedAddCommGroup Spec] [NormedSpace ℝ Spec]
    (Dδ : Reg × Spec →L[ℝ] Core) : Reg × (Core × Spec) →L[ℝ] Reg × (Core × Spec) :=
  (ContinuousLinearMap.fst ℝ Reg (Core × Spec)).prod
    (((ContinuousLinearMap.fst ℝ Core Spec).comp (ContinuousLinearMap.snd ℝ Reg (Core × Spec))
        - Dδ.comp ((ContinuousLinearMap.fst ℝ Reg (Core × Spec)).prod
            ((ContinuousLinearMap.snd ℝ Core Spec).comp
              (ContinuousLinearMap.snd ℝ Reg (Core × Spec))))).prod
      ((ContinuousLinearMap.snd ℝ Core Spec).comp (ContinuousLinearMap.snd ℝ Reg (Core × Spec))))

@[simp] theorem coreShearSymmCLM_apply {Reg Core Spec : Type*}
    [NormedAddCommGroup Reg] [NormedSpace ℝ Reg]
    [NormedAddCommGroup Core] [NormedSpace ℝ Core]
    [NormedAddCommGroup Spec] [NormedSpace ℝ Spec]
    (Dδ : Reg × Spec →L[ℝ] Core) (q : Reg × (Core × Spec)) :
    coreShearSymmCLM Dδ q = (q.1, q.2.1 - Dδ (q.1, q.2.2), q.2.2) := rfl

/-- **The general core-shear-symm strict derivative.** `coreShearHomeo shift|>.symm` has strict
derivative `coreShearSymmCLM Dδ` at `0` when `D(shift)(0) = Dδ` (any `Dδ`; `shift 0` value need not
vanish — only the derivative matters). Generalizes `hasStrictFDerivAt_coreShearHomeo_symm_zero`. -/
theorem hasStrictFDerivAt_coreShearHomeo_symm_gen {Reg Core Spec : Type*}
    [NormedAddCommGroup Reg] [NormedSpace ℝ Reg]
    [NormedAddCommGroup Core] [NormedSpace ℝ Core]
    [NormedAddCommGroup Spec] [NormedSpace ℝ Spec]
    (shift : Reg × Spec → Core) (hcont : Continuous shift)
    (Dδ : Reg × Spec →L[ℝ] Core)
    (hshift : HasStrictFDerivAt shift Dδ ((0 : Reg), (0 : Spec))) :
    HasStrictFDerivAt (fun q : Reg × (Core × Spec) => (coreShearHomeo shift hcont).symm q)
      (coreShearSymmCLM Dδ) 0 := by
  -- `symm q = (q.1, (q.2.1 − shift (q.1, q.2.2), q.2.2))`.
  have hfst : HasStrictFDerivAt (fun q : Reg × (Core × Spec) => q.1)
      (ContinuousLinearMap.fst ℝ Reg (Core × Spec)) 0 :=
    (ContinuousLinearMap.fst ℝ Reg (Core × Spec)).hasStrictFDerivAt
  have hsnd : HasStrictFDerivAt (fun q : Reg × (Core × Spec) => q.2)
      (ContinuousLinearMap.snd ℝ Reg (Core × Spec)) 0 :=
    (ContinuousLinearMap.snd ℝ Reg (Core × Spec)).hasStrictFDerivAt
  have hcore : HasStrictFDerivAt (fun q : Reg × (Core × Spec) => q.2.1)
      ((ContinuousLinearMap.fst ℝ Core Spec).comp (ContinuousLinearMap.snd ℝ Reg (Core × Spec))) 0 :=
    ((ContinuousLinearMap.fst ℝ Core Spec).hasStrictFDerivAt).comp (x := (0 : Reg × (Core × Spec))) hsnd
  have hspec : HasStrictFDerivAt (fun q : Reg × (Core × Spec) => q.2.2)
      ((ContinuousLinearMap.snd ℝ Core Spec).comp (ContinuousLinearMap.snd ℝ Reg (Core × Spec))) 0 :=
    ((ContinuousLinearMap.snd ℝ Core Spec).hasStrictFDerivAt).comp (x := (0 : Reg × (Core × Spec))) hsnd
  -- The `(reg, spec)` read into `shift`'s domain.
  have hrs : HasStrictFDerivAt (fun q : Reg × (Core × Spec) => (q.1, q.2.2))
      ((ContinuousLinearMap.fst ℝ Reg (Core × Spec)).prod
        ((ContinuousLinearMap.snd ℝ Core Spec).comp
          (ContinuousLinearMap.snd ℝ Reg (Core × Spec)))) 0 :=
    hfst.prodMk hspec
  -- `shift ∘ (reg,spec)` has strict deriv `Dδ ∘ (read)` at `0` (the read sends `0 ↦ (0,0)`).
  have hshiftcomp : HasStrictFDerivAt (fun q : Reg × (Core × Spec) => shift (q.1, q.2.2))
      (Dδ.comp ((ContinuousLinearMap.fst ℝ Reg (Core × Spec)).prod
        ((ContinuousLinearMap.snd ℝ Core Spec).comp
          (ContinuousLinearMap.snd ℝ Reg (Core × Spec))))) 0 := by
    have hshift' : HasStrictFDerivAt shift Dδ
        (((0 : Reg × (Core × Spec)).1, (0 : Reg × (Core × Spec)).2.2)) := hshift
    exact hshift'.comp (x := (0 : Reg × (Core × Spec))) hrs
  -- The core slot `q.2.1 − shift (q.1, q.2.2)`.
  have hcoreshift : HasStrictFDerivAt
      (fun q : Reg × (Core × Spec) => q.2.1 - shift (q.1, q.2.2))
      ((ContinuousLinearMap.fst ℝ Core Spec).comp (ContinuousLinearMap.snd ℝ Reg (Core × Spec))
        - Dδ.comp ((ContinuousLinearMap.fst ℝ Reg (Core × Spec)).prod
            ((ContinuousLinearMap.snd ℝ Core Spec).comp
              (ContinuousLinearMap.snd ℝ Reg (Core × Spec))))) 0 :=
    hcore.sub hshiftcomp
  -- Assemble: `symm = (reg, (core − shift, spec))`.
  exact hfst.prodMk (hcoreshift.prodMk hspec)

/-! ## The conjugated `hTilde` — the reg-absorb peel's local-diffeo data (CONJ side)

The conjugated core absorb `deepestCoreAbsorbConj` has a NONZERO shift derivative `Dδ`, so
`D(coreAbsorbConj.symm)(0)` is the genuine shear `coreShearSymmCLM Dδ`, NOT `id` (unlike the bare side).
Nonetheless the conjugated straightening `regStraightenOf2 (deepestEFull ∘ coreAbsorbConj.symm)` is a
local diffeo at `0` with the SAME reg-block `F` as the bare PIN-1 frame: the shear `Dδ` only moves the
CORE slot, and `D(deepestEFull)(0)` ANNIHILATES the core direction (the value-fold atom
`deepestEFull_coreConstant`, a44dd7e4). So `eTilde = e` reuses `deepestEFull_deriv`'s `e`. -/

/-- **The core-in embedding** `Fin (flatDim deepestM) → ℝ →L DeepestSplit`, `c ↦ (0, c, 0)` — the
core-block reader for `D(deepestEFull)(0)`. -/
noncomputable def coreInCLM (H : Fin (L + 1) → ℕ) (r : ℕ) :
    (Fin (flatDim (deepestM H r)) → ℝ) →L[ℝ] DeepestSplit H r (deepestNGauge H r) :=
  (0 : (Fin (flatDim (deepestM H r)) → ℝ) →L[ℝ] (Fin (deepestNReg H r) → ℝ)).prod
    ((ContinuousLinearMap.id ℝ (Fin (flatDim (deepestM H r)) → ℝ)).prod 0)

@[simp] theorem coreInCLM_apply (H : Fin (L + 1) → ℕ) (r : ℕ)
    (c : Fin (flatDim (deepestM H r)) → ℝ) :
    coreInCLM H r c = ((0 : Fin (deepestNReg H r) → ℝ), c, (0 : Fin (deepestNGauge H r) → ℝ)) := rfl

/-- **`D(deepestEFull)(0)` annihilates the core direction** (`L = 2`): the value-fold atom
`deepestEFull_coreConstant` makes `c ↦ deepestEFull (0, c, 0)` constant, so its fderiv at `0` is `0`;
that fderiv IS `(fderiv deepestEFull 0).comp coreInCLM` (chain rule). -/
theorem deepestEFull_coreInBlock_zero (H : Fin 3 → ℕ) (r : ℕ)
    (hr : ∀ s : Fin 3, r ≤ H s) (hL : (1 : ℕ) ≤ 2)
    (J : Fin r ↪ Fin (H (Fin.last 2))) (hJfront : J = frontEmbed H r hr)
    (Pf : (s : Fin 2) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Qf : (s : Fin 2) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ)
    (hPtri : ∀ s : Fin 2, (Matrix.reindex (rThresholdSplit r (H s.castSucc) (hr s.castSucc))
        (rThresholdSplit r (H s.castSucc) (hr s.castSucc)) (Pf s)).toBlocks₁₂ = 0)
    (hQtri : ∀ s : Fin 2, (Matrix.reindex (rThresholdSplit r (H s.succ) (hr s.succ))
        (rThresholdSplit r (H s.succ) (hr s.succ)) (Qf s)).toBlocks₂₁ = 0) :
    (fderiv ℝ (deepestEFull H r hr hL J Pf Qf) 0).comp (coreInCLM H r)
      = (0 : (Fin (flatDim (deepestM H r)) → ℝ) →L[ℝ] (Fin (deepestNReg H r) → ℝ)) := by
  -- `g := fun c => deepestEFull (0, c, 0)` is CONSTANT (the value-fold atom).
  have hconst : (fun c : Fin (flatDim (deepestM H r)) → ℝ =>
        deepestEFull H r hr hL J Pf Qf
          ((0 : Fin (deepestNReg H r) → ℝ), c, (0 : Fin (deepestNGauge H r) → ℝ)))
      = fun _ => deepestEFull H r hr hL J Pf Qf
          ((0 : Fin (deepestNReg H r) → ℝ),
            (0 : Fin (flatDim (deepestM H r)) → ℝ), (0 : Fin (deepestNGauge H r) → ℝ)) := by
    funext c; exact deepestEFull_coreConstant H r hr hL J hJfront Pf Qf hPtri hQtri c
  -- Its fderiv at `0` is `0` (constant function).
  have hgderiv0 : fderiv ℝ (fun c : Fin (flatDim (deepestM H r)) → ℝ =>
        deepestEFull H r hr hL J Pf Qf
          ((0 : Fin (deepestNReg H r) → ℝ), c, (0 : Fin (deepestNGauge H r) → ℝ))) 0
      = 0 := by
    rw [hconst]
    exact (hasFDerivAt_const _ (0 : Fin (flatDim (deepestM H r)) → ℝ)).fderiv
  -- That same fderiv is `D_E.comp coreInCLM` (chain rule: `g = deepestEFull ∘ coreInCLM`).
  set D_E := fderiv ℝ (deepestEFull H r hr hL J Pf Qf) 0 with hD_E
  have hsd : HasStrictFDerivAt (deepestEFull H r hr hL J Pf Qf) D_E 0 :=
    (deepestEFull_contdiff H r hr hL J Pf Qf).hasStrictFDerivAt (by simp)
  have hcoreIn : HasStrictFDerivAt (fun c : Fin (flatDim (deepestM H r)) → ℝ =>
      ((0 : Fin (deepestNReg H r) → ℝ), c, (0 : Fin (deepestNGauge H r) → ℝ)))
      (coreInCLM H r) 0 := by
    have := (coreInCLM H r).hasStrictFDerivAt (x := (0 : Fin (flatDim (deepestM H r)) → ℝ))
    simpa [coreInCLM] using this
  have hsd0 : HasStrictFDerivAt (deepestEFull H r hr hL J Pf Qf) D_E
      ((0 : Fin (deepestNReg H r) → ℝ),
        (0 : Fin (flatDim (deepestM H r)) → ℝ), (0 : Fin (deepestNGauge H r) → ℝ)) := hsd
  have hchain := hsd0.comp (x := (0 : Fin (flatDim (deepestM H r)) → ℝ)) hcoreIn
  -- `hchain`'s fderiv = `D_E.comp coreInCLM`; uniqueness vs `hgderiv0`.
  have := hchain.hasFDerivAt.fderiv
  rw [this] at hgderiv0
  exact hgderiv0

/-- **The conjugated `hTilde`** — the conjugated reg-absorb peel's local-diffeo data. The conjugated
straightening `regStraightenOf2 (deepestEFull ∘ deepestCoreAbsorbConj.symm)` is `ContDiff ⊤` with an
INVERTIBLE strict derivative `eTilde` at `0`. Despite the conjugated shift's nonzero derivative `Dδ`
(so `D(coreAbsorbConj.symm)(0) = coreShearSymmCLM Dδ ≠ id`), the reg-block stays the PIN-1 frame `F`:
`Dδ` moves only the core slot, which `D(deepestEFull)(0)` annihilates (`deepestEFull_coreInBlock_zero`).
So `eTilde` is the SAME `e` from `deepestEFull_deriv`. The CONJ analogue of the wire's bare `hTilde`. -/
theorem deepestEFull_conj_hTilde_exists (H : Fin 3 → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last 2))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin 3, r ≤ H s) (hL : (1 : ℕ) ≤ 2)
    (hDA : ∀ s : Fin 2, IsUnit (deepBlkA H r B hB hr hL s))
    (hbdy : ∀ s : Fin 2, deepBlkY H r B hB hr hL s = 0 ∨ deepBlkZ H r B hB hr hL s = 0)
    (J : Fin r ↪ Fin (H (Fin.last 2))) (hJfront : J = frontEmbed H r hr)
    (Pf : (s : Fin 2) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Qf : (s : Fin 2) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ)
    (hPf : IsUnit (Pf (firstLayer hL))) (hQf : IsUnit (Qf (lastLayer hL)))
    (hQf0 : Qf (firstLayer hL) = 1) (hPfL : Pf (lastLayer hL) = 1)
    (hQf22 : IsUnit ((Matrix.reindex
        (pivotThresholdSplit r (H ((lastLayer hL).succ)) (hr _) (pivotJSucc H r hL J))
        (pivotThresholdSplit r (H ((lastLayer hL).succ)) (hr _) (pivotJSucc H r hL J))
        (Qf (lastLayer hL))).toBlocks₂₂))
    (hPtri : ∀ s : Fin 2, (Matrix.reindex (rThresholdSplit r (H s.castSucc) (hr s.castSucc))
        (rThresholdSplit r (H s.castSucc) (hr s.castSucc)) (Pf s)).toBlocks₁₂ = 0)
    (hQtri : ∀ s : Fin 2, (Matrix.reindex (rThresholdSplit r (H s.succ) (hr s.succ))
        (rThresholdSplit r (H s.succ) (hr s.succ)) (Qf s)).toBlocks₂₁ = 0) :
    ∃ eTilde : DeepestSplit H r (deepestNGauge H r) ≃L[ℝ] DeepestSplit H r (deepestNGauge H r),
      ContDiff ℝ (⊤ : ℕ∞)
        (regStraightenOf2 (fun q => deepestEFull H r hr hL J Pf Qf
          ((deepestCoreAbsorbConj H r B hB hr hL hDA).symm q))) ∧
      HasStrictFDerivAt (regStraightenOf2 (fun q => deepestEFull H r hr hL J Pf Qf
          ((deepestCoreAbsorbConj H r B hB hr hL hDA).symm q)))
        (eTilde : DeepestSplit H r (deepestNGauge H r) →L[ℝ]
          DeepestSplit H r (deepestNGauge H r)) 0 := by
  set coreAbsorb := deepestCoreAbsorbConj H r B hB hr hL hDA with hca_def
  -- PIN-1 invertible reg-block `F` (`(F:→L) = D_E.comp regInCLM`).
  set D_E := fderiv ℝ (deepestEFull H r hr hL J Pf Qf) 0 with hD_E
  have hsd : HasStrictFDerivAt (deepestEFull H r hr hL J Pf Qf) D_E 0 :=
    (deepestEFull_contdiff H r hr hL J Pf Qf).hasStrictFDerivAt (by simp)
  obtain ⟨F, hF⟩ := deepestEPivot_regSlice_fderiv H r hr hL (le_refl 2) J Pf Qf hPf hQf hQf0 hPfL hQf22
  -- `(F:→L) = D_E.comp regInCLM` — the same block identity `deepestEFull_deriv` derives.
  have hregIn : HasStrictFDerivAt (fun r0 : Fin (deepestNReg H r) → ℝ =>
      ((r0, 0) : DeepestSplit H r (deepestNGauge H r)))
      (regInCLM : (Fin (deepestNReg H r) → ℝ) →L[ℝ] DeepestSplit H r (deepestNGauge H r)) 0 := by
    have := (regInCLM : (Fin (deepestNReg H r) → ℝ) →L[ℝ]
      DeepestSplit H r (deepestNGauge H r)).hasStrictFDerivAt (x := 0)
    simpa [regInCLM] using this
  have hregslice : HasStrictFDerivAt (fun r0 : Fin (deepestNReg H r) → ℝ =>
      deepestEFull H r hr hL J Pf Qf (r0, 0))
      (F : (Fin (deepestNReg H r) → ℝ) →L[ℝ] (Fin (deepestNReg H r) → ℝ)) 0 := by
    have hbridge : (fun r0 : Fin (deepestNReg H r) → ℝ => deepestEFull H r hr hL J Pf Qf (r0, 0))
        = fun r0 : Fin (deepestNReg H r) → ℝ => deepestEPivot H r hr hL J Pf Qf (r0, 0) := by
      funext r0; exact deepestEFull_coreZero H r hr hL J Pf Qf r0 0
    rw [hbridge]; exact hF
  have hcomp : HasStrictFDerivAt (fun r0 : Fin (deepestNReg H r) → ℝ =>
      deepestEFull H r hr hL J Pf Qf (r0, 0)) (D_E.comp regInCLM) 0 :=
    hsd.comp (x := (0 : Fin (deepestNReg H r) → ℝ)) hregIn
  have hblock : (F : (Fin (deepestNReg H r) → ℝ) →L[ℝ] (Fin (deepestNReg H r) → ℝ))
      = D_E.comp (regInCLM : (Fin (deepestNReg H r) → ℝ) →L[ℝ]
        DeepestSplit H r (deepestNGauge H r)) := by
    have h1 := hcomp.hasFDerivAt.fderiv
    have h2 := hregslice.hasFDerivAt.fderiv
    rw [← h1, ← h2]
  -- D_E annihilates the core direction (the value-fold atom).
  have hcoreZero : D_E.comp (coreInCLM H r)
      = (0 : (Fin (flatDim (deepestM H r)) → ℝ) →L[ℝ] (Fin (deepestNReg H r) → ℝ)) :=
    deepestEFull_coreInBlock_zero H r hr hL J hJfront Pf Qf hPtri hQtri
  -- The conjugated shift's (arbitrary) strict derivative `Dδ` at `0`.
  have hcds : ContDiff ℝ (⊤ : ℕ∞) (schurCutoffShiftConj H r B hB hr hL hDA) :=
    contDiff_schurCutoffShiftConj H r B hB hr hL hDA
  set Dδ := fderiv ℝ (schurCutoffShiftConj H r B hB hr hL hDA) 0 with hDδ
  have hshift_sd : HasStrictFDerivAt (schurCutoffShiftConj H r B hB hr hL hDA) Dδ 0 :=
    hcds.hasStrictFDerivAt (by simp)
  -- `coreAbsorb.symm` ContDiff ⊤ + strict deriv `coreShearSymmCLM Dδ` at `0`.
  have hsymm_cd : ContDiff ℝ (⊤ : ℕ∞)
      (fun q : DeepestSplit H r (deepestNGauge H r) => coreAbsorb.symm q) := by
    rw [hca_def, deepestCoreAbsorbConj]
    exact contDiff_coreShearHomeo_symm (schurCutoffShiftConj H r B hB hr hL hDA)
      (continuous_schurCutoffShiftConj H r B hB hr hL hDA) hcds
  have hsymm_sd : HasStrictFDerivAt
      (fun q : DeepestSplit H r (deepestNGauge H r) => coreAbsorb.symm q)
      (coreShearSymmCLM Dδ) 0 := by
    rw [hca_def, deepestCoreAbsorbConj]
    exact hasStrictFDerivAt_coreShearHomeo_symm_gen (schurCutoffShiftConj H r B hB hr hL hDA)
      (continuous_schurCutoffShiftConj H r B hB hr hL hDA) Dδ hshift_sd
  -- `Ecomp := deepestEFull ∘ coreAbsorb.symm`.
  set Ecomp : DeepestSplit H r (deepestNGauge H r) → (Fin (deepestNReg H r) → ℝ) :=
    fun q => deepestEFull H r hr hL J Pf Qf (coreAbsorb.symm q) with hEcomp
  -- (A) ContDiff.
  have hEcomp_cd : ContDiff ℝ (⊤ : ℕ∞) Ecomp :=
    (deepestEFull_contdiff H r hr hL J Pf Qf).comp hsymm_cd
  have hcontdiff : ContDiff ℝ (⊤ : ℕ∞) (regStraightenOf2 Ecomp) :=
    contDiff_regStraightenOf2 Ecomp hEcomp_cd
  -- (B) Strict deriv: `D(Ecomp)(0) = D_E ∘ (coreShearSymmCLM Dδ)` (chain rule, `symm 0 = 0`).
  have hsymm0 : coreAbsorb.symm (0 : DeepestSplit H r (deepestNGauge H r)) = 0 := by
    have hca_base : coreAbsorb 0 = 0 := by
      rw [hca_def]
      exact deepestCoreAbsorbConj_basepoint H r B hB hr hL hDA hbdy
    conv_lhs => rw [← hca_base]; rw [coreAbsorb.symm_apply_apply]
  have hEcomp_sd : HasStrictFDerivAt Ecomp (D_E.comp (coreShearSymmCLM Dδ)) 0 := by
    have hsd' : HasStrictFDerivAt (deepestEFull H r hr hL J Pf Qf) D_E
        (coreAbsorb.symm (0 : DeepestSplit H r (deepestNGauge H r))) := by
      rw [hsymm0]; exact hsd
    exact hsd'.comp (x := (0 : DeepestSplit H r (deepestNGauge H r))) hsymm_sd
  have hreg_sd := hasStrictFDerivAt_regStraightenOf2_gen Ecomp (D_E.comp (coreShearSymmCLM Dδ)) hEcomp_sd
  -- The reg-block of `D_E ∘ S` equals `F`: `(D_E∘S∘regInCLM) r0 = D_E(r0, −Dδ(r0,0), 0) = F r0`
  -- (the `−Dδ(r0,0)` core perturbation is annihilated by `D_E.comp coreInCLM = 0`).
  have hregblock : (F : (Fin (deepestNReg H r) → ℝ) →L[ℝ] (Fin (deepestNReg H r) → ℝ))
      = (D_E.comp (coreShearSymmCLM Dδ)).comp
        (regInCLM : (Fin (deepestNReg H r) → ℝ) →L[ℝ] DeepestSplit H r (deepestNGauge H r)) := by
    refine ContinuousLinearMap.ext (fun r0 => ?_)
    rw [hblock]
    -- LHS: `D_E (r0, 0, 0)`; RHS: `D_E (coreShearSymmCLM Dδ (r0, 0, 0)) = D_E (r0, −Dδ(r0,0), 0)`.
    simp only [ContinuousLinearMap.comp_apply, regInCLM_apply, coreShearSymmCLM_apply]
    -- `(r0,0,0).1 = r0`, `(r0,0,0).2.1 = 0`, `(r0,0,0).2.2 = 0`; so RHS arg = `(r0, 0 − Dδ(r0,0), 0)`.
    show D_E ((r0 : Fin (deepestNReg H r) → ℝ),
        (0 : Fin (flatDim (deepestM H r)) → ℝ), (0 : Fin (deepestNGauge H r) → ℝ))
      = D_E ((r0, (0 : Fin (flatDim (deepestM H r)) → ℝ)
          - Dδ (r0, (0 : Fin (deepestNGauge H r) → ℝ)), (0 : Fin (deepestNGauge H r) → ℝ)))
    -- Decompose the RHS arg as `(r0,0,0) + (0, −Dδ(r0,0), 0)` and use linearity + `hcoreZero`.
    rw [show ((r0 : Fin (deepestNReg H r) → ℝ),
          (0 : Fin (flatDim (deepestM H r)) → ℝ) - Dδ (r0, (0 : Fin (deepestNGauge H r) → ℝ)),
          (0 : Fin (deepestNGauge H r) → ℝ))
        = ((r0, (0 : Fin (flatDim (deepestM H r)) → ℝ), (0 : Fin (deepestNGauge H r) → ℝ))
            : DeepestSplit H r (deepestNGauge H r))
          + coreInCLM H r (- Dδ (r0, (0 : Fin (deepestNGauge H r) → ℝ))) from by
      simp only [coreInCLM_apply, Prod.mk_add_mk, add_zero, zero_add, zero_sub]]
    rw [map_add]
    have : D_E (coreInCLM H r (- Dδ (r0, (0 : Fin (deepestNGauge H r) → ℝ)))) = 0 := by
      have := ContinuousLinearMap.ext_iff.1 hcoreZero (- Dδ (r0, (0 : Fin (deepestNGauge H r) → ℝ)))
      simpa using this
    rw [this, add_zero]
  -- Build `eTilde` from the reg-block being the invertible `F`.
  obtain ⟨e, he⟩ := regStraightenTotalCLM2_equiv_of_regBlock_isUnit
    (W := (Fin (flatDim (deepestM H r)) → ℝ) × (Fin (deepestNGauge H r) → ℝ))
    (D_E.comp (coreShearSymmCLM Dδ)) F hregblock
  refine ⟨e, hcontdiff, ?_⟩
  rw [he]
  exact hreg_sd

/-- **The bare `hTilde`** — the BARE reg-absorb peel's local-diffeo data (IS the wire's `hTilde`,
DeepestL2Wiring:238). The bare core absorb `deepestCoreAbsorb` has a VANISHING shift derivative
(`hasStrictFDerivAt_schurCutoffShift_zero`), so `D(coreAbsorb.symm)(0) = id` and `eTilde = e` from
`deepestEFull_deriv` directly. Packaged as a standalone lemma (parallel to the conjugated
`deepestEFull_conj_hTilde_exists`) so the LINK-2 wire consumes both uniformly. -/
theorem deepestEFull_bare_hTilde_exists (H : Fin 3 → ℕ) (r : ℕ)
    (hr : ∀ s : Fin 3, r ≤ H s) (hL : (1 : ℕ) ≤ 2)
    (J : Fin r ↪ Fin (H (Fin.last 2)))
    (Pf : (s : Fin 2) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Qf : (s : Fin 2) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ)
    (hPf : IsUnit (Pf (firstLayer hL))) (hQf : IsUnit (Qf (lastLayer hL)))
    (hQf0 : Qf (firstLayer hL) = 1) (hPfL : Pf (lastLayer hL) = 1)
    (hQf22 : IsUnit ((Matrix.reindex
        (pivotThresholdSplit r (H ((lastLayer hL).succ)) (hr _) (pivotJSucc H r hL J))
        (pivotThresholdSplit r (H ((lastLayer hL).succ)) (hr _) (pivotJSucc H r hL J))
        (Qf (lastLayer hL))).toBlocks₂₂)) :
    ∃ eTilde : DeepestSplit H r (deepestNGauge H r) ≃L[ℝ] DeepestSplit H r (deepestNGauge H r),
      ContDiff ℝ (⊤ : ℕ∞)
        (regStraightenOf2 (fun q => deepestEFull H r hr hL J Pf Qf
          ((deepestCoreAbsorb H r hr hL).symm q))) ∧
      HasStrictFDerivAt (regStraightenOf2 (fun q => deepestEFull H r hr hL J Pf Qf
          ((deepestCoreAbsorb H r hr hL).symm q)))
        (eTilde : DeepestSplit H r (deepestNGauge H r) →L[ℝ]
          DeepestSplit H r (deepestNGauge H r)) 0 := by
  set coreAbsorb := deepestCoreAbsorb H r hr hL with hca_def
  obtain ⟨D_E, e, hsd, he⟩ :=
    deepestEFull_deriv H r hr hL (le_refl 2) J Pf Qf hPf hQf hQf0 hPfL hQf22
  have hcds : ContDiff ℝ (⊤ : ℕ∞) (schurCutoffShift H r hr hL) :=
    contDiff_schurCutoffShift H r hr hL
  have hsymm_cd : ContDiff ℝ (⊤ : ℕ∞)
      (fun q : DeepestSplit H r (deepestNGauge H r) => coreAbsorb.symm q) := by
    rw [hca_def, deepestCoreAbsorb]
    exact contDiff_coreShearHomeo_symm (schurCutoffShift H r hr hL)
      (continuous_schurCutoffShift H r hr hL) hcds
  have hsymm_sd : HasStrictFDerivAt
      (fun q : DeepestSplit H r (deepestNGauge H r) => coreAbsorb.symm q)
      (ContinuousLinearMap.id ℝ (DeepestSplit H r (deepestNGauge H r))) 0 := by
    rw [hca_def, deepestCoreAbsorb]
    exact hasStrictFDerivAt_coreShearHomeo_symm_zero (schurCutoffShift H r hr hL)
      (continuous_schurCutoffShift H r hr hL) (hasStrictFDerivAt_schurCutoffShift_zero H r hr hL)
  set Ecomp : DeepestSplit H r (deepestNGauge H r) → (Fin (deepestNReg H r) → ℝ) :=
    fun q => deepestEFull H r hr hL J Pf Qf (coreAbsorb.symm q) with hEcomp
  have hEcomp_cd : ContDiff ℝ (⊤ : ℕ∞) Ecomp :=
    (deepestEFull_contdiff H r hr hL J Pf Qf).comp hsymm_cd
  have hcontdiff : ContDiff ℝ (⊤ : ℕ∞) (regStraightenOf2 Ecomp) :=
    contDiff_regStraightenOf2 Ecomp hEcomp_cd
  have hEcomp_sd : HasStrictFDerivAt Ecomp D_E 0 := by
    have hsymm0 : coreAbsorb.symm (0 : DeepestSplit H r (deepestNGauge H r)) = 0 := by
      have hca_base : coreAbsorb 0 = 0 := by
        rw [hca_def]; exact (deepest_coreAbsorb_exists H r hr hL).1
      conv_lhs => rw [← hca_base]; rw [coreAbsorb.symm_apply_apply]
    have hsd' : HasStrictFDerivAt (deepestEFull H r hr hL J Pf Qf) D_E
        (coreAbsorb.symm (0 : DeepestSplit H r (deepestNGauge H r))) := by
      rw [hsymm0]; exact hsd
    have hchain := hsd'.comp (x := (0 : DeepestSplit H r (deepestNGauge H r))) hsymm_sd
    have hchain' : HasStrictFDerivAt Ecomp (D_E.comp
        (ContinuousLinearMap.id ℝ (DeepestSplit H r (deepestNGauge H r)))) 0 := hchain
    rw [ContinuousLinearMap.comp_id] at hchain'
    exact hchain'
  have hreg_sd := hasStrictFDerivAt_regStraightenOf2_gen Ecomp D_E hEcomp_sd
  refine ⟨e, hcontdiff, ?_⟩
  rw [he]
  exact hreg_sd

end DLNFibre.DLN.RLCT
