import DLNFibre.DLN.RLCT.Validate.DeepestSchurShift
import DLNFibre.DLN.RLCT.Foundations.ParamsFlatLinear

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

/-- Each reduced-core read `(paramsEquivFlat (deepestM)).symm q.2.1 s a b` is `ContDiff ⊤` in `q`: the
core slot `q.2.1` is a `ContDiff` linear projection, `(paramsEquivFlat (deepestM)).symm` is a `ContDiff`
continuous-linear equiv (`paramsEquivFlatCLE.symm`), then layer/entry selection are `ContDiff` applies.
The full-`framedParams` analogue of the `readX/Y/Z` ContDiff (the L2-PIN2 core read). -/
theorem contDiff_coreRead_entry (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (s : Fin L)
    (a : Fin (deepestM H r s.castSucc)) (b : Fin (deepestM H r s.succ)) :
    ContDiff ℝ (⊤ : ℕ∞) (fun q : DeepestSplit H r (deepestNGauge H r) =>
      (paramsEquivFlat (deepestM H r)).symm q.2.1 s a b) := by
  -- `(paramsEquivFlat (deepestM)).symm = (paramsEquivFlatCLE (deepestM)).symm` as functions (same
  -- forward map ⟹ same inverse), and the CLE's symm is `ContDiff`. Then layer/entry selection + the
  -- ContDiff core-slot projection compose.
  have hsymm_coe : ⇑(paramsEquivFlat (deepestM H r)).symm
      = ⇑(paramsEquivFlatCLE (deepestM H r)).symm := by
    funext y
    apply (paramsEquivFlat (deepestM H r)).injective
    rw [(paramsEquivFlat (deepestM H r)).apply_symm_apply]
    have h1 : (paramsEquivFlat (deepestM H r)) ((paramsEquivFlatCLE (deepestM H r)).symm y)
        = (paramsEquivFlatCLE (deepestM H r)) ((paramsEquivFlatCLE (deepestM H r)).symm y) := by
      rw [paramsEquivFlatCLE_coe]
    rw [h1, (paramsEquivFlatCLE (deepestM H r)).apply_symm_apply]
  have hcle : ContDiff ℝ (⊤ : ℕ∞) (fun y : Fin (flatDim (deepestM H r)) → ℝ =>
      (paramsEquivFlat (deepestM H r)).symm y) := by
    rw [hsymm_coe]
    exact (paramsEquivFlatCLE (deepestM H r)).symm.contDiff
  -- The scalar entry `y ↦ (paramsEquivFlat M).symm y s a b` is a continuous-linear functional of `y`
  -- (eval ∘ the CLE.symm); compose with the ContDiff core-slot projection `q ↦ q.2.1`. Built via the
  -- CLM `evalCLM` to dodge the `Matrix`-norm-instance friction (no intermediate Matrix-typed ContDiff).
  set evalCLM : (Params (deepestM H r)) →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (deepestM H r s.succ) => ℝ) b).comp
      ((ContinuousLinearMap.proj (R := ℝ)
          (φ := fun _ : Fin (deepestM H r s.castSucc) => Fin (deepestM H r s.succ) → ℝ) a).comp
        (ContinuousLinearMap.proj (R := ℝ)
          (φ := fun s : Fin L => Matrix (Fin (deepestM H r s.castSucc))
            (Fin (deepestM H r s.succ)) ℝ) s)) with hevalCLM
  have hfun : (fun q : DeepestSplit H r (deepestNGauge H r) =>
      (paramsEquivFlat (deepestM H r)).symm q.2.1 s a b)
      = fun q : DeepestSplit H r (deepestNGauge H r) =>
        evalCLM ((paramsEquivFlat (deepestM H r)).symm q.2.1) := by
    funext q; rfl
  rw [hfun]
  exact evalCLM.contDiff.comp (hcle.comp (contDiff_snd.fst))

/-- **The per-layer FRAME-CONJUGATED normal-form matrix** (#80 frame-wiring). The deepest-point block
corner `corM = reindex(fromBlocks 1 0 0 0)` PLUS the frame-conjugated raw deviation
`P_s · reindex(fromBlocks X_s Y_s Z_s T_s) · Q_s`, where `(P_s, Q_s)` is the per-layer gauge frame
(supplied explicitly so this def stays free of the rank machinery / `Classical.choose`). The gauge
blocks `(X_s, Y_s, Z_s)` are the regular/spectator gauge DEVIATION entries (off `gaugeSlotRead`); `T_s`
is the reduced-core deviation block.

The frame is wired into the READING (not the MP `split`): at the deepest gauge slot the deviation is
`0` so `framedLayer = corM` (frame-INDEPENDENT base, preserving the idempotent fold), and away from it
the deviation is frame-conjugated to MATCH the endpoint-telescoped product
(`framedLayer (frame) (raw deviation blocks of w) = P_s · (paramsSymm w)_s · Q_s` via
`P_s · deepestPoint_s · Q_s = corM`). With `P = Q = 1` it degenerates to the old additive chart
`corM + reindex(fromBlocks X Y Z T)`. -/
noncomputable def framedLayer (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (s : Fin L)
    (P : Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Q : Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ)
    (X : Matrix (Fin r) (Fin r) ℝ) (Y : Matrix (Fin r) (Fin (H s.succ - r)) ℝ)
    (Z : Matrix (Fin (H s.castSucc - r)) (Fin r) ℝ)
    (T : Matrix (Fin (H s.castSucc - r)) (Fin (H s.succ - r)) ℝ) :
    Matrix (Fin (H s.castSucc)) (Fin (H s.succ)) ℝ :=
  Matrix.reindex (rThresholdSplit r (H s.castSucc) (hr s.castSucc)).symm
      (rThresholdSplit r (H s.succ) (hr s.succ)).symm
      (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℝ) 0 0 0)
    + P * Matrix.reindex (rThresholdSplit r (H s.castSucc) (hr s.castSucc)).symm
        (rThresholdSplit r (H s.succ) (hr s.succ)).symm
        (Matrix.fromBlocks X Y Z T) * Q

/-- **The framed parameter tuple** `C : Params H` reconstructed from a `DeepestSplit` point: each layer
is `framedLayer` of the gauge blocks `(X_s, Y_s, Z_s)` (read off the reg+spectator slot via
`readX/readY/readZ`) and the reduced core `T_s` (read off the core slot via `paramsEquivFlat (deepestM)`).
The framed product `∏C = prod H (framedParams q)` is the shared object; `dlnLoss = ‖∏A − B‖²` relates to
`‖∏C − D‖²` through the endpoint conjugation (the #77 (iii) telescoping). Decision-independent (the
product `∏C` is well-defined regardless of (iii)/(B); those affect how it relates to `dlnLoss`/`Ereg`). -/
noncomputable def framedParams (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (P : (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Q : (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ)
    (q : DeepestSplit H r (deepestNGauge H r)) : Params H :=
  fun s =>
    framedLayer H r hr s (P s) (Q s)
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
    (P : (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Q : (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ)
    (p : (Fin (deepestNReg H r) → ℝ) × (Fin (deepestNGauge H r) → ℝ)) : Params H :=
  fun s =>
    framedLayer H r hr s (P s) (Q s)
      (readX H r hr hL p s) (readY H r hr hL p s) (readZ H r hr hL p s)
      (0 : Matrix (Fin (H s.castSucc - r)) (Fin (H s.succ - r)) ℝ)

/-- At the origin gauge slot, `framedParamsReg` is the **block-normal identity chain**: every layer is
`framedLayer 0 0 0 0 = reindex (fromBlocks 1 0 0 0)` (the deepest value `blockdiag[I_r, 0]`). The base
fact for `deepestEPivot`'s `_base` (the residual of `∏ blockdiag[I_r,0]` is `0`). -/
theorem framedParamsReg_zero (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (P : (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Q : (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ) (s : Fin L) :
    framedParamsReg H r hr hL P Q 0 s
      = Matrix.reindex (rThresholdSplit r (H s.castSucc) (hr s.castSucc)).symm
          (rThresholdSplit r (H s.succ) (hr s.succ)).symm
          (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℝ) 0 0 0) := by
  -- At the deepest gauge slot the deviation `fromBlocks 0 0 0 0 = 0`, so the frame term
  -- `P · reindex 0 · Q = 0` vanishes and `framedLayer = corM` (frame-INDEPENDENT base).
  simp only [framedParamsReg, framedLayer, readX_zero H r hr hL s, readY_zero H r hr hL s,
    readZ_zero H r hr hL s]
  rw [show Matrix.fromBlocks (0 : Matrix (Fin r) (Fin r) ℝ) 0 0 0 = 0 from by
      ext a b; rcases a with a | a <;> rcases b with b | b <;> rfl]
  simp [Matrix.reindex_apply, Matrix.submatrix_zero]

/-- Each `framedParamsReg` layer ENTRY is `ContDiff ⊤` in the `(reg, gauge)` slots: the entry is a
`fromBlocks (1+X) Y Z 0` block entry (reindexed), i.e. `1+readX` / `readY` / `readZ` / `0`, each
`ContDiff` (the read entries + `const`). The `_contdiff` layer input to `contDiff_prod_entry`. -/
theorem contDiff_framedParamsReg_entry (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (P : (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Q : (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ) (s : Fin L)
    (i : Fin (H s.castSucc)) (j : Fin (H s.succ)) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p => framedParamsReg H r hr hL P Q p s i j) := by
  -- The entry is `corM i j + (P · reindex(fromBlocks X Y Z 0) · Q) i j`. `corM i j` is a constant;
  -- the frame term expands by `Matrix.mul_apply` to `∑ m, ∑ n, P i m · reindex(...) m n · Q n j` with
  -- `P, Q` constant and each `reindex(...) m n` a block read (`readX/Y/Z` entry, ContDiff) or `0`.
  -- Each entry of the raw-deviation matrix `D(p) = reindex(fromBlocks (readX) (readY) (readZ) 0)` is
  -- ContDiff (block read).
  have hD : ∀ (m : Fin (H s.castSucc)) (n : Fin (H s.succ)),
      ContDiff ℝ (⊤ : ℕ∞) (fun p => (Matrix.reindex
          (rThresholdSplit r (H s.castSucc) (hr s.castSucc)).symm
          (rThresholdSplit r (H s.succ) (hr s.succ)).symm
          (Matrix.fromBlocks (readX H r hr hL p s) (readY H r hr hL p s) (readZ H r hr hL p s)
            (0 : Matrix (Fin (H s.castSucc - r)) (Fin (H s.succ - r)) ℝ))) m n) := by
    intro m n
    have hmn : (fun p => (Matrix.reindex (rThresholdSplit r (H s.castSucc) (hr s.castSucc)).symm
          (rThresholdSplit r (H s.succ) (hr s.succ)).symm
          (Matrix.fromBlocks (readX H r hr hL p s) (readY H r hr hL p s) (readZ H r hr hL p s)
            (0 : Matrix (Fin (H s.castSucc - r)) (Fin (H s.succ - r)) ℝ))) m n)
        = fun p => Matrix.fromBlocks (readX H r hr hL p s) (readY H r hr hL p s)
            (readZ H r hr hL p s) (0 : Matrix (Fin (H s.castSucc - r)) (Fin (H s.succ - r)) ℝ)
            ((rThresholdSplit r (H s.castSucc) (hr s.castSucc)) m)
            ((rThresholdSplit r (H s.succ) (hr s.succ)) n) := by
      funext p
      simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm]
    rw [hmn]
    rcases (rThresholdSplit r (H s.castSucc) (hr s.castSucc)) m with a | a <;>
      rcases (rThresholdSplit r (H s.succ) (hr s.succ)) n with b | b <;>
      simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
        Matrix.fromBlocks_apply₂₂, Matrix.zero_apply]
    · exact contDiff_readX_entry H r hr hL s a b
    · exact contDiff_readY_entry H r hr hL s a b
    · exact contDiff_readZ_entry H r hr hL s a b
    · exact contDiff_const
  -- The framedParamsReg entry = `corM i j + (P s * D(p) * Q s) i j`; the latter is a double sum of
  -- (const · D-entry · const) by `Matrix.mul_apply`.
  have hentry : (fun p => framedParamsReg H r hr hL P Q p s i j)
      = fun p =>
          (Matrix.reindex (rThresholdSplit r (H s.castSucc) (hr s.castSucc)).symm
              (rThresholdSplit r (H s.succ) (hr s.succ)).symm
              (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℝ) 0 0 0)) i j
          + (P s * Matrix.reindex (rThresholdSplit r (H s.castSucc) (hr s.castSucc)).symm
                  (rThresholdSplit r (H s.succ) (hr s.succ)).symm
                  (Matrix.fromBlocks (readX H r hr hL p s) (readY H r hr hL p s)
                    (readZ H r hr hL p s)
                    (0 : Matrix (Fin (H s.castSucc - r)) (Fin (H s.succ - r)) ℝ)) * Q s) i j := by
    funext p
    simp only [framedParamsReg, framedLayer, Matrix.add_apply]
  rw [hentry]
  refine contDiff_const.add ?_
  -- `(P · D · Q) i j = ∑ n, (P · D) i n · Q n j = ∑ n, (∑ m, P i m · D m n) · Q n j`.
  simp only [Matrix.mul_apply]
  refine ContDiff.sum (fun n _ => ?_)
  refine ContDiff.mul (ContDiff.sum (fun m _ => ?_)) contDiff_const
  exact contDiff_const.mul (hD m n)

/-- Each FULL `framedParams` layer ENTRY is `ContDiff ⊤` in the `DeepestSplit` slot — the same block-read
structure as `framedParamsReg`, but the `(1,1)` block carries the reduced core read (`contDiff_coreRead_entry`)
instead of `0`. The full-product analogue, the `_contdiff` input for `deepestEFull`. -/
theorem contDiff_framedParams_entry (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (P : (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Q : (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ) (s : Fin L)
    (i : Fin (H s.castSucc)) (j : Fin (H s.succ)) :
    ContDiff ℝ (⊤ : ℕ∞) (fun q : DeepestSplit H r (deepestNGauge H r) =>
      framedParams H r hr hL P Q q s i j) := by
  -- Each entry of `D(q) = reindex(fromBlocks (readX) (readY) (readZ) (coreRead))` is ContDiff (a block
  -- read or the core read), then the framedLayer entry is `corM + (P·D·Q)`.
  have hD : ∀ (m : Fin (H s.castSucc)) (n : Fin (H s.succ)),
      ContDiff ℝ (⊤ : ℕ∞) (fun q : DeepestSplit H r (deepestNGauge H r) => (Matrix.reindex
          (rThresholdSplit r (H s.castSucc) (hr s.castSucc)).symm
          (rThresholdSplit r (H s.succ) (hr s.succ)).symm
          (Matrix.fromBlocks (readX H r hr hL (q.1, q.2.2) s) (readY H r hr hL (q.1, q.2.2) s)
            (readZ H r hr hL (q.1, q.2.2) s)
            ((paramsEquivFlat (deepestM H r)).symm q.2.1 s))) m n) := by
    intro m n
    have hmn : (fun q : DeepestSplit H r (deepestNGauge H r) => (Matrix.reindex
          (rThresholdSplit r (H s.castSucc) (hr s.castSucc)).symm
          (rThresholdSplit r (H s.succ) (hr s.succ)).symm
          (Matrix.fromBlocks (readX H r hr hL (q.1, q.2.2) s) (readY H r hr hL (q.1, q.2.2) s)
            (readZ H r hr hL (q.1, q.2.2) s)
            ((paramsEquivFlat (deepestM H r)).symm q.2.1 s))) m n)
        = fun q : DeepestSplit H r (deepestNGauge H r) =>
            Matrix.fromBlocks (readX H r hr hL (q.1, q.2.2) s) (readY H r hr hL (q.1, q.2.2) s)
              (readZ H r hr hL (q.1, q.2.2) s) ((paramsEquivFlat (deepestM H r)).symm q.2.1 s)
              ((rThresholdSplit r (H s.castSucc) (hr s.castSucc)) m)
              ((rThresholdSplit r (H s.succ) (hr s.succ)) n) := by
      funext q
      simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm]
    rw [hmn]
    -- The reg slot `(q.1, q.2.2)` is ContDiff (fst + snd∘snd); compose with the read entries.
    have hreg : ContDiff ℝ (⊤ : ℕ∞) (fun q : DeepestSplit H r (deepestNGauge H r) =>
        ((q.1, q.2.2) : (Fin (deepestNReg H r) → ℝ) × (Fin (deepestNGauge H r) → ℝ))) :=
      contDiff_fst.prodMk (contDiff_snd.snd)
    rcases (rThresholdSplit r (H s.castSucc) (hr s.castSucc)) m with a | a <;>
      rcases (rThresholdSplit r (H s.succ) (hr s.succ)) n with b | b <;>
      simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
        Matrix.fromBlocks_apply₂₂]
    · exact (contDiff_readX_entry H r hr hL s a b).comp hreg
    · exact (contDiff_readY_entry H r hr hL s a b).comp hreg
    · exact (contDiff_readZ_entry H r hr hL s a b).comp hreg
    · exact contDiff_coreRead_entry H r hr hL s a b
  have hentry : (fun q : DeepestSplit H r (deepestNGauge H r) => framedParams H r hr hL P Q q s i j)
      = fun q : DeepestSplit H r (deepestNGauge H r) =>
          (Matrix.reindex (rThresholdSplit r (H s.castSucc) (hr s.castSucc)).symm
              (rThresholdSplit r (H s.succ) (hr s.succ)).symm
              (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℝ) 0 0 0)) i j
          + (P s * Matrix.reindex (rThresholdSplit r (H s.castSucc) (hr s.castSucc)).symm
                  (rThresholdSplit r (H s.succ) (hr s.succ)).symm
                  (Matrix.fromBlocks (readX H r hr hL (q.1, q.2.2) s) (readY H r hr hL (q.1, q.2.2) s)
                    (readZ H r hr hL (q.1, q.2.2) s)
                    ((paramsEquivFlat (deepestM H r)).symm q.2.1 s)) * Q s) i j := by
    funext q
    simp only [framedParams, framedLayer, Matrix.add_apply]
  rw [hentry]
  refine contDiff_const.add ?_
  simp only [Matrix.mul_apply]
  refine ContDiff.sum (fun n _ => ?_)
  refine ContDiff.mul (ContDiff.sum (fun m _ => ?_)) contDiff_const
  exact contDiff_const.mul (hD m n)

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

`deepestEPivot` is `pack ∘ residual ∘ reindex ∘ prod ∘ framedParamsReg`; its `ContDiff ⊤` reduces to
`ContDiff ⊤ (fun x => prod H (g x))` for `g = framedParamsReg` (each layer affine in the slots, so
`ContDiff`). The product is the dependent-Fin `prodAux` fold — `ContDiff` ENTRY-WISE (matrix = nested
`Pi`; `contDiff_pi'` twice), mirroring the green `continuous_prodAux`: base `prodAux 0 = 1` const, step
`(prodAux k * layer) i j = ∑ m, prodAux k i m · layer m j` (`ContDiff.sum` of `ContDiff.mul`). No
`ContDiff.matrix_mul` lemma exists in v4.29 — the entry-wise route sidesteps it. -/

/-- **`ContDiff` of the partial-product ENTRIES** under a smooth reconstruction `g : X → Params H`
(each layer ENTRY `ContDiff ⊤`). Entry-wise to dodge the matrix-norm-instance friction (`Matrix` has
no canonical `NormedSpace` — `ContDiff` of a matrix-VALUED map needs an opt-in norm; the entries are
plain ℝ-valued). Induction on `k`, mirroring `continuous_prodAux`: the matrix-mul step is
`(prodAux k * layer) i j = ∑ m, prodAux k i m · layer m j` (`ContDiff.sum` of `ContDiff.mul`). -/
theorem contDiff_prodAux_entry {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (H : Fin (L + 1) → ℕ) (g : X → Params H)
    (hg : ∀ (s : Fin L) (i : Fin (H s.castSucc)) (j : Fin (H s.succ)),
      ContDiff ℝ (⊤ : ℕ∞) (fun x => g x s i j))
    (k : ℕ) (hk : k < L + 1) :
    ∀ (i : Fin (H 0)) (j : Fin (H ⟨k, hk⟩)),
      ContDiff ℝ (⊤ : ℕ∞) (fun x => prodAux H (g x) k hk i j) := by
  revert hk
  induction k with
  | zero =>
      intro hk i j
      -- `prodAux 0 = 1`; each entry is `0` or `1`, constant.
      have : (fun x => prodAux H (g x) 0 hk i j)
          = fun _ => (1 : Matrix (Fin (H 0)) (Fin (H 0)) ℝ) i j := rfl
      rw [this]; exact contDiff_const
  | succ k ih =>
      intro hk i j
      have hk' : k < L + 1 := Nat.lt_of_succ_lt hk
      have hkL : k < L := Nat.lt_of_succ_lt_succ hk
      have e1 : (⟨k, hk'⟩ : Fin (L + 1)) = (⟨k, hkL⟩ : Fin L).castSucc := by
        apply Fin.ext; simp [Fin.castSucc]
      have e2 : (⟨k + 1, hk⟩ : Fin (L + 1)) = (⟨k, hkL⟩ : Fin L).succ := by
        apply Fin.ext; simp [Fin.succ]
      -- `prodAux (k+1) i j = ∑ m, prodAux k i m · (cast layer k) m j`.
      have hentry : (fun x => prodAux H (g x) (k + 1) hk i j)
          = fun x => ∑ m, prodAux H (g x) k hk' i m
              * ((by rw [e1, e2]; exact g x ⟨k, hkL⟩ :
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
