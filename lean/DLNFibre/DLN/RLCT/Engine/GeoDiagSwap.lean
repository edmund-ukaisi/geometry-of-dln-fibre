import DLNFibre.DLN.RLCT.Engine.GeoJacobianFold

/-!
# `DLNFibre.DLN.RLCT.Engine.GeoDiagSwap` — the diagonal-normalization source swap `S` (t11, #35 fork 15)

The cube-invariant, det-1 SOURCE swap `S = flatSwapCLE p d` that the fork-15 diagonal-normalization
composes into `geoChartMap` as `(β ∘ S)`: it transposes flat coordinates `p` (the off-diagonal fan-out
pivot `cNodeOf node ⟨pivot⟩`) and `d` (the `divBirthCoord` diagonal the ledger references), so `β ∘ S`
blows up the DIAGONAL cell `z_d` where pure `β` blew up `z_p`. Codex-confirmed realization
(`threads/10-coverage/codex/s35-swap-realization-answer.md`, Option A): a flat-coordinate transposition
`E⁻¹ ∘ (precompose by Equiv.swap p d) ∘ E` (`E = paramsEquivFlatCLE`), composed on the SOURCE
(`β ∘ S`, NOT `S ∘ β` — target swapping is det-neutral but leaves the atom reading `z_p`).

Banked here (all sorry-free): `flatSwapCLE`, the flat-read `z_c(S w) = z_{swap p d c}(w)`, involutivity,
`|det D S| = 1` (via `clm_involutive_abs_det_one`), differentiability, and cube-membership invariance
(for the cover, clause C2). The per-edge det through `β ∘ S` is then `|z_d(w)|^{dCN−1}` via
`abs_det_fderiv_comp_det_one_gauge` + the banked per-edge atom (`geoChartMap_fderiv_det`).
-/

namespace DLNFibre.DLN.RLCT.Engine

open DLNFibre.DLN.RLCT
open scoped BigOperators

variable {L : ℕ} {M : Fin (L + 1) → ℕ}

/-- **The diagonal-normalization source swap** `S` as a continuous linear equivalence of `Params M`:
transpose flat coordinates `p` and `d` (`E⁻¹ ∘ (precompose by `Equiv.swap p d`) ∘ E`). Linear (so its
fderiv is itself) and involutive (so `|det| = 1`). -/
noncomputable def flatSwapCLE (M : Fin (L + 1) → ℕ) (p d : Fin (flatDim M)) :
    Params M ≃L[ℝ] Params M :=
  (paramsEquivFlatCLE M).trans
    (((LinearEquiv.piCongrLeft ℝ (fun _ : Fin (flatDim M) => ℝ)
        (Equiv.swap p d)).toContinuousLinearEquiv).trans (paramsEquivFlatCLE M).symm)

/-- **The flat read of `S`**: `z_c(S w) = z_{swap p d c}(w)` — the swap relabels the flat coordinate. -/
theorem flatSwapCLE_apply_flat (M : Fin (L + 1) → ℕ) (p d : Fin (flatDim M)) (w : Params M)
    (c : Fin (flatDim M)) :
    paramsEquivFlat M (flatSwapCLE M p d w) c = paramsEquivFlat M w (Equiv.swap p d c) := by
  have hcoe : ⇑(LinearEquiv.piCongrLeft ℝ (fun _ : Fin (flatDim M) => ℝ) (Equiv.swap p d))
      = ⇑(Equiv.piCongrLeft (fun _ : Fin (flatDim M) => ℝ) (Equiv.swap p d)) := rfl
  have hE : ⇑(paramsEquivFlatCLE M) = ⇑(paramsEquivFlat M) := paramsEquivFlatCLE_coe M
  unfold flatSwapCLE
  rw [← paramsEquivFlatCLE_coe]
  simp only [ContinuousLinearEquiv.trans_apply, LinearEquiv.coe_toContinuousLinearEquiv',
    ContinuousLinearEquiv.apply_symm_apply, hcoe, hE]
  rw [show c = Equiv.swap p d (Equiv.swap p d c) from (Equiv.swap_apply_self p d c).symm,
    Equiv.piCongrLeft_apply_apply, Equiv.swap_apply_self]

/-- `S` is an involution (a transposition applied twice is the identity). -/
theorem flatSwapCLE_involutive (M : Fin (L + 1) → ℕ) (p d : Fin (flatDim M)) (w : Params M) :
    flatSwapCLE M p d (flatSwapCLE M p d w) = w := by
  apply (paramsEquivFlat M).injective
  funext c
  rw [flatSwapCLE_apply_flat, flatSwapCLE_apply_flat, Equiv.swap_apply_self]

/-- The underlying CLM of `S` composed with itself is the identity (involution, CLM form). -/
theorem flatSwapCLE_comp_self (M : Fin (L + 1) → ℕ) (p d : Fin (flatDim M)) :
    (flatSwapCLE M p d).toContinuousLinearMap.comp (flatSwapCLE M p d).toContinuousLinearMap
      = ContinuousLinearMap.id ℝ (Params M) := by
  ext w
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearEquiv.coe_coe]
  exact flatSwapCLE_involutive M p d w

/-- **`|det D S| = 1`** — `S` is a linear involution, so its determinant has modulus `1`
(`clm_involutive_abs_det_one`). The det-neutrality the `β ∘ S` composition needs. -/
theorem flatSwapCLE_abs_det_fderiv_one (M : Fin (L + 1) → ℕ) (p d : Fin (flatDim M)) (x : Params M) :
    |(fderiv ℝ (flatSwapCLE M p d) x).det| = 1 := by
  rw [(flatSwapCLE M p d).hasFDerivAt.fderiv]
  exact clm_involutive_abs_det_one _ (flatSwapCLE_comp_self M p d)

/-- `S` is differentiable (it is a continuous linear equivalence). -/
theorem flatSwapCLE_differentiable (M : Fin (L + 1) → ℕ) (p d : Fin (flatDim M)) :
    Differentiable ℝ (flatSwapCLE M p d) :=
  (flatSwapCLE M p d).differentiable

/-- **Cube-membership invariance** (clause C2): `S` maps the flat cube into itself both ways — a
coordinate transposition preserves the symmetric box `∀ c, |z_c| ≤ R`. -/
theorem flatSwapCLE_mem_cube_iff (M : Fin (L + 1) → ℕ) (p d : Fin (flatDim M)) (R : ℝ) (w : Params M) :
    flatSwapCLE M p d w ∈ ⇑(paramsEquivFlat M) ⁻¹' cubeBox (flatDim M) R ↔
      w ∈ ⇑(paramsEquivFlat M) ⁻¹' cubeBox (flatDim M) R := by
  simp only [Set.mem_preimage, cubeBox, Set.mem_pi, Set.mem_univ, forall_true_left]
  constructor
  · intro h c
    have := h (Equiv.swap p d c)
    rwa [flatSwapCLE_apply_flat, Equiv.swap_apply_self] at this
  · intro h c
    rw [flatSwapCLE_apply_flat]
    exact h (Equiv.swap p d c)

end DLNFibre.DLN.RLCT.Engine
