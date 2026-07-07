import DLNFibre.DLN.RLCT.Validate.DeepestGaugeChart
import DLNFibre.DLN.RLCT.Validate.DeepestPsiStrictDeriv
import DLNFibre.DLN.RLCT.Foundations.ParamsFlatLinear

/-!
# `DLNFibre.DLN.RLCT.Validate.DeepestPsi` — the general-`L` absorbing diffeo `Ψ` (#120 `hstep2`, piece 1)

The absorbing diffeo of the general-`L` deepest-gauge bridge acts on the **core** coordinate of the
split space `DeepestSplit H r nGauge` by the per-layer left shear `S_s ↦ (1 − K_s)·S_s`, and is the
identity on the regular and spectator coordinates. Here `S_s` is layer `s`'s reduced-core matrix
(the core coordinate decoded through `paramsEquivFlat (deepestM H r)`) and `K_s` is the off-pivot
coupling (`Kcoup` at the framed DLN blocks — the cert's `K_k`), a square `m_s × m_s` matrix depending
on the whole split point.

`Ψ` is defined here **parameterized by the coupling family `K`** — its signature is fixed and the
`ContDiff`/strict-derivative facts (pieces 2–3) are proved against `K`'s analytic hypotheses. The
concrete DLN coupling (relating `K_s` to the framed product via the abstract Schur recursion
`schur_product_ldu_rec` and the `Fin (H k)`-width block bridge) is supplied at assembly (pieces 4–5);
it does not enter this definition or the derivative computation.

At the split basepoint `0` (the deepest point in split coordinates) the core vanishes, so
`Ψ K 0 = 0` unconditionally (`deepestPsiCoreShear_basepoint`) — the fixed point the RLCT-invariance
bridge `rlctAtOn_comp_localDiffeo` requires.
-/

namespace DLNFibre.DLN.RLCT

open Matrix

variable {L : ℕ}

/-- The **coupling family** shape: for each layer `s : Fin L`, a square `m_s × m_s` matrix
(`m_s = deepestM H r s.castSucc`) depending on the split point — the cert's `K_s`, left-multiplying
the layer's reduced core in the absorbing shear. -/
abbrev DeepestCoupling (H : Fin (L + 1) → ℕ) (r nGauge : ℕ) : Type :=
  (s : Fin L) → DeepestSplit H r nGauge →
    Matrix (Fin (deepestM H r s.castSucc)) (Fin (deepestM H r s.castSucc)) ℝ

/-- **The general-`L` absorbing shear `Ψ` on `DeepestSplit`** (parameterized by the coupling `K`).
Regular (`.1`) and spectator (`.2.2`) coordinates are unchanged; on the core (`.2.1`), decode to the
reduced-core tuple `S`, replace each layer `S_s` by `(1 − K_s q)·S_s`, and re-encode. -/
noncomputable def deepestPsiCoreShear (H : Fin (L + 1) → ℕ) (r nGauge : ℕ)
    (K : DeepestCoupling H r nGauge) (q : DeepestSplit H r nGauge) :
    DeepestSplit H r nGauge :=
  (q.1,
    (paramsEquivFlat (deepestM H r)
        (fun s => (1 - K s q) * (paramsEquivFlat (deepestM H r)).symm q.2.1 s),
      q.2.2))

/-- **`Ψ` fixes the split basepoint** (`Ψ K 0 = 0`), for any coupling `K`. At `q = 0` the core
coordinate is `0`, so every decoded layer `S_s = 0` and `(1 − K_s 0)·0 = 0`; re-encoding `0` gives
`0`, and the regular/spectator coordinates are `0`. This is the fixed point `rlctAtOn_comp_localDiffeo`
needs. -/
theorem deepestPsiCoreShear_basepoint (H : Fin (L + 1) → ℕ) (r nGauge : ℕ)
    (K : DeepestCoupling H r nGauge) :
    deepestPsiCoreShear H r nGauge K 0 = 0 := by
  -- `paramsEquivFlat` preserves `0` (it agrees with the linear `paramsEquivFlatCLE`).
  have hfwd0 : paramsEquivFlat (deepestM H r) (0 : Params (deepestM H r)) = 0 := by
    rw [← paramsEquivFlatCLE_coe]; exact map_zero _
  have hsymm0 : (paramsEquivFlat (deepestM H r)).symm
      (0 : Fin (flatDim (deepestM H r)) → ℝ) = (0 : Params (deepestM H r)) := by
    conv_lhs => rw [← hfwd0]
    exact (paramsEquivFlat (deepestM H r)).symm_apply_apply 0
  unfold deepestPsiCoreShear
  -- The core coordinate at `0` decodes to the zero tuple, so each sheared layer is `(1 − K_s 0)·0 = 0`.
  have hshear : (fun s => (1 - K s 0) * (paramsEquivFlat (deepestM H r)).symm
        (0 : DeepestSplit H r nGauge).2.1 s) = (0 : Params (deepestM H r)) := by
    funext s
    show (1 - K s 0) * (paramsEquivFlat (deepestM H r)).symm
        (0 : Fin (flatDim (deepestM H r)) → ℝ) s = 0
    rw [hsymm0]
    show (1 - K s 0) * (0 : Matrix (Fin (deepestM H r s.castSucc))
        (Fin (deepestM H r s.succ)) ℝ) = 0
    exact Matrix.mul_zero _
  rw [hshear]
  -- Re-encoding the zero tuple gives `0`; the regular/spectator coordinates of `0` are `0`.
  show ((0 : DeepestSplit H r nGauge).1,
      (paramsEquivFlat (deepestM H r) (0 : Params (deepestM H r)),
        (0 : DeepestSplit H r nGauge).2.2)) = 0
  rw [hfwd0]
  rfl

end DLNFibre.DLN.RLCT
