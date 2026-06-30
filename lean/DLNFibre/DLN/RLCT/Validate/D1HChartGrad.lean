import DLNFibre.DLN.RLCT.Validate.D1HChartFlatten
import DLNFibre.DLN.RLCT.Validate.DeepestRegSliceFderiv

/-!
# `DLNFibre.DLN.RLCT.Validate.D1HChartGrad` — the gradient functional for the concrete D1 chart

Step 2a of the concrete selected-minor `Φ` build: the gradient of each loss-entry
`g_ij = (prod − B)_ij` in the flat, origin-centred coordinates, as a continuous-linear functional on
`Fin N → ℝ`. Built ENTRY-WISE (per the `Params H`-not-normed finding): the reconstruction
`gmap w = flatSymm (w + flat v)` has each layer entry `gmap w s i j = (w + flat v)(idx s i j)` a
single flat coordinate (`paramsEquivFlat_symm_entry`), so its strict derivative is the
coordinate-projection CLM `proj idx` — clean, no normed `Params`. These per-entry `g'` feed the
banked Leibniz gradient `hasStrictFDerivAt_prodAux_entry_explicit`, giving each product entry —
hence each `g_ij` — its explicit gradient functional, the input to the H_indep rank argument.

STATUS: step 2a built sorry-free, axiom-clean.
-/

open MeasureTheory
open scoped ENNReal Topology
namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-- The flat index of the layer coordinate `(s, i, j)` under the flattening. -/
noncomputable def flatIdx (H : Fin (L + 1) → ℕ)
    (s : Fin L) (i : Fin (H s.castSucc)) (j : Fin (H s.succ)) : Fin (flatDim H) :=
  (Fintype.equivFin (FlatIdx H)) ⟨⟨s, i⟩, j⟩

/-- **The layer-entry gradient** (step 2a). The reconstruction `gmap w = flatSymm (w + flat v)` has
each layer entry `w ↦ gmap w s i j` equal to the single flat coordinate `w ↦ (w + flat v)(idx)`
(`paramsEquivFlat_symm_entry`); its strict derivative at any point is the coordinate-projection CLM
`ContinuousLinearMap.proj (flatIdx H s i j)`. The `g'` feeding the banked Leibniz gradient. -/
theorem hasStrictFDerivAt_gmap_entry (H : Fin (L + 1) → ℕ) (v : Params H)
    (s : Fin L) (i : Fin (H s.castSucc)) (j : Fin (H s.succ)) (w : Fin (flatDim H) → ℝ) :
    HasStrictFDerivAt
      (fun w : Fin (flatDim H) → ℝ => ((paramsEquivFlat H).symm (w + (paramsEquivFlat H) v)) s i j)
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (flatDim H) => ℝ)
        (flatIdx H s i j)) w := by
  -- rewrite the entry as the flat coordinate `(w + flat v)(idx)`.
  have hfun : (fun w : Fin (flatDim H) → ℝ =>
        ((paramsEquivFlat H).symm (w + (paramsEquivFlat H) v)) s i j)
      = fun w => (w + (paramsEquivFlat H) v) (flatIdx H s i j) := by
    funext w; rw [paramsEquivFlat_symm_entry]; rfl
  rw [hfun]
  -- `w ↦ (w + c)(idx)`: the coordinate proj of `w + c`. Derivative = `proj idx`.
  have hproj : HasStrictFDerivAt
      (fun w : Fin (flatDim H) → ℝ => w (flatIdx H s i j))
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (flatDim H) => ℝ) (flatIdx H s i j)) w :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (flatDim H) => ℝ)
      (flatIdx H s i j)).hasStrictFDerivAt
  -- `(w + c)(idx) = w idx + c idx`; add a constant.
  have heq : (fun w : Fin (flatDim H) → ℝ => (w + (paramsEquivFlat H) v) (flatIdx H s i j))
      = fun w => w (flatIdx H s i j) + ((paramsEquivFlat H) v) (flatIdx H s i j) := by
    funext w; simp [Pi.add_apply]
  rw [heq]
  exact hproj.add_const _

end DLNFibre.DLN.RLCT
