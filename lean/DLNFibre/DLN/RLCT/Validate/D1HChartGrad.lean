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

/-- The flat-coordinate reconstruction `gmap w = flatSymm (w + flat v)` — the smooth `Params`-valued
map whose loss-entry gradients feed H_indep. -/
noncomputable def gmapAt (H : Fin (L + 1) → ℕ) (v : Params H) :
    (Fin (flatDim H) → ℝ) → Params H :=
  fun w => (paramsEquivFlat H).symm (w + (paramsEquivFlat H) v)

/-- The per-layer-entry strict derivative of `gmapAt`: the coordinate proj CLM at `flatIdx`. -/
noncomputable def gmapDeriv (H : Fin (L + 1) → ℕ)
    (s : Fin L) (i : Fin (H s.castSucc)) (j : Fin (H s.succ)) : (Fin (flatDim H) → ℝ) →L[ℝ] ℝ :=
  ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (flatDim H) => ℝ) (flatIdx H s i j)

/-- **The loss-entry gradient** (step 3a). Each loss entry `g_ij = (prod − B)_ij` in flat
origin-centred coordinates has, at any point `w₀`, the explicit strict derivative
`prodAuxEntryDeriv H (gmapAt H v) w₀ gmapDeriv L _ i j` — the banked Leibniz gradient
(`hasStrictFDerivAt_prodAux_entry_explicit`) fed the layer-derivative `gmapDeriv` from step 2a. The
constant `−B` does not change the derivative. This gradient functional is the input to the H_indep
rank/independence argument (whether the `nReg` selected `∇g_ij(0)` are linearly independent). -/
theorem hasStrictFDerivAt_lossEntry (H : Fin (L + 1) → ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (v : Params H)
    (w₀ : Fin (flatDim H) → ℝ) (i : Fin (H 0)) (j : Fin (H (Fin.last L))) :
    HasStrictFDerivAt
      (fun w => (prod H (gmapAt H v w) - B) i j)
      (prodAuxEntryDeriv H (gmapAt H v) w₀ (fun s a b => gmapDeriv H s a b) L
        (Nat.lt_succ_self L) i j) w₀ := by
  -- the layer-entry derivatives (step 2a), repackaged at `gmapAt`/`gmapDeriv`.
  have hlayer : ∀ (s : Fin L) (a : Fin (H s.castSucc)) (b : Fin (H s.succ)),
      HasStrictFDerivAt (fun w => gmapAt H v w s a b) (gmapDeriv H s a b) w₀ := by
    intro s a b
    exact hasStrictFDerivAt_gmap_entry H v s a b w₀
  -- the Leibniz gradient of the product entry (banked), at `k = L`.
  have hprodEntry : HasStrictFDerivAt (fun w => prodAux H (gmapAt H v w) L (Nat.lt_succ_self L) i j)
      (prodAuxEntryDeriv H (gmapAt H v) w₀ (fun s a b => gmapDeriv H s a b) L
        (Nat.lt_succ_self L) i j) w₀ :=
    hasStrictFDerivAt_prodAux_entry_explicit H (gmapAt H v) w₀
      (fun s a b => gmapDeriv H s a b) hlayer L (Nat.lt_succ_self L) i j
  -- `prod = prodAux L`; the `−B` entry is a constant subtraction.
  have hsubst : (fun w => (prod H (gmapAt H v w) - B) i j)
      = fun w => prodAux H (gmapAt H v w) L (Nat.lt_succ_self L) i j - B i j := rfl
  rw [hsubst]
  exact hprodEntry.sub_const _

end DLNFibre.DLN.RLCT
