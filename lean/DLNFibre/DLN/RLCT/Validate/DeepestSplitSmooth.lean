import DLNFibre.DLN.RLCT.Validate.DeepestSplitConcrete

/-!
# `DLNFibre.DLN.RLCT.Validate.DeepestSplitSmooth` — `deepestSplit` is a smooth affine chart

`deepestSplit` (in `DeepestSplitConcrete`) is typed only as a `Homeomorph`, but its construction is
`subRight wstar` (the affine translation `w ↦ w − wstar`) followed by a chain of coordinate
isomorphisms (`piCongrLeft` reindex, `sumPiEquivProdPi` regroupings, `prodCongr`), every one of which
is `ContinuousLinearEquiv` — so the whole map is the affine map `w ↦ L(w − wstar)` for the linear
coordinate iso `L = deepestSplitCLE`. This module records that structure as the reusable facts the
diffeo-bridge build (`hstep2`, `DeepestGaugeConstruction`) needs to transport smoothness through `split`:

* `deepestSplitCLE` — the linear part of `deepestSplit` as a `≃L[ℝ]`.
* `deepestSplit_eq_cle` — `deepestSplit w = deepestSplitCLE (w − wstar)` (definitional).
* `contDiff_deepestSplit` / `contDiff_deepestSplit_symm` — both directions are `ContDiff ⊤`.
* `hasStrictFDerivAt_deepestSplit` — the strict Fréchet derivative everywhere is `deepestSplitCLE`
  (the translation contributes the identity, dropping the basepoint).

All declarations are sorry-free: the CLE composition matches the `Homeomorph` composition by `rfl`
(both reduce to the same underlying coordinate map), and the smooth/derivative facts are the standard
affine-map calculus (`ContinuousLinearEquiv.contDiff`, `HasStrictFDerivAt` chain rule + `sub_const`).
-/

open MeasureTheory Matrix
open scoped ENNReal BigOperators Topology
namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-- **The linear part of `deepestSplit`** as a `ContinuousLinearEquiv`: the `piCongrLeft` reindex
followed by the two `sumPiEquivProdPi` regroupings and the `prodCongr` — verbatim `deepestSplit`'s
factors with the leading `subRight wstar` translation dropped. `deepestSplit w = deepestSplitCLE
(w − wstar)` (`deepestSplit_eq_cle`). -/
noncomputable def deepestSplitCLE (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) :
    (Fin (flatDim H) → ℝ) ≃L[ℝ] DeepestSplit H r (deepestNGauge H r) :=
  (ContinuousLinearEquiv.piCongrLeft ℝ (fun _ => ℝ) (deepestRoleIndexEquiv H r hr hL)).trans
    ((ContinuousLinearEquiv.sumPiEquivProdPi ℝ (Fin (deepestNReg H r))
        (Fin (flatDim (deepestM H r)) ⊕ Fin (deepestNGauge H r)) (fun _ => ℝ)).trans
      (ContinuousLinearEquiv.prodCongr (ContinuousLinearEquiv.refl ℝ (Fin (deepestNReg H r) → ℝ))
        (ContinuousLinearEquiv.sumPiEquivProdPi ℝ (Fin (flatDim (deepestM H r)))
          (Fin (deepestNGauge H r)) (fun _ => ℝ))))

/-- **`deepestSplit` is the affine map `w ↦ deepestSplitCLE (w − wstar)`** (definitional). The CLE
composition matches the `Homeomorph` composition because both reduce to the same coordinate map; the
`subRight wstar` factor is the translation `w ↦ w − wstar`. -/
theorem deepestSplit_eq_cle (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (wstar w : Fin (flatDim H) → ℝ) :
    deepestSplit H r hr hL wstar w = deepestSplitCLE H r hr hL (w - wstar) := rfl

/-- **`deepestSplit` is `ContDiff ⊤`** — the affine map `deepestSplitCLE ∘ (· − wstar)`. -/
theorem contDiff_deepestSplit (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (wstar : Fin (flatDim H) → ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (deepestSplit H r hr hL wstar) := by
  have heq : ⇑(deepestSplit H r hr hL wstar)
      = fun w => deepestSplitCLE H r hr hL (w - wstar) := by
    funext w; exact deepestSplit_eq_cle H r hr hL wstar w
  rw [heq]
  exact (deepestSplitCLE H r hr hL).contDiff.comp (contDiff_id.sub contDiff_const)

/-- **The strict Fréchet derivative of `deepestSplit` is `deepestSplitCLE` everywhere.** The
translation `· − wstar` has derivative `id`, so the affine map's strict derivative is its linear
part. (Used at `wstar` to feed `rlctAtOn_comp_localDiffeo`, but holds at every base point.) -/
theorem hasStrictFDerivAt_deepestSplit (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (wstar w : Fin (flatDim H) → ℝ) :
    HasStrictFDerivAt (deepestSplit H r hr hL wstar)
      ((deepestSplitCLE H r hr hL : (Fin (flatDim H) → ℝ) →L[ℝ]
        DeepestSplit H r (deepestNGauge H r))) w := by
  have heq : ⇑(deepestSplit H r hr hL wstar)
      = fun w => deepestSplitCLE H r hr hL (w - wstar) := by
    funext w; exact deepestSplit_eq_cle H r hr hL wstar w
  rw [heq]
  have hsub : HasStrictFDerivAt (fun w : Fin (flatDim H) → ℝ => w - wstar)
      (ContinuousLinearMap.id ℝ (Fin (flatDim H) → ℝ)) w :=
    (hasStrictFDerivAt_id w).sub_const wstar
  have hcle := (deepestSplitCLE H r hr hL).hasStrictFDerivAt (x := w - wstar)
  simpa using hcle.comp w hsub

/-- **`deepestSplit.symm` is the affine map `q ↦ deepestSplitCLE.symm q + wstar`** (definitional). -/
theorem deepestSplit_symm_eq_cle (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (wstar : Fin (flatDim H) → ℝ)
    (q : DeepestSplit H r (deepestNGauge H r)) :
    (deepestSplit H r hr hL wstar).symm q = (deepestSplitCLE H r hr hL).symm q + wstar := rfl

/-- **`deepestSplit.symm` is `ContDiff ⊤`** — the affine map `deepestSplitCLE.symm + wstar`. -/
theorem contDiff_deepestSplit_symm (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (wstar : Fin (flatDim H) → ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (deepestSplit H r hr hL wstar).symm := by
  have heq : ⇑(deepestSplit H r hr hL wstar).symm
      = fun q => (deepestSplitCLE H r hr hL).symm q + wstar := by
    funext q; exact deepestSplit_symm_eq_cle H r hr hL wstar q
  rw [heq]
  exact (deepestSplitCLE H r hr hL).symm.contDiff.add contDiff_const

/-- **The strict Fréchet derivative of `deepestSplit.symm` is `deepestSplitCLE.symm` everywhere.** -/
theorem hasStrictFDerivAt_deepestSplit_symm (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (wstar : Fin (flatDim H) → ℝ)
    (q : DeepestSplit H r (deepestNGauge H r)) :
    HasStrictFDerivAt (deepestSplit H r hr hL wstar).symm
      (((deepestSplitCLE H r hr hL).symm : DeepestSplit H r (deepestNGauge H r) →L[ℝ]
        (Fin (flatDim H) → ℝ))) q := by
  have heq : ⇑(deepestSplit H r hr hL wstar).symm
      = fun q => (deepestSplitCLE H r hr hL).symm q + wstar := by
    funext q; exact deepestSplit_symm_eq_cle H r hr hL wstar q
  rw [heq]
  have hcle := (deepestSplitCLE H r hr hL).symm.hasStrictFDerivAt (x := q)
  simpa using hcle.add_const wstar

end DLNFibre.DLN.RLCT
