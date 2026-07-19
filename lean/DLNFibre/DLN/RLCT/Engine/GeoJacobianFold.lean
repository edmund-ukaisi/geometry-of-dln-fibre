import DLNFibre.DLN.RLCT.Engine.GeoJacobianSpec

/-!
# `DLNFibre.DLN.RLCT.Engine.GeoJacobianFold` — the parametric chain-rule fold (t11, Phase 2)

The construction-STABLE half of the fold-Jacobian: a chain-rule / determinant-multiplicativity fold over
an ABSTRACT list of maps (`abs_det_fderiv_foldr_comp`), stated PARAMETRIC in the path so it survives the
`GeoChart.lean` emission churn (t10's tGeo reshape + the rollover/chartless `id`-passthrough) — per
team-lead ruling (b). The composite determinant is the product of the per-factor determinants **at the
intermediate fold points**:

    |det D(f₀ ∘ f₁ ∘ … ∘ fₙ₋₁) w| = ∏ᵢ |det D(fᵢ)( (fᵢ₊₁ ∘ … ∘ fₙ₋₁) w )|

The per-factor determinant is then read off by the banked per-edge atoms (`geoChartMap_fderiv_det` on-cone,
`geoChartMap_fderiv_det_offcone` = 1 for the `id`-passthrough edges) once the concrete atlas stabilises.
The remaining (cert-gated) step is the **regrouping** of these intermediate-point factors onto the
source-`w` per-piece ledger (finding-2 addendum; `fold-jacobian-specify-addendum-t11.md`).

`Params M` is finite-dimensional, so every `Differentiable` map has a genuine `fderiv` and
`ContinuousLinearMap.det` is multiplicative under composition.
-/

namespace DLNFibre.DLN.RLCT.Engine

open DLNFibre.DLN.RLCT
open scoped BigOperators

variable {L : ℕ} {M : Fin (L + 1) → ℕ}

/-- **`ContinuousLinearMap.det` is multiplicative under composition** on `Params M` (via
`LinearMap.det_comp` on the underlying linear maps). -/
theorem clm_det_comp (A B : Params M →L[ℝ] Params M) : (A.comp B).det = A.det * B.det := by
  change LinearMap.det (A.comp B : Params M →ₗ[ℝ] Params M)
      = LinearMap.det (A : Params M →ₗ[ℝ] Params M) * LinearMap.det (B : Params M →ₗ[ℝ] Params M)
  rw [ContinuousLinearMap.coe_comp, LinearMap.det_comp]

/-- **An involutive continuous linear map has determinant of modulus `1`** (`E ∘ E = id ⟹ |det E| = 1`).
The det-neutrality atom the diagonal-normalization swap consumes (fork 15): the source swap
`S = (pivot ↔ divBirthCoord diagonal)` is a coordinate transposition, hence an involution, so composing
it into `geoChartMap` leaves the per-edge Jacobian modulus unchanged (`|det S| = 1`) — the atom then
reads the diagonal cell where it read the pivot. Proof: `det E · det E = det (E ∘ E) = det id = 1`, so
`det E = ±1`. -/
theorem clm_involutive_abs_det_one (E : Params M →L[ℝ] Params M)
    (hinv : E.comp E = ContinuousLinearMap.id ℝ (Params M)) : |E.det| = 1 := by
  have hsq : E.det * E.det = 1 := by
    rw [← clm_det_comp, hinv]
    change LinearMap.det (ContinuousLinearMap.id ℝ (Params M) : Params M →ₗ[ℝ] Params M) = 1
    simp [LinearMap.det_id]
  rcases mul_self_eq_one_iff.mp hsq with h | h <;> rw [h] <;> norm_num

/-- **The intermediate-point per-factor determinant product** of a list of maps: the abs-det of each
map's derivative, read at the point reached by folding the SUFFIX of the list onto `w`. The RHS of the
chain-rule fold. -/
noncomputable def foldrCompAbsDet : List (Params M → Params M) → Params M → ℝ
  | [], _ => 1
  | f :: fs, w => |(fderiv ℝ f ((fs.foldr (· ∘ ·) id) w)).det| * foldrCompAbsDet fs w

/-- The `foldr`-composite of a list of `Differentiable` maps is `Differentiable`. -/
theorem foldr_comp_differentiable (l : List (Params M → Params M))
    (hdiff : ∀ f ∈ l, Differentiable ℝ f) : Differentiable ℝ (l.foldr (· ∘ ·) id) := by
  induction l with
  | nil =>
    simp only [List.foldr_nil]
    exact (differentiable_id : Differentiable ℝ (id : Params M → Params M))
  | cons f fs ih =>
    simp only [List.foldr_cons]
    exact (hdiff f (List.mem_cons_self)).comp
      (ih (fun g hg => hdiff g (List.mem_cons_of_mem f hg)))

/-- **The parametric chain-rule fold** (Phase 2, construction-stable): for a list of `Differentiable`
maps, the composite's Fréchet-derivative determinant (modulus) is the product of the per-factor
determinant moduli at the intermediate fold points. Consumes the banked per-edge atoms at instantiation
(`geoChartMap_fderiv_det` / `_offcone`); the `id`-passthrough edges contribute a factor `1`. -/
theorem abs_det_fderiv_foldr_comp (l : List (Params M → Params M))
    (hdiff : ∀ f ∈ l, Differentiable ℝ f) (w : Params M) :
    |(fderiv ℝ (l.foldr (· ∘ ·) id) w).det| = foldrCompAbsDet l w := by
  induction l with
  | nil =>
    change |(fderiv ℝ (id : Params M → Params M) w).det| = 1
    rw [fderiv_id]
    rw [show (ContinuousLinearMap.id ℝ (Params M)).det
        = LinearMap.det (ContinuousLinearMap.id ℝ (Params M)).toLinearMap from rfl]
    simp [LinearMap.det_id]
  | cons f fs ih =>
    have hgdiff : Differentiable ℝ (fs.foldr (· ∘ ·) id) :=
      foldr_comp_differentiable fs (fun g hg => hdiff g (List.mem_cons_of_mem f hg))
    have hfdiff : Differentiable ℝ f := hdiff f (List.mem_cons_self)
    have hInner : HasFDerivAt (fs.foldr (· ∘ ·) id)
        (fderiv ℝ (fs.foldr (· ∘ ·) id) w) w := (hgdiff w).hasFDerivAt
    have hOuter : HasFDerivAt f (fderiv ℝ f ((fs.foldr (· ∘ ·) id) w))
        ((fs.foldr (· ∘ ·) id) w) := (hfdiff _).hasFDerivAt
    have hcomp : HasFDerivAt (f ∘ (fs.foldr (· ∘ ·) id))
        ((fderiv ℝ f ((fs.foldr (· ∘ ·) id) w)).comp (fderiv ℝ (fs.foldr (· ∘ ·) id) w)) w :=
      hOuter.comp w hInner
    have hfd : fderiv ℝ ((f :: fs).foldr (· ∘ ·) id) w
        = (fderiv ℝ f ((fs.foldr (· ∘ ·) id) w)).comp (fderiv ℝ (fs.foldr (· ∘ ·) id) w) := by
      rw [List.foldr_cons]; exact hcomp.fderiv
    rw [hfd, clm_det_comp, abs_mul, ih (fun g hg => hdiff g (List.mem_cons_of_mem f hg))]
    rfl

/-- **`geoChartMap` is differentiable everywhere** — on-cone it is the linear-conjugated blow-up
(`conjBlockMap`, differentiable via the q-CLE + `pivotChart`), off-cone it is `id`. So any list of
`geoChartMap`s satisfies the `abs_det_fderiv_foldr_comp` hypothesis; the per-factor dets are then the
banked atoms. -/
theorem geoChartMap_differentiable (g : GeoChart M) :
    Differentiable ℝ (geoChartMap (dCenterOfNode M) (qNodeOf M) g) := by
  by_cases h : dCenterOfNode M g.node ≤ flatDim M ∧ g.pivot < dCenterOfNode M g.node
  · obtain ⟨hd, hp⟩ := h
    have hinj : Function.Injective (cNodeOf M g.node hd) := cNodeOf_injective M g.node hd
    have hfun : geoChartMap (dCenterOfNode M) (qNodeOf M) g
        = conjBlockMap (qOfCenterCLE M (cNodeOf M g.node hd) hinj)
            (pivotChart (⟨g.pivot, hp⟩ : Fin (dCenterOfNode M g.node))) := by
      unfold geoChartMap qNodeOf conjBlockMap
      rw [dif_pos hd, dif_pos hp]
      rfl
    rw [hfun]
    intro x
    exact (conjBlock_hasFDerivAt _ _ _ (pivotChart_hasFDerivAt _) x).differentiableAt
  · have hid : geoChartMap (dCenterOfNode M) (qNodeOf M) g = id := by
      unfold geoChartMap
      split_ifs with hd hp
      · exact absurd ⟨hd, hp⟩ h
      · rfl
      · rfl
    rw [hid]
    exact differentiable_id

end DLNFibre.DLN.RLCT.Engine
