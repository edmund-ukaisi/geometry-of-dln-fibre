/-
Copyright (c) 2026. Released under Apache 2.0; see LICENSE.
-/
import DLNFibre.Core.ChartLocalizedAlgEquiv
import DLNFibre.Core.DeterminantalBasePresentation
import DLNFibre.Core.FibreNormalForm
import DLNFibre.Core.ChartEvalRealize
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.TensorProduct.MvPolynomial

/-!
# `DLNFibre.Core.FibreBundleReduced` — the per-chart product trivialization (Tier-R, B1–B4)

The **reduced fibre variety** decomposes, on the BUILT pivot chart, as a product over the rank-`r`
matrix stratum. The chart `AlgEquiv` `e_β = chartLocalizedAlgEquiv`
(`Away chartDsig ≃ₐ[k] Away chartGfib`) lives on the **reduced** variety: `chartGfib` localizes the
polynomial ring over `sweepFibreRing = k[Rep]/vanishingIdeal(F)`, NOT the scheme cut `FibreAlg =
k[Rep]/fibreGenIdeal` (which needs the months-scale reducedness wall — out of scope here).

**Scope of the bundle claim.** Only the single top-left pivot chart `e_β` is built; this module
proves (B1–B2) that chart is a product `SchurLoc ⊗_k sweepFibreRing`, and (B4) that the rank-`r`
target stratum is a single `GL × GL` base-change orbit, so every fibre is — after a base change —
the one product-trivialized model chart. This is **base-change homogeneity + single-chart
triviality**, NOT a full bundle local-triviality over a per-minor-position open cover of `Mat^{=r}`
(that chart family is not built here).

This module lands **rung B1** (thread 10 Part 2): the **tensor-package** identifying the schur-side
chart coordinate ring as a product

> `Away chartGfib ≃ₐ[k] SchurLoc ⊗_k sweepFibreRing`

(`SchurLoc = Localization.Away detSchurS` the free Schur localization; `sweepFibreRing = O(F)` the
reduced fibre coordinate ring). The general lemma `mvPolynomialAwayMapTensorAlgEquiv` is reusable:
for **any** `k`-algebra `F` and any `f : MvPolynomial ι k`,

> `Away (map (algebraMap k F) f) ≃ₐ[k] (Away f) ⊗_k F`.

The mechanism is the polynomial base-change `MvPolynomial ι F ≃ₐ[k] (MvPolynomial ι k) ⊗_k F`
(`algebraTensorAlgEquiv` then `Algebra.TensorProduct.comm`, carrying `map (algebraMap k F) f ↦
algebraMap _ _ f`), followed by the localization base-change
`IsLocalization.tensorProduct_tensorProduct` (`(Away f) ⊗_k F` is the localization of
`(MvPolynomial ι k) ⊗_k F` at `powers f ⊆ MvPolynomial ι k`), glued by
`IsLocalization.algEquivOfAlgEquiv`.

**Dependency rule:** `Core` only — never import `DLNFibre.DLN`.
-/

namespace DLNFibre.Core

open MvPolynomial Matrix
open scoped TensorProduct

universe u v

variable {k : Type u} [Field k]

attribute [local instance] Algebra.TensorProduct.rightAlgebra

section TensorBaseChange

variable {F : Type v} [CommRing F] [Algebra k F] {ι : Type*} (f : MvPolynomial ι k)

/-- The `A ⊗_k F`-algebra structure on `B ⊗_k F` induced by the base ring hom `A → B`
(`A = MvPolynomial ι k`, `B = Localization.Away f`), via `Algebra.TensorProduct.map (A → B) (id F)`.
Used only locally to feed `IsLocalization.tensorProduct_tensorProduct`. -/
noncomputable local instance tensorAlgebra :
    Algebra (MvPolynomial ι k ⊗[k] F) (Localization.Away f ⊗[k] F) :=
  (Algebra.TensorProduct.map
    (IsScalarTower.toAlgHom k (MvPolynomial ι k) (Localization.Away f))
    (AlgHom.id k F)).toRingHom.toAlgebra

/-- The local `tensorAlgebra` structure forms a scalar tower with the base `MvPolynomial ι k`. -/
local instance tensorIsScalarTower :
    IsScalarTower (MvPolynomial ι k) (MvPolynomial ι k ⊗[k] F) (Localization.Away f ⊗[k] F) := by
  refine IsScalarTower.of_algebraMap_eq (fun x ↦ ?_)
  -- both sides send `x` to `(algebraMap A B x) ⊗ₜ 1` via `includeLeft`.
  show algebraMap (MvPolynomial ι k) (Localization.Away f ⊗[k] F) x
      = (Algebra.TensorProduct.map
          (IsScalarTower.toAlgHom k (MvPolynomial ι k) (Localization.Away f)) (AlgHom.id k F))
        (algebraMap (MvPolynomial ι k) (MvPolynomial ι k ⊗[k] F) x)
  rw [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.algebraMap_apply,
    Algebra.algebraMap_self_apply, Algebra.TensorProduct.map_tmul, map_one,
    IsScalarTower.coe_toAlgHom']

/-- **The away-localization base-change `AlgEquiv` (the reusable keystone, B1).** For any
commutative `k`-algebra `F` and any `f : MvPolynomial ι k`, inverting the `F`-coefficient image
`map (algebraMap k F) f` of `f` in `MvPolynomial ι F` is the base change of the away-localization
`Away f` by `F`:

> `Localization.Away (map (algebraMap k F) f) ≃ₐ[k] (Localization.Away f) ⊗_k F`.

Built from the polynomial base-change `MvPolynomial ι F ≃ₐ[k] (MvPolynomial ι k) ⊗_k F`
(`algebraTensorAlgEquiv`, sending `map (algebraMap k F) f ↦ algebraMap _ _ f`) and the localization
base-change `IsLocalization.tensorProduct_tensorProduct`, glued by `algEquivOfAlgEquiv`. -/
noncomputable def mvPolynomialAwayMapTensorAlgEquiv :
    Localization.Away (MvPolynomial.map (algebraMap k F) f)
      ≃ₐ[k] Localization.Away f ⊗[k] F := by
  -- `e : MvPolynomial ι F ≃ₐ[k] (MvPolynomial ι k) ⊗_k F`, carrying `g ↦ algebraMap _ _ f`.
  let e : MvPolynomial ι F ≃ₐ[k] MvPolynomial ι k ⊗[k] F :=
    ((MvPolynomial.algebraTensorAlgEquiv k F).symm.restrictScalars k).trans
      (Algebra.TensorProduct.comm k F (MvPolynomial ι k))
  have heg : e (MvPolynomial.map (algebraMap k F) f)
      = algebraMap (MvPolynomial ι k) (MvPolynomial ι k ⊗[k] F) f := by
    show (Algebra.TensorProduct.comm k F (MvPolynomial ι k))
        ((MvPolynomial.algebraTensorAlgEquiv k F).symm
          (MvPolynomial.map (algebraMap k F) f))
      = algebraMap (MvPolynomial ι k) (MvPolynomial ι k ⊗[k] F) f
    rw [MvPolynomial.algebraTensorAlgEquiv_symm_map, Algebra.TensorProduct.comm_tmul,
      Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self_apply]
  -- the compatibility hypothesis for `tensorProduct_tensorProduct`.
  have H : (algebraMap (MvPolynomial ι k ⊗[k] F) (Localization.Away f ⊗[k] F)).comp
        Algebra.TensorProduct.includeRight.toRingHom
      = Algebra.TensorProduct.includeRight.toRingHom := by
    have hmap : ((Algebra.TensorProduct.map
          (IsScalarTower.toAlgHom k (MvPolynomial ι k) (Localization.Away f))
          (AlgHom.id k F)).comp Algebra.TensorProduct.includeRight)
        = (Algebra.TensorProduct.includeRight.comp (AlgHom.id k F)) :=
      Algebra.TensorProduct.map_comp_includeRight _ _
    rw [AlgHom.comp_id] at hmap
    -- transport the AlgHom equation down to ring homs (`algebraMap = map.toRingHom`)
    show ((Algebra.TensorProduct.map
        (IsScalarTower.toAlgHom k (MvPolynomial ι k) (Localization.Away f))
        (AlgHom.id k F)).toRingHom).comp Algebra.TensorProduct.includeRight.toRingHom
      = Algebra.TensorProduct.includeRight.toRingHom
    exact congrArg AlgHom.toRingHom hmap
  -- the target is the localization of `(MvPolynomial ι k) ⊗_k F` at `powers (algebraMap _ _ f)`.
  haveI hlocTarget : IsLocalization
      (Submonoid.powers (algebraMap (MvPolynomial ι k) (MvPolynomial ι k ⊗[k] F) f))
      (Localization.Away f ⊗[k] F) := by
    have := IsLocalization.tensorProduct_tensorProduct (R := k) (S := F)
      (A := MvPolynomial ι k) (M := Submonoid.powers f) (B := Localization.Away f) H
    simpa only [Algebra.algebraMapSubmonoid, Submonoid.map_powers] using this
  -- glue the two localizations along `e`.
  have Hpow : Submonoid.map (e : MvPolynomial ι F →+* MvPolynomial ι k ⊗[k] F)
        (Submonoid.powers (MvPolynomial.map (algebraMap k F) f))
      = Submonoid.powers (algebraMap (MvPolynomial ι k) (MvPolynomial ι k ⊗[k] F) f) := by
    rw [Submonoid.map_powers]; exact congrArg Submonoid.powers heg
  exact IsLocalization.algEquivOfAlgEquiv
    (Localization.Away (MvPolynomial.map (algebraMap k F) f))
    (Localization.Away f ⊗[k] F) e Hpow

/-- **The base-change keystone on a generator.** `mvPolynomialAwayMapTensorAlgEquiv f` sends the
structure-map image of a single variable `X v` (coefficient-extended to `MvPolynomial ι F`) to the
left tensor factor `(algebraMap _ (Away f) (X v)) ⊗ₜ 1`. This is the computational handle on the
opaque `mvPolynomialAwayMapTensorAlgEquiv` (built as `IsLocalization.algEquivOfAlgEquiv … e Hpow`),
established here — in the section that owns the local `tensorAlgebra` instance — via
`IsLocalization.algEquivOfAlgEquiv_eq` and the base-change `algebraTensorAlgEquiv_symm_map`.
The downstream `SchurLoc`-linearity of the chart trivialization reduces to exactly this. -/
theorem mvPolynomialAwayMapTensorAlgEquiv_algebraMap_X (v : ι) :
    mvPolynomialAwayMapTensorAlgEquiv (k := k) (F := F) (ι := ι) f
        (algebraMap (MvPolynomial ι F) (Localization.Away (MvPolynomial.map (algebraMap k F) f))
          (MvPolynomial.map (algebraMap k F) (X v)))
      = (algebraMap (MvPolynomial ι k) (Localization.Away f) (X v)) ⊗ₜ[k] (1 : F) := by
  -- re-derive the `e`, `Hpow` of the def (defeq, since the local instances are this section's).
  let e : MvPolynomial ι F ≃ₐ[k] MvPolynomial ι k ⊗[k] F :=
    ((MvPolynomial.algebraTensorAlgEquiv k F).symm.restrictScalars k).trans
      (Algebra.TensorProduct.comm k F (MvPolynomial ι k))
  have heg : e (MvPolynomial.map (algebraMap k F) f)
      = algebraMap (MvPolynomial ι k) (MvPolynomial ι k ⊗[k] F) f := by
    show (Algebra.TensorProduct.comm k F (MvPolynomial ι k))
        ((MvPolynomial.algebraTensorAlgEquiv k F).symm
          (MvPolynomial.map (algebraMap k F) f))
      = algebraMap (MvPolynomial ι k) (MvPolynomial ι k ⊗[k] F) f
    rw [MvPolynomial.algebraTensorAlgEquiv_symm_map, Algebra.TensorProduct.comm_tmul,
      Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self_apply]
  have Hpow : Submonoid.map (e : MvPolynomial ι F →+* MvPolynomial ι k ⊗[k] F)
        (Submonoid.powers (MvPolynomial.map (algebraMap k F) f))
      = Submonoid.powers (algebraMap (MvPolynomial ι k) (MvPolynomial ι k ⊗[k] F) f) := by
    rw [Submonoid.map_powers]; exact congrArg Submonoid.powers heg
  -- re-derive the `IsLocalization` instance on the target (the def's `hlocTarget`).
  have H : (algebraMap (MvPolynomial ι k ⊗[k] F) (Localization.Away f ⊗[k] F)).comp
        Algebra.TensorProduct.includeRight.toRingHom
      = Algebra.TensorProduct.includeRight.toRingHom := by
    have hmap : ((Algebra.TensorProduct.map
          (IsScalarTower.toAlgHom k (MvPolynomial ι k) (Localization.Away f))
          (AlgHom.id k F)).comp Algebra.TensorProduct.includeRight)
        = (Algebra.TensorProduct.includeRight.comp (AlgHom.id k F)) :=
      Algebra.TensorProduct.map_comp_includeRight _ _
    rw [AlgHom.comp_id] at hmap
    show ((Algebra.TensorProduct.map
        (IsScalarTower.toAlgHom k (MvPolynomial ι k) (Localization.Away f))
        (AlgHom.id k F)).toRingHom).comp Algebra.TensorProduct.includeRight.toRingHom
      = Algebra.TensorProduct.includeRight.toRingHom
    exact congrArg AlgHom.toRingHom hmap
  haveI hlocTarget : IsLocalization
      (Submonoid.powers (algebraMap (MvPolynomial ι k) (MvPolynomial ι k ⊗[k] F) f))
      (Localization.Away f ⊗[k] F) := by
    have := IsLocalization.tensorProduct_tensorProduct (R := k) (S := F)
      (A := MvPolynomial ι k) (M := Submonoid.powers f) (B := Localization.Away f) H
    simpa only [Algebra.algebraMapSubmonoid, Submonoid.map_powers] using this
  -- `mvPolynomialAwayMapTensorAlgEquiv f = algEquivOfAlgEquiv … e Hpow`, then the `_eq` lemma.
  show IsLocalization.algEquivOfAlgEquiv
      (Localization.Away (MvPolynomial.map (algebraMap k F) f))
      (Localization.Away f ⊗[k] F) e Hpow
      (algebraMap (MvPolynomial ι F) (Localization.Away (MvPolynomial.map (algebraMap k F) f))
        (MvPolynomial.map (algebraMap k F) (X v)))
    = (algebraMap (MvPolynomial ι k) (Localization.Away f) (X v)) ⊗ₜ[k] (1 : F)
  rw [IsLocalization.algEquivOfAlgEquiv_eq]
  -- `e (map (algebraMap k F) (X v)) = X v ⊗ₜ 1`; then `algebraMap (local) (X v ⊗ₜ 1)`.
  have he : e (MvPolynomial.map (algebraMap k F) (X v))
      = (X v : MvPolynomial ι k) ⊗ₜ[k] (1 : F) := by
    show (Algebra.TensorProduct.comm k F (MvPolynomial ι k))
        ((MvPolynomial.algebraTensorAlgEquiv k F).symm (MvPolynomial.map (algebraMap k F) (X v)))
      = (X v : MvPolynomial ι k) ⊗ₜ[k] (1 : F)
    rw [MvPolynomial.algebraTensorAlgEquiv_symm_map, Algebra.TensorProduct.comm_tmul]
  rw [he]
  -- the local `algebraMap` is `Algebra.TensorProduct.map (toAlgHom …) (id F)`, sending `X v ⊗ₜ 1`.
  show (Algebra.TensorProduct.map
      (IsScalarTower.toAlgHom k (MvPolynomial ι k) (Localization.Away f)) (AlgHom.id k F))
      ((X v : MvPolynomial ι k) ⊗ₜ[k] (1 : F))
    = (algebraMap (MvPolynomial ι k) (Localization.Away f) (X v)) ⊗ₜ[k] (1 : F)
  rw [Algebra.TensorProduct.map_tmul, map_one, IsScalarTower.coe_toAlgHom']

end TensorBaseChange

section ChartGfib

variable {N : ℕ}

/-- **B1 — the per-chart schur-side product trivialization of the REDUCED fibre variety.** The
schur-side localized chart coordinate ring `Away chartGfib` is, over the field `k`, the product of
the free Schur localization `SchurLoc` with the **reduced** fibre coordinate ring
`sweepFibreRing = k[Rep]/vanishingIdeal(F)`:

> `Away (chartGfib d r) ≃ₐ[k] SchurLoc (d 0) (d (last (N+1))) r ⊗_k sweepFibreRing d r`.

This is the reduced variety (`sweepFibreRing`), NOT the scheme cut `FibreAlg`. `chartGfib =
map (algebraMap k (sweepFibreRing)) detSchurS`, so this is `mvPolynomialAwayMapTensorAlgEquiv` at
`f = detSchurS`, `F = sweepFibreRing`, `ι = SchurVar`. The `SchurLoc` factor is the local (matrix)
fibre direction; the `sweepFibreRing` factor is the reduced fibre. -/
noncomputable def reducedFibre_chartGfib_tensorEquiv_reducedVariety (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0) :
    Localization.Away (chartGfib k d r hp hq)
      ≃ₐ[k] SchurLoc (k := k) (d 0) (d (Fin.last (N + 1))) r ⊗[k] sweepFibreRing k d r hp hq :=
  mvPolynomialAwayMapTensorAlgEquiv (F := sweepFibreRing k d r hp hq)
    (ι := SchurVar (d 0) (d (Fin.last (N + 1))) r) (detSchurS (d 0) (d (Fin.last (N + 1))) r)

end ChartGfib

section ChartDsig

variable {N : ℕ}

/-- **B2 — the per-chart product trivialization at the source `{detΔ ≠ 0}` chart.** Composing the
BUILT localized chart `AlgEquiv` `e_β = chartLocalizedAlgEquiv`
(`Away chartDsig ≃ₐ[k] Away chartGfib`) with the schur-side product trivialization B1 gives the
**per-chart product trivialization** of the reduced fibre variety:

> `Away (chartDsig d r) ≃ₐ[k] SchurLoc (d 0) (d (last (N+1))) r ⊗_k sweepFibreRing d r`.

`Away chartDsig` is the coordinate ring of the source pivot chart `{detΔ ≠ 0}` of the rank-`r`
product locus `Σ^r`; this exhibits it (over `k`) as the product of the local matrix direction
`SchurLoc` with the **reduced** fibre coordinate ring `sweepFibreRing`. This is the honest
local-triviality statement on the reduced variety — NOT the scheme cut `FibreAlg`. Needs
`[Infinite k]` (the chart `e_β` does). -/
noncomputable def reducedFibre_chartDsig_tensorEquiv_reducedVariety [Infinite k]
    (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0) :
    Localization.Away (chartDsig k d r hp hq)
      ≃ₐ[k] SchurLoc (k := k) (d 0) (d (Fin.last (N + 1))) r ⊗[k] sweepFibreRing k d r hp hq :=
  (chartLocalizedAlgEquiv k d r hp hq).trans
    (reducedFibre_chartGfib_tensorEquiv_reducedVariety d r hp hq)

end ChartDsig

section BaseHomogeneity

variable {N : ℕ}

/-- **B4 — the bundle-base homogeneity: every rank-`r` fibre is a base-change image of the model
fibre.** For `N ≥ 1` (`hN`, the two end vertices distinct), every target matrix `B` of rank `r` lies
in the single `GL(d_{last}) × GL(d_0)` orbit of the rank-`r` normal form `E_r`, and the fibre
`mult⁻¹(B)` is the image of the **model fibre** `mult⁻¹(E_r)` under the linear automorphism
`A ↦ P • A`:

> `∃ P, fibre d B = (P • ·) '' fibre d (normalForm …)`.

This is the bundle-base homogeneity (`exists_baseChange_of_rank_eq` = `GL × GL`-transitivity on
rank-`r` matrices) wired to the fibre transport `image_smul_fibre`. Together with the model chart's
product trivialization (B2, `reducedFibre_chartDsig_tensorEquiv_reducedVariety`), it identifies
every rank-`r` fibre — after a base change — with the single product-trivialized model
`SchurLoc ⊗_k sweepFibreRing`. (This is single-chart triviality + rank-orbit homogeneity, not a full
bundle local-triviality over a per-minor-position open cover.) -/
theorem reducedFibre_baseChangeHomogeneous (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0)
    (B : Matrix (Fin (d (Fin.last (N + 1)))) (Fin (d 0)) k) (hB : B.rank = r) :
    ∃ P : BaseChangeGroup (k := k) d,
      fibre d B
        = (fun A ↦ P • A) ''
            fibre d (normalForm (d (Fin.last (N + 1))) (d 0) r hp hq) := by
  -- `0 ≠ Fin.last (N + 1)` since `N + 1 ≥ 1`.
  have hN : (0 : Fin (N + 2)) ≠ Fin.last (N + 1) := by
    simp [Fin.ext_iff, Fin.last]
  -- `E_r` and `B` have equal rank `r`, so a base change carries `E_r` to `B`.
  have hrank : (normalForm (k := k) (d (Fin.last (N + 1))) (d 0) r hp hq).rank = B.rank := by
    rw [rank_normalForm, hB]
  obtain ⟨P, hP⟩ := exists_baseChange_of_rank_eq d hN
    (normalForm (d (Fin.last (N + 1))) (d 0) r hp hq) B hrank
  -- the fibre transport: `fibre d (P_N · E_r · P_0⁻¹) = (P • ·) '' fibre d E_r`.
  refine ⟨P, ?_⟩
  rw [hP, image_smul_fibre]

/-- **The reduced fibre variety: single-chart triviality + rank-orbit homogeneity (Tier-R
headline).** Combining the base homogeneity (B4) with the per-chart product trivialization (B2): for
every rank-`r` `B`, there is a base change `P` carrying the model fibre `mult⁻¹(E_r)` onto
`mult⁻¹(B)`, and the model fibre's reduced coordinate chart `Away (chartDsig d r)` is the product
`SchurLoc ⊗_k sweepFibreRing` of the local matrix direction with the **reduced** fibre coordinate
ring. So every fibre of the reduced variety over the rank-`r` stratum is, after a base change, the
single product-trivialized model chart. Needs `[Infinite k]` (the chart `e_β`). This is the reduced
variety (`sweepFibreRing`), NOT the scheme cut `FibreAlg`; and it is single-chart triviality, NOT
full bundle local-triviality over a per-minor-position open cover (that chart family is unbuilt). -/
theorem reducedFibre_singleChartTrivial_reducedVariety [Infinite k]
    (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0)
    (B : Matrix (Fin (d (Fin.last (N + 1)))) (Fin (d 0)) k) (hB : B.rank = r) :
    (∃ P : BaseChangeGroup (k := k) d,
      fibre d B = (fun A ↦ P • A) ''
        fibre d (normalForm (d (Fin.last (N + 1))) (d 0) r hp hq))
    ∧ Nonempty (Localization.Away (chartDsig k d r hp hq)
        ≃ₐ[k] SchurLoc (k := k) (d 0) (d (Fin.last (N + 1))) r ⊗[k] sweepFibreRing k d r hp hq) :=
  ⟨reducedFibre_baseChangeHomogeneous d r hp hq B hB,
    ⟨reducedFibre_chartDsig_tensorEquiv_reducedVariety d r hp hq⟩⟩

end BaseHomogeneity

end DLNFibre.Core
