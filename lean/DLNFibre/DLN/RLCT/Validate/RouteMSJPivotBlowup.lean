import DLNFibre.DLN.RLCT.Validate.RouteMSJRadialPolar
import DLNFibre.DLN.RLCT.Validate.RouteMSJCorankStep
import DLNFibre.DLN.RLCT.Foundations.ParamsFlat

set_option linter.style.longLine false

/-!
# `RouteMSJPivotBlowup` — Brick D-A: the P-radial blow-up change-of-variables

**Thread `genm-sj5-domination`, aoyagi-full Stage 2, S1 head-split domination.** The single
from-scratch analytic seam of `RouteMSJDeeperFlagCore.headSplit_domination` (Brick D): the polar
(radial) blow-up of the merged front block `W = (P | B₁₂)` of the freed Schur chart, exposing the
Jacobian monomial `r^{u·M₁−1}` and factoring the degree-2-homogeneous pivot energy `frobSq(W·Q)`.

## Design (locked with the controller, 2026-07-13)
The radial-polar CoV is ALREADY banked (`RouteMSJRadialPolar.lintegral_pi_radial_polar_factor`,
ordinary unit sphere). This module supplies the one genuinely-new measure step — the matrix↔flat
reshape `(Fin p → Fin q → ℝ) ≃ᵐ (Fin (p·q) → ℝ)` transport (pattern:
`ParamsFlat.measurePreserving_paramsEquivFlat`) — and the pivot-energy specialisation.

Locked scope (see `s1-spine-headsplit-cert` §A.2 + `s1-Chle-angular-integrability-cert`):
* **Exponent** — this brick owns the HONEST joint-block Jacobian `r^{u·M₁−1}` (`N = u·M₁`); the
  downstream drop to `minAdm(M')−1` is an on-`[0,1]` power domination the assembly does (in scope
  `hpiv : minAdm(M') ≤ u·ρ`).
* **Ordinary unit sphere** — NO `|det P̂| = 1` de-scaling (the det-1 hypersurface is the refuted red
  herring of `s1-Chle-angular §3`: `σ_max` is unbounded there). The direction `matReshape ω` is the
  raw unit-sphere point.
* **CoV only, exact equality** — NO finiteness claim. `C_hle < ⊤` is a SEPARATE brick (D-B,
  `RouteMSJRankRCodim.lintegral_cube_frobSq_neg_of_finrank_range`, the codim-`u·ρ` argument).

## What lands here
* **`matReshapeEquiv`** — the measure-preserving `(Fin p → Fin q → ℝ) ≃ᵐ (Fin (p·q) → ℝ)`
  (`piCurry.symm` then `arrowCongr'` reindex by `finProdFinEquiv`).
* **`matReshape`** — its inverse composed with `WithLp.ofLp`: a unit-sphere point `ω` read back as a
  `p×q` matrix (the de-scaled direction `P̂`).
* **`lintegral_matrix_radial_polar_factor`** — the matrix-space radial blow-up CoV for any measurable
  degree-2-homogeneous loss `g` (reusable vehicle).
* **`pivotBlock_radial_blowup`** — its specialisation to the pivot energy `g W = frobSq(W·Q)`
  (Brick D-A's interface, consumed by `headSplit_domination`).

Network-free measure theory on the banked polar CoV; S2-FREE; axiom-clean
`[propext, Classical.choice, Quot.sound]`.
-/

namespace DLNFibre.DLN.RLCT

open MeasureTheory Set Metric
open scoped ENNReal

/-! ## The measure-preserving matrix↔flat reshape -/

/-- **The reshape** `(Fin p → Fin q → ℝ) ≃ᵐ (Fin (p·q) → ℝ)`: curry-collapse the two `Fin` levels to
the sigma index `Σ _ : Fin p, Fin q` (`piCurry.symm`), then re-index to `Fin (p·q)` by
`(sigmaEquivProd).trans finProdFinEquiv` (`arrowCongr'`). Mirrors
`ParamsFlat.paramsEquivFlat` (the one-level, non-dependent case). -/
noncomputable def matReshapeEquiv (p q : ℕ) : (Fin p → Fin q → ℝ) ≃ᵐ (Fin (p * q) → ℝ) :=
  (MeasurableEquiv.piCurry (fun (_ : Fin p) (_ : Fin q) => ℝ)).symm.trans
    (MeasurableEquiv.arrowCongr'
      ((Equiv.sigmaEquivProd (Fin p) (Fin q)).trans finProdFinEquiv)
      (MeasurableEquiv.refl ℝ))

/-- The reshape's inverse reads coordinate `(i, j)` off `y` at the flat index `finProdFinEquiv (i, j)`. -/
theorem matReshapeEquiv_symm_apply (p q : ℕ) (y : Fin (p * q) → ℝ) (i : Fin p) (j : Fin q) :
    (matReshapeEquiv p q).symm y i j = y (finProdFinEquiv (i, j)) := rfl

/-- The reshape's inverse is `ℝ`-scalar-homogeneous (a pure coordinate re-index). -/
theorem matReshapeEquiv_symm_smul (p q : ℕ) (r : ℝ) (y : Fin (p * q) → ℝ) :
    (matReshapeEquiv p q).symm (r • y) = r • (matReshapeEquiv p q).symm y := by
  ext i j
  simp only [Pi.smul_apply, matReshapeEquiv_symm_apply]

/-- **The reshape is measure-preserving** for the product Lebesgue measure. Assembled exactly as
`ParamsFlat.measurePreserving_paramsEquivFlat`: `measurePreserving_piCurry` (`.symm`) then
`volume_preserving_arrowCongr'`; the measures join by `rfl` (`Fin p → Fin q → ℝ`'s `volume` is
definitionally the nested `Measure.pi`). -/
theorem measurePreserving_matReshapeEquiv (p q : ℕ) :
    MeasurePreserving (matReshapeEquiv p q)
      (volume : Measure (Fin p → Fin q → ℝ)) (volume : Measure (Fin (p * q) → ℝ)) := by
  unfold matReshapeEquiv
  have h1 := measurePreserving_piCurry (fun (_ : Fin p) (_ : Fin q) => ℝ)
    (fun _ _ => (volume : Measure ℝ))
  have ha := volume_preserving_arrowCongr'
    ((Equiv.sigmaEquivProd (Fin p) (Fin q)).trans finProdFinEquiv)
    (MeasurableEquiv.refl ℝ) (MeasurePreserving.id (volume : Measure ℝ))
  exact (h1.symm _).trans ha

/-- **`matReshape ω`** — the unit-sphere direction `ω : sphere 0 1 ⊆ EuclideanSpace ℝ (Fin (p·q))`
read back as a `p×q` real matrix (`WithLp.ofLp` to plain coordinates, then the inverse reshape). This
is the de-scaled direction `P̂` of the P-radial blow-up (ordinary unit sphere — no det-1). -/
noncomputable def matReshape (p q : ℕ) (ω : sphere (0 : EuclideanSpace ℝ (Fin (p * q))) 1) :
    Fin p → Fin q → ℝ :=
  (matReshapeEquiv p q).symm (WithLp.ofLp (ω : EuclideanSpace ℝ (Fin (p * q))))

/-! ## The matrix-space radial blow-up CoV (generic homogeneous loss) -/

/-- **The matrix-space radial-blow-up CoV.** For a measurable degree-2-homogeneous loss
`g : (Fin p → Fin q → ℝ) → ℝ` (`g (r • W) = r²·g W`) and any measurable `φ : ℝ → ℝ`, the whole
matrix-space lower integral of `ofReal (φ (g W))` polar-blows-up the block (dimension `N = p·q`) to
an angular (ordinary unit sphere) × radial integral with the Jacobian monomial `r^{p·q−1}` exposed
and the loss factored along the radius:

    ∫⁻ W, ofReal (φ (g W))
      = ∫⁻ ω ∂toSphere, ∫⁻ r in Ioi 0, ofReal (r^{p·q−1}) · ofReal (φ (r²·g (matReshape ω))).

The reusable vehicle: transport the matrix integral to `Fin (p·q) → ℝ` (measure-preserving
`matReshapeEquiv`), then apply the banked `lintegral_pi_radial_polar_factor` to `g ∘ reshape⁻¹`
(still homogeneous, `matReshapeEquiv_symm_smul`). -/
theorem lintegral_matrix_radial_polar_factor {p q : ℕ} [NeZero (p * q)]
    (g : (Fin p → Fin q → ℝ) → ℝ) (hg : Measurable g)
    (hom : ∀ (r : ℝ) (W : Fin p → Fin q → ℝ), g (r • W) = r ^ 2 * g W)
    (φ : ℝ → ℝ) (hφ : Measurable φ) :
    ∫⁻ W : Fin p → Fin q → ℝ, ENNReal.ofReal (φ (g W))
      = ∫⁻ ω : sphere (0 : EuclideanSpace ℝ (Fin (p * q))) 1,
          ∫⁻ r in Ioi (0 : ℝ),
            ENNReal.ofReal (r ^ (p * q - 1))
              * ENNReal.ofReal (φ (r ^ 2 * g (matReshape p q ω)))
          ∂(volume : Measure ℝ)
          ∂((volume : Measure (EuclideanSpace ℝ (Fin (p * q)))).toSphere) := by
  -- transport the matrix integral to the flat pi-space `Fin (p·q) → ℝ`
  have hMP : MeasurePreserving (matReshapeEquiv p q).symm
      (volume : Measure (Fin (p * q) → ℝ)) (volume : Measure (Fin p → Fin q → ℝ)) :=
    (measurePreserving_matReshapeEquiv p q).symm _
  have hFmeas : Measurable (fun W : Fin p → Fin q → ℝ => ENNReal.ofReal (φ (g W))) :=
    ENNReal.measurable_ofReal.comp (hφ.comp hg)
  have hstep1 : (∫⁻ W : Fin p → Fin q → ℝ, ENNReal.ofReal (φ (g W)))
      = ∫⁻ x : Fin (p * q) → ℝ, ENNReal.ofReal (φ (g ((matReshapeEquiv p q).symm x))) :=
    (hMP.lintegral_comp hFmeas).symm
  rw [hstep1]
  -- apply the banked pi-space polar factor to `g' = g ∘ reshape⁻¹`
  have hg' : Measurable (fun x : Fin (p * q) → ℝ => g ((matReshapeEquiv p q).symm x)) :=
    hg.comp (matReshapeEquiv p q).symm.measurable
  have hom' : ∀ (r : ℝ) (x : Fin (p * q) → ℝ),
      g ((matReshapeEquiv p q).symm (r • x)) = r ^ 2 * g ((matReshapeEquiv p q).symm x) := by
    intro r x
    rw [matReshapeEquiv_symm_smul, hom]
  exact lintegral_pi_radial_polar_factor
    (fun x => g ((matReshapeEquiv p q).symm x)) hg' hom' φ hφ

/-! ## Brick D-A — the pivot-block radial blow-up CoV -/

/-- **Brick D-A: the pivot-block radial blow-up CoV.** For the merged front block
`W : Fin u → Fin w → ℝ` (`w = u + b = M₁`, the `(P | B₁₂)` columns) and a fixed deep-tail product
`Q : Matrix (Fin w) (Fin n) ℝ`, and any measurable `φ : ℝ → ℝ`, the whole-block lower integral of
`ofReal (φ (frobSq (W·Q)))` polar-blows-up the joint block (dimension `N = u·w = u·M₁`) to an angular
(ordinary unit sphere) × radial integral with the Jacobian monomial `r^{u·w−1}` exposed and the pivot
energy factored `frobSq((r•W)·Q) = r²·frobSq(W·Q)`:

    ∫⁻ W, ofReal (φ (frobSq (W·Q)))
      = ∫⁻ ω ∂toSphere, ∫⁻ r in Ioi 0, ofReal (r^{u·w−1}) · ofReal (φ (r²·frobSq (P̂·Q))),   P̂ = matReshape ω.

`lintegral_matrix_radial_polar_factor` at `g W = frobSq (of W * Q)`, with the pivot energy
degree-2-homogeneous by the banked `frobSq_smul_mul`. This is Aoyagi §5 step (i) as a standalone
measure identity — CoV only; finiteness (`C_hle < ⊤`) is Brick D-B. -/
theorem pivotBlock_radial_blowup {u w n : ℕ} [NeZero (u * w)]
    (Q : Matrix (Fin w) (Fin n) ℝ) (φ : ℝ → ℝ) (hφ : Measurable φ) :
    ∫⁻ W : Fin u → Fin w → ℝ,
        ENNReal.ofReal (φ (frobSq ((Matrix.of W * Q : Matrix (Fin u) (Fin n) ℝ))))
      = ∫⁻ ω : sphere (0 : EuclideanSpace ℝ (Fin (u * w))) 1,
          ∫⁻ r in Ioi (0 : ℝ),
            ENNReal.ofReal (r ^ (u * w - 1))
              * ENNReal.ofReal
                  (φ (r ^ 2 * frobSq ((Matrix.of (matReshape u w ω) * Q : Matrix (Fin u) (Fin n) ℝ))))
          ∂(volume : Measure ℝ)
          ∂((volume : Measure (EuclideanSpace ℝ (Fin (u * w)))).toSphere) := by
  refine lintegral_matrix_radial_polar_factor
    (fun W => frobSq ((Matrix.of W * Q : Matrix (Fin u) (Fin n) ℝ))) ?_ ?_ φ hφ
  · -- measurability of the pivot energy in `W`
    unfold frobSq
    refine Finset.measurable_sum _ (fun i _ => Finset.measurable_sum _ (fun j _ => ?_))
    refine Measurable.pow_const ?_ 2
    have heq : (fun W : Fin u → Fin w → ℝ => (Matrix.of W * Q : Matrix (Fin u) (Fin n) ℝ) i j)
        = (fun W : Fin u → Fin w → ℝ => ∑ k, W i k * Q k j) := by
      funext W; simp only [Matrix.mul_apply, Matrix.of_apply]
    rw [heq]
    refine Finset.measurable_sum _ (fun k _ => ?_)
    have hik : Measurable (fun W : Fin u → Fin w → ℝ => W i k) :=
      (measurable_pi_apply k).comp (measurable_pi_apply i)
    exact hik.mul_const (Q k j)
  · -- degree-2 homogeneity of the pivot energy (banked `frobSq_smul_mul`)
    intro r W
    show frobSq ((Matrix.of (r • W) : Matrix (Fin u) (Fin w) ℝ) * Q)
        = r ^ 2 * frobSq ((Matrix.of W : Matrix (Fin u) (Fin w) ℝ) * Q)
    rw [show (Matrix.of (r • W) : Matrix (Fin u) (Fin w) ℝ) = r • Matrix.of W from rfl,
      frobSq_smul_mul]

end DLNFibre.DLN.RLCT
