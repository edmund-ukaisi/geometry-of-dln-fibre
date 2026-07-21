import DLNFibre.Core.Aoyagi.PrincipalInv
import Meta.Cordon

/-!
# `Core.Aoyagi.PathAtoms` — W0: the build-once substrate atoms for the path/shear/blow-up fold

**BLUEPRINT (aoyagi-engine monument wave, W0 seat).** The network-free, reusable atoms the coupled
product-ideal resolution monument (charter §1.B) folds along a root→leaf branch: the Jacobian chain
rule for `pathMap`, the analyticity/origin-fixing of a composed branch, the a.e.-injective
composition bookkeeping, the `CenterCoordAligned` constructor, and the concrete unipotent **shear**
(`blockShear`) whose Jacobian is exactly `1` (shear-pin certificate, thread 33). These are the
signatures the L4 (coupled preservation) and L5/L6 (fold / chart geometry) seats build against.

## What is already landed upstream (do NOT re-prove)

`OriginBlowup.lean` provides the blow-up atoms over general `Fin D`: `jacDet_blowupMap`
(`= (w p)^(D-1)`), `injOn_blowupMap` (off `{w_p = 0}`), `analyticOnNhd_blowupMap`,
`volume_blowup_excep`, `ball_subset_iUnion_blowup_image`, `jacWeight_blowup_jac`. The atoms here sit
ON those; they add the COMPOSITION layer (chain rule / analyticity / injectivity of `pathMap`) and
the shear.

## The shear (shear-pin, thread 33): `blockShear`

Per the shear-pin certificate, each per-step coordinate change `= (unipotent shears) ∘ (monomial
blow-ups)`, and the shears are Jacobian-EXACTLY-1 (block-triangular, identity diagonal). The
canonical such shear here is `blockShear φ u = u + φ u`, where the displacement `φ` **keeps** a set
of coordinates fixed (`hkeep`) and **reads only** those kept coordinates (`hread`): its Jacobian is
then block-triangular with two identity diagonal blocks (`det = 1`), and it is a polynomial
automorphism with inverse `v ↦ v - φ v`. The Schur reduction
`(C₁₂, C₂₁, C₂₂) ↦ (C₁₂, C₂₁, C₂₂ − C₂₁·C₁₂)` is the motivating instance (kept = `{C₁₂, C₂₁}`, `φ`
places `−C₂₁·C₁₂` in the `C₂₂` slots).
-/

open MeasureTheory Set Filter Topology RLCT
open Meta.Cordon

namespace DLNFibre.Core.Aoyagi

variable {D : ℕ}

/-! ## jacDet composition atoms (the chain rule)

`jacDet_id` (`jacDet id u = 1`, the `pathMap [] = id` base case) is landed upstream in
`ResolutionInhabited.lean`; reused here, not re-declared. -/

/-- **jacDet is multiplicative under composition (the chain rule).** `jacDet (f ∘ g) u =
jacDet f (g u) · jacDet g u`, given differentiability at the relevant points. The single step of the
`pathMap` Jacobian product. -/
@[blueprint]
theorem jacDet_comp {f g : (Fin D → ℝ) → (Fin D → ℝ)} (u : Fin D → ℝ)
    (hf : DifferentiableAt ℝ f (g u)) (hg : DifferentiableAt ℝ g u) :
    jacDet (f ∘ g) u = jacDet f (g u) * jacDet g u := by
  -- map: W0-jacDet-comp (fderiv_comp + LinearMap.det_comp)
  sorry

/-! ## The unipotent block shear (`blockShear`) — shear-pin, thread 33 -/

/-- **The block shear** `u ↦ u + φ u`: a unipotent coordinate change (shear-pin certificate). When
`φ` keeps a coordinate set fixed and reads only those coordinates (`hkeep`/`hread` below), its
Jacobian is block-triangular with identity diagonal blocks. -/
def blockShear (φ : (Fin D → ℝ) → (Fin D → ℝ)) : (Fin D → ℝ) → (Fin D → ℝ) :=
  fun u ↦ u + φ u

/-- **The inverse block shear** `v ↦ v - φ v` — the polynomial inverse of `blockShear φ`. -/
def blockShearInv (φ : (Fin D → ℝ) → (Fin D → ℝ)) : (Fin D → ℝ) → (Fin D → ℝ) :=
  fun v ↦ v - φ v

/-- **The block shear fixes the origin** when the displacement does. -/
@[blueprint]
theorem blockShear_zero (φ : (Fin D → ℝ) → (Fin D → ℝ)) (hφ0 : φ 0 = 0) :
    blockShear φ 0 = 0 := by
  -- map: W0-blockShear-zero
  sorry

/-- **The block shear is analytic** when the displacement is (`id + φ`). -/
@[blueprint]
theorem analyticOnNhd_blockShear (φ : (Fin D → ℝ) → (Fin D → ℝ))
    (hφ : AnalyticOnNhd ℝ φ Set.univ) :
    AnalyticOnNhd ℝ (blockShear φ) Set.univ := by
  -- map: W0-analyticOnNhd-blockShear
  sorry

/-- **`blockShearInv` is a left inverse of `blockShear`** when `φ` keeps and reads only the kept
coordinates: `blockShearInv φ (blockShear φ u) = u`. -/
@[blueprint]
theorem blockShearInv_leftInverse (φ : (Fin D → ℝ) → (Fin D → ℝ)) (keep : Fin D → Prop)
    (hkeep : ∀ u i, keep i → φ u i = 0)
    (hread : ∀ u v : Fin D → ℝ, (∀ i, keep i → u i = v i) → φ u = φ v) :
    Function.LeftInverse (blockShearInv φ) (blockShear φ) := by
  -- map: W0-blockShearInv-leftInverse
  sorry

/-- **`blockShearInv` is a right inverse of `blockShear`** (same hypotheses) — so `blockShear φ` is
a bijection with polynomial inverse `blockShearInv φ`. -/
@[blueprint]
theorem blockShearInv_rightInverse (φ : (Fin D → ℝ) → (Fin D → ℝ)) (keep : Fin D → Prop)
    (hkeep : ∀ u i, keep i → φ u i = 0)
    (hread : ∀ u v : Fin D → ℝ, (∀ i, keep i → u i = v i) → φ u = φ v) :
    Function.RightInverse (blockShearInv φ) (blockShear φ) := by
  -- map: W0-blockShearInv-rightInverse
  sorry

/-- **The block shear is injective** (it is a bijection with polynomial inverse). -/
@[blueprint]
theorem injective_blockShear (φ : (Fin D → ℝ) → (Fin D → ℝ)) (keep : Fin D → Prop)
    (hkeep : ∀ u i, keep i → φ u i = 0)
    (hread : ∀ u v : Fin D → ℝ, (∀ i, keep i → u i = v i) → φ u = φ v) :
    Function.Injective (blockShear φ) := by
  -- map: W0-injective-blockShear
  sorry

/-- **The block shear's Jacobian determinant is exactly 1** (the shear-pin, thread 33): the fderiv
is block-triangular (`hkeep` kills the kept rows of `Dφ`; `hread` kills the non-kept columns), with
both identity diagonal blocks. -/
@[blueprint]
theorem jacDet_blockShear (φ : (Fin D → ℝ) → (Fin D → ℝ)) (keep : Fin D → Prop)
    (hφ_diff : Differentiable ℝ φ)
    (hkeep : ∀ u i, keep i → φ u i = 0)
    (hread : ∀ u v : Fin D → ℝ, (∀ i, keep i → u i = v i) → φ u = φ v)
    (u : Fin D → ℝ) :
    jacDet (blockShear φ) u = 1 := by
  -- map: W0-jacDet-blockShear (block-triangular, identity diagonal blocks; shear-pin unit ≡ 1)
  sorry

/-! ## blow-up convenience atom -/

/-- **`blowupMap p` is differentiable** (a polynomial map; from `analyticOnNhd_blowupMap`). The form
`jacDet_comp` consumes when composing a step's blow-up. -/
@[blueprint]
theorem differentiable_blowupMap (p : Fin D) : Differentiable ℝ (blowupMap p) := by
  -- map: W0-differentiable-blowupMap
  sorry

/-! ## pathMap composition atoms -/

/-- **`pathMap` fixes the origin** when every step does. -/
@[blueprint]
theorem pathMap_zero (l : List ((Fin D → ℝ) → (Fin D → ℝ)))
    (hl : ∀ σ ∈ l, σ 0 = 0) : pathMap l 0 = 0 := by
  -- map: W0-pathMap-zero
  sorry

/-- **`pathMap` of a list of analytic maps is analytic.** -/
@[blueprint]
theorem analyticOnNhd_pathMap (l : List ((Fin D → ℝ) → (Fin D → ℝ)))
    (hl : ∀ σ ∈ l, AnalyticOnNhd ℝ σ Set.univ) :
    AnalyticOnNhd ℝ (pathMap l) Set.univ := by
  -- map: W0-analyticOnNhd-pathMap
  sorry

/-- **`pathMap` of a list of differentiable maps is differentiable** (to feed the chain rule). -/
@[blueprint]
theorem differentiable_pathMap (l : List ((Fin D → ℝ) → (Fin D → ℝ)))
    (hl : ∀ σ ∈ l, Differentiable ℝ σ) : Differentiable ℝ (pathMap l) := by
  -- map: W0-differentiable-pathMap
  sorry

/-- **The `pathMap` Jacobian chain-rule step.** `jacDet (pathMap (σ :: rest)) u =
jacDet σ (pathMap rest u) · jacDet (pathMap rest) u`. Iterating this is the "`jacDet (pathMap l) =
∏ per-step jacDets along the orbit`" product (each factor evaluated at the partial composition). -/
@[blueprint]
theorem jacDet_pathMap_cons (σ : (Fin D → ℝ) → (Fin D → ℝ))
    (rest : List ((Fin D → ℝ) → (Fin D → ℝ))) (u : Fin D → ℝ)
    (hσ : DifferentiableAt ℝ σ (pathMap rest u))
    (hrest : DifferentiableAt ℝ (pathMap rest) u) :
    jacDet (pathMap (σ :: rest)) u
      = jacDet σ (pathMap rest u) * jacDet (pathMap rest) u := by
  -- map: W0-jacDet-pathMap-cons (chain rule along the list)
  sorry

/-- **The absolute-value `pathMap` Jacobian chain-rule step** — the form the monomial fold consumes
(`|det D(pathMap)|` is the product of the per-step `|det|`s, each a pure blow-up monomial). -/
@[blueprint]
theorem abs_jacDet_pathMap_cons (σ : (Fin D → ℝ) → (Fin D → ℝ))
    (rest : List ((Fin D → ℝ) → (Fin D → ℝ))) (u : Fin D → ℝ)
    (hσ : DifferentiableAt ℝ σ (pathMap rest u))
    (hrest : DifferentiableAt ℝ (pathMap rest) u) :
    |jacDet (pathMap (σ :: rest)) u|
      = |jacDet σ (pathMap rest u)| * |jacDet (pathMap rest) u| := by
  -- map: W0-abs-jacDet-pathMap-cons
  sorry

/-! ## a.e.-injective composition + `CenterCoordAligned` -/

/-- **The a.e.-injective composition bookkeeping (measure-free).** If `f` is injective off `Ef` and
`g` is injective off `Eg`, then `f ∘ g` is injective off `Eg ∪ g⁻¹' Ef`. Combined with the nullity
of the two pieces (`volume Eg = 0`, `volume (g⁻¹' Ef) = 0` — supplied by the caller from the
concrete polynomial structure, `measure_union_null`), this gives a.e.-injectivity of a branch. -/
@[blueprint]
theorem injOn_comp_diff {f g : (Fin D → ℝ) → (Fin D → ℝ)} {Ef Eg : Set (Fin D → ℝ)}
    (hf : Set.InjOn f (Set.univ \ Ef)) (hg : Set.InjOn g (Set.univ \ Eg)) :
    Set.InjOn (f ∘ g) (Set.univ \ (Eg ∪ g ⁻¹' Ef)) := by
  -- map: W0-injOn-comp-diff
  sorry

/-- **The `CenterCoordAligned` constructor.** For a GLOBALLY injective shear `sh` (e.g. any
`blockShear`), `sh ∘ blowupMap p` is injective off `{u_p = 0}` — the pnp-cover coherence field of a
`StepInvChild`. (Injectivity of `sh` composed with `injOn_blowupMap p`.) -/
@[blueprint]
theorem centerCoordAligned_of_injective (sh : (Fin D → ℝ) → (Fin D → ℝ)) (p : Fin D)
    (hsh : Function.Injective sh) : CenterCoordAligned sh p := by
  -- map: W0-centerCoordAligned-of-injective
  sorry

/-! ## the shear ∘ blow-up step: `|det|` is the pure blow-up monomial (unit ≡ 1) -/

/-- **A shear ∘ blow-up step has `|det D|` = the pure blow-up monomial** (`unit ≡ 1`, the
shear-pin): `|jacDet (fun u ↦ sh (blowupMap p u)) u| = |u p| ^ (D-1)`, given the shear's
`jacDet sh = 1`. This is the per-step `GeoStep.hσ_jac` content; the total-branch monomial is the
`pathMap` product of these (`abs_jacDet_pathMap_cons`) — assembled downstream (L6). -/
@[blueprint]
theorem abs_jacDet_shear_comp_blowup (hD : 2 ≤ D) (sh : (Fin D → ℝ) → (Fin D → ℝ)) (p : Fin D)
    (hsh_diff : Differentiable ℝ sh) (hsh_jac : ∀ w, jacDet sh w = 1) (u : Fin D → ℝ) :
    |jacDet (fun u ↦ sh (blowupMap p u)) u| = |u p| ^ (D - 1) := by
  -- map: W0-abs-jacDet-shear-comp-blowup (chain rule; shear det 1; jacDet_blowupMap)
  sorry

end DLNFibre.Core.Aoyagi
