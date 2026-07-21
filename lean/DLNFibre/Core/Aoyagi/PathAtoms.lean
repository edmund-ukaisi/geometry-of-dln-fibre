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
theorem jacDet_comp {f g : (Fin D → ℝ) → (Fin D → ℝ)} (u : Fin D → ℝ)
    (hf : DifferentiableAt ℝ f (g u)) (hg : DifferentiableAt ℝ g u) :
    jacDet (f ∘ g) u = jacDet f (g u) * jacDet g u := by
  unfold jacDet
  rw [fderiv_comp u hf hg]
  rw [show ((fderiv ℝ f (g u)).comp (fderiv ℝ g u)).toLinearMap
      = (fderiv ℝ f (g u)).toLinearMap.comp (fderiv ℝ g u).toLinearMap from rfl,
    LinearMap.det_comp]

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
theorem blockShear_zero (φ : (Fin D → ℝ) → (Fin D → ℝ)) (hφ0 : φ 0 = 0) :
    blockShear φ 0 = 0 := by
  simp [blockShear, hφ0]

/-- **The block shear is analytic** when the displacement is (`id + φ`). -/
theorem analyticOnNhd_blockShear (φ : (Fin D → ℝ) → (Fin D → ℝ))
    (hφ : AnalyticOnNhd ℝ φ Set.univ) :
    AnalyticOnNhd ℝ (blockShear φ) Set.univ := by
  have hid : AnalyticOnNhd ℝ (fun u : Fin D → ℝ ↦ u) Set.univ := analyticOnNhd_id
  exact hid.add hφ

/-- **`blockShearInv` is a left inverse of `blockShear`** when `φ` keeps and reads only the kept
coordinates: `blockShearInv φ (blockShear φ u) = u`. -/
theorem blockShearInv_leftInverse (φ : (Fin D → ℝ) → (Fin D → ℝ)) (keep : Fin D → Prop)
    (hkeep : ∀ u i, keep i → φ u i = 0)
    (hread : ∀ u v : Fin D → ℝ, (∀ i, keep i → u i = v i) → φ u = φ v) :
    Function.LeftInverse (blockShearInv φ) (blockShear φ) := by
  intro u
  have h : φ (u + φ u) = φ u :=
    hread (u + φ u) u (fun i hi ↦ by simp [hkeep u i hi])
  show (u + φ u) - φ (u + φ u) = u
  rw [h, add_sub_cancel_right]

/-- **`blockShearInv` is a right inverse of `blockShear`** (same hypotheses) — so `blockShear φ` is
a bijection with polynomial inverse `blockShearInv φ`. -/
theorem blockShearInv_rightInverse (φ : (Fin D → ℝ) → (Fin D → ℝ)) (keep : Fin D → Prop)
    (hkeep : ∀ u i, keep i → φ u i = 0)
    (hread : ∀ u v : Fin D → ℝ, (∀ i, keep i → u i = v i) → φ u = φ v) :
    Function.RightInverse (blockShearInv φ) (blockShear φ) := by
  intro v
  have h : φ (v - φ v) = φ v :=
    hread (v - φ v) v (fun i hi ↦ by simp [hkeep v i hi])
  show (v - φ v) + φ (v - φ v) = v
  rw [h, sub_add_cancel]

/-- **The block shear is injective** (it is a bijection with polynomial inverse). -/
theorem injective_blockShear (φ : (Fin D → ℝ) → (Fin D → ℝ)) (keep : Fin D → Prop)
    (hkeep : ∀ u i, keep i → φ u i = 0)
    (hread : ∀ u v : Fin D → ℝ, (∀ i, keep i → u i = v i) → φ u = φ v) :
    Function.Injective (blockShear φ) :=
  (blockShearInv_leftInverse φ keep hkeep hread).injective

/-- **The block shear's Jacobian determinant is exactly 1** (the shear-pin, thread 33): the fderiv
is block-triangular (`hkeep` kills the kept rows of `Dφ`; `hread` kills the non-kept columns), with
both identity diagonal blocks. -/
theorem jacDet_blockShear (φ : (Fin D → ℝ) → (Fin D → ℝ)) (keep : Fin D → Prop)
    (hφ_diff : Differentiable ℝ φ)
    (hkeep : ∀ u i, keep i → φ u i = 0)
    (hread : ∀ u v : Fin D → ℝ, (∀ i, keep i → u i = v i) → φ u = φ v)
    (u : Fin D → ℝ) :
    jacDet (blockShear φ) u = 1 := by
  classical
  set L : (Fin D → ℝ) →L[ℝ] (Fin D → ℝ) := fderiv ℝ φ u with hL
  have hφ_at : HasFDerivAt φ L u := (hφ_diff u).hasFDerivAt
  -- The Jacobian of `blockShear φ = id + φ` is `id + L`.
  have hfd : fderiv ℝ (blockShear φ) u = ContinuousLinearMap.id ℝ (Fin D → ℝ) + L := by
    rw [hL, show blockShear φ = (id : (Fin D → ℝ) → (Fin D → ℝ)) + φ from rfl,
      fderiv_add differentiableAt_id (hφ_diff u), fderiv_id]
  -- Row vanishing: `keep a ⇒ (L v) a = 0` (`φ · a` is the constant 0).
  have hrow : ∀ (a : Fin D), keep a → ∀ v, (L v) a = 0 := by
    intro a hka v
    have hpa : HasFDerivAt (fun w ↦ φ w a)
        ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin D ↦ ℝ) a).comp L) u :=
      (hasFDerivAt_apply (𝕜 := ℝ) a (φ u)).comp u hφ_at
    have hzero : (fun w ↦ φ w a) = fun _ ↦ (0 : ℝ) := funext fun w ↦ hkeep w a hka
    have hpa0 : HasFDerivAt (fun w : Fin D → ℝ ↦ φ w a) (0 : (Fin D → ℝ) →L[ℝ] ℝ) u := by
      rw [hzero]; exact hasFDerivAt_const (𝕜 := ℝ) (0 : ℝ) u
    have hcomp0 := hpa.unique hpa0
    have hv0 := congrArg (fun T : (Fin D → ℝ) →L[ℝ] ℝ ↦ T v) hcomp0
    simpa using hv0
  -- Column vanishing: `¬keep c ⇒ L (e_c) = 0` (`φ` is constant along the `c`-direction).
  have hcol : ∀ (c : Fin D), ¬ keep c → L (Pi.single c 1 : Fin D → ℝ) = 0 := by
    intro c hc
    set v : Fin D → ℝ := Pi.single c 1 with hv
    have hconst : (fun t : ℝ ↦ φ (u + t • v)) = fun _ ↦ φ u := by
      funext t
      refine hread _ _ (fun i hi ↦ ?_)
      have hic : i ≠ c := by rintro rfl; exact hc hi
      simp [hv, hic]
    have hg : HasDerivAt (fun t : ℝ ↦ u + t • v) v 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add u
    have hφat0 : HasFDerivAt φ L ((fun t : ℝ ↦ u + t • v) 0) := by simpa using hφ_at
    have hd2 : HasDerivAt (fun t : ℝ ↦ φ (u + t • v)) (L v) 0 := hφat0.comp_hasDerivAt 0 hg
    have hd1 : HasDerivAt (fun t : ℝ ↦ φ (u + t • v)) 0 0 := by
      rw [hconst]; exact hasDerivAt_const 0 (φ u)
    exact hd2.unique hd1
  -- Pass to the matrix and split by the `keep` block function (clean rows/cols at `b = 1`).
  unfold jacDet
  rw [hfd,
    ← LinearMap.det_toMatrix' (ContinuousLinearMap.id ℝ (Fin D → ℝ) + L).toLinearMap]
  set M := LinearMap.toMatrix' (ContinuousLinearMap.id ℝ (Fin D → ℝ) + L).toLinearMap with hM
  set b : Fin D → ℕ := fun a ↦ if keep a then 1 else 0 with hb
  have hMentry : ∀ a c, M a c
      = (if a = c then (1 : ℝ) else 0) + (L (Pi.single c 1 : Fin D → ℝ)) a := by
    intro a c
    rw [hM, LinearMap.toMatrix'_apply]
    show ((ContinuousLinearMap.id ℝ (Fin D → ℝ) + L) (Pi.single c 1 : Fin D → ℝ)) a = _
    rw [ContinuousLinearMap.add_apply, Pi.add_apply, ContinuousLinearMap.id_apply]
    simp only [Pi.single_apply]
  -- On any diagonal block the `L`-entry vanishes (row if `keep`, column if not).
  have hNblock : ∀ a c, b a = b c → (L (Pi.single c 1 : Fin D → ℝ)) a = 0 := by
    intro a c hbac
    by_cases hka : keep a
    · exact hrow a hka _
    · have hkc : ¬ keep c := by
        intro h
        have hba : b a = 0 := by simp [hb, hka]
        have hbc : b c = 1 := by simp [hb, h]
        omega
      simp [hcol c hkc]
  have hbt : M.BlockTriangular b := by
    intro a c hlt
    have hka : keep a := by
      by_contra h
      have hba : b a = 0 := by simp [hb, h]
      omega
    have hac : a ≠ c := fun h ↦ by subst h; exact lt_irrefl _ hlt
    rw [hMentry, if_neg hac, zero_add, hrow a hka]
  rw [hbt.det]
  refine Finset.prod_eq_one (fun k _ ↦ ?_)
  have hblk : M.toSquareBlock b k = 1 := by
    ext p q
    rw [Matrix.toSquareBlock_def, Matrix.of_apply, hMentry,
      hNblock ↑p ↑q (by rw [p.2, q.2]), add_zero, Matrix.one_apply]
    simp [Subtype.ext_iff]
  rw [hblk, Matrix.det_one]

/-! ## blow-up convenience atom -/

/-- **`blowupMap p` is differentiable** (a polynomial map; from `analyticOnNhd_blowupMap`). The form
`jacDet_comp` consumes when composing a step's blow-up. -/
theorem differentiable_blowupMap (p : Fin D) : Differentiable ℝ (blowupMap p) :=
  differentiableOn_univ.mp (analyticOnNhd_blowupMap p).differentiableOn

/-! ## pathMap composition atoms -/

/-- **`pathMap` fixes the origin** when every step does. -/
theorem pathMap_zero (l : List ((Fin D → ℝ) → (Fin D → ℝ)))
    (hl : ∀ σ ∈ l, σ 0 = 0) : pathMap l 0 = 0 := by
  induction l with
  | nil => rfl
  | cons σ rest ih =>
    have hrest : pathMap rest 0 = 0 := ih (fun τ hτ ↦ hl τ (List.mem_cons.mpr (Or.inr hτ)))
    show σ (pathMap rest 0) = 0
    rw [hrest]; exact hl σ (List.mem_cons.mpr (Or.inl rfl))

/-- **`pathMap` of a list of analytic maps is analytic.** -/
theorem analyticOnNhd_pathMap (l : List ((Fin D → ℝ) → (Fin D → ℝ)))
    (hl : ∀ σ ∈ l, AnalyticOnNhd ℝ σ Set.univ) :
    AnalyticOnNhd ℝ (pathMap l) Set.univ := by
  induction l with
  | nil => exact analyticOnNhd_id
  | cons σ rest ih =>
    have hrest := ih (fun τ hτ ↦ hl τ (List.mem_cons.mpr (Or.inr hτ)))
    have hσ := hl σ (List.mem_cons.mpr (Or.inl rfl))
    exact hσ.comp hrest (Set.mapsTo_univ _ _)

/-- **`pathMap` of a list of differentiable maps is differentiable** (to feed the chain rule). -/
theorem differentiable_pathMap (l : List ((Fin D → ℝ) → (Fin D → ℝ)))
    (hl : ∀ σ ∈ l, Differentiable ℝ σ) : Differentiable ℝ (pathMap l) := by
  induction l with
  | nil => exact differentiable_id
  | cons σ rest ih =>
    have hrest := ih (fun τ hτ ↦ hl τ (List.mem_cons.mpr (Or.inr hτ)))
    have hσ := hl σ (List.mem_cons.mpr (Or.inl rfl))
    exact hσ.comp hrest

/-- **The `pathMap` Jacobian chain-rule step.** `jacDet (pathMap (σ :: rest)) u =
jacDet σ (pathMap rest u) · jacDet (pathMap rest) u`. Iterating this is the "`jacDet (pathMap l) =
∏ per-step jacDets along the orbit`" product (each factor evaluated at the partial composition). -/
theorem jacDet_pathMap_cons (σ : (Fin D → ℝ) → (Fin D → ℝ))
    (rest : List ((Fin D → ℝ) → (Fin D → ℝ))) (u : Fin D → ℝ)
    (hσ : DifferentiableAt ℝ σ (pathMap rest u))
    (hrest : DifferentiableAt ℝ (pathMap rest) u) :
    jacDet (pathMap (σ :: rest)) u
      = jacDet σ (pathMap rest u) * jacDet (pathMap rest) u := by
  rw [pathMap_cons]
  exact jacDet_comp u hσ hrest

/-- **The absolute-value `pathMap` Jacobian chain-rule step** — the form the monomial fold consumes
(`|det D(pathMap)|` is the product of the per-step `|det|`s, each a pure blow-up monomial). -/
theorem abs_jacDet_pathMap_cons (σ : (Fin D → ℝ) → (Fin D → ℝ))
    (rest : List ((Fin D → ℝ) → (Fin D → ℝ))) (u : Fin D → ℝ)
    (hσ : DifferentiableAt ℝ σ (pathMap rest u))
    (hrest : DifferentiableAt ℝ (pathMap rest) u) :
    |jacDet (pathMap (σ :: rest)) u|
      = |jacDet σ (pathMap rest u)| * |jacDet (pathMap rest) u| := by
  rw [jacDet_pathMap_cons σ rest u hσ hrest, abs_mul]

/-! ## a.e.-injective composition + `CenterCoordAligned` -/

/-- **The a.e.-injective composition bookkeeping (measure-free).** If `f` is injective off `Ef` and
`g` is injective off `Eg`, then `f ∘ g` is injective off `Eg ∪ g⁻¹' Ef`. Combined with the nullity
of the two pieces (`volume Eg = 0`, `volume (g⁻¹' Ef) = 0` — supplied by the caller from the
concrete polynomial structure, `measure_union_null`), this gives a.e.-injectivity of a branch. -/
theorem injOn_comp_diff {f g : (Fin D → ℝ) → (Fin D → ℝ)} {Ef Eg : Set (Fin D → ℝ)}
    (hf : Set.InjOn f (Set.univ \ Ef)) (hg : Set.InjOn g (Set.univ \ Eg)) :
    Set.InjOn (f ∘ g) (Set.univ \ (Eg ∪ g ⁻¹' Ef)) := by
  intro x hx y hy hxy
  have hxg : g x ∈ Set.univ \ Ef :=
    ⟨Set.mem_univ _, fun h ↦ hx.2 (Or.inr h)⟩
  have hyg : g y ∈ Set.univ \ Ef :=
    ⟨Set.mem_univ _, fun h ↦ hy.2 (Or.inr h)⟩
  have hgxy : g x = g y := hf hxg hyg hxy
  exact hg ⟨Set.mem_univ _, fun h ↦ hx.2 (Or.inl h)⟩
    ⟨Set.mem_univ _, fun h ↦ hy.2 (Or.inl h)⟩ hgxy

/-- **The `CenterCoordAligned` constructor.** For a GLOBALLY injective shear `sh` (e.g. any
`blockShear`), `sh ∘ blowupMap p` is injective off `{u_p = 0}` — the pnp-cover coherence field of a
`StepInvChild`. (Injectivity of `sh` composed with `injOn_blowupMap p`.) -/
theorem centerCoordAligned_of_injective (sh : (Fin D → ℝ) → (Fin D → ℝ)) (p : Fin D)
    (hsh : Function.Injective sh) : CenterCoordAligned sh p := by
  show Set.InjOn (fun u ↦ sh (blowupMap p u)) (Set.univ \ {w : Fin D → ℝ | w p = 0})
  exact hsh.injOn.comp (injOn_blowupMap p) (Set.mapsTo_univ _ _)

/-! ## the shear ∘ blow-up step: `|det|` is the pure blow-up monomial (unit ≡ 1) -/

/-- **A shear ∘ blow-up step has `|det D|` = the pure blow-up monomial** (`unit ≡ 1`, the
shear-pin): `|jacDet (fun u ↦ sh (blowupMap p u)) u| = |u p| ^ (D-1)`, given the shear's
`jacDet sh = 1`. This is the per-step `GeoStep.hσ_jac` content; the total-branch monomial is the
`pathMap` product of these (`abs_jacDet_pathMap_cons`) — assembled downstream (L6). -/
theorem abs_jacDet_shear_comp_blowup (hD : 2 ≤ D) (sh : (Fin D → ℝ) → (Fin D → ℝ)) (p : Fin D)
    (hsh_diff : Differentiable ℝ sh) (hsh_jac : ∀ w, jacDet sh w = 1) (u : Fin D → ℝ) :
    |jacDet (fun u ↦ sh (blowupMap p u)) u| = |u p| ^ (D - 1) := by
  have hcomp : jacDet (sh ∘ blowupMap p) u
      = jacDet sh (blowupMap p u) * jacDet (blowupMap p) u :=
    jacDet_comp u (hsh_diff (blowupMap p u)) (differentiable_blowupMap p u)
  show |jacDet (sh ∘ blowupMap p) u| = |u p| ^ (D - 1)
  rw [hcomp, hsh_jac, one_mul, jacDet_blowupMap hD, abs_pow]

end DLNFibre.Core.Aoyagi
