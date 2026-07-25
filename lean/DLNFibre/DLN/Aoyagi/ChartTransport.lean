import DLNFibre.Core.Aoyagi.ProductResolution
import DLNFibre.DLN.Aoyagi.Corank2ChartJac
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Dynamics.Ergodic.MeasurePreserving

/-!
# `DLN.Aoyagi.ChartTransport` — RUNG 5d crux (B): the generic `transportChart`

The **reusable core** of crux (B): transport a certified `Chart F x₀` across a coordinate
permutation `σ : Equiv.Perm (Fin D)`, given that the generator family `F` is **equivariant
up-to-index-perm** under `σ` (`∀ i, F i ∘ permOf σ = F (τ i)` for an index permutation
`τ : Equiv.Perm (Fin M)` — the load-bearing hypothesis, crux (B)'s analogue of crux (A)).

The transported chart resolves the SAME family `F` at the conjugated deepest point
`permOf σ.symm x₀`, with map `g' = permOf σ.symm ∘ g ∘ permOf σ`. All five certificate
groups transport:

* **geometry** (`hg0`/`hg_cont`/`hg_analytic`) — `permOf` is a linear homeo, fixing `0`;
* **Jacobian** (`hjac`) — `|jacDet permOf| = 1` (banked `abs_jacDet_permCoord`) absorbs the
  conjugating perms, so `|jacDet g'| = |jacDet g ∘ permOf σ|`; the exponent vector is
  `jac ∘ σ.symm` (values PRESERVED, axes permuted — the fan-invariance);
* **injectivity** (`hg_inj`/`hexcep`) — `permOf` is a measure-preserving bijection, so
  `excep' = (permOf σ)⁻¹' excep` is null + measurable and `InjOn` transports;
* **ideal** (`hideal_fwd`/`hideal_bwd`) — the cofactors conjugate along `σ`, consuming the
  `F`-equivariance; `bexp' = bexp ∘ σ.symm`;
* **binding** (`hchain`/`hbind`/`hunit_mult`) — the binding axes map by `σ`, VALUES preserved.

This core is **route-agnostic**: it produces a valid `Chart` for any `σ` under which `F` is
equivariant (e.g. any element of the `S₄×S₃×S₃` coreGen-symmetry group for the DLN application).
-/

open MeasureTheory Set
open DLNFibre.Core.Aoyagi
open DLNFibre.DLN.Aoyagi.Corank2ChartJac

namespace DLNFibre.DLN.Aoyagi

variable {D M : ℕ}

/-! ## §0 — the coordinate-permutation map `permOf` and its basic calculus -/

/-- The **coordinate-permutation map** `permOf σ w = w ∘ σ` (`= fun i ↦ w (σ i)`) — exactly the
form `abs_jacDet_permCoord` consumes. -/
def permOf (σ : Equiv.Perm (Fin D)) : (Fin D → ℝ) → (Fin D → ℝ) := fun w i ↦ w (σ i)

@[simp] theorem permOf_apply (σ : Equiv.Perm (Fin D)) (w : Fin D → ℝ) (i : Fin D) :
    permOf σ w i = w (σ i) := rfl

@[simp] theorem permOf_zero (σ : Equiv.Perm (Fin D)) : permOf σ (0 : Fin D → ℝ) = 0 := by
  funext i; simp [permOf]

/-- `permOf σ.symm` undoes `permOf σ`. -/
theorem permOf_symm_permOf (σ : Equiv.Perm (Fin D)) (w : Fin D → ℝ) :
    permOf σ.symm (permOf σ w) = w := by funext i; simp [permOf]

/-- `permOf σ` undoes `permOf σ.symm`. -/
theorem permOf_permOf_symm (σ : Equiv.Perm (Fin D)) (w : Fin D → ℝ) :
    permOf σ (permOf σ.symm w) = w := by funext i; simp [permOf]

/-- `permOf` as a continuous linear map (a coordinate reindex of the `pi` projections). -/
def permOfCLM (σ : Equiv.Perm (Fin D)) : (Fin D → ℝ) →L[ℝ] (Fin D → ℝ) :=
  ContinuousLinearMap.pi (fun i ↦ ContinuousLinearMap.proj (σ i))

theorem permOf_eq_permOfCLM (σ : Equiv.Perm (Fin D)) : permOf σ = permOfCLM σ := by
  funext w i; simp [permOf, permOfCLM]

theorem continuous_permOf (σ : Equiv.Perm (Fin D)) : Continuous (permOf σ) := by
  rw [permOf_eq_permOfCLM]; exact (permOfCLM σ).continuous

theorem measurable_permOf (σ : Equiv.Perm (Fin D)) : Measurable (permOf σ) :=
  (continuous_permOf σ).measurable

theorem differentiable_permOf (σ : Equiv.Perm (Fin D)) : Differentiable ℝ (permOf σ) := by
  rw [permOf_eq_permOfCLM]; exact (permOfCLM σ).differentiable

theorem analyticOnNhd_permOf (σ : Equiv.Perm (Fin D)) :
    AnalyticOnNhd ℝ (permOf σ) Set.univ := by
  rw [permOf_eq_permOfCLM]; exact (permOfCLM σ).analyticOnNhd _

theorem injective_permOf (σ : Equiv.Perm (Fin D)) : Function.Injective (permOf σ) := by
  intro x y h
  have := congrArg (permOf σ.symm) h
  rwa [permOf_symm_permOf, permOf_symm_permOf] at this

/-- **The Jacobian of `permOf` is `±1`** (banked `abs_jacDet_permCoord`, reused). -/
theorem abs_jacDet_permOf (σ : Equiv.Perm (Fin D)) (u : Fin D → ℝ) :
    |jacDet (permOf σ) u| = 1 := abs_jacDet_permCoord σ u

/-- **`permOf` is measure-preserving** (a coordinate reindex is a `piCongrLeft` measurable equiv). -/
theorem measurePreserving_permOf (σ : Equiv.Perm (Fin D)) :
    MeasurePreserving (permOf σ) (volume : Measure (Fin D → ℝ)) volume := by
  have h := volume_measurePreserving_piCongrLeft (fun _ : Fin D ↦ ℝ) σ.symm
  have he : permOf σ = ⇑(MeasurableEquiv.piCongrLeft (fun _ : Fin D ↦ ℝ) σ.symm) := by
    funext w i
    rw [MeasurableEquiv.coe_piCongrLeft]
    have hpc := Equiv.piCongrLeft_apply_apply (fun _ : Fin D ↦ ℝ) σ.symm w (σ i)
    simp only [Equiv.symm_apply_apply] at hpc
    exact hpc.symm
  rw [he]; exact h

/-- `(permOf σ)⁻¹' S = permOf σ.symm '' S` (preimage under a bijection is the inverse image). -/
theorem permOf_preimage_eq_image (σ : Equiv.Perm (Fin D)) (S : Set (Fin D → ℝ)) :
    (permOf σ)⁻¹' S = permOf σ.symm '' S := by
  ext y
  constructor
  · intro hy; exact ⟨permOf σ y, hy, permOf_symm_permOf σ y⟩
  · rintro ⟨x, hx, rfl⟩
    show permOf σ (permOf σ.symm x) ∈ S
    rw [permOf_permOf_symm]; exact hx

/-! ## §1 — transport of the monomial calculus (`jacWeight`, `monomialFam`, `bindingAxes`) -/

/-- `jacWeight h (permOf σ u) = jacWeight (h ∘ σ.symm) u` — the weight's exponents reindex by `σ.symm`
(values preserved, axes permuted). -/
theorem jacWeight_permOf (h : Fin D → ℕ) (σ : Equiv.Perm (Fin D)) (u : Fin D → ℝ) :
    jacWeight h (permOf σ u) = jacWeight (fun d ↦ h (σ.symm d)) u := by
  simp only [jacWeight, permOf]
  conv_rhs => rw [← Equiv.prod_comp σ (fun e ↦ |u e| ^ (h (σ.symm e)))]
  refine Finset.prod_congr rfl (fun d _ ↦ ?_)
  rw [σ.symm_apply_apply]

/-- `monomialFam e k (permOf σ u) = monomialFam (e ∘ σ.symm) k u` — same reindex, for the monomials. -/
theorem monomialFam_permOf (e : Fin M → Fin D → ℕ) (σ : Equiv.Perm (Fin D)) (k : Fin M)
    (u : Fin D → ℝ) :
    monomialFam e k (permOf σ u) = monomialFam (fun k d ↦ e k (σ.symm d)) k u := by
  simp only [monomialFam, permOf]
  conv_rhs => rw [← Equiv.prod_comp σ (fun d ↦ (u d) ^ (e k (σ.symm d)))]
  refine Finset.prod_congr rfl (fun d _ ↦ ?_)
  rw [σ.symm_apply_apply]

/-- `bindingAxes (kexp ∘ σ.symm) = (bindingAxes kexp).map σ` — the binding axes map by `σ`. -/
theorem bindingAxes_comp_symm (kexp : Fin D → ℕ) (σ : Equiv.Perm (Fin D)) :
    bindingAxes (fun d ↦ kexp (σ.symm d)) = (bindingAxes kexp).map σ.toEmbedding := by
  ext d
  simp only [bindingAxes, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
    Equiv.coe_toEmbedding]
  constructor
  · intro h; exact ⟨σ.symm d, h, σ.apply_symm_apply d⟩
  · rintro ⟨a, ha, rfl⟩; rwa [σ.symm_apply_apply]

/-! ## §2 — the generic `transportChart` -/

/-- **`transportChart σ τ hequiv chart` — the generic (B) core.** Transport a certified
`Chart F x₀` across the coordinate permutation `σ`, under the equivariance
`∀ i, F i ∘ permOf σ = F (τ i)`. Produces a certified `Chart F (permOf σ.symm x₀)` for the
conjugated map `g' = permOf σ.symm ∘ g ∘ permOf σ`, resolving the SAME family `F`. -/
noncomputable def transportChart {F : Fin M → (Fin D → ℝ) → ℝ} {x₀ : Fin D → ℝ}
    (σ : Equiv.Perm (Fin D)) (τ : Equiv.Perm (Fin M))
    (hequiv : ∀ i, F i ∘ permOf σ = F (τ i)) (chart : Chart F x₀) :
    Chart F (permOf σ.symm x₀) where
  g := permOf σ.symm ∘ chart.g ∘ permOf σ
  hg0 := by simp only [Function.comp_apply, permOf_zero, chart.hg0]
  hg_cont := (continuous_permOf _).comp (chart.hg_cont.comp (continuous_permOf _))
  hg_analytic :=
    (analyticOnNhd_permOf _).comp
      (chart.hg_analytic.comp (analyticOnNhd_permOf _) (Set.mapsTo_univ _ _))
      (Set.mapsTo_univ _ _)
  hFmeas := chart.hFmeas
  dom := (permOf σ)⁻¹' chart.dom
  hdom_compact := by
    rw [permOf_preimage_eq_image]; exact chart.hdom_compact.image (continuous_permOf _)
  hdom_zero := by simp only [Set.mem_preimage, permOf_zero]; exact chart.hdom_zero
  nbhd := (permOf σ)⁻¹' chart.nbhd
  hnbhd_open := chart.hnbhd_open.preimage (continuous_permOf _)
  hdom_sub := Set.preimage_mono chart.hdom_sub
  excep := (permOf σ)⁻¹' chart.excep
  hexcep_meas := chart.hexcep_meas.preimage (measurable_permOf _)
  hexcep_null :=
    ((measurePreserving_permOf σ).measure_preimage
      chart.hexcep_meas.nullMeasurableSet).trans chart.hexcep_null
  hg_inj := by
    intro x hx y hy hxy
    have hxmem : permOf σ x ∈ chart.nbhd \ chart.excep := ⟨hx.1, hx.2⟩
    have hymem : permOf σ y ∈ chart.nbhd \ chart.excep := ⟨hy.1, hy.2⟩
    have h1 : chart.g (permOf σ x) = chart.g (permOf σ y) := by
      have := congrArg (permOf σ) hxy
      simpa only [Function.comp_apply, permOf_permOf_symm] using this
    have h2 : permOf σ x = permOf σ y := chart.hg_inj hxmem hymem h1
    exact injective_permOf σ h2
  M' := chart.M'
  bexp := fun k d ↦ chart.bexp k (σ.symm d)
  k₀ := chart.k₀
  hchain := fun k d ↦ chart.hchain k (σ.symm d)
  hbind := by
    rw [bindingAxes_comp_symm]; exact chart.hbind.map
  hunit_mult := by
    intro d hd
    rw [bindingAxes_comp_symm] at hd
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hd
    simp only [Equiv.coe_toEmbedding, σ.symm_apply_apply]
    exact chart.hunit_mult a ha
  jac := fun d ↦ chart.jac (σ.symm d)
  unit := fun u ↦ chart.unit (permOf σ u)
  hunit_cont :=
    chart.hunit_cont.comp (continuous_permOf σ).continuousOn (Set.mapsTo_preimage _ _)
  hunit_ne := fun u hu ↦ chart.hunit_ne (permOf σ u) hu
  hjac := by
    intro u hu
    have hw : permOf σ u ∈ chart.nbhd := hu
    have hgd : Differentiable ℝ chart.g :=
      differentiableOn_univ.mp chart.hg_analytic.differentiableOn
    have hpσ : Differentiable ℝ (permOf σ) := differentiable_permOf σ
    have hpσs : Differentiable ℝ (permOf σ.symm) := differentiable_permOf σ.symm
    have key : |jacDet (permOf σ.symm ∘ chart.g ∘ permOf σ) u|
        = |jacDet chart.g (permOf σ u)| := by
      rw [jacDet_comp u hpσs.differentiableAt (hgd.comp hpσ).differentiableAt,
        jacDet_comp u hgd.differentiableAt hpσ.differentiableAt, abs_mul, abs_mul,
        abs_jacDet_permOf, abs_jacDet_permOf, mul_one, one_mul]
    change |jacDet (permOf σ.symm ∘ chart.g ∘ permOf σ) u|
      = jacWeight (fun d ↦ chart.jac (σ.symm d)) u * |chart.unit (permOf σ u)|
    rw [key, chart.hjac (permOf σ u) hw, jacWeight_permOf]
  hideal_fwd := by
    have hequiv_symm : ∀ i, F i ∘ permOf σ.symm = F (τ.symm i) := by
      intro i
      have h := hequiv (τ.symm i)
      rw [τ.apply_symm_apply] at h
      funext w
      have hc := congrFun h (permOf σ.symm w)
      simp only [Function.comp_apply, permOf_permOf_symm] at hc
      simp only [Function.comp_apply]
      exact hc.symm
    obtain ⟨a, hac, hae⟩ := chart.hideal_fwd
    refine ⟨fun i j u ↦ a (τ.symm i) j (permOf σ u), ?_, ?_⟩
    · intro i j
      exact (hac (τ.symm i) j).comp (continuous_permOf σ).continuousOn (Set.mapsTo_preimage _ _)
    · intro u hu i
      have hw : permOf σ u ∈ chart.nbhd := hu
      have hae' := hae (permOf σ u) hw (τ.symm i)
      simp only [Function.comp_apply] at hae'
      have hlhs : (F i ∘ (permOf σ.symm ∘ chart.g ∘ permOf σ)) u
          = F (τ.symm i) (chart.g (permOf σ u)) := by
        simp only [Function.comp_apply]
        rw [show F i (permOf σ.symm (chart.g (permOf σ u)))
              = (F i ∘ permOf σ.symm) (chart.g (permOf σ u)) from rfl, hequiv_symm i]
      change (F i ∘ (permOf σ.symm ∘ chart.g ∘ permOf σ)) u
        = ∑ j, a (τ.symm i) j (permOf σ u)
            * monomialFam (fun k d ↦ chart.bexp k (σ.symm d)) j u
      rw [hlhs, hae']
      refine Finset.sum_congr rfl (fun j _ ↦ ?_)
      rw [monomialFam_permOf]
  hideal_bwd := by
    have hequiv_symm : ∀ i, F i ∘ permOf σ.symm = F (τ.symm i) := by
      intro i
      have h := hequiv (τ.symm i)
      rw [τ.apply_symm_apply] at h
      funext w
      have hc := congrFun h (permOf σ.symm w)
      simp only [Function.comp_apply, permOf_permOf_symm] at hc
      simp only [Function.comp_apply]
      exact hc.symm
    obtain ⟨b, hbc, hbe⟩ := chart.hideal_bwd
    refine ⟨fun k i u ↦ b k (τ.symm i) (permOf σ u), ?_, ?_⟩
    · intro k i
      exact (hbc k (τ.symm i)).comp (continuous_permOf σ).continuousOn (Set.mapsTo_preimage _ _)
    · intro u hu k
      have hw : permOf σ u ∈ chart.nbhd := hu
      change monomialFam (fun k d ↦ chart.bexp k (σ.symm d)) k u
        = ∑ i, b k (τ.symm i) (permOf σ u) * (F i ∘ (permOf σ.symm ∘ chart.g ∘ permOf σ)) u
      rw [show monomialFam (fun k d ↦ chart.bexp k (σ.symm d)) k u
            = monomialFam chart.bexp k (permOf σ u) from (monomialFam_permOf chart.bexp σ k u).symm,
        hbe (permOf σ u) hw k]
      conv_rhs => rw [← Equiv.sum_comp τ (fun i ↦
        b k (τ.symm i) (permOf σ u) * (F i ∘ (permOf σ.symm ∘ chart.g ∘ permOf σ)) u)]
      refine Finset.sum_congr rfl (fun i _ ↦ ?_)
      rw [τ.symm_apply_apply]
      congr 1
      change (F i ∘ chart.g) (permOf σ u)
        = (F (τ i) ∘ (permOf σ.symm ∘ chart.g ∘ permOf σ)) u
      have hti : F (τ i) ∘ permOf σ.symm = F i := by
        have := hequiv_symm (τ i); rwa [τ.symm_apply_apply] at this
      simp only [Function.comp_apply]
      rw [show F (τ i) (permOf σ.symm (chart.g (permOf σ u)))
            = (F (τ i) ∘ permOf σ.symm) (chart.g (permOf σ u)) from rfl, hti]

end DLNFibre.DLN.Aoyagi
