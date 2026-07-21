import DLNFibre.Core.Aoyagi.ProductResolution

/-!
# `Core.Aoyagi.ConjResolution` — conjugation transport of a `Chart` / `Resolution`

**CORE-LIFT (aoyagi-engine rung C).** The conjugation transport of a certified resolution across a
continuous-linear-equiv coordinate change `Φ` plus a generator re-index `ρ`. Lifted from rung (B)'s
`DLN.Aoyagi.GeometricAtlasD12` (where it was "Core-native in spirit"): it references only the Core
`Chart` / `Resolution` records, `jacDet`, and Mathlib linear-algebra / Haar-measure API — nothing
network-specific — so it belongs in the network-free engine, where the coupled monument reuses it.

If `res : Resolution G 0` and `F i = G (ρ i) ∘ Φ`, then
`conjResolution res Φ ρ F hF : Resolution F 0`. Each chart map becomes `Φ.symm ∘ g_c` (so
`F i ∘ g'_c = G (ρ i) ∘ g_c`); the exponent data `bexp / k₀ / jac` is UNCHANGED, and the Jacobian
picks up the constant factor `det Φ.symm`, absorbed into the chart `unit` (nonvanishing, since
`Φ.symm` is invertible).
-/

open MeasureTheory Set Filter Topology RLCT

namespace DLNFibre.Core.Aoyagi

/-- The Jacobian determinant of `Φ.symm ∘ g` scales by the constant `det Φ.symm`. -/
theorem jacDet_conj_eq {D : ℕ} (Φ : (Fin D → ℝ) ≃L[ℝ] (Fin D → ℝ))
    (g : (Fin D → ℝ) → (Fin D → ℝ)) (u : Fin D → ℝ) (hg : DifferentiableAt ℝ g u) :
    jacDet (fun w ↦ Φ.symm (g w)) u
      = LinearMap.det ((Φ.symm : (Fin D → ℝ) →L[ℝ] (Fin D → ℝ)).toLinearMap) * jacDet g u := by
  have hgf : HasFDerivAt g (fderiv ℝ g u) u := hg.hasFDerivAt
  have hcomp : HasFDerivAt (fun w ↦ Φ.symm (g w))
      ((Φ.symm : (Fin D → ℝ) →L[ℝ] (Fin D → ℝ)).comp (fderiv ℝ g u)) u :=
    Φ.symm.hasFDerivAt.comp u hgf
  unfold jacDet
  rw [hcomp.fderiv]
  exact LinearMap.det_comp _ _

/-- `det Φ.symm ≠ 0` (the underlying linear map of the equiv `Φ.symm` is a unit). -/
theorem det_symm_ne_zero {D : ℕ} (Φ : (Fin D → ℝ) ≃L[ℝ] (Fin D → ℝ)) :
    LinearMap.det ((Φ.symm : (Fin D → ℝ) →L[ℝ] (Fin D → ℝ)).toLinearMap) ≠ 0 := by
  have h1 : LinearMap.det ((Φ.symm : (Fin D → ℝ) →L[ℝ] (Fin D → ℝ)).toLinearMap) *
      LinearMap.det ((Φ : (Fin D → ℝ) →L[ℝ] (Fin D → ℝ)).toLinearMap) = 1 := by
    rw [← LinearMap.det_comp]
    have : ((Φ.symm : (Fin D → ℝ) →L[ℝ] (Fin D → ℝ)).toLinearMap).comp
        ((Φ : (Fin D → ℝ) →L[ℝ] (Fin D → ℝ)).toLinearMap) = LinearMap.id := by
      ext x
      simp
    rw [this, LinearMap.det_id]
  intro h0
  rw [h0, zero_mul] at h1
  exact one_ne_zero h1.symm

/-- **Chart conjugation.** Transport a chart of `G` at `0` across a CLE `Φ` + reindex `ρ` to a chart
of `F` at `0`, where `F i = G (ρ i) ∘ Φ`. Chart map `g'_c := Φ.symm ∘ g_c`; exponents unchanged. -/
noncomputable def conjChart {D M₁ M₂ : ℕ} {G : Fin M₁ → (Fin D → ℝ) → ℝ}
    (Φ : (Fin D → ℝ) ≃L[ℝ] (Fin D → ℝ))
    (ρ : Fin M₂ ≃ Fin M₁) (F : Fin M₂ → (Fin D → ℝ) → ℝ)
    (hF : ∀ i, F i = fun u ↦ G (ρ i) (Φ u))
    (c : Chart G (0 : Fin D → ℝ)) : Chart F (0 : Fin D → ℝ) where
  g := fun w ↦ Φ.symm (c.g w)
  hg0 := by rw [c.hg0]; exact map_zero _
  hg_cont := Φ.symm.continuous.comp c.hg_cont
  hg_analytic := (Φ.symm : (Fin D → ℝ) →L[ℝ] (Fin D → ℝ)).comp_analyticOnNhd c.hg_analytic
  hFmeas := fun i ↦ by rw [hF i]; exact (c.hFmeas (ρ i)).comp Φ.continuous.measurable
  dom := c.dom
  hdom_compact := c.hdom_compact
  hdom_zero := c.hdom_zero
  nbhd := c.nbhd
  hnbhd_open := c.hnbhd_open
  hdom_sub := c.hdom_sub
  excep := c.excep
  hexcep_meas := c.hexcep_meas
  hexcep_null := c.hexcep_null
  hg_inj := Φ.symm.injective.comp_injOn c.hg_inj
  M' := c.M'
  bexp := c.bexp
  k₀ := c.k₀
  hchain := c.hchain
  hbind := c.hbind
  hunit_mult := c.hunit_mult
  jac := c.jac
  unit := fun u ↦ LinearMap.det ((Φ.symm : (Fin D → ℝ) →L[ℝ] (Fin D → ℝ)).toLinearMap) * c.unit u
  hunit_cont := continuousOn_const.mul c.hunit_cont
  hunit_ne := fun u hu ↦ mul_ne_zero (det_symm_ne_zero Φ) (c.hunit_ne u hu)
  hjac := by
    intro u hu
    rw [jacDet_conj_eq Φ c.g u ((c.hg_analytic u (Set.mem_univ u)).differentiableAt),
      abs_mul, abs_mul, c.hjac u hu]
    ring
  hideal_fwd := by
    obtain ⟨a, ha_cont, ha_rep⟩ := c.hideal_fwd
    refine ⟨fun i j ↦ a (ρ i) j, fun i j ↦ ha_cont (ρ i) j, ?_⟩
    intro u hu i
    have hFg : (F i ∘ fun w ↦ Φ.symm (c.g w)) u = (fun k ↦ G k ∘ c.g) (ρ i) u := by
      simp only [Function.comp_apply, hF i]
      rw [Φ.apply_symm_apply]
    simp only [hFg]
    exact ha_rep u hu (ρ i)
  hideal_bwd := by
    obtain ⟨b, hb_cont, hb_rep⟩ := c.hideal_bwd
    refine ⟨fun j i ↦ b j (ρ i), fun j i ↦ hb_cont j (ρ i), ?_⟩
    intro u hu j
    have hFg : ∀ i, (F i ∘ fun w ↦ Φ.symm (c.g w)) u = (G (ρ i) ∘ c.g) u := by
      intro i
      simp only [Function.comp_apply, hF i]
      rw [Φ.apply_symm_apply]
    rw [hb_rep u hu j, ← Equiv.sum_comp ρ (fun k ↦ b j k u * (fun i ↦ G i ∘ c.g) k u)]
    refine Finset.sum_congr rfl (fun i _ ↦ ?_)
    simp only [hFg i]

/-- **Resolution conjugation.** Transport `Resolution G 0` across a CLE `Φ` + reindex `ρ` to
`Resolution F 0` for `F i = G (ρ i) ∘ Φ`. -/
noncomputable def conjResolution {D M₁ M₂ : ℕ} {G : Fin M₁ → (Fin D → ℝ) → ℝ}
    (res : Resolution G (0 : Fin D → ℝ))
    (Φ : (Fin D → ℝ) ≃L[ℝ] (Fin D → ℝ))
    (ρ : Fin M₂ ≃ Fin M₁) (F : Fin M₂ → (Fin D → ℝ) → ℝ)
    (hF : ∀ i, F i = fun u ↦ G (ρ i) (Φ u)) : Resolution F (0 : Fin D → ℝ) where
  numCharts := res.numCharts
  charts := fun c ↦ conjChart Φ ρ F hF (res.charts c)
  hne := res.hne
  U := Φ.symm '' res.U
  hU := by simpa using Φ.symm.isOpenMap.image_mem_nhds res.hU
  hcover := by
    have hunion : ⋃ c, (conjChart Φ ρ F hF (res.charts c)).g ''
        (conjChart Φ ρ F hF (res.charts c)).dom
        = Φ.symm '' (⋃ c, (res.charts c).g '' (res.charts c).dom) := by
      rw [Set.image_iUnion]
      refine Set.iUnion_congr (fun c ↦ ?_)
      change (fun w ↦ Φ.symm ((res.charts c).g w)) '' (res.charts c).dom
        = Φ.symm '' ((res.charts c).g '' (res.charts c).dom)
      rw [Set.image_image]
    rw [hunion, ← Set.image_diff Φ.symm.injective,
      Measure.addHaar_image_continuousLinearEquiv, res.hcover, mul_zero]

end DLNFibre.Core.Aoyagi
