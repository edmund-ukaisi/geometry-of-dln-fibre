import DLNFibre.Core.Aoyagi.OriginBlowup
import DLNFibre.DLN.Aoyagi.LearningCoefficient

/-!
# `DLN.Aoyagi.GeometricAtlasD12` — rung (B): the geometric obligation for `d = (1,2)`

The FIRST genuine end-to-end discharge of the geometric obligation
`∃ res : Resolution (coreGen d e) 0, AtlasRealizesExponents d res` on a real singular DLN instance —
`d = ![1,2]`, `N = 1`. Here `mult` is the single 2×1 layer, and (via the linear flatten `e`) the
flattened core family `coreGen ![1,2] e` is the coordinate family `coordFam (flatDim ![1,2])`
precomposed with a linear coordinate change `Φ`. So the universal origin blow-up
`blowupResolution (D := flatDim ![1,2])` (`Core.Aoyagi.OriginBlowup`), CONJUGATED by `Φ`, is a
`Resolution (coreGen ![1,2] e) 0`; and its charts' exponents (`jac a + 1 = flatDim - 1 + 1 = 2 =
minAdm ![1,2]`) realise the built tree's terminal spectrum.

This proves the BODY of `exists_coreResolution`'s `sorry` at the first genuinely singular instance
(`d = ![1,2]`); it does NOT remove the `∀ d` library sorry. It also derives the first fully-proven
DLN learning-coefficient instance through the engine: `2·rlctAt (∑ coreGenᵢ²) 0 = cCodim ![1,2] 0`.

## The conjugation transport (reusable)

`conjResolution` transports a `Resolution G 0` across a continuous-linear-equiv conjugation `Φ` plus
an F-index reindex `ρ`, producing `Resolution F 0` for `F i = G (ρ i) ∘ Φ`. Each chart's map becomes
`Φ.symm ∘ g_c` (so `F i ∘ g'_c = G (ρ i) ∘ g_c`); the exponent data `bexp/k₀/jac` is UNCHANGED, and
the Jacobian picks up the constant factor `det Φ.symm`, absorbed into the chart `unit`.
-/

open MeasureTheory Set Filter Topology RLCT
open DLNFibre.Core DLNFibre.Core.Aoyagi DLNFibre.DLN.RLCT DLNFibre.DLN.RLCT.Engine

namespace DLNFibre.DLN.Aoyagi

/-! ## The conjugation transport of a `Resolution` (Core-native; reusable) -/

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

/-! ## The `d = ![1,2]` instantiation -/

/-- For `N = 1`, `mult` is the single (last) layer matrix. -/
theorem mult_d12 (A : Tuple (k := ℝ) ![1, 2]) : mult ![1, 2] A = A 0 :=
  Matrix.mul_one (A 0)

/-- `flatDim ![1,2] = 2`. -/
theorem flatDim_d12 : flatDim ![1, 2] = 2 := by decide

/-- The F-index reindex `Fin (d_N·d_0) ≃ Fin (flatDim d)` at `d = ![1,2]` (both `= 2`). -/
def rhoD12 : Fin (![1, 2] (Fin.last 1) * ![1, 2] 0) ≃ Fin (flatDim ![1, 2]) :=
  finCongr (by decide)

/-! ## The flattened core `coreGen ![1,2] e` is linear in the parameter -/

/-- Each flattened core generator `coreGen ![1,2] e i` is additive in the parameter (from `e`
linear + `mult ![1,2] A = A 0`). -/
theorem coreGen_d12_map_add (e : (Fin (flatDim ![1, 2]) → ℝ) ≃ₜ Tuple (k := ℝ) ![1, 2])
    (he_lin : IsLinearMap ℝ ⇑e) (i) (x y : Fin (flatDim ![1, 2]) → ℝ) :
    coreGen ![1, 2] e i (x + y) = coreGen ![1, 2] e i x + coreGen ![1, 2] e i y := by
  simp only [coreGen, mult_d12]
  rw [he_lin.map_add]
  rfl

/-- Each flattened core generator `coreGen ![1,2] e i` is `ℝ`-homogeneous in the parameter. -/
theorem coreGen_d12_map_smul (e : (Fin (flatDim ![1, 2]) → ℝ) ≃ₜ Tuple (k := ℝ) ![1, 2])
    (he_lin : IsLinearMap ℝ ⇑e) (i) (c : ℝ) (x : Fin (flatDim ![1, 2]) → ℝ) :
    coreGen ![1, 2] e i (c • x) = c • coreGen ![1, 2] e i x := by
  simp only [coreGen, mult_d12]
  rw [he_lin.map_smul]
  rfl

/-- **The linear coordinate change `Φ`** at `d = ![1,2]`: the flattened core family IS the
coordinate family precomposed with a continuous linear equiv,
`coreGen ![1,2] e i = coordFam (flatDim) (ρ i) ∘ Φ`. `Φ u k := coreGen ![1,2] e (ρ.symm k) u` is
linear (each component is) and injective (`e` injective, via the single matrix entry-support), hence
— on the finite-dimensional `ℝ^flatDim` — a linear iso. -/
theorem exists_coreGen_d12_cle
    (e : (Fin (flatDim ![1, 2]) → ℝ) ≃ₜ Tuple (k := ℝ) ![1, 2]) (he_lin : IsLinearMap ℝ ⇑e) :
    ∃ Φ : (Fin (flatDim ![1, 2]) → ℝ) ≃L[ℝ] (Fin (flatDim ![1, 2]) → ℝ),
      ∀ i, coreGen ![1, 2] e i = fun u ↦ coordFam (flatDim ![1, 2]) (rhoD12 i) (Φ u) := by
  set Tfun : (Fin (flatDim ![1, 2]) → ℝ) → (Fin (flatDim ![1, 2]) → ℝ) :=
    fun u k ↦ coreGen ![1, 2] e (rhoD12.symm k) u with hTfun
  have hTlin : IsLinearMap ℝ Tfun := by
    refine ⟨fun x y ↦ ?_, fun c x ↦ ?_⟩
    · funext k
      simp only [hTfun, Pi.add_apply]
      exact coreGen_d12_map_add e he_lin (rhoD12.symm k) x y
    · funext k
      simp only [hTfun, Pi.smul_apply]
      exact coreGen_d12_map_smul e he_lin (rhoD12.symm k) c x
  have hTinj : Function.Injective (IsLinearMap.mk' Tfun hTlin) := by
    intro u u' huu
    have hcore : ∀ i, coreGen ![1, 2] e i u = coreGen ![1, 2] e i u' := by
      intro i
      have h := congrFun huu (rhoD12 i)
      simpa only [IsLinearMap.mk'_apply, hTfun, Equiv.symm_apply_apply] using h
    have heq : ⇑e u = ⇑e u' := by
      funext j
      obtain rfl : j = 0 := Subsingleton.elim j 0
      ext r c
      have hi := hcore (finProdFinEquiv (r, c))
      simpa only [coreGen, mult_d12, Equiv.symm_apply_apply] using hi
    exact e.injective heq
  have hTsurj : Function.Surjective (IsLinearMap.mk' Tfun hTlin) :=
    LinearMap.injective_iff_surjective.mp hTinj
  refine ⟨(LinearEquiv.ofBijective (IsLinearMap.mk' Tfun hTlin)
    ⟨hTinj, hTsurj⟩).toContinuousLinearEquiv, ?_⟩
  intro i
  funext u
  simp only [coordFam, LinearEquiv.coe_toContinuousLinearEquiv', LinearEquiv.ofBijective_apply,
    IsLinearMap.mk'_apply, hTfun, Equiv.symm_apply_apply]

/-! ## The leaf-divisor membership helper and the two-clause seam -/

/-- The pivot axis `c` binds in a single-pivot exponent `fun j ↦ if j = c then 1 else 0`. -/
theorem self_mem_bindingAxes {D : ℕ} (c : Fin D) :
    c ∈ bindingAxes (fun j ↦ if j = c then 1 else 0) := by
  simp [bindingAxes]

/-- A leaf's divisor exponent is a terminal exponent of the tree. -/
theorem leaf_divExp_mem_terminalExponents {L : ℕ} {M : Fin (L + 1) → ℕ}
    (t : ResolutionTree M) (l : LeafData M) (hl : l ∈ ResolutionTree.leaves t) (k : Fin l.numDiv) :
    l.divExp k ∈ ResolutionTree.terminalExponents t := by
  rw [ResolutionTree.terminalExponents, List.mem_flatMap]
  refine ⟨l, hl, ?_⟩
  rw [List.mem_append]
  exact Or.inl (List.mem_map.mpr ⟨k, List.mem_finRange k, rfl⟩)

/-! ## The headline: the geometric obligation's BODY at `d = ![1,2]` -/

/-- **RUNG (B) — the geometric obligation for `d = ![1,2]`.** For any linear flatten `e` (a linear
map fixes `0`, so `exists_coreResolution`'s `he0` is subsumed by `he_lin`), the flattened
zero-product core `∑ (coreGen ![1,2] e)ᵢ²` admits a certified resolution atlas at `0` (the origin
blow-up of `ℝ^flatDim`, conjugated by the linear coordinate change `Φ` that turns the coordinate
family into `coreGen ![1,2] e`) whose binding-axis exponents realise the built tree's terminal
spectrum (`jac a + 1 = flatDim - 1 + 1 = 2 = minAdm ![1,2]`). This discharges the BODY of
`exists_coreResolution`'s `sorry` at the first genuinely singular DLN instance. -/
theorem exists_atlasRealizesExponents_d12
    (e : (Fin (flatDim ![1, 2]) → ℝ) ≃ₜ Tuple (k := ℝ) ![1, 2]) (he_lin : IsLinearMap ℝ ⇑e) :
    ∃ res : Resolution (coreGen ![1, 2] e) 0, AtlasRealizesExponents ![1, 2] res := by
  obtain ⟨Φ, hΦ⟩ := exists_coreGen_d12_cle e he_lin
  have hD : 2 ≤ flatDim ![1, 2] := by rw [flatDim_d12]
  set res := conjResolution (blowupResolution hD) Φ rhoD12 (coreGen ![1, 2] e) hΦ with hres
  have hbexp : ∀ c : Fin res.numCharts,
      (res.charts c).bexp (res.charts c).k₀ = fun j ↦ if j = c then 1 else 0 := fun c ↦ rfl
  have hjacf : ∀ c : Fin res.numCharts,
      (res.charts c).jac = fun j ↦ if j = c then flatDim ![1, 2] - 1 else 0 := fun c ↦ rfl
  refine ⟨res, ?_, ?_⟩
  · -- clause (i): every binding-axis exponent is a terminal exponent (= minAdm, in the spectrum)
    intro c a ha
    have ha' : a = c := by
      rw [hbexp c] at ha
      have h2 : (0 : ℕ) < if a = c then 1 else 0 := (Finset.mem_filter.mp ha).2
      by_contra hac
      rw [if_neg hac] at h2
      exact absurd h2 (lt_irrefl 0)
    subst ha'
    have hjc : (res.charts a).jac a + 1 = minAdm ![1, 2] := by
      have hj : (res.charts a).jac a = flatDim ![1, 2] - 1 := by rw [hjacf a]; exact if_pos rfl
      rw [hj]; decide
    rw [hjc]
    obtain ⟨l, hl, k, hk⟩ := o5_core_realized ![1, 2] (by decide) (by decide)
    rw [← hk]
    exact leaf_divExp_mem_terminalExponents _ l hl k
  · -- clause (ii): the minimiser (= minAdm) is realised by a chart's binding axis
    intro l hl k hlk
    have h0 : (0 : ℕ) < flatDim ![1, 2] := by decide
    refine ⟨⟨0, h0⟩, ⟨0, h0⟩, ?_, ?_⟩
    · rw [hbexp ⟨0, h0⟩]
      exact self_mem_bindingAxes ⟨0, h0⟩
    · have hj : (res.charts ⟨0, h0⟩).jac ⟨0, h0⟩ = flatDim ![1, 2] - 1 := by
        rw [hjacf ⟨0, h0⟩]; exact if_pos rfl
      rw [hj, hlk]; decide

/-! ## The first fully-proven DLN learning-coefficient instance through the engine -/

/-- **The `d = ![1,2]` engine value** `2·rlctAt (∑ coreGenᵢ²) 0 = cCodim ![1,2] 0` — the first fully
proven DLN learning-coefficient instance obtained through the NEW machinery (record + seam),
with NO frontier `sorry` on its cone. Wired: the geometric atlas
(`exists_atlasRealizesExponents_d12`) → the salvage adapter
(`hlb_hattain_of_atlasRealizesExponents`) → the abstract engine value
(`Resolution.two_mul_rlctAt_eq_cCodim`). -/
theorem two_mul_rlctAt_coreGen_d12
    (e : (Fin (flatDim ![1, 2]) → ℝ) ≃ₜ Tuple (k := ℝ) ![1, 2]) (he_lin : IsLinearMap ℝ ⇑e) :
    2 * _root_.RLCT.rlctAt (sumSqFam (coreGen ![1, 2] e)) 0
      = ((cCodim ![1, 2] 0 (by decide)).toNat : ℝ) := by
  obtain ⟨res, hreal⟩ := exists_atlasRealizesExponents_d12 e he_lin
  have hd : Monotone (![1, 2] : Fin 2 → ℕ) := by decide
  have hpos : ∀ k, 0 < (![1, 2] : Fin 2 → ℕ) k := by decide
  have hne : (qipFeasible ![1, 2]).Nonempty := by decide
  have h : (kostantPartitions ![1, 2] 0).Nonempty :=
    (kostant_nonempty_iff_qipFeasible_nonempty ![1, 2] hd).mpr hne
  obtain ⟨hlb, hattain⟩ :=
    hlb_hattain_of_atlasRealizesExponents ![1, 2] hd (by decide) hpos h hne res hreal
  exact res.two_mul_rlctAt_eq_cCodim ![1, 2] hd h hne hlb hattain

end DLNFibre.DLN.Aoyagi
