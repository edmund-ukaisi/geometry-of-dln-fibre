import DLNFibre.Core.Aoyagi.ProductResolution

/-!
# `Core.Aoyagi.ResolutionInhabited` — the positive inhabitation test for `Chart` / `Resolution`

**Purpose (de-risking).** `ProductResolution` defines the `Chart` / `Resolution` records (Object B's
certified atlas) but never *inhabits* them: before this module no `Chart` or `Resolution` term existed
in the library, so the record's field set was untested — a hidden over-constraint would only surface
when the geometric monument tried to inhabit it. This module supplies the **positive inhabitation
test** the `Resolution` docstring calls for: for a normal-crossing monomial family `∑ bₖ²`
(a divisibility chain, so `⟨b₁,…,b_M⟩` is already principal), the **identity chart** `g = id`
inhabits every `Chart` field, and a single-chart atlas over a compact box inhabits `Resolution`.

This is the CLEAN end of Object B (`g` already normal-crossing, no blow-up) — deliberately NOT the
coupled corank-≥2 monument (charter §1.B), which needs a genuine analytic `g` and the two-sided ideal
identity via regular `Q,P`. It proves the record is inhabitable and that the downstream per-chart
value machinery (`Chart.chartMin`, `Resolution.divisorMin`) composes on a real term, sorry-free.
-/

open MeasureTheory Set Filter Topology RLCT
open Meta.Cordon

namespace DLNFibre.Core.Aoyagi

variable {M D : ℕ}

/-- `jacDet id u = 1`: the identity map has `fderiv` the identity `ContinuousLinearMap`, whose
determinant is `1`. -/
theorem jacDet_id (u : Fin D → ℝ) : jacDet (id : (Fin D → ℝ) → (Fin D → ℝ)) u = 1 := by
  unfold jacDet
  rw [fderiv_id]
  rw [ContinuousLinearMap.coe_id]
  exact LinearMap.det_id

/-- The Jacobian weight of the all-zero exponent vector is the constant `1`. -/
theorem jacWeight_zero (u : Fin D → ℝ) : jacWeight (fun _ ↦ 0 : Fin D → ℕ) u = 1 := by
  unfold jacWeight
  simp

/-- **The identity chart of a normal-crossing monomial family.** For an exponent matrix `e` with a
divisibility-minimal generator `k₀` (`hchain`) that is squarefree on its binding axes (`hunit_mult`)
and binds somewhere (`hbind`), the identity map `g = id` inhabits every `Chart` field for the family
`∑ (bₖ)²` at the origin: `g` analytic, `|det Dg| = 1 = jacWeight 0 · 1`, the ideal identity is the
Kronecker representation (`bₖ ∘ id = bₖ`), and the chart is injective everywhere (`excep = ∅`). The
compact domain is the unit box; the certificates hold on `nbhd = univ`. -/
noncomputable def idChart (e : Fin M → Fin D → ℕ) (k₀ : Fin M)
    (hchain : ∀ k d, e k₀ d ≤ e k d) (hbind : (bindingAxes (e k₀)).Nonempty)
    (hunit_mult : ∀ d ∈ bindingAxes (e k₀), e k₀ d = 1) :
    Chart (monomialFam e) (0 : Fin D → ℝ) where
  g := id
  hg0 := rfl
  hg_cont := continuous_id
  hg_analytic := analyticOnNhd_id
  hFmeas := by intro i; unfold monomialFam; fun_prop
  dom := Metric.closedBall 0 1
  hdom_compact := isCompact_closedBall 0 1
  hdom_zero := Metric.mem_closedBall_self (by norm_num)
  nbhd := univ
  hnbhd_open := isOpen_univ
  hdom_sub := subset_univ _
  excep := ∅
  hexcep_meas := MeasurableSet.empty
  hexcep_null := measure_empty
  hg_inj := by intro x _ y _ h; simpa using h
  M' := M
  bexp := e
  k₀ := k₀
  hchain := hchain
  hbind := hbind
  hunit_mult := hunit_mult
  jac := fun _ ↦ 0
  unit := fun _ ↦ 1
  hunit_cont := continuousOn_const
  hunit_ne := fun _ _ ↦ one_ne_zero
  hjac := by
    intro u _
    rw [jacDet_id, jacWeight_zero]
    norm_num
  hideal_fwd := by
    refine ⟨fun i j ↦ fun _ ↦ (if i = j then (1 : ℝ) else 0), fun _ _ ↦ continuousOn_const, ?_⟩
    intro u _ i
    simp only [Function.comp_apply, id_eq, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq, Finset.mem_univ, if_true]
  hideal_bwd := by
    refine ⟨fun i j ↦ fun _ ↦ (if i = j then (1 : ℝ) else 0), fun _ _ ↦ continuousOn_const, ?_⟩
    intro u _ i
    simp only [Function.comp_apply, id_eq, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq, Finset.mem_univ, if_true]

/-- **The single-chart identity resolution of a normal-crossing monomial family.** One `idChart` over
the unit box a.e.-covers the open unit ball (the box contains the ball), inhabiting `Resolution`. -/
noncomputable def idResolution (e : Fin M → Fin D → ℕ) (k₀ : Fin M)
    (hchain : ∀ k d, e k₀ d ≤ e k d) (hbind : (bindingAxes (e k₀)).Nonempty)
    (hunit_mult : ∀ d ∈ bindingAxes (e k₀), e k₀ d = 1) :
    Resolution (monomialFam e) (0 : Fin D → ℝ) where
  numCharts := 1
  charts := fun _ ↦ idChart e k₀ hchain hbind hunit_mult
  hne := Finset.univ_nonempty
  U := Metric.ball 0 1
  hU := Metric.ball_mem_nhds 0 (by norm_num)
  hcover := by
    have hsub : Metric.ball (0 : Fin D → ℝ) 1
        ⊆ ⋃ c : Fin 1, (idChart e k₀ hchain hbind hunit_mult).g ''
            (idChart e k₀ hchain hbind hunit_mult).dom := by
      refine subset_trans Metric.ball_subset_closedBall ?_
      intro x hx
      exact Set.mem_iUnion.2 ⟨0, by simpa [idChart] using hx⟩
    rw [Set.diff_eq_empty.2 hsub]
    exact measure_empty

/-- **The identity resolution's divisor minimum is `⨅_{binding} 1`.** Its `jac` is the all-zero
vector, so every binding-axis exponent `jac a + 1 = 1`; hence `divisorMin = 1`. Sorry-free — the
per-chart value machinery composes on a real term. -/
theorem idResolution_divisorMin (e : Fin M → Fin D → ℕ) (k₀ : Fin M)
    (hchain : ∀ k d, e k₀ d ≤ e k d) (hbind : (bindingAxes (e k₀)).Nonempty)
    (hunit_mult : ∀ d ∈ bindingAxes (e k₀), e k₀ d = 1) :
    (idResolution e k₀ hchain hbind hunit_mult).divisorMin = 1 := by
  rw [Resolution.divisorMin]
  -- Every chart's `chartMin` is `1` (its `jac` is all-zero, so every binding exponent is `1`).
  have hc : ∀ c, ((idResolution e k₀ hchain hbind hunit_mult).charts c).chartMin = 1 := by
    intro c
    rw [Chart.chartMin]
    have key : ∀ a, (((idResolution e k₀ hchain hbind hunit_mult).charts c).jac a + 1 : ℝ) = 1 :=
      fun a ↦ by show ((0 : ℕ) : ℝ) + 1 = 1; norm_num
    obtain ⟨a₀, ha₀⟩ := ((idResolution e k₀ hchain hbind hunit_mult).charts c).hbind
    exact le_antisymm ((Finset.inf'_le _ ha₀).trans (key a₀).le)
      (Finset.le_inf' _ _ (fun a _ ↦ (key a).ge))
  -- Hence the `inf'` over the (single) chart is `1`.
  obtain ⟨c₀, hc₀⟩ := (idResolution e k₀ hchain hbind hunit_mult).hne
  exact le_antisymm ((Finset.inf'_le _ hc₀).trans (hc c₀).le)
    (Finset.le_inf' _ _ (fun c _ ↦ (hc c).ge))

/-! ## A concrete non-vacuous witness — the single monomial `∏_d u_d` over `Fin (D+1)` -/

/-- The single all-ones-exponent family `b₀ = ∏_d u_d` over `Fin (D+1)` (one generator, `M = 1`). Its
binding axes are all `D+1` coordinates (each exponent `1`), so it is a genuine normal-crossing
singularity, not the regular point. -/
def allOnes (D : ℕ) : Fin 1 → Fin (D + 1) → ℕ := fun _ _ ↦ 1

theorem bindingAxes_allOnes (D : ℕ) : bindingAxes (allOnes D 0) = Finset.univ := by
  unfold bindingAxes allOnes
  simp

/-- The single monomial `∏_d u_d` inhabits `Resolution` — the concrete non-vacuous witness that the
record is inhabitable and the value machinery gives `divisorMin = 1` (the RLCT of `(∏u_d)²` is `½`). -/
noncomputable def allOnesResolution (D : ℕ) :
    Resolution (monomialFam (allOnes D)) (0 : Fin (D + 1) → ℝ) :=
  idResolution (allOnes D) 0
    (fun _ _ ↦ le_refl 1)
    (by rw [bindingAxes_allOnes]; exact Finset.univ_nonempty)
    (fun _ _ ↦ rfl)

theorem allOnesResolution_divisorMin (D : ℕ) : (allOnesResolution D).divisorMin = 1 :=
  idResolution_divisorMin _ _ _ _ _

end DLNFibre.Core.Aoyagi
