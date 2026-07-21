import DLNFibre.Core.Aoyagi.IdealInvariance
import DLNFibre.Core.Aoyagi.MonomialRLCT
import DLNFibre.Core.Aoyagi.Waypoint
import DLNFibre.Core.Aoyagi.AreaFormula
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Determinant
import Meta.Cordon

/-!
# `Core.Aoyagi.ProductResolution` — Object B: the certified product-ideal resolution (an ATLAS)

**BLUEPRINT (v3).** The geometric heart: Aoyagi's proper resolution that turns the core loss
`∑ (∏C)ᵢⱼ²` into a sum of squared monomials in each exceptional chart (worked.tex:173–189, 475–520),
with `⟨(∏C)∘g_c⟩ = ⟨diag(b₁,…,b_M)_c⟩` and the `bᵢ` forming a divisibility chain in each chart.

## The soundness fixes (v2 defect 1, BOTH halves)

* **Jacobian certificate (half 1), DOM-WIDE.** Each chart certifies, as a **propositional field**
  `hjac` holding on the whole region `nbhd` (D1: not merely a germ at the origin — a germ-only
  certificate could be discharged by a chart covering far regions where the ideal identity fails, the
  monument-cheapening hole), that the actual `|det Dg_c|` equals the declared monomial weight times a
  unit nonvanishing on `nbhd`. Likewise `hideal_fwd`/`hideal_bwd` hold as `RegionRepresents` on
  `nbhd`. `no_unit_forces_axis_jac_coupled` shows this forbids the false axis exponent of the coupled
  chart `g = (u₀u₁², u₀²u₁)`. Per-chart a.e.-injectivity (`excep`/`hexcep_null`/`hg_inj`) is restored
  (D2 — the `≤` direction of the CoV needs bounded multiplicity).

* **Min-over-charts (half 2) — the ATLAS.** v3's first draft asserted a *single-chart* CoV equality
  `rlctAt (∑Fᵢ²) x₀ = wrlctAt |det Dg| (∑(Fᵢ∘g)²) 0`. That is FALSE (an independent hunt found
  `K = x²+y⁴`, chart `g(u,v)=(u,uv)`: `rlctAt = 3/4` but the single-chart weighted value is `1`; the
  binding direction lives in the *other* chart) — the same class of error as the original v2 defect.
  The paper's rule is a **minimum over charts** (worked.tex:178: `rlct = min_{charts U} min_j
  (h_j+1)/(2k_j)`; the terminal candidates are minimised across branches, worked.tex:529–542). So a
  `Resolution` here is an **atlas**: a finite family of certified charts whose images of **compact
  source domains** (`hcover` over `dom`, the properness / no-escape content at the atlas level —
  individual blow-up charts are not proper) a.e.-cover a neighbourhood of `x₀`, and the RLCT is the
  `min` of the per-chart weighted values (`rlctAt_sumSqFam_eq_iInf_charts`). The single point `0` of
  one chart only gives an upper bound; the covering family gives equality. The `ℝ²`-at-`0` blow-up
  (two charts, compact boxes over the affine `ℙ¹`) inhabits the record — the positive test.
-/

open MeasureTheory Set Filter Topology RLCT
open Meta.Cordon

namespace DLNFibre.Core.Aoyagi

variable {M D : ℕ}

/-- The **absolute Jacobian determinant** `|det Dg(u)|` of a chart `g : ℝᴰ → ℝᴰ` (`fderiv`'s
determinant), which the Jacobian certificate `hjac` pins to a monomial weight times a nonvanishing
unit. -/
noncomputable def jacDet (g : (Fin D → ℝ) → (Fin D → ℝ)) (u : Fin D → ℝ) : ℝ :=
  LinearMap.det (fderiv ℝ g u).toLinearMap

/-- **One certified resolution chart** of `∑ Fᵢ²` at the deepest point `x₀` (Aoyagi Cases 1 & 2,
regular `Q, P`; worked.tex:475–520). Every hypothesis Aoyagi's proper chart needs is a propositional
field (the v2-defect-1 fix). Dimension-preserving (`ℝᴰ → ℝᴰ`). The chart is one branch of the
exceptional fibre over `x₀`; the RLCT is the minimum over an atlas of these (`Resolution`). -/
structure Chart (F : Fin M → (Fin D → ℝ) → ℝ) (x₀ : Fin D → ℝ) where
  /-- The resolution chart. -/
  g : (Fin D → ℝ) → (Fin D → ℝ)
  /-- The chart origin maps to the deepest point `x₀`. -/
  hg0 : g 0 = x₀
  /-- `g` is continuous (measurability of the pulled-back integrand). -/
  hg_cont : Continuous g
  /-- `g` is analytic (Hironaka's map is analytic). -/
  hg_analytic : AnalyticOnNhd ℝ g Set.univ
  /-- The generators are measurable (the per-chart change-of-variables needs it; D3b). -/
  hFmeas : ∀ i, Measurable (F i)
  /-- The chart's **compact source domain** (the properness / no-escape content, at the chart level:
  the CoV integral is over this bounded region), containing the chart origin. -/
  dom : Set (Fin D → ℝ)
  hdom_compact : IsCompact dom
  hdom_zero : (0 : Fin D → ℝ) ∈ dom
  /-- An **open region carrying the certificates** — a neighbourhood of the domain. The certificates
  (`hjac`, `hunit_*`, `hideal_*`) hold on ALL of `nbhd`, not merely at the origin (D1): a germ-only
  certificate could be discharged by a chart covering FAR regions where its ideal identity fails. -/
  nbhd : Set (Fin D → ℝ)
  hnbhd_open : IsOpen nbhd
  hdom_sub : dom ⊆ nbhd
  /-- The **exceptional locus** (where `g` is not injective) — the birational content (D2, restored). -/
  excep : Set (Fin D → ℝ)
  hexcep_meas : MeasurableSet excep
  /-- The exceptional locus is null: `g` is a.e.-injective on the region (birational). The `≤`
  direction of the CoV needs this bounded multiplicity; the `≥` direction does not. -/
  hexcep_null : volume excep = 0
  hg_inj : Set.InjOn g (nbhd \ excep)
  /-- The number of diagonal monomials `b₁,…,b_{M'}` in this chart (the paper's `M(L+1)`). -/
  M' : ℕ
  /-- The exceptional-monomial exponents: `bₖ(u) = ∏_d u_d ^ (bexp k d)`. -/
  bexp : Fin M' → Fin D → ℕ
  /-- The dominant (divisibility-minimal) monomial index `b_{k₀}`. -/
  k₀ : Fin M'
  /-- **The divisibility chain** `b_{k₀} | bₖ` (worked.tex:483–488) — Aoyagi's own invariant. -/
  hchain : ∀ k d, bexp k₀ d ≤ bexp k d
  /-- Some divisor binds in this chart (needed for the boxed min). -/
  hbind : (bindingAxes (bexp k₀)).Nonempty
  /-- **Unit divisor multiplicity** `k_d = 1` on binding axes (worked.tex:495). -/
  hunit_mult : ∀ d ∈ bindingAxes (bexp k₀), bexp k₀ d = 1
  /-- The Jacobian monomial exponents `h_d` (the paper's `M_{s,k} − 1`; worked.tex:492–497). -/
  jac : Fin D → ℕ
  /-- The unit of the Jacobian certificate — continuous and NONVANISHING on the whole region. -/
  unit : (Fin D → ℝ) → ℝ
  hunit_cont : ContinuousOn unit nbhd
  hunit_ne : ∀ u ∈ nbhd, unit u ≠ 0
  /-- **The Jacobian certificate, DOM-WIDE** (v2-defect-1 fix + D1): the actual `|det Dg|` equals the
  declared monomial weight times the nonvanishing unit, on the whole region `nbhd`. -/
  hjac : ∀ u ∈ nbhd, |jacDet g u| = jacWeight jac u * |unit u|
  /-- **The ideal identity** `⟨(∏C)∘g⟩ ⊆ ⟨diag b⟩` on the region (D1: `RegionRepresents` on `nbhd`,
  coefficients continuous ON `nbhd`; not a germ at `0`). -/
  hideal_fwd : RegionRepresents (fun i ↦ F i ∘ g) (monomialFam bexp) nbhd
  /-- **The ideal identity** `⟨diag b⟩ ⊆ ⟨(∏C)∘g⟩` on the region. -/
  hideal_bwd : RegionRepresents (monomialFam bexp) (fun i ↦ F i ∘ g) nbhd

/-- **The certified product-ideal resolution — an ATLAS of charts.** A finite family of certified
`Chart`s whose images (of the charts' **compact** source domains — the properness / no-escape content,
per chart; individual blow-up charts like `(u,uv)` are NOT proper, so properness is carried as a
compact domain, not a proper-map field) a.e.-cover a neighbourhood of `x₀`. Fix for v2 defect 1,
half 2: the RLCT is a minimum over the covering charts, not a single-chart value; the cover LOCALIZES
the source to compact domains (an unrestricted `∃ u, g u = w` lets preimages escape). The standard
`ℝ²`-at-`0` blow-up (two affine charts, compact source boxes covering `ℙ¹`, ideal identities holding
globally on those doms) inhabits this — the positive inhabitation test. -/
structure Resolution (F : Fin M → (Fin D → ℝ) → ℝ) (x₀ : Fin D → ℝ) where
  /-- The number of charts (branches of the exceptional fibre over `x₀`). -/
  numCharts : ℕ
  /-- The atlas of certified charts. -/
  charts : Fin numCharts → Chart F x₀
  /-- The atlas is nonempty (there is a chart). -/
  hne : (Finset.univ : Finset (Fin numCharts)).Nonempty
  /-- A neighbourhood of `x₀` the atlas covers. -/
  U : Set (Fin D → ℝ)
  hU : U ∈ 𝓝 x₀
  /-- **The localizing cover** — `U` is covered, up to a null set, by the images of the charts'
  COMPACT source domains `(charts c).dom` (properness + covering, both localized). Inhabited by the
  blow-up, unlike an escaping `∃ u, g u = w`. -/
  hcover : volume (U \ ⋃ c, (charts c).g '' (charts c).dom) = 0

/-- The Jacobian weight `w ↦ |det Dg_c w|` of a chart. -/
noncomputable def Chart.jacWeightFn {F : Fin M → (Fin D → ℝ) → ℝ} {x₀ : Fin D → ℝ}
    (c : Chart F x₀) : (Fin D → ℝ) → ℝ :=
  fun u ↦ |jacDet c.g u|

/-- The chart's **integer divisor minimum** `⨅ binding (jac d + 1)` (the boxed value `2·rlct` of this
chart under unit multiplicity `k_d = 1`). -/
noncomputable def Chart.chartMin {F : Fin M → (Fin D → ℝ) → ℝ} {x₀ : Fin D → ℝ}
    (c : Chart F x₀) : ℝ :=
  (bindingAxes (c.bexp c.k₀)).inf' c.hbind (fun a ↦ (c.jac a + 1 : ℝ))

/-- The resolution's **divisor minimum** — the `min` over the atlas of the per-chart divisor minima
(`min over charts`, worked.tex:178). Object D bridges this to `qipMin`/`cCodim`. -/
noncomputable def Resolution.divisorMin {F : Fin M → (Fin D → ℝ) → ℝ} {x₀ : Fin D → ℝ}
    (res : Resolution F x₀) : ℝ :=
  Finset.univ.inf' res.hne (fun c ↦ (res.charts c).chartMin)

/-! ## The change-of-variables (min over charts) and the value

The atlas change-of-variables `rlctAt_sumSqFam_eq_iInf_charts` and the always-valid single-chart
bound `rlctAt_sumSqFam_le_chart` are proven **below** (`## The atlas change-of-variables …`), after
the per-chart set form and the two CoV legs they ride. -/

/-! ### Shared discharge helpers for the per-chart value (leaf 1) -/

/-- `RegionRepresents` on an open set gives `GermRepresents` at any interior point: the coefficients
are `ContinuousAt` (interior + `ContinuousOn`), and the representation holds eventually (the open set
is a neighbourhood). The dom-wide → germ-at-origin bridge Object B's charts ride into Object A. -/
lemma RegionRepresents.germRepresents_of_isOpen {p q : ℕ}
    {G : Fin p → (Fin D → ℝ) → ℝ} {H : Fin q → (Fin D → ℝ) → ℝ}
    {V : Set (Fin D → ℝ)} {x : Fin D → ℝ}
    (h : RegionRepresents G H V) (hV : IsOpen V) (hx : x ∈ V) :
    GermRepresents G H x := by
  obtain ⟨a, hcont, hrep⟩ := h
  refine ⟨a, fun i j ↦ (hcont i j).continuousAt (hV.mem_nhds hx), ?_⟩
  filter_upwards [hV.mem_nhds hx] with u hu using hrep u hu

/-- The zero set of a monomial family's sum-of-squares is locally null: the dominant generator
`b_{k₀} = ∏_d u_d^(e k₀ d)` is a nonzero polynomial (a monic monomial), so `{∑ bₖ² = 0} ⊆ {b_{k₀}=0}`
is null (`volume_zeroSet_eq_zero`). No binding-axis hypothesis needed (an empty exponent gives the
constant `1`, whose zero set is empty). -/
lemma locallyNullZeros_sumSqFam_monomialFam {p : ℕ} (e : Fin p → Fin D → ℕ) (k₀ : Fin p)
    (x : Fin D → ℝ) :
    LocallyNullZeros (sumSqFam (monomialFam e)) x := by
  refine locallyNullZeros_sumSqFam_of_polynomial k₀
    (∏ d, MvPolynomial.X d ^ (e k₀ d)) ?_ ?_
  · rw [Finset.prod_ne_zero_iff]
    exact fun d _ ↦ pow_ne_zero _ (MvPolynomial.X_ne_zero d)
  · intro w; simp only [monomialFam, map_prod, map_pow, MvPolynomial.eval_X]

/-- The zero set of a monomial `∏_d u_d^(e k₀ d)` itself is `volume`-null. -/
lemma volume_monomialFam_zeroSet {p : ℕ} (e : Fin p → Fin D → ℕ) (k₀ : Fin p) :
    volume {u : Fin D → ℝ | monomialFam e k₀ u = 0} = 0 := by
  have hset : {u : Fin D → ℝ | monomialFam e k₀ u = 0}
      = {u | MvPolynomial.eval u (∏ d, MvPolynomial.X d ^ (e k₀ d)) = 0} := by
    ext u; simp only [Set.mem_setOf_eq, monomialFam, map_prod, map_pow, MvPolynomial.eval_X]
  rw [hset]
  exact MvPolynomial.volume_zeroSet_eq_zero _
    (by rw [Finset.prod_ne_zero_iff]; exact fun d _ ↦ pow_ne_zero _ (MvPolynomial.X_ne_zero d))

/-- The Jacobian weight `|det Dg|` of an analytic chart is continuous (analytic ⟹ `C¹` ⟹ `fderiv`
continuous; `det` is continuous on `E →L E`), hence measurable. -/
lemma Chart.continuous_jacWeightFn {F : Fin M → (Fin D → ℝ) → ℝ} {x₀ : Fin D → ℝ}
    (c : Chart F x₀) : Continuous c.jacWeightFn := by
  have hcd : ContDiff ℝ 1 c.g :=
    contDiffOn_univ.mp (c.hg_analytic.contDiffOn_of_completeSpace)
  have hfder : Continuous (fun u ↦ fderiv ℝ c.g u) := hcd.continuous_fderiv one_ne_zero
  have hdet : Continuous (fun u ↦ (fderiv ℝ c.g u).det) :=
    ContinuousLinearMap.continuous_det.comp hfder
  have heq : c.jacWeightFn = fun u ↦ |(fderiv ℝ c.g u).det| := by
    funext u; rfl
  rw [heq]; exact hdet.abs

/-- **STRIKE-ABLE/FRONTIER — per-chart value.** In each chart, the weighted RLCT of the pulled-back
loss equals `½·(⨅ binding (jac d + 1))` (chart-local): Object A's weighted two-sided ideal invariance
(`hideal_fwd`/`hideal_bwd`, under the nonnegative weight `|det Dg_c| ≥ 0`) transports the pulled-back
generators to the diagonal monomials, and Object C's boxed rule under the chain `hchain` + unit
multiplicity `hunit_mult` gives the integer divisor min. -/
theorem Chart.two_mul_wrlctAt_eq_chartMin {F : Fin M → (Fin D → ℝ) → ℝ} {x₀ : Fin D → ℝ}
    (c : Chart F x₀) :
    2 * wrlctAt c.jacWeightFn (sumSqFam (fun i ↦ F i ∘ c.g)) 0 = c.chartMin := by
  -- map: B-chart-value (weighted-A ideal invariance ∘ C-dln-unit-multiplicity, per chart)
  classical
  -- `0 ∈ nbhd` (open), so `nbhd ∈ 𝓝 0`; the certificates hold on `nbhd`.
  have h0nbhd : (0 : Fin D → ℝ) ∈ c.nbhd := c.hdom_sub c.hdom_zero
  have hnbhd_mem : c.nbhd ∈ 𝓝 (0 : Fin D → ℝ) := c.hnbhd_open.mem_nhds h0nbhd
  -- The weight `W = |det Dg|` is continuous (hence measurable) and nonnegative.
  have hWcont : Continuous c.jacWeightFn := c.continuous_jacWeightFn
  have hWmeas : Measurable c.jacWeightFn := hWcont.measurable
  have hWnn : ∀ᶠ w in 𝓝 (0 : Fin D → ℝ), 0 ≤ c.jacWeightFn w :=
    Filter.Eventually.of_forall (fun w ↦ abs_nonneg _)
  -- measurabilities of the two generator families
  have hGmeas : ∀ i, Measurable (fun u ↦ (F i ∘ c.g) u) :=
    fun i ↦ (c.hFmeas i).comp c.hg_cont.measurable
  have hMmeas : ∀ j, Measurable (monomialFam c.bexp j) := by
    intro j; unfold monomialFam; fun_prop
  -- germ-ideal identities (dom-wide → germ at origin)
  have hGF : GermRepresents (fun i ↦ F i ∘ c.g) (monomialFam c.bexp) 0 :=
    c.hideal_fwd.germRepresents_of_isOpen c.hnbhd_open h0nbhd
  have hFG : GermRepresents (monomialFam c.bexp) (fun i ↦ F i ∘ c.g) 0 :=
    c.hideal_bwd.germRepresents_of_isOpen c.hnbhd_open h0nbhd
  -- nullness of the two sum-of-squares zero sets at `0`
  have hFnull : LocallyNullZeros (sumSqFam (monomialFam c.bexp)) 0 :=
    locallyNullZeros_sumSqFam_monomialFam c.bexp c.k₀ 0
  have hGnull : LocallyNullZeros (sumSqFam (fun i ↦ F i ∘ c.g)) 0 := by
    obtain ⟨a, _hacont, harep⟩ := c.hideal_bwd
    refine ⟨c.nbhd, hnbhd_mem, measure_mono_null ?_ (volume_monomialFam_zeroSet c.bexp c.k₀)⟩
    intro u hu
    have hu0 : u ∈ {w | sumSqFam (fun i ↦ F i ∘ c.g) w = 0} := hu.1
    have hall : ∀ i, (F i ∘ c.g) u = 0 :=
      fun i ↦ sumSqFam_zeroSet_subset (fun i ↦ F i ∘ c.g) i hu0
    show monomialFam c.bexp c.k₀ u = 0
    rw [harep u hu.2 c.k₀]
    refine Finset.sum_eq_zero (fun i _ ↦ ?_)
    show a c.k₀ i u * (F i ∘ c.g) u = 0
    rw [hall i, mul_zero]
  -- the weighted admissible sets coincide (Object A, set form) ⟹ the `wrlctAt`s coincide
  have hset := wLocalAdmissibleExponents_sumSqFam_eq_of_germ_eq
    (W := c.jacWeightFn) hWmeas hMmeas hGmeas hWnn hGnull hFnull hGF hFG
  have hval : wrlctAt c.jacWeightFn (sumSqFam (fun i ↦ F i ∘ c.g)) 0
      = wrlctAt c.jacWeightFn (sumSqFam (monomialFam c.bexp)) 0 := by
    unfold wrlctAt; rw [hset]
  -- the measurable Jacobian-unit factor `um = |unit|` (extended measurably off `nbhd`)
  set um : (Fin D → ℝ) → ℝ := Set.piecewise c.nbhd (fun u ↦ |c.unit u|) (fun _ ↦ 1) with hum
  have hum_eq : ∀ u ∈ c.nbhd, um u = |c.unit u| :=
    fun u hu ↦ Set.piecewise_eq_of_mem _ _ _ hu
  have hcabsOn : ContinuousOn (fun u ↦ |c.unit u|) c.nbhd := c.hunit_cont.abs
  have hum_meas : Measurable um := by
    apply measurable_of_isOpen
    intro t ht
    obtain ⟨v, v_open, hv⟩ : ∃ v : Set (Fin D → ℝ), IsOpen v ∧
        (fun u ↦ |c.unit u|) ⁻¹' t ∩ c.nbhd = v ∩ c.nbhd :=
      continuousOn_iff'.1 hcabsOn t ht
    rw [hum, Set.piecewise_preimage, Set.ite, hv]
    exact (v_open.measurableSet.inter c.hnbhd_open.measurableSet).union
      ((measurable_const ht.measurableSet).diff c.hnbhd_open.measurableSet)
  have hum_ev : um =ᶠ[𝓝 0] fun u ↦ |c.unit u| := by
    filter_upwards [hnbhd_mem] with u hu using hum_eq u hu
  have hum_cont : ContinuousAt um 0 :=
    ((c.hunit_cont.continuousAt hnbhd_mem).abs).congr hum_ev.symm
  have hum0 : um 0 ≠ 0 := by
    rw [hum_eq 0 h0nbhd]; exact abs_ne_zero.mpr (c.hunit_ne 0 h0nbhd)
  -- the Jacobian certificate, in the `W = jacWeight jac · um` form Object C consumes
  have hW_eq : ∀ᶠ u in 𝓝 (0 : Fin D → ℝ),
      c.jacWeightFn u = jacWeight c.jac u * um u := by
    filter_upwards [hnbhd_mem] with u hu
    show |jacDet c.g u| = jacWeight c.jac u * um u
    rw [c.hjac u hu, hum_eq u hu]
  -- assemble: value invariance ∘ Object C's boxed rule
  rw [Chart.chartMin, hval]
  exact monomialSumSq_two_mul_wrlctAt_eq_min c.hchain c.hbind c.hunit_mult
    hum_cont hum0 hum_meas hW_eq

/-! ### Per-chart set form and per-point machinery (the atlas CoV substrate) -/

/-- The chart's Jacobian weight `|det Dg|` factors as `jacWeight jac · unit` on a neighbourhood of any
`p ∈ nbhd`, with the (measurably extended) `|unit|` continuous and nonzero at `p`. The dom-wide
`hjac` certificate, packaged in the `jacWeight · unit` form Object C consumes, at an arbitrary base
point of the region (not just the origin). -/
theorem Chart.jacWeight_form_at {F : Fin M → (Fin D → ℝ) → ℝ} {x₀ : Fin D → ℝ}
    (c : Chart F x₀) {p : Fin D → ℝ} (hp : p ∈ c.nbhd) :
    ∃ unit : (Fin D → ℝ) → ℝ, ContinuousAt unit p ∧ unit p ≠ 0 ∧ Measurable unit ∧
      ∀ᶠ u in 𝓝 p, c.jacWeightFn u = jacWeight c.jac u * unit u := by
  classical
  have hnbhd_mem : c.nbhd ∈ 𝓝 p := c.hnbhd_open.mem_nhds hp
  set um : (Fin D → ℝ) → ℝ := Set.piecewise c.nbhd (fun u ↦ |c.unit u|) (fun _ ↦ 1) with hum
  have hum_eq : ∀ u ∈ c.nbhd, um u = |c.unit u| :=
    fun u hu ↦ Set.piecewise_eq_of_mem _ _ _ hu
  have hcabsOn : ContinuousOn (fun u ↦ |c.unit u|) c.nbhd := c.hunit_cont.abs
  have hum_meas : Measurable um := by
    apply measurable_of_isOpen
    intro t ht
    obtain ⟨v, v_open, hv⟩ : ∃ v : Set (Fin D → ℝ), IsOpen v ∧
        (fun u ↦ |c.unit u|) ⁻¹' t ∩ c.nbhd = v ∩ c.nbhd :=
      continuousOn_iff'.1 hcabsOn t ht
    rw [hum, Set.piecewise_preimage, Set.ite, hv]
    exact (v_open.measurableSet.inter c.hnbhd_open.measurableSet).union
      ((measurable_const ht.measurableSet).diff c.hnbhd_open.measurableSet)
  refine ⟨um, ?_, ?_, hum_meas, ?_⟩
  · have hum_ev : um =ᶠ[𝓝 p] fun u ↦ |c.unit u| := by
      filter_upwards [hnbhd_mem] with u hu using hum_eq u hu
    exact ((c.hunit_cont.continuousAt hnbhd_mem).abs).congr hum_ev.symm
  · rw [hum_eq p hp]; exact abs_ne_zero.mpr (c.hunit_ne p hp)
  · filter_upwards [hnbhd_mem] with u hu
    show |jacDet c.g u| = jacWeight c.jac u * um u
    rw [c.hjac u hu, hum_eq u hu]

/-- **Object A at a base point of the region.** The weighted admissible sets of the pulled-back loss
`∑ (Fᵢ∘g)²` and of the diagonal monomial sum `∑ bₖ²` coincide at any `p ∈ nbhd` — the germ ideals
agree there (`RegionRepresents` both ways, via `germRepresents_of_isOpen`), and the junk-`0` guards
discharge as in the origin case (the polynomial-zero-set nullity). Legalises replacing the loss by
its monomial normal form pointwise across the chart domain. -/
theorem Chart.wLocalAdmissible_swap {F : Fin M → (Fin D → ℝ) → ℝ} {x₀ : Fin D → ℝ}
    (c : Chart F x₀) {p : Fin D → ℝ} (hp : p ∈ c.nbhd) :
    wLocalAdmissibleExponents c.jacWeightFn (sumSqFam (fun i ↦ F i ∘ c.g)) p
      = wLocalAdmissibleExponents c.jacWeightFn (sumSqFam (monomialFam c.bexp)) p := by
  have hnbhd_mem : c.nbhd ∈ 𝓝 p := c.hnbhd_open.mem_nhds hp
  have hWmeas : Measurable c.jacWeightFn := c.continuous_jacWeightFn.measurable
  have hMmeas : ∀ j, Measurable (monomialFam c.bexp j) := by
    intro j; unfold monomialFam; fun_prop
  have hGmeas : ∀ i, Measurable (fun u ↦ (F i ∘ c.g) u) :=
    fun i ↦ (c.hFmeas i).comp c.hg_cont.measurable
  have hWnn : ∀ᶠ w in 𝓝 p, 0 ≤ c.jacWeightFn w :=
    Filter.Eventually.of_forall (fun w ↦ abs_nonneg _)
  have hGF : GermRepresents (fun i ↦ F i ∘ c.g) (monomialFam c.bexp) p :=
    c.hideal_fwd.germRepresents_of_isOpen c.hnbhd_open hp
  have hFG : GermRepresents (monomialFam c.bexp) (fun i ↦ F i ∘ c.g) p :=
    c.hideal_bwd.germRepresents_of_isOpen c.hnbhd_open hp
  have hFnull : LocallyNullZeros (sumSqFam (monomialFam c.bexp)) p :=
    locallyNullZeros_sumSqFam_monomialFam c.bexp c.k₀ p
  have hGnull : LocallyNullZeros (sumSqFam (fun i ↦ F i ∘ c.g)) p := by
    obtain ⟨a, _hacont, harep⟩ := c.hideal_bwd
    refine ⟨c.nbhd, hnbhd_mem, measure_mono_null ?_ (volume_monomialFam_zeroSet c.bexp c.k₀)⟩
    intro u hu
    have hu0 : u ∈ {w | sumSqFam (fun i ↦ F i ∘ c.g) w = 0} := hu.1
    have hall : ∀ i, (F i ∘ c.g) u = 0 :=
      fun i ↦ sumSqFam_zeroSet_subset (fun i ↦ F i ∘ c.g) i hu0
    show monomialFam c.bexp c.k₀ u = 0
    rw [harep u hu.2 c.k₀]
    refine Finset.sum_eq_zero (fun i _ ↦ ?_)
    show a c.k₀ i u * (F i ∘ c.g) u = 0
    rw [hall i, mul_zero]
  exact wLocalAdmissibleExponents_sumSqFam_eq_of_germ_eq hWmeas hMmeas hGmeas hWnn hGnull hFnull
    hGF hFG

/-- **Per-chart set form.** The chart's weighted admissible set at the origin is exactly `[0, T)`,
`T` its boxed threshold: Object-A-at-`0` swaps the loss for its monomial normal form, and the origin
S2 rule (`monomialSumSq_wLocalAdmissible_eq`) reads off the `Ico`. -/
theorem Chart.wLocalAdmissibleExponents_eq_Ico {F : Fin M → (Fin D → ℝ) → ℝ} {x₀ : Fin D → ℝ}
    (c : Chart F x₀) :
    wLocalAdmissibleExponents c.jacWeightFn (sumSqFam (fun i ↦ F i ∘ c.g)) 0
      = Set.Ico 0 (monomialThreshold (c.bexp c.k₀) c.jac c.hbind) := by
  have h0 : (0 : Fin D → ℝ) ∈ c.nbhd := c.hdom_sub c.hdom_zero
  obtain ⟨unit, hunit_cont, hunit0, hunitmeas, hW⟩ := c.jacWeight_form_at h0
  rw [c.wLocalAdmissible_swap h0]
  exact monomialSumSq_wLocalAdmissible_eq c.hchain c.hbind hunit_cont hunit0 hunitmeas hW

/-- The chart's weighted RLCT is its boxed threshold `T` (`sSup [0,T) = T`, `T > 0`). -/
theorem Chart.wrlctAt_eq_threshold {F : Fin M → (Fin D → ℝ) → ℝ} {x₀ : Fin D → ℝ}
    (c : Chart F x₀) :
    wrlctAt c.jacWeightFn (sumSqFam (fun i ↦ F i ∘ c.g)) 0
      = monomialThreshold (c.bexp c.k₀) c.jac c.hbind := by
  unfold wrlctAt
  rw [c.wLocalAdmissibleExponents_eq_Ico, csSup_Ico (monomialThreshold_pos _ _ _)]

/-- **Per-point convergence (the `≥`-leg input).** At any `p ∈ nbhd`, an exponent below the chart's
boxed threshold `T` is weighted-admissible for the pulled-back loss: Object-A-at-`p` reduces to the
monomial normal form, and the off-origin convergence engine
(`monomialSumSq_integrableAtFilter_of_lt`) handles the base point `p` (worst singularity at `0`, so
`c < T` suffices everywhere). -/
theorem Chart.integrableAtFilter_of_lt {F : Fin M → (Fin D → ℝ) → ℝ} {x₀ : Fin D → ℝ}
    (c : Chart F x₀) {p : Fin D → ℝ} (hp : p ∈ c.nbhd) {cc : ℝ}
    (hlt : cc < monomialThreshold (c.bexp c.k₀) c.jac c.hbind) (hc0 : 0 ≤ cc) :
    IntegrableAtFilter (fun u ↦ c.jacWeightFn u * negPow (sumSqFam (fun i ↦ F i ∘ c.g)) cc u)
      (𝓝 p) := by
  obtain ⟨unit, hunit_cont, hunit0, hunitmeas, hW⟩ := c.jacWeight_form_at hp
  have hβ := (monomial_forall_neg_one_lt_iff_lt_threshold c.bexp c.jac c.k₀ c.hbind cc).mpr hlt
  have hP2 : IntegrableAtFilter
      (fun u ↦ c.jacWeightFn u * negPow (sumSqFam (monomialFam c.bexp)) cc u) (𝓝 p) :=
    monomialSumSq_integrableAtFilter_of_lt c.hchain hβ hunit_cont hunit0 hunitmeas hW
  have hmem : cc ∈ wLocalAdmissibleExponents c.jacWeightFn (sumSqFam (monomialFam c.bexp)) p :=
    ⟨hc0, hP2⟩
  have hmem' : cc ∈ wLocalAdmissibleExponents c.jacWeightFn (sumSqFam (fun i ↦ F i ∘ c.g)) p := by
    rw [c.wLocalAdmissible_swap hp]; exact hmem
  exact hmem'.2

/-- **The per-chart `≤` leg (single-chart change-of-variables).** Every exponent locally admissible
for the loss at `x₀` is weighted-admissible for the pulled-back loss at the chart origin: a small
source ball `s ⊆ g⁻¹ s₀ ∩ nbhd` has `g '' s ⊆ s₀`, and the InjOn-off-null area formula
(`AreaFormula`) turns `∫_s |det Dg|·(K∘g)^(-c)` into `∫_{g '' s} K^(-c) ≤ ∫_{s₀} K^(-c) < ∞`. -/
theorem Chart.mem_wLocalAdmissible_of_localAdmissible {F : Fin M → (Fin D → ℝ) → ℝ}
    {x₀ : Fin D → ℝ} (c : Chart F x₀) {cc : ℝ}
    (hmem : cc ∈ localAdmissibleExponents (sumSqFam F) x₀) :
    cc ∈ wLocalAdmissibleExponents c.jacWeightFn (sumSqFam (fun i ↦ F i ∘ c.g)) 0 := by
  obtain ⟨hc0, s₀, hs₀mem, hs₀int⟩ := hmem
  refine ⟨hc0, ?_⟩
  have hnbhd0 : c.nbhd ∈ 𝓝 (0 : Fin D → ℝ) := c.hnbhd_open.mem_nhds (c.hdom_sub c.hdom_zero)
  have hg0mem : c.g ⁻¹' s₀ ∈ 𝓝 (0 : Fin D → ℝ) :=
    (c.hg_cont.continuousAt).preimage_mem_nhds (show s₀ ∈ 𝓝 (c.g 0) by rw [c.hg0]; exact hs₀mem)
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.1 (Filter.inter_mem hg0mem hnbhd0)
  set s := Metric.ball (0 : Fin D → ℝ) ε with hsdef
  have hsmeas : MeasurableSet s := measurableSet_ball
  have hgs_sub : c.g '' s ⊆ s₀ := by
    rintro y ⟨u, hu, rfl⟩; exact (hεsub hu).1
  have hs_nbhd : s ⊆ c.nbhd := fun u hu ↦ (hεsub hu).2
  have hgdiff : Differentiable ℝ c.g := differentiableOn_univ.mp c.hg_analytic.differentiableOn
  have hg_inj_s : Set.InjOn c.g (s \ c.excep) :=
    c.hg_inj.mono (Set.diff_subset_diff_left hs_nbhd)
  have hInt_meas :
      Measurable (fun u ↦ c.jacWeightFn u * negPow (sumSqFam (fun i ↦ F i ∘ c.g)) cc u) := by
    have h2 : Measurable (sumSqFam (fun i ↦ F i ∘ c.g)) := by
      unfold sumSqFam
      exact Finset.measurable_sum _ (fun i _ ↦ ((c.hFmeas i).comp c.hg_cont.measurable).pow_const 2)
    exact c.continuous_jacWeightFn.measurable.mul (measurable_negPow h2 cc)
  have hInt_nonneg :
      ∀ u, 0 ≤ c.jacWeightFn u * negPow (sumSqFam (fun i ↦ F i ∘ c.g)) cc u :=
    fun u ↦ mul_nonneg (abs_nonneg _) (negPow_nonneg (sumSqFam_nonneg _ _) cc)
  -- convert the source integrand to the image integrand via the area formula.
  have hpt : ∀ u, ENNReal.ofReal (c.jacWeightFn u * negPow (sumSqFam (fun i ↦ F i ∘ c.g)) cc u)
      = ENNReal.ofReal |(fderiv ℝ c.g u).det|
        * ENNReal.ofReal (negPow (sumSqFam F) cc (c.g u)) := by
    intro u
    rw [show c.jacWeightFn u = |(fderiv ℝ c.g u).det| from rfl,
      show negPow (sumSqFam (fun i ↦ F i ∘ c.g)) cc u = negPow (sumSqFam F) cc (c.g u) from by
        simp only [negPow_apply, sumSqFam, Function.comp_apply],
      ENNReal.ofReal_mul (abs_nonneg _)]
  have key : (∫⁻ u in s, ENNReal.ofReal
        (c.jacWeightFn u * negPow (sumSqFam (fun i ↦ F i ∘ c.g)) cc u))
      = ∫⁻ x in c.g '' s, ENNReal.ofReal (negPow (sumSqFam F) cc x) := by
    simp_rw [hpt]
    rw [← lintegral_image_eq_lintegral_abs_det_fderiv_mul_of_injOn_off_null volume hsmeas hgdiff
        c.hexcep_meas c.hexcep_null hg_inj_s (fun x ↦ ENNReal.ofReal (negPow (sumSqFam F) cc x))]
  have hfin : (∫⁻ u in s, ENNReal.ofReal
        (c.jacWeightFn u * negPow (sumSqFam (fun i ↦ F i ∘ c.g)) cc u)) < ⊤ := by
    rw [key]
    calc ∫⁻ x in c.g '' s, ENNReal.ofReal (negPow (sumSqFam F) cc x)
        ≤ ∫⁻ x in s₀, ENNReal.ofReal (negPow (sumSqFam F) cc x) := lintegral_mono_set hgs_sub
      _ < ⊤ := hs₀int.setLIntegral_lt_top
  exact ⟨s, Metric.ball_mem_nhds 0 hε, hInt_meas.aestronglyMeasurable,
    (hasFiniteIntegral_iff_ofReal (ae_of_all _ hInt_nonneg)).mpr hfin⟩

/-! ## The atlas change-of-variables (min over charts) — the landed leaf -/

/-- **The atlas `≥` leg.** If `cc` is below every chart's boxed threshold, it is locally admissible
for the loss at `x₀`. Each chart's compact domain is integrable (per-point local integrability from
`Chart.integrableAtFilter_of_lt` + `LocallyIntegrableOn.integrableOn_isCompact`); the InjOn-off-null
area formula pushes each `∫_{dom_c} |det Dg_c|·(K∘g_c)^(-c)` down to `∫_{g_c '' dom_c} K^(-c)`; and
the a.e.-cover `hcover` (subadditivity over the finite atlas union, no injectivity across charts)
transfers integrability onto a neighbourhood `U` of `x₀`. -/
theorem Resolution.mem_localAdmissible_of_lt {F : Fin M → (Fin D → ℝ) → ℝ} {x₀ : Fin D → ℝ}
    (res : Resolution F x₀) {cc : ℝ} (hc0 : 0 ≤ cc)
    (hlt : ∀ c, cc < monomialThreshold ((res.charts c).bexp (res.charts c).k₀)
      (res.charts c).jac (res.charts c).hbind) :
    cc ∈ localAdmissibleExponents (sumSqFam F) x₀ := by
  refine ⟨hc0, ?_⟩
  -- each chart's image is integrable, via the area formula from the compact-domain integrability.
  have step1 : ∀ c, IntegrableOn (negPow (sumSqFam F) cc)
      ((res.charts c).g '' (res.charts c).dom) := by
    intro c
    set cc' := res.charts c with hcc'
    have hgdiff : Differentiable ℝ cc'.g := differentiableOn_univ.mp cc'.hg_analytic.differentiableOn
    have hdommeas : MeasurableSet cc'.dom := cc'.hdom_compact.measurableSet
    have hg_inj_dom : Set.InjOn cc'.g (cc'.dom \ cc'.excep) :=
      cc'.hg_inj.mono (Set.diff_subset_diff_left cc'.hdom_sub)
    -- compact-domain integrability of the pulled-back weighted loss.
    have hdom_int : IntegrableOn
        (fun u ↦ cc'.jacWeightFn u * negPow (sumSqFam (fun i ↦ F i ∘ cc'.g)) cc u) cc'.dom := by
      apply LocallyIntegrableOn.integrableOn_isCompact ?_ cc'.hdom_compact
      intro p hp
      exact IntegrableAtFilter.filter_mono nhdsWithin_le_nhds
        (cc'.integrableAtFilter_of_lt (cc'.hdom_sub hp) (hlt c) hc0)
    -- push down through the area formula, get a finite image lintegral.
    have hpt : ∀ u, ENNReal.ofReal |(fderiv ℝ cc'.g u).det|
          * ENNReal.ofReal (negPow (sumSqFam F) cc (cc'.g u))
        = ENNReal.ofReal (cc'.jacWeightFn u * negPow (sumSqFam (fun i ↦ F i ∘ cc'.g)) cc u) := by
      intro u
      rw [show cc'.jacWeightFn u = |(fderiv ℝ cc'.g u).det| from rfl,
        show negPow (sumSqFam (fun i ↦ F i ∘ cc'.g)) cc u = negPow (sumSqFam F) cc (cc'.g u) from by
          simp only [negPow_apply, sumSqFam, Function.comp_apply],
        ENNReal.ofReal_mul (abs_nonneg _)]
    have hfin : ∫⁻ x in cc'.g '' cc'.dom, ENNReal.ofReal (negPow (sumSqFam F) cc x) < ⊤ := by
      rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul_of_injOn_off_null volume hdommeas hgdiff
        cc'.hexcep_meas cc'.hexcep_null hg_inj_dom
        (fun x ↦ ENNReal.ofReal (negPow (sumSqFam F) cc x))]
      simp_rw [hpt]
      exact hdom_int.setLIntegral_lt_top
    have hKmeas : Measurable (sumSqFam F) := by
      unfold sumSqFam
      exact Finset.measurable_sum _ (fun i _ ↦ (cc'.hFmeas i).pow_const 2)
    have hnn : ∀ x, 0 ≤ negPow (sumSqFam F) cc x :=
      fun x ↦ negPow_nonneg (sumSqFam_nonneg _ _) cc
    exact ⟨(measurable_negPow hKmeas cc).aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal (ae_of_all _ hnn)).mpr hfin⟩
  -- assemble over the finite atlas union and transfer onto `U` via `hcover`.
  set uc : Set (Fin D → ℝ) := ⋃ c, (res.charts c).g '' (res.charts c).dom with hucdef
  have hunion : IntegrableOn (negPow (sumSqFam F) cc) uc :=
    integrableOn_finite_iUnion.mpr step1
  set Uc : Set (Fin D → ℝ) := res.U ∩ uc with hUcdef
  have hUeq : res.U =ᵐ[volume] Uc := by
    rw [ae_eq_set]
    refine ⟨measure_mono_null ?_ res.hcover, measure_mono_null ?_ (measure_empty (μ := volume))⟩
    · intro x hx
      refine ⟨hx.1, fun hxuc ↦ hx.2 ?_⟩
      rw [hUcdef]; exact Set.mem_inter hx.1 hxuc
    · intro x hx
      have hxUc : x ∈ Uc := hx.1
      rw [hUcdef] at hxUc
      exact absurd hxUc.1 hx.2
  have hUcint : IntegrableOn (negPow (sumSqFam F) cc) Uc := by
    rw [hUcdef]; exact hunion.mono_set Set.inter_subset_right
  exact ⟨res.U, res.hU, hUcint.congr_set_ae hUeq⟩

/-- **The atlas change-of-variables (min over charts) — LANDED.** For the certified atlas,
`rlctAt (∑Fᵢ²) x₀ = min_c wrlctAt |det Dg_c| (∑(Fᵢ∘g_c)²) 0`. The local admissible set at `x₀` equals
`[0, R)` with `R = min_c T_c` the atlas minimum of the per-chart boxed thresholds: the `≤` leg
(`Chart.mem_wLocalAdmissible_of_localAdmissible`) shows admissibility at `x₀` forces `cc < T_c` in
every chart; the `≥` leg (`Resolution.mem_localAdmissible_of_lt`) shows `cc < R` is admissible. Then
`rlctAt = sSup [0, R) = R` and each `wrlctAt_c = T_c`, so the `inf'` is `R` (worked.tex:178, the
`min over charts`). -/
theorem rlctAt_sumSqFam_eq_iInf_charts {F : Fin M → (Fin D → ℝ) → ℝ} {x₀ : Fin D → ℝ}
    (res : Resolution F x₀) :
    rlctAt (sumSqFam F) x₀
      = Finset.univ.inf' res.hne
          (fun c ↦ wrlctAt (res.charts c).jacWeightFn
            (sumSqFam (fun i ↦ F i ∘ (res.charts c).g)) 0) := by
  have hval : ∀ c, wrlctAt (res.charts c).jacWeightFn
        (sumSqFam (fun i ↦ F i ∘ (res.charts c).g)) 0
      = monomialThreshold ((res.charts c).bexp (res.charts c).k₀)
          (res.charts c).jac (res.charts c).hbind :=
    fun c ↦ (res.charts c).wrlctAt_eq_threshold
  rw [Finset.inf'_congr res.hne rfl (fun c _ ↦ hval c)]
  set R := Finset.univ.inf' res.hne
    (fun c ↦ monomialThreshold ((res.charts c).bexp (res.charts c).k₀)
      (res.charts c).jac (res.charts c).hbind) with hRdef
  have hRpos : 0 < R := by
    rw [hRdef, Finset.lt_inf'_iff]; exact fun c _ ↦ monomialThreshold_pos _ _ _
  have hset : localAdmissibleExponents (sumSqFam F) x₀ = Set.Ico 0 R := by
    ext cc
    constructor
    · intro hmem
      rw [Set.mem_Ico]
      refine ⟨hmem.1, ?_⟩
      rw [hRdef, Finset.lt_inf'_iff]
      intro c _
      have hmemc := (res.charts c).mem_wLocalAdmissible_of_localAdmissible hmem
      rw [(res.charts c).wLocalAdmissibleExponents_eq_Ico, Set.mem_Ico] at hmemc
      exact hmemc.2
    · intro hmem
      rw [Set.mem_Ico] at hmem
      refine res.mem_localAdmissible_of_lt hmem.1 (fun c ↦ ?_)
      rw [hRdef, Finset.lt_inf'_iff] at hmem
      exact hmem.2 c (Finset.mem_univ c)
  rw [rlctAt_def, hset, csSup_Ico hRpos]

/-- **STRIKE-ABLE — one chart gives an upper bound.** For any single chart, `rlctAt (∑Fᵢ²) x₀ ≤
wrlctAt |det Dg_c| (∑(Fᵢ∘g_c)²) 0`: the always-valid direction of the min-over-charts equality
(`Finset.inf'_le`). -/
theorem rlctAt_sumSqFam_le_chart {F : Fin M → (Fin D → ℝ) → ℝ} {x₀ : Fin D → ℝ}
    (res : Resolution F x₀) (c : Fin res.numCharts) :
    rlctAt (sumSqFam F) x₀
      ≤ wrlctAt (res.charts c).jacWeightFn (sumSqFam (fun i ↦ F i ∘ (res.charts c).g)) 0 := by
  rw [rlctAt_sumSqFam_eq_iInf_charts res]
  exact Finset.inf'_le _ (Finset.mem_univ c)

/-- **Object B — the resolution value `2·rlctAt (∑Fᵢ²) x₀ = divisorMin` (min over charts).** Wired:
the min-over-charts CoV (`rlctAt_sumSqFam_eq_iInf_charts`) followed by the per-chart
integer value (`Chart.two_mul_wrlctAt_eq_chartMin`, weighted-A ∘ C). The `transfer` is thus
**derived**, never assumed; and the min over charts — the half of defect 1 that killed the
single-chart draft — is on the page. -/
theorem Resolution.two_mul_rlctAt_eq_divisorMin {F : Fin M → (Fin D → ℝ) → ℝ} {x₀ : Fin D → ℝ}
    (res : Resolution F x₀) :
    2 * rlctAt (sumSqFam F) x₀ = res.divisorMin := by
  -- map: B-value (min-over-charts CoV ∘ per-chart value); 2·min = min of 2·(each)
  rw [rlctAt_sumSqFam_eq_iInf_charts res, Resolution.divisorMin]
  -- `2·min` distributes over the atlas `inf'` (`2 ≥ 0` monotone), then each chart's per-chart value.
  have hg : ∀ x y : ℝ, 2 * (x ⊓ y) = 2 * x ⊓ 2 * y := by
    intro x y
    rcases le_total x y with hxy | hxy
    · rw [inf_of_le_left hxy, inf_of_le_left (by linarith : 2 * x ≤ 2 * y)]
    · rw [inf_of_le_right hxy, inf_of_le_right (by linarith : 2 * y ≤ 2 * x)]
  rw [Finset.comp_inf'_eq_inf'_comp res.hne (fun x : ℝ ↦ 2 * x) hg]
  refine Finset.inf'_congr res.hne rfl (fun c _ ↦ ?_)
  simp only [Function.comp_apply]
  exact (res.charts c).two_mul_wrlctAt_eq_chartMin

/-! ## The negative-example guard (v2 defect 1), a provable arithmetic obstruction

The coupled chart `g(u) = (u₀u₁², u₀²u₁)` has `|det Dg| = 3|u₀|²|u₁|² = 3·jacWeight ![2,2]`. No
Jacobian certificate can declare its exponent `jac = ![1,1]`: that would need a unit `w` with
`3·jacWeight ![2,2] u = jacWeight ![1,1] u · w u` near `0`, forcing `w u = 3|u₀||u₁| → 0` and
contradicting `w 0 ≠ 0`. So the `Chart` record cannot be inhabited with the false v2 data. -/

/-- **Negative-example obstruction (defect 1) — FRONTIER leaf (statement TRUE, proof deferred).** No
continuous, `0`-nonvanishing unit `w` satisfies `3·jacWeight ![2,2] = jacWeight ![1,1] · w`
**eventually near `0`** (the quantifier matching the certificate field `hjac`'s `∀ᶠ u in 𝓝 0`). On
the punctured neighbourhood the identity forces `w u = 3|u₀||u₁|`, whose limit at `0` is `0`,
contradicting `w 0 ≠ 0` by continuity. So a `Chart` for the coupled chart `(u₀u₁², u₀²u₁)` cannot
carry the false axis exponent `jac = ![1,1]` — the certificate pins the honest `![2,2]`. The
statement is TRUE (a `tendsto`/continuity argument); landed sorry-free (mon-cov; docstring refreshed post-landing) here (guard, not on the
value path). LANDED sorry-free (aoyagi-engine, SEAT-B). -/
theorem no_unit_forces_axis_jac_coupled :
    ¬ ∃ w : (Fin 2 → ℝ) → ℝ, ContinuousAt w 0 ∧ w 0 ≠ 0 ∧
      (∀ᶠ u in 𝓝 (0 : Fin 2 → ℝ),
        3 * jacWeight (D := 2) ![2, 2] u = jacWeight ![1, 1] u * w u) := by
  -- map: B-negative-guard (the Jacobian certificate forbids v2's false axis exponent; tendsto arg)
  rintro ⟨w, hwc, hw0, hev⟩
  -- The diagonal curve `γ t = (t, t)` sends `0 ↦ 0`, continuously.
  set γ : ℝ → (Fin 2 → ℝ) := fun t ↦ fun _ ↦ t with hγ
  have hγ0 : γ 0 = 0 := by funext i; simp [hγ]
  have hγc : Continuous γ := by
    rw [hγ]; exact continuous_pi (fun _ ↦ continuous_id)
  have hγtend : Filter.Tendsto γ (𝓝 (0 : ℝ)) (𝓝 (0 : Fin 2 → ℝ)) :=
    hγc.tendsto' 0 0 hγ0
  -- Pull the eventual identity back along the curve.
  have hevγ : ∀ᶠ t in 𝓝 (0 : ℝ),
      3 * jacWeight (D := 2) ![2, 2] (γ t) = jacWeight ![1, 1] (γ t) * w (γ t) :=
    hγtend.eventually hev
  -- On the punctured neighbourhood, `t ≠ 0`, so the identity solves to `w (γ t) = 3 t²`.
  have hkey : (fun t ↦ w (γ t)) =ᶠ[𝓝[≠] (0 : ℝ)] fun t ↦ 3 * t ^ 2 := by
    have hne : ∀ᶠ t in 𝓝[≠] (0 : ℝ), t ≠ 0 := self_mem_nhdsWithin
    filter_upwards [hevγ.filter_mono nhdsWithin_le_nhds, hne] with t hid ht
    -- evaluate the two monomials on the curve
    have h22 : jacWeight (D := 2) ![2, 2] (γ t) = t ^ 2 * t ^ 2 := by
      simp [jacWeight, Fin.prod_univ_two, hγ, sq_abs]
    have h11 : jacWeight (D := 2) ![1, 1] (γ t) = t * t := by
      simp [jacWeight, Fin.prod_univ_two, hγ, pow_one, abs_mul_abs_self]
    rw [h22, h11] at hid
    have htt : t * t ≠ 0 := mul_ne_zero ht ht
    -- `3·t²·t² = (t·t)·w`, cancel the nonzero `t·t`
    have hstep : t * t * w (γ t) = t * t * (3 * t ^ 2) := by linear_combination -hid
    exact mul_left_cancel₀ htt hstep
  -- limit uniqueness: `w ∘ γ → w 0` (continuity) and `w ∘ γ → 0` (the `3t²` germ) on `𝓝[≠] 0`.
  have hlim1 : Filter.Tendsto (fun t ↦ w (γ t)) (𝓝[≠] (0 : ℝ)) (𝓝 (w 0)) :=
    hwc.tendsto.comp (hγtend.mono_left nhdsWithin_le_nhds)
  have hlim2 : Filter.Tendsto (fun t ↦ w (γ t)) (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
    have hpoly : Filter.Tendsto (fun t : ℝ ↦ 3 * t ^ 2) (𝓝[≠] 0) (𝓝 0) := by
      have h : Filter.Tendsto (fun t : ℝ ↦ 3 * t ^ 2) (𝓝 0) (𝓝 0) := by
        simpa using (continuous_const.mul (continuous_pow 2)).tendsto (0 : ℝ)
      exact h.mono_left nhdsWithin_le_nhds
    exact hpoly.congr' hkey.symm
  exact hw0 (tendsto_nhds_unique hlim1 hlim2)

end DLNFibre.Core.Aoyagi
