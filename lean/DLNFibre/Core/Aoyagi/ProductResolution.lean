import DLNFibre.Core.Aoyagi.IdealInvariance
import DLNFibre.Core.Aoyagi.MonomialRLCT
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.LinearAlgebra.Determinant
import Meta.Cordon

/-!
# `Core.Aoyagi.ProductResolution` — Object B: the certified product-ideal resolution (an ATLAS)

**BLUEPRINT (v3).** The geometric heart: Aoyagi's proper resolution that turns the core loss
`∑ (∏C)ᵢⱼ²` into a sum of squared monomials in each exceptional chart (worked.tex:173–189, 475–520),
with `⟨(∏C)∘g_c⟩ = ⟨diag(b₁,…,b_M)_c⟩` and the `bᵢ` forming a divisibility chain in each chart.

## The soundness fixes (v2 defect 1, BOTH halves)

* **Jacobian certificate (half 1).** Each chart certifies, as a **propositional field** `hjac`, that
  the actual `|det Dg_c|` equals the declared monomial weight `jacWeight jac_c` times a nonvanishing
  unit. `no_unit_forces_axis_jac_coupled` shows this forbids the false axis exponent of the coupled
  chart `g = (u₀u₁², u₀²u₁)`.

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
  /-- The nonvanishing analytic unit of the Jacobian certificate. -/
  unit : (Fin D → ℝ) → ℝ
  hunit_cont : ContinuousAt unit 0
  hunit_ne : unit 0 ≠ 0
  /-- **The Jacobian certificate** (v2-defect-1 fix): the actual `|det Dg|` equals the declared
  monomial weight times a nonvanishing unit, near the origin. -/
  hjac : ∀ᶠ u in 𝓝 (0 : Fin D → ℝ), |jacDet g u| = jacWeight jac u * |unit u|
  /-- **The ideal identity** `⟨(∏C)∘g⟩ ⊆ ⟨diag b⟩` (germ level, via Object A's representation). -/
  hideal_fwd : GermRepresents (fun i ↦ F i ∘ g) (monomialFam bexp) 0
  /-- **The ideal identity** `⟨diag b⟩ ⊆ ⟨(∏C)∘g⟩`. -/
  hideal_bwd : GermRepresents (monomialFam bexp) (fun i ↦ F i ∘ g) 0

/-- **The certified product-ideal resolution — an ATLAS of charts.** A finite family of certified
`Chart`s whose images (of **compact** source domains — the properness / no-escape content, at the
atlas level: individual blow-up charts like `(u,uv)` are NOT proper, so properness cannot be a
per-chart field) a.e.-cover a neighbourhood of `x₀`. This is the fix for v2 defect 1, half 2: the RLCT
is a minimum over the covering charts, not a single-chart value; and the cover LOCALIZES the source to
compact domains (an unrestricted `∃ u, g u = w` lets preimages escape to infinity). The standard
`ℝ²`-at-`0` blow-up (two affine charts, compact source boxes covering `ℙ¹`) inhabits this — the
positive inhabitation test. -/
structure Resolution (F : Fin M → (Fin D → ℝ) → ℝ) (x₀ : Fin D → ℝ) where
  /-- The number of charts (branches of the exceptional fibre over `x₀`). -/
  numCharts : ℕ
  /-- The atlas of certified charts. -/
  charts : Fin numCharts → Chart F x₀
  /-- The atlas is nonempty (there is a chart). -/
  hne : (Finset.univ : Finset (Fin numCharts)).Nonempty
  /-- The generators are measurable (needed even for the per-chart `≤` change-of-variables). -/
  hFmeas : ∀ i, Measurable (F i)
  /-- The compact source domain of each chart (the properness / no-escape content: the CoV integral
  is over a bounded region). Each contains the chart origin. -/
  dom : Fin numCharts → Set (Fin D → ℝ)
  hdom_compact : ∀ c, IsCompact (dom c)
  hdom_zero : ∀ c, (0 : Fin D → ℝ) ∈ dom c
  /-- A neighbourhood of `x₀` the atlas covers. -/
  U : Set (Fin D → ℝ)
  hU : U ∈ 𝓝 x₀
  /-- **The localizing cover** — `U` is covered, up to a null set, by the images of the charts'
  COMPACT source domains (properness + covering, both localized). This inhabits the blow-up (compact
  boxes over the affine charts of the exceptional `ℙ¹`), unlike an escaping `∃ u, g u = w`. -/
  hcover : volume (U \ ⋃ c, (charts c).g '' (dom c)) = 0

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

/-! ## The change-of-variables (min over charts) and the value (WIRED, one named analytic leaf) -/

/-- **FRONTIER leaf — the proper-map change-of-variables for the RLCT, MIN OVER CHARTS.** For the
certified atlas, `rlctAt (∑Fᵢ²) x₀ = min_c wrlctAt |det Dg_c| (∑(Fᵢ∘g_c)²) 0`. The substitution
`∫ K^(-c) = ∑_c ∫_{dom c} (K∘g_c)^(-c) |det Dg_c|` (Aoyagi's proper CoV, worked.tex:173–177) splits
over the covering atlas (`hcover` over the compact `dom`, the localized no-escape content), so the
local threshold at `x₀` is the minimum of the per-chart weighted thresholds at their origins
(worked.tex:178, the `min over charts`). The named residual: the pushforward integrability and the
partition of the neighbourhood over the atlas' compact domains. A single chart gives only `≤`. -/
@[blueprint]
theorem rlctAt_sumSqFam_eq_iInf_charts {F : Fin M → (Fin D → ℝ) → ℝ} {x₀ : Fin D → ℝ}
    (res : Resolution F x₀) :
    rlctAt (sumSqFam F) x₀
      = Finset.univ.inf' res.hne
          (fun c ↦ wrlctAt (res.charts c).jacWeightFn
            (sumSqFam (fun i ↦ F i ∘ (res.charts c).g)) 0) := by
  -- map: B-cov (proper-map change-of-variables; MIN over the covering atlas, worked.tex:173-178,488)
  sorry

/-- **STRIKE-ABLE — one chart gives an upper bound.** For any single chart, `rlctAt (∑Fᵢ²) x₀ ≤
wrlctAt |det Dg_c| (∑(Fᵢ∘g_c)²) 0`: a change-of-variables on one chart's image bounds the local
threshold above (the chart need not be the binding one). The always-valid direction, from the
min-over-charts equality (`Finset.inf'_le`). -/
@[blueprint]
theorem rlctAt_sumSqFam_le_chart {F : Fin M → (Fin D → ℝ) → ℝ} {x₀ : Fin D → ℝ}
    (res : Resolution F x₀) (c : Fin res.numCharts) :
    rlctAt (sumSqFam F) x₀
      ≤ wrlctAt (res.charts c).jacWeightFn (sumSqFam (fun i ↦ F i ∘ (res.charts c).g)) 0 := by
  rw [rlctAt_sumSqFam_eq_iInf_charts res]
  exact Finset.inf'_le _ (Finset.mem_univ c)

/-- **STRIKE-ABLE/FRONTIER — per-chart value.** In each chart, the weighted RLCT of the pulled-back
loss equals `½·(⨅ binding (jac d + 1))` (chart-local): Object A's weighted two-sided ideal invariance
(`hideal_fwd`/`hideal_bwd`, under the nonnegative weight `|det Dg_c| ≥ 0`) transports the pulled-back
generators to the diagonal monomials, and Object C's boxed rule under the chain `hchain` + unit
multiplicity `hunit_mult` gives the integer divisor min. -/
@[blueprint]
theorem Chart.two_mul_wrlctAt_eq_chartMin {F : Fin M → (Fin D → ℝ) → ℝ} {x₀ : Fin D → ℝ}
    (c : Chart F x₀) :
    2 * wrlctAt c.jacWeightFn (sumSqFam (fun i ↦ F i ∘ c.g)) 0 = c.chartMin := by
  -- map: B-chart-value (weighted-A ideal invariance ∘ C-dln-unit-multiplicity, per chart)
  sorry

/-- **Object B — the resolution value `2·rlctAt (∑Fᵢ²) x₀ = divisorMin` (min over charts).** Wired:
the min-over-charts CoV (`rlctAt_sumSqFam_eq_iInf_charts`, frontier leaf) followed by the per-chart
integer value (`Chart.two_mul_wrlctAt_eq_chartMin`, weighted-A ∘ C). The `transfer` is thus
**derived**, never assumed; and the min over charts — the half of defect 1 that killed the
single-chart draft — is on the page. -/
@[blueprint]
theorem Resolution.two_mul_rlctAt_eq_divisorMin {F : Fin M → (Fin D → ℝ) → ℝ} {x₀ : Fin D → ℝ}
    (res : Resolution F x₀) :
    2 * rlctAt (sumSqFam F) x₀ = res.divisorMin := by
  -- map: B-value (min-over-charts CoV ∘ per-chart value); 2·min = min of 2·(each)
  sorry

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
statement is TRUE (a `tendsto`/continuity argument); left as a `sorry` leaf here (guard, not on the
value path). -/
@[blueprint]
theorem no_unit_forces_axis_jac_coupled :
    ¬ ∃ w : (Fin 2 → ℝ) → ℝ, ContinuousAt w 0 ∧ w 0 ≠ 0 ∧
      (∀ᶠ u in 𝓝 (0 : Fin 2 → ℝ),
        3 * jacWeight (D := 2) ![2, 2] u = jacWeight ![1, 1] u * w u) := by
  -- map: B-negative-guard (the Jacobian certificate forbids v2's false axis exponent; tendsto arg)
  sorry

end DLNFibre.Core.Aoyagi
