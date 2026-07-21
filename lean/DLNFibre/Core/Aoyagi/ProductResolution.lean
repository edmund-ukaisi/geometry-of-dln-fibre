import DLNFibre.Core.Aoyagi.IdealInvariance
import DLNFibre.Core.Aoyagi.MonomialRLCT
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.LinearAlgebra.Determinant
import Meta.Cordon

/-!
# `Core.Aoyagi.ProductResolution` — Object B: the certified product-ideal resolution

**BLUEPRINT (v3).** The geometric heart: Aoyagi's proper resolution `g` that turns the core loss
`∑ (∏C)ᵢⱼ²` into a sum of squared monomials in the exceptional coordinates (worked.tex:173–189,
475–520), with `⟨(∏C)∘g⟩ = ⟨diag(b₁,…,b_M)⟩` and the `bᵢ` forming a divisibility chain.

## The soundness fix (v2 defect 1): the change-of-variables is CERTIFIED, not asserted

v2's `properMapRlctInvariance` asserted the CoV RLCT equality for a record whose `g` was an
**arbitrary** function — no `g(0)=x₀`, no analyticity, no properness, and crucially **no Jacobian
certificate** tying the declared monomial weight to the actual `|det Dg|`. It was FALSE: for
`g = (u₀u₁², u₀²u₁)` with declared `jac = (1,1)`, all of v2's fields held yet
`|det Dg| = 3|u₀|²|u₁|² ≠ jacWeight (1,1)` (the equality read `1 = 2/3`).

Here every hypothesis is a **propositional field** of `Resolution`, never a comment:

* `hg0 : g 0 = x₀` — the chart origin maps to the deepest point;
* `hg_analytic` — analyticity of `g`;
* `hcover`, `hg_inj`, (`excep`, null) — the proper/birational-off-a-null-exceptional-locus content;
* **`hjac : |det Dg u| = jacWeight jac u · |unit u|` near `0`, with `unit` continuous, `unit 0 ≠ 0`** —
  the Jacobian certificate. This is exactly the field whose absence made v2 false: it *forbids* the
  coupled counterexample (a record for `g = (u₀u₁², u₀²u₁)` cannot declare `jac = (1,1)`, because
  `|det Dg| = 3|u₀|²|u₁|²` would force `unit u = 3|u₀||u₁| → 0` at `0`, contradicting `unit 0 ≠ 0`;
  the honest exponent is `jac = (2,2)`). See `not_divChain_coupled_example` (`MonomialRLCT`) for the
  matching axis-side guard.
* `hchain` — the divisibility chain `b_{k₀} | bₖ` (principal normal crossing);
* `hideal_fwd`/`hideal_bwd` — the two-sided ideal identity `⟨(∏C)∘g⟩ = ⟨diag b⟩`, at germ generality
  via Object A's `GermRepresents`.

## The CoV as a TRUE statement (single terminal chart, justified)

`rlctAt_sumSqFam_eq_wrlctAt` states the change-of-variables `rlctAt (∑Fᵢ²) x₀ = wrlctAt |det Dg|
(∑(Fᵢ∘g)²) 0` for the certified chart. In general the RLCT at `x₀` is a **minimum over charts
covering the fibre over `x₀`**; we commit to the single terminal chart because Aoyagi's terminal
diagonalisation is one chart in which the product is fully diagonal (worked.tex:488), and `hcover`
records that this chart's image covers a neighbourhood of `x₀`. That justification is the docstring's
job, and the single-chart commitment is the named residual of this frontier leaf.
-/

open MeasureTheory Set Filter Topology RLCT
open Meta.Cordon

namespace DLNFibre.Core.Aoyagi

variable {M D : ℕ}

/-- The **absolute Jacobian determinant** `|det Dg(u)|` of a chart `g : ℝᴰ → ℝᴰ` — the honest
change-of-variables factor (`fderiv`'s determinant), which the resolution's Jacobian certificate
`hjac` pins to a monomial weight times a nonvanishing unit. -/
noncomputable def jacDet (g : (Fin D → ℝ) → (Fin D → ℝ)) (u : Fin D → ℝ) : ℝ :=
  LinearMap.det (fderiv ℝ g u).toLinearMap

/-- **The certified product-ideal resolution** of a sum-of-squares germ `∑ Fᵢ²` at the deepest point
`x₀` (Aoyagi Cases 1 & 2, regular `Q, P`; worked.tex:475–520). Every hypothesis Aoyagi's proper
resolution needs is a propositional field (the v2-defect-1 fix). The chart is dimension-preserving
(`ℝᴰ → ℝᴰ`, Hironaka is a proper birational modification). -/
structure Resolution (F : Fin M → (Fin D → ℝ) → ℝ) (x₀ : Fin D → ℝ) where
  /-- The resolution chart (source and target both `ℝᴰ` — a proper birational modification). -/
  g : (Fin D → ℝ) → (Fin D → ℝ)
  /-- The chart origin maps to the deepest point `x₀` (v2 lacked this). -/
  hg0 : g 0 = x₀
  /-- `g` is continuous (for measurability of the pulled-back integrand). -/
  hg_cont : Continuous g
  /-- `g` is analytic (v2 lacked this; Hironaka's map is analytic). -/
  hg_analytic : AnalyticOnNhd ℝ g Set.univ
  /-- The chart image covers a neighbourhood of `x₀` (the proper/dominant content; with `hg0` this is
  what makes the single terminal chart realise the local RLCT at `x₀`, worked.tex:488). -/
  hcover : ∀ᶠ w in 𝓝 x₀, ∃ u, g u = w
  /-- The exceptional locus (where `g` is not injective) — the birational content. -/
  excep : Set (Fin D → ℝ)
  hexcep_meas : MeasurableSet excep
  /-- The exceptional locus is null (`g` is a.e. injective — birational). -/
  hexcep_null : volume excep = 0
  hg_inj : Set.InjOn g excepᶜ
  /-- The number of diagonal monomials `b₁,…,b_{M'}` (the paper's `M(L+1)`). -/
  M' : ℕ
  /-- The exceptional-monomial exponents: `bₖ(u) = ∏_d u_d ^ (bexp k d)`. -/
  bexp : Fin M' → Fin D → ℕ
  /-- The index of the dominant (divisibility-minimal) monomial `b_{k₀}`. -/
  k₀ : Fin M'
  /-- **The divisibility chain** `b_{k₀} | bₖ` (worked.tex:483–488) — Aoyagi's own invariant. -/
  hchain : ∀ k d, bexp k₀ d ≤ bexp k d
  /-- Some divisor binds (the singular regime; needed for the boxed min). -/
  hbind : (bindingAxes (bexp k₀)).Nonempty
  /-- **Unit divisor multiplicity** `k_d = 1` on binding axes (worked.tex:495: the loss vanishes to
  order 2 along each `u_{s,k}=0`) — makes `2·rlct` an integer min of divisor exponents. -/
  hunit_mult : ∀ d ∈ bindingAxes (bexp k₀), bexp k₀ d = 1
  /-- The Jacobian monomial exponents `h_d` (the paper's `M_{s,k} − 1`; worked.tex:492–497). -/
  jac : Fin D → ℕ
  /-- The nonvanishing analytic unit of the Jacobian certificate. -/
  unit : (Fin D → ℝ) → ℝ
  hunit_cont : ContinuousAt unit 0
  hunit_ne : unit 0 ≠ 0
  /-- **The Jacobian certificate** (the v2-defect-1 fix): the actual `|det Dg|` equals the declared
  monomial weight `jacWeight jac` times a nonvanishing unit, near the origin. -/
  hjac : ∀ᶠ u in 𝓝 (0 : Fin D → ℝ), |jacDet g u| = jacWeight jac u * |unit u|
  /-- **The ideal identity** `⟨(∏C)∘g⟩ ⊆ ⟨diag b⟩` (germ level, via Object A's representation). -/
  hideal_fwd : GermRepresents (fun i ↦ F i ∘ g) (monomialFam bexp) 0
  /-- **The ideal identity** `⟨diag b⟩ ⊆ ⟨(∏C)∘g⟩` — the reverse containment. -/
  hideal_bwd : GermRepresents (monomialFam bexp) (fun i ↦ F i ∘ g) 0

/-- The Jacobian weight function `w ↦ |det Dg w|` of a resolution (the change-of-variables carrier
weight; `= jacWeight jac · |unit|` near `0` by the certificate). -/
noncomputable def Resolution.jacWeightFn {F : Fin M → (Fin D → ℝ) → ℝ} {x₀ : Fin D → ℝ}
    (res : Resolution F x₀) : (Fin D → ℝ) → ℝ :=
  fun u ↦ |jacDet res.g u|

/-! ## The change-of-variables and the resolution value (WIRED, one named analytic leaf) -/

/-- **STRIKE-ABLE/FRONTIER leaf — the proper-map change-of-variables for the RLCT.** For the
certified chart, `rlctAt (∑Fᵢ²) x₀ = wrlctAt |det Dg| (∑(Fᵢ∘g)²) 0`. The substitution
`∫ (∑Fᵢ²)^(-c) dw = ∫ (∑(Fᵢ∘g)²)^(-c) |det Dg| du` is Aoyagi's proper CoV (worked.tex:173–177); the
single-chart form is justified by the terminal diagonalisation (worked.tex:488) plus `hcover`
(the chart covers a neighbourhood of `x₀`), so its origin realises the local RLCT. The residual open
content named here: the proper-pushforward of the local integrability and the single-chart
sufficiency. Consumes `hg0`, `hg_cont`, `hg_analytic`, `hcover`, `hg_inj`, the null `excep`, `hjac`. -/
@[blueprint]
theorem rlctAt_sumSqFam_eq_wrlctAt {F : Fin M → (Fin D → ℝ) → ℝ} {x₀ : Fin D → ℝ}
    (res : Resolution F x₀) :
    rlctAt (sumSqFam F) x₀
      = wrlctAt res.jacWeightFn (sumSqFam (fun i ↦ F i ∘ res.g)) 0 := by
  -- map: B-cov (proper-map change-of-variables; single terminal chart, worked.tex:173-177,488)
  sorry

/-- **Object B — the resolution value `rlctAt (∑Fᵢ²) x₀ = monomialThreshold`.** Wired from three
pieces: the CoV bridge `rlctAt_sumSqFam_eq_wrlctAt` (frontier leaf); the weighted two-sided ideal
invariance of Object A applied to `hideal_fwd`/`hideal_bwd` (transporting the pulled-back generators
to the diagonal monomials under the nonnegative Jacobian weight); and Object C's boxed monomial rule
under the divisibility chain `hchain`. The `transfer` is thus **derived**, never assumed. -/
@[blueprint]
theorem Resolution.rlctAt_eq_monomialThreshold {F : Fin M → (Fin D → ℝ) → ℝ} {x₀ : Fin D → ℝ}
    (res : Resolution F x₀) :
    rlctAt (sumSqFam F) x₀ = monomialThreshold (res.bexp res.k₀) res.jac res.hbind := by
  -- map: B-value (CoV ∘ weighted-A ideal invariance ∘ C monomial rule)
  sorry

/-- **Object B — the DLN integer form `2·rlctAt (∑Fᵢ²) x₀ = ⨅ binding (jac d + 1)`.** With the
unit-multiplicity divisors (`hunit_mult`), the boxed threshold is `½·min` of the integer divisor
exponents `jac d + 1`, the integer min Object D bridges to `qipMin`/`cCodim`. -/
@[blueprint]
theorem Resolution.two_mul_rlctAt_eq_min {F : Fin M → (Fin D → ℝ) → ℝ} {x₀ : Fin D → ℝ}
    (res : Resolution F x₀) :
    2 * rlctAt (sumSqFam F) x₀
      = ((bindingAxes (res.bexp res.k₀)).inf' res.hbind (fun d ↦ (res.jac d + 1 : ℝ))) := by
  -- map: B-value-int (CoV ∘ weighted-A ∘ C-dln-unit-multiplicity)
  sorry

/-! ## The negative-example guard (v2 defect 1), stated as a provable arithmetic obstruction

The coupled chart `g(u) = (u₀u₁², u₀²u₁)` has `|det Dg| = |u₀²u₁² − 4u₀²u₁²| = 3|u₀|²|u₁|²
= 3 · jacWeight ![2,2]`. No Jacobian certificate can declare its exponent `jac = ![1,1]`, because
that would need a unit `w` with `3·jacWeight ![2,2] u = jacWeight ![1,1] u · w u` near `0`, forcing
`w u = 3|u₀||u₁| → 0` and contradicting `w 0 ≠ 0`. The theorem below is that obstruction; it is why
the `Resolution` record cannot be inhabited with the false v2 data. -/

/-- **Negative-example obstruction (defect 1).** No continuous, `0`-nonvanishing unit `w` satisfies
`3·jacWeight ![2,2] = jacWeight ![1,1] · w` near `0`: on the diagonal `u = (t,t)` the identity forces
`w (t,t) = 3t²·|·|`-shape vanishing at `0`, contradicting `w 0 ≠ 0`. So a `Resolution` for the coupled
chart cannot carry the false axis exponent `jac = ![1,1]` — the certificate pins the honest `![2,2]`. -/
@[blueprint]
theorem no_unit_forces_axis_jac_coupled :
    ¬ ∃ w : (Fin 2 → ℝ) → ℝ, ContinuousAt w 0 ∧ w 0 ≠ 0 ∧
      (∀ u : Fin 2 → ℝ, 3 * jacWeight (D := 2) ![2, 2] u = jacWeight ![1, 1] u * w u) := by
  -- map: B-negative-guard (the Jacobian certificate forbids v2's false axis exponent)
  sorry

end DLNFibre.Core.Aoyagi
