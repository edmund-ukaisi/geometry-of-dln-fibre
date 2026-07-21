import DLNFibre.Core.Aoyagi.ProductResolution
import Meta.Cordon

/-!
# `Core.Aoyagi.Order` — Object E: the order `ρ` (a NAMED, DEFERRED node)

**BLUEPRINT (v3), deprioritised.** The order `ρ = θ_{w*}(K)` — the multiplicity of the largest pole
of the loss's zeta function (Def 1, worked.tex:140; the RLCT *multiplicity*, NOT the geometric
component count `Core.numTop`). Aoyagi's closed form is `ρ = a(ℓ−a)+1` (Lemmas 4–5,
worked.tex:727–750); the boxed-rule form is `ρ = max_u #{j : (h_j+1)/(2k_j) = rlct}` (p.182).

## What this module provides, and the seam it names honestly

* `boxedOrder res` — the **combinatorial** boxed-rule count for a resolution: the number of binding
  divisors whose ratio attains the RLCT (under unit multiplicity `k_d = 1`, the number of binding
  axes `d` with `jac d + 1` minimal). This is a definable, strike-able combinatorial object.

* `one_le_boxedOrder` — `boxedOrder` is a genuine count (`≥ 1`; the min is attained), PROVED.

* The two **frontier seams**, named — not faked (v2 defect 6):
  1. The **closed-form count** `boxedOrder = a(ℓ−a)+1` (the two partial-sum envelopes + the Lemma-5
     union count, worked.tex:733–750) — combinatorial but genuine; DEFERRED (not stated as a leaf
     here, since a truthful statement needs the `(ℓ,a)`-balancing relation to `res` from Lemma 3,
     worked.tex:670–693, which this deprioritised node does not yet set up).
  2. **The analytic identification** `boxedOrder res = (multiplicity of the largest pole of the zeta
     function `RLCT.Zeta.zeta`)` — **DEFERRED and NOT stated as a theorem here**, because a pole
     multiplicity requires meromorphic continuation Mathlib lacks (`RLCT.Zeta` bundles only the
     *location* of the largest pole, `= −rlct`, as its cite; there is no pole-*order* operation to
     equate against). Faking it with the counting identity `boxedOrder` is exactly the v2-defect-6
     error; the honest move is to leave the analytic order un-built and flag it. When the
     order-tracking form of the monomial rule (S2 with multiplicities) is built, this seam closes.

`aoyagiPoleOrder ℓ a = a(ℓ−a)+1` (the closed-form count) and the count-vs-order *distinction*
(`numTop ≠ aoyagiPoleOrder`) already live in `DLN.Aoyagi.ThetaOrderDistinction`; this module is the
resolution-side combinatorial `boxedOrder` and the named analytic seam. `Core` never imports `DLN`.
-/

open MeasureTheory Filter Topology RLCT
open Meta.Cordon

namespace DLNFibre.Core.Aoyagi

variable {M D : ℕ}

/-- **The combinatorial boxed-rule order** of a resolution **chart**: the number of binding divisors
whose integer exponent `jac d + 1` attains the chart's LOCAL divisor minimum (worked.tex:182, under
unit multiplicity `k_d = 1`). The whole-resolution order is `atlasOrder res (global minAdm)` — the
MAX over charts of the count at the GLOBAL minimum (P6.2 ratified shape; NOT the sum, NOT the
chart-local min — a non-binding chart's local tie-count would pollute it). `boxedOrder` is the
chart-LOCAL instance `chartOrderAt c c.chartMinN` (see `boxedOrder_eq_chartOrderAt`); the analytic
pole multiplicity it is *meant* to feed is the deferred seam (see the module docstring). -/
noncomputable def boxedOrder {F : Fin M → (Fin D → ℝ) → ℝ} {x₀ : Fin D → ℝ}
    (c : Chart F x₀) : ℕ :=
  ((bindingAxes (c.bexp c.k₀)).filter
      (fun a ↦ c.jac a + 1
        = (bindingAxes (c.bexp c.k₀)).inf' c.hbind (fun b ↦ c.jac b + 1))).card

/-- **`boxedOrder` is a genuine count — at least one binding divisor attains the minimum.** The
divisor minimum `inf'` over the nonempty binding set is attained, so the min-achiever filter is
nonempty and `1 ≤ boxedOrder c`. A provable well-definedness property (the order is never `0` in
the singular regime), fixing the object's non-vacuity. The closed-form value `a(ℓ−a)+1` and the
analytic pole-multiplicity identification are the deferred seams named in the module docstring. -/
@[blueprint]
theorem one_le_boxedOrder {F : Fin M → (Fin D → ℝ) → ℝ} {x₀ : Fin D → ℝ}
    (c : Chart F x₀) :
    1 ≤ boxedOrder c := by
  -- map: E-nonvacuity (the inf' is attained on the nonempty binding set)
  obtain ⟨a, ha, hae⟩ :=
    (bindingAxes (c.bexp c.k₀)).exists_mem_eq_inf' c.hbind (fun b ↦ c.jac b + 1)
  refine Finset.card_pos.mpr ⟨a, ?_⟩
  simp only [Finset.mem_filter]
  exact ⟨ha, hae.symm⟩

/-! ## The atlas-max scaffold (P6.2 Tier-1e): the count against an EXPLICIT global target

The ratified P6.2 object is `atlasOrder res (global minAdm)` — the max over the resolution's charts
of the number of binding divisors attaining the GLOBAL minimum. The explicit `target` argument is
the elder's global-filter pin reified: `boxedOrder` (the chart-LOCAL min-count) is the special case
`chartOrderAt c c.chartMinN`, pointing at this general object. These are value-neutral count API —
no `ρ`/order/multiplicity claim attaches (that rides with the two incidence lemmas + the Tier-3
realization, both deferred). -/

/-- The chart's **local** integer divisor minimum `⨅_{binding} (jac b + 1)` (the `ℕ` value the
landed `boxedOrder` filters against). -/
noncomputable def Chart.chartMinN {F : Fin M → (Fin D → ℝ) → ℝ} {x₀ : Fin D → ℝ}
    (c : Chart F x₀) : ℕ :=
  (bindingAxes (c.bexp c.k₀)).inf' c.hbind (fun b ↦ c.jac b + 1)

/-- **The per-chart count at an EXPLICIT target** `#{binding a : jac a + 1 = target}`. The global
filter's building block: at `target = globalMin` this counts a chart's GLOBAL-minimum-attaining
binding divisors (`0` on a non-binding chart, `chartMinN > target`); at `target = c.chartMinN` it is
`boxedOrder c`. -/
noncomputable def chartOrderAt {F : Fin M → (Fin D → ℝ) → ℝ} {x₀ : Fin D → ℝ}
    (c : Chart F x₀) (target : ℕ) : ℕ :=
  ((bindingAxes (c.bexp c.k₀)).filter (fun a ↦ c.jac a + 1 = target)).card

/-- `boxedOrder` is the chart-LOCAL instance of `chartOrderAt` (target = the chart's minimum). -/
theorem boxedOrder_eq_chartOrderAt {F : Fin M → (Fin D → ℝ) → ℝ} {x₀ : Fin D → ℝ}
    (c : Chart F x₀) : boxedOrder c = chartOrderAt c c.chartMinN := rfl

/-- **The atlas order at an explicit target** — the MAX over the resolution's charts of the
per-chart count at `target`. **VALUE-NEUTRAL API**: this equals Aoyagi's pole multiplicity `ρ` ONLY
at `target = the global minimum minAdm` AND under the (deferred, Tier-3) realization that `res`'s
charts are the built resolution tree's leaves. As stated it is a `Finset.sup` of `ℕ`-valued
target-attainer counts — no `ρ`/order/multiplicity is claimed. Empty atlas ⟹ `0` (`Finset.sup`
bot); `res.hne` gives nonemptiness where it is used. -/
noncomputable def atlasOrder {F : Fin M → (Fin D → ℝ) → ℝ} {x₀ : Fin D → ℝ}
    (res : Resolution F x₀) (target : ℕ) : ℕ :=
  (Finset.univ : Finset (Fin res.numCharts)).sup (fun c ↦ chartOrderAt (res.charts c) target)

/-- Each chart's target-count is `≤ atlasOrder` (the `sup` is an upper bound). -/
theorem chartOrderAt_le_atlasOrder {F : Fin M → (Fin D → ℝ) → ℝ} {x₀ : Fin D → ℝ}
    (res : Resolution F x₀) (target : ℕ) (c : Fin res.numCharts) :
    chartOrderAt (res.charts c) target ≤ atlasOrder res target := by
  unfold atlasOrder
  apply Finset.le_sup (Finset.mem_univ c)

end DLNFibre.Core.Aoyagi
