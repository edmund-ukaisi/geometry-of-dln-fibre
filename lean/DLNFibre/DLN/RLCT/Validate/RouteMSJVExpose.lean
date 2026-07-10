import DLNFibre.DLN.RLCT.Validate.RouteMSJGoodCoords

/-!
# `DLNFibre.DLN.RLCT.Validate.RouteMSJVExpose` — the endpoint with the boundary rows `v` exposed

**Thread `genm-covmount`, Stage 2 (S,J) CoV mountain.** The good-chart cross-coupled loss
`sjGoodChartLoss x Γ Ã₁ A₂` (`RouteMSJGoodCoords`) depends on the front factor `Ã₁` only through the
boundary rows `v = (Ã₁)_p + P⁻¹·B₁₂·(Ã₁)_b` and the corank map `W = (Ã₁)_b`. The `(S,J)` descent's
change-of-variables exposes `v` as a FREE box variable (the pivot rows `(Ã₁)_p ↦ v` translation).
This module builds the RECONSTRUCTION the CoV lands on and closes the resulting joint `(Γ, v)`-box
integral by the banked endpoint `sjGoodMap_loss_matBox_lt_top`.

* **`assembleFront`** — the front factor rebuilt from a free `v` and a fixed corank map `W`: corank
  rows `= W`, pivot rows `= v − P⁻¹·B₁₂·W` (the inverse of the depth reduction, so the reconstructed
  boundary rows are exactly `v`).
* **`sjGoodChartLoss_assembleFront`** — the reconstruction identity:
  `sjGoodChartLoss x Γ (assembleFront x v W) A₂ = frobSq (sjGoodMap P C W A₂ (Γ, v)).1 + …`,
  i.e. the good-chart loss on the reconstructed front factor is EXACTLY the endpoint's
  `sjGoodMap`-loss at `(Γ, v)`.
* **`sjGoodChartLoss_endpoint_lt_top`** — the terminal endpoint in freed coordinates: on the good
  chart (pivot `P` left-invertible, corank map `W` and deep factor `A₂` right-invertible) and below
  the joint threshold `c' < (a·b + t·h)/2`, the joint `(Γ, v)`-box integral of
  `(sjGoodChartLoss x Γ (assembleFront x v W) A₂)^{−c'}` is finite. This is the shape the
  `v`-exposure CoV produces; it closes by the banked endpoint after the reconstruction rewrite.

The `v`-exposure CoV itself (transporting `∫_{A'} ∫_Γ` with `v` DETERMINED by `A'` into
`∫_{env} ∫_{(Γ,v)}` with `v` free, via the pivot-row translation) and the environment integration
remain the un-banked labour. `sjJointResolution` (`RouteMSJResolution`) stays untouched.

Axiom-clean `[propext, Classical.choice, Quot.sound]` (matrix algebra + the banked endpoint).
-/

namespace DLNFibre.DLN.RLCT

open Matrix MeasureTheory
open scoped BigOperators ENNReal

variable {t a b h o : ℕ}

/-- **The front factor reconstructed from a free `v`.** Corank rows `= W`, pivot rows
`= v − P⁻¹·B₁₂·W` (`P = of x.1.1`, `B₁₂ = of x.1.2`) — chosen so the depth-reduction boundary rows
`(pivot) + P⁻¹·B₁₂·(corank)` collapse back to `v`. The inverse of the depth reduction. -/
noncomputable def assembleFront (x : SJOuter t a b) (v : Matrix (Fin t) (Fin h) ℝ)
    (W : Matrix (Fin b) (Fin h) ℝ) : Matrix (Fin t ⊕ Fin b) (Fin h) ℝ :=
  Matrix.of (Sum.elim (v - (Matrix.of x.1.1)⁻¹ * Matrix.of x.1.2 * W) W)

@[simp] theorem assembleFront_inl (x : SJOuter t a b) (v : Matrix (Fin t) (Fin h) ℝ)
    (W : Matrix (Fin b) (Fin h) ℝ) :
    (assembleFront x v W).submatrix Sum.inl id
      = v - (Matrix.of x.1.1)⁻¹ * Matrix.of x.1.2 * W := rfl

@[simp] theorem assembleFront_inr (x : SJOuter t a b) (v : Matrix (Fin t) (Fin h) ℝ)
    (W : Matrix (Fin b) (Fin h) ℝ) :
    (assembleFront x v W).submatrix Sum.inr id = W := rfl

/-- **The reconstruction identity.** The good-chart loss on the reconstructed front factor is
exactly the endpoint's `sjGoodMap`-loss at `(Γ, v)`: the corank rows are `W` and the depth-reduction
boundary rows `(v − P⁻¹·B₁₂·W) + P⁻¹·B₁₂·W = v`. -/
theorem sjGoodChartLoss_assembleFront (x : SJOuter t a b) (Γ : Fin a → Fin b → ℝ)
    (v : Matrix (Fin t) (Fin h) ℝ) (W : Matrix (Fin b) (Fin h) ℝ) (A2 : Matrix (Fin h) (Fin o) ℝ) :
    sjGoodChartLoss x Γ (assembleFront x v W) A2
      = frobSq (sjGoodMap (Matrix.of x.1.1) (Matrix.of x.2) W A2 (Matrix.of Γ, v)).1
        + frobSq (sjGoodMap (Matrix.of x.1.1) (Matrix.of x.2) W A2 (Matrix.of Γ, v)).2 := by
  unfold sjGoodChartLoss
  rw [assembleFront_inl, assembleFront_inr]
  rw [sub_add_cancel]

/-- **The terminal endpoint in freed coordinates (the `v`-exposed joint block finiteness).** On the
good chart — pivot `P = of x.1.1` left-invertible (`LP·P = 1`), corank map `W` right-invertible
(`W·RW = 1`), deep factor `A₂` right-invertible (`A₂·RA = 1`) — and below the joint threshold
`c' < (a·b + t·h)/2`, the joint `(Γ, v)`-box integral of the good-chart loss on the reconstructed
front factor is finite. Rewrite the integrand to the endpoint's `sjGoodMap`-loss
(`sjGoodChartLoss_assembleFront`) and apply the banked `sjGoodMap_loss_matBox_lt_top`. -/
theorem sjGoodChartLoss_endpoint_lt_top [NeZero (a * b + t * h)] (x : SJOuter t a b)
    (LP : Matrix (Fin t) (Fin t) ℝ) (hP : LP * Matrix.of x.1.1 = 1)
    (W : Matrix (Fin b) (Fin h) ℝ) (RW : Matrix (Fin h) (Fin b) ℝ) (hW : W * RW = 1)
    (A2 : Matrix (Fin h) (Fin o) ℝ) (RA : Matrix (Fin o) (Fin h) ℝ) (hA2 : A2 * RA = 1)
    (c' : NNReal) (hc' : (c' : ℝ) < (a * b + t * h : ℝ) / 2) :
    ∫⁻ y in matBox a b 1 ×ˢ matBox t h 1,
        ENNReal.ofReal ((sjGoodChartLoss x y.1 (assembleFront x y.2 W) A2) ^ (-(c' : ℝ))) < ⊤ := by
  have hrw : ∀ y : (Fin a → Fin b → ℝ) × (Fin t → Fin h → ℝ),
      sjGoodChartLoss x y.1 (assembleFront x y.2 W) A2
        = frobSq (sjGoodMap (Matrix.of x.1.1) (Matrix.of x.2) W A2 y).1
          + frobSq (sjGoodMap (Matrix.of x.1.1) (Matrix.of x.2) W A2 y).2 := by
    intro y
    rw [sjGoodChartLoss_assembleFront]
    rfl
  simp only [hrw]
  exact sjGoodMap_loss_matBox_lt_top (Matrix.of x.1.1) LP hP (Matrix.of x.2) W RW hW A2 RA hA2
    c' hc'

end DLNFibre.DLN.RLCT
