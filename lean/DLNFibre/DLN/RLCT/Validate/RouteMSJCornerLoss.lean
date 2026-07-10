import DLNFibre.DLN.RLCT.Validate.RouteMSJCorankStep
import DLNFibre.DLN.RLCT.Validate.RouteMSJRadialPolar

/-!
# `DLNFibre.DLN.RLCT.Validate.RouteMSJCornerLoss` — the DLN loss ↦ corner-block hypotheses

**Thread `genm-covprod`, Stage 2 (S,J) native resolution, the L2 caller-obligation bridge.** The
corner-block finiteness `RouteMSJRadialPolar.corner_block_cube_lintegral_lt_top` consumes an
ABSTRACT degree-2-homogeneous measurable loss `g` (with the §8 unit lower bound). This module
discharges the `hom` (degree-2-homogeneity) and `hg` (measurability) hypotheses for the **actual DLN
loss shape** `frobSq (rmatMul X A₂)` (the squared Frobenius of a resolved block `X` times the shared
deep factor `A₂`), which is the atom the corner loss `g = gX(Γ) + gY(v) + …` is built from (one term
per resolved block/row, vslice cert §5).

## What lands here

* **`frobSq_rmatMul_smul`** — degree-2-homogeneity:
  `frobSq (rmatMul (r • X) A₂) = r²·frobSq (rmatMul X A₂)`.
* **`measurable_frobSq_rmatMul`** — the loss `X ↦ frobSq (rmatMul X A₂)` is measurable (continuous
  polynomial in the block entries).

These are the per-block `hom`/`hg` discharges; the caller sums them over the joint block (obligation
(a): disjoint blocks, no cross-terms) and flattens to the `Fin n → ℝ` shape `corner_block_cube`
consumes (obligation (b): joint dim = codimension SUM = `minAdm`). S2-FREE; axiom-clean.
-/

namespace DLNFibre.DLN.RLCT

open scoped BigOperators

/-- **The matrix-product loss is degree-2-homogeneous.** Scaling the block `X` by `r` scales the
loss `frobSq (rmatMul X A₂)` by `r²`: `frobSq (rmatMul (r • X) A₂) = r²·frobSq (rmatMul X A₂)`. This
is the `hom` hypothesis of the corner-block finiteness theorems for the DLN loss shape; the corner
loss is a SUM of such terms, each 2-homogeneous. `rmatMul` is linear in `X` (the scalar pulls
through the contraction sum), then `frobSq` is degree-2 (`frobSq_smul_fun`). -/
theorem frobSq_rmatMul_smul {p q m : ℕ} (r : ℝ) (X : Fin p → Fin q → ℝ) (A₂ : Fin q → Fin m → ℝ) :
    frobSq (rmatMul (r • X) A₂) = r ^ 2 * frobSq (rmatMul X A₂) := by
  have h : rmatMul (r • X) A₂ = fun i j => r * rmatMul X A₂ i j := by
    funext i j
    simp only [rmatMul, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun k _ => by ring)
  rw [h, frobSq_smul_fun]

/-- **The matrix-product loss is measurable.** `X ↦ frobSq (rmatMul X A₂)` is a polynomial in the
block entries, hence measurable — the `hg` hypothesis of the corner-block finiteness theorems for
the DLN loss shape. -/
theorem measurable_frobSq_rmatMul {p q m : ℕ} (A₂ : Fin q → Fin m → ℝ) :
    Measurable (fun X : Fin p → Fin q → ℝ => frobSq (rmatMul X A₂)) := by
  unfold frobSq rmatMul
  fun_prop

end DLNFibre.DLN.RLCT
