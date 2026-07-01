import DLNFibre.DLN.RLCT.Validate.RouteMInteriorLiveGenAmbient

/-!
# `RouteMInteriorLiveGenSchurGate` — the shared per-boundary Schur-frame recovery gate (∀L)

The bricks the general-`L` boundary-factor recovery stands on, SHARED between the injectivity side
(`RouteMInteriorLiveGenInjRec`, the `BchartLeafGen`-recovery residual) and — if needed — the determinant
side. The diamond is clean (importers pull this leaf).

* `interiorLiveInjDomGen` — the general-`L` injectivity domain `{u | u leafPivot ≠ 0 ∧ ∀ j, u j ≠ 0}`.
* `detK_ne_zero_gen` — `det (readK y k) ≠ 0` at EVERY interior boundary `k : Fin L`, for `y` in the
  kLDU-image of `pbo '' injDom`. The general-`L` lift of the `L = 2`
  `RouteMInteriorLiveContract.slotReadV0_K_det_ne_zero_of_mem` (boundary-`0`-pinned). Route: the
  LDU-lensed K-core has MONOMIAL det `∏_i (readK (pbo x) k) i i` (`readK_kLDU_det`), each factor
  `= readK x k i i = x (diagAxis) ≠ 0` on the all-nonzero domain (`readK_pbo_all`).

Axiom-clean `[propext, Classical.choice, Quot.sound]` (banked K-monomial + pbo-fixing; no analysis).
-/

open Matrix
open scoped BigOperators

namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-- The general-`L` injectivity domain — `{u | u leafPivot ≠ 0 ∧ ∀ j, u j ≠ 0}` (the L=2 `E = univ`
choice: all coords nonzero, exactly what `kLens_injOn_qneGen` needs). Shared with the injectivity side
(`RouteMInteriorLiveGenInj` / `…Rec`) and the gate below. -/
def interiorLiveInjDomGen (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) (hL : 0 < L)
    (h0r : 0 < Text M (tach M) L) (h0c : 0 < Wext M L) : Set (Fin (routeMAmbient M) → ℝ) :=
  {u | u (leafPivot M ha hL h0r h0c) ≠ 0 ∧ ∀ j, u j ≠ 0}

/-- The general-`L` injectivity domain forces ALL coords nonzero (the `E = univ` choice). -/
theorem interiorLiveInjDomGen_all_nonzero (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M))
    (hL : 0 < L) (h0r : 0 < Text M (tach M) L) (h0c : 0 < Wext M L)
    {x₀ : Fin (routeMAmbient M) → ℝ} (hx₀ : x₀ ∈ interiorLiveInjDomGen M ha hL h0r h0c) :
    ∀ j, x₀ j ≠ 0 := hx₀.2

/-- **`pbo x₀` is all-nonzero** for `x₀` in the injectivity domain — `pivotBlowupOn` scales by the
pivot coord (nonzero) or leaves coords fixed, so every output coord is a product of nonzero coords. -/
theorem pbo_all_nonzero_of_mem (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) (hL : 0 < L)
    (h0r : 0 < Text M (tach M) L) (h0c : 0 < Wext M L)
    {x₀ : Fin (routeMAmbient M) → ℝ} (hx₀ : x₀ ∈ interiorLiveInjDomGen M ha hL h0r h0c) (q) :
    pivotBlowupOn (activeMGen M ha) (leafPivot M ha hL h0r h0c) x₀ q ≠ 0 := by
  have hall : ∀ j, x₀ j ≠ 0 := interiorLiveInjDomGen_all_nonzero M ha hL h0r h0c hx₀
  rw [pivotBlowupOn]
  split
  · exact hall _
  · split
    · exact mul_ne_zero (hall _) (hall _)
    · exact hall _

/-- **The recovered K-block is nonsingular at EVERY boundary** (general-`L`). For `y = kLDU (pbo x₀)`
with `x₀ ∈ injDom` (all coords nonzero), `det (readK y k) = ∏_i (readK (pbo x₀) k) i i`
(`readK_kLDU_det`) where each diagonal K-core entry `= (pbo x₀)(K-diag-slot) ≠ 0`. The general-`L`
lift of `slotReadV0_K_det_ne_zero_of_mem`. -/
theorem detK_ne_zero_gen (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) (hL : 0 < L)
    (h0r : 0 < Text M (tach M) L) (h0c : 0 < Wext M L)
    {y : Fin (routeMAmbient M) → ℝ}
    (hy : y ∈ kLDU M (tach M) ha ''
      (pivotBlowupOn (activeMGen M ha) (leafPivot M ha hL h0r h0c) ''
        interiorLiveInjDomGen M ha hL h0r h0c))
    (k : Fin L) :
    (Matrix.of (readK M (tach M) ha y k)).det ≠ 0 := by
  obtain ⟨z, ⟨x₀, hx₀, rfl⟩, rfl⟩ := hy
  rw [readK_kLDU_det M (tach M) ha _ k, Finset.prod_ne_zero_iff]
  intro i _
  show (matrixSplit (Matrix.of (readK M (tach M) ha
    (pivotBlowupOn (activeMGen M ha) (leafPivot M ha hL h0r h0c) x₀) k))).2.1 i ≠ 0
  show (Matrix.of (readK M (tach M) ha
    (pivotBlowupOn (activeMGen M ha) (leafPivot M ha hL h0r h0c) x₀) k)) i i ≠ 0
  rw [Matrix.of_apply, readK]
  exact pbo_all_nonzero_of_mem M ha hL h0r h0c hx₀ _

end DLNFibre.DLN.RLCT
