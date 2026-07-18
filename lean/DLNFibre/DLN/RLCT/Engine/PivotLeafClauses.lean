import DLNFibre.DLN.RLCT.Engine.EngineDefs
import DLNFibre.DLN.RLCT.Engine.PivotCover

/-!
# `DLNFibre.DLN.RLCT.Engine.PivotLeafClauses` — pre-staged per-leaf `ChartBridge` clauses (rung 3)

The CONSTRUCTION-INDEPENDENT half of the per-leaf `ChartBridge` clauses, proven over the
contract-shaped leaf so `buildTree`'s leaves satisfy them by construction (controller steer, answer
(b) — CoRank2Spike-style, generalised). Covers ONLY:
* the **srcBox clauses** — `MeasurableSet` and bounded-in-flat-cube — for the flat-cube-preimage
  form `srcBox = paramsEquivFlat ⁻¹' cubeBox (flatDim M) R` (the `CoRank2Spike` form) and for the
  `q`-preimage form `srcBox = q ⁻¹' (pivotChartDom i R ×ˢ B)` (`node_pivotCover_of_atom`'s
  childRegion shape);
* the **coordinate clauses** — `Injective` + `Disjoint` — from disjoint index families.

NOT here (rung-3 proper, chart-data-fed): `LeafPullback`, `LeafJacobian`, and the a.e.-`InjOn`
clause (the exceptional-set specifics). `pivotChartDom` measurability is included (feeds `q`-form).
-/

namespace DLNFibre.DLN.RLCT.Engine

open DLNFibre.DLN.RLCT
open MeasureTheory Set

variable {L : ℕ} {M : Fin (L + 1) → ℕ}

/-! ## srcBox clauses -/

/-- `cubeBox N R` is measurable (a finite product of closed intervals). -/
theorem measurableSet_cubeBox (N : ℕ) (R : ℝ) : MeasurableSet (cubeBox N R) :=
  MeasurableSet.univ_pi (fun _ => measurableSet_Icc)

/-- **srcBox measurable** (flat-cube-preimage form): `paramsEquivFlat ⁻¹' cubeBox` is measurable
(`paramsEquivFlat` is a `MeasurableEquiv`). -/
theorem flatCubeSrcBox_measurableSet (R : ℝ) :
    MeasurableSet (⇑(paramsEquivFlat M) ⁻¹' cubeBox (flatDim M) R) :=
  (measurableSet_cubeBox _ _).preimage (paramsEquivFlat M).measurable

/-- **srcBox bounded-in-flat-cube** (flat-cube-preimage form): the `ChartBridge` bounded clause
holds trivially with the same radius. -/
theorem flatCubeSrcBox_bounded {R : ℝ} (hR : 0 < R) :
    ∃ R' : ℝ, 0 < R' ∧ (⇑(paramsEquivFlat M) ⁻¹' cubeBox (flatDim M) R)
      ⊆ ⇑(paramsEquivFlat M) ⁻¹' cubeBox (flatDim M) R' :=
  ⟨R, hR, subset_rfl⟩

/-- `pivotChartDom i R` is measurable (a finite intersection of closed `|·| ≤ c` conditions). -/
theorem measurableSet_pivotChartDom {d : ℕ} (i : Fin d) (R : ℝ) :
    MeasurableSet (pivotChartDom i R) := by
  have h1 : MeasurableSet {u : Fin d → ℝ | |u i| ≤ R} :=
    measurableSet_le (by fun_prop) measurable_const
  have h2 : MeasurableSet {u : Fin d → ℝ | ∀ k, k ≠ i → |u k| ≤ 1} := by
    have : {u : Fin d → ℝ | ∀ k, k ≠ i → |u k| ≤ 1}
        = ⋂ k, ⋂ (_ : k ≠ i), {u : Fin d → ℝ | |u k| ≤ 1} := by
      ext u; simp only [Set.mem_iInter, Set.mem_setOf_eq]
    rw [this]
    exact MeasurableSet.iInter fun k => MeasurableSet.iInter fun _ =>
      measurableSet_le (by fun_prop) measurable_const
  exact h1.inter h2

/-- **srcBox measurable** (`q`-preimage form): for a homeomorphism `q` and measurable `B`, the leaf
box `q ⁻¹' (pivotChartDom i R ×ˢ B)` (the `node_pivotCover_of_atom` childRegion shape) is
measurable. -/
theorem qPreimageSrcBox_measurableSet {d : ℕ} {E : Type*} [TopologicalSpace E] [MeasurableSpace E]
    (q : Params M ≃ₜ (Fin d → ℝ) × E) [MeasurableSpace (Params M)]
    (hq : Measurable q) (i : Fin d) (R : ℝ) {B : Set E} (hB : MeasurableSet B) :
    MeasurableSet (q ⁻¹' (pivotChartDom i R ×ˢ B)) :=
  ((measurableSet_pivotChartDom i R).prod hB).preimage hq

/-! ## coordinate clauses -/

/-- **Coordinate disjointness** from a pointwise-`≠` family: if every divisor coordinate differs
from every Morse coordinate, their ranges are disjoint (the `ChartBridge` disjoint clause). -/
theorem coords_disjoint_of_ne {nd nr : ℕ} (dc : Fin nd → Fin (flatDim M))
    (rc : Fin nr → Fin (flatDim M)) (hne : ∀ k j, dc k ≠ rc j) :
    Disjoint (Set.range dc) (Set.range rc) := by
  rw [Set.disjoint_left]
  rintro x ⟨k, rfl⟩ ⟨j, hj⟩
  exact hne k j hj.symm

/-- **Coordinate clauses bundle** (disjoint offset blocks): injective divisor/Morse coordinate
families with pairwise-distinct ranges give all three `ChartBridge` coordinate clauses at once. The
shape `buildTree` discharges each leaf's coordinate clauses through. -/
theorem coord_clauses {nd nr : ℕ} (dc : Fin nd → Fin (flatDim M)) (rc : Fin nr → Fin (flatDim M))
    (hdc : Function.Injective dc) (hrc : Function.Injective rc) (hne : ∀ k j, dc k ≠ rc j) :
    Function.Injective dc ∧ Function.Injective rc ∧ Disjoint (Set.range dc) (Set.range rc) :=
  ⟨hdc, hrc, coords_disjoint_of_ne dc rc hne⟩

end DLNFibre.DLN.RLCT.Engine
