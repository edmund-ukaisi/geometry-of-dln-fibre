import DLNFibre.DLN.RLCT.Validate.RouteMSmearedContract

/-!
# `RouteMSmearedPerFamily` — the ∀M (L = 2 first) smeared per-family `ψ_M` / `U` / `subBox` build

Discharges the per-family ingredients behind `routeMCore_box_diverges_smearedContract` (#159), over
OPAQUE widths, starting with **L = 2** (the worked `(2,3,1)`/`(1,2,1)` classes have `L = 2`: `front = A⁰`
a single factor, no prefix product). The L ≥ 3 front-prefix-product (`P = A⁰···A^{L−2}` telescoping) is a
SEPARATE gated sub-tide (controller, 2026-06-28) — surfaced when reached; not built here.

Design (`design.md` thread 59, from `certificate-genM-smeared.md` §2, validated 46/46): a single uniform
reparametrization (front | z-pivot + H̄-angular | S_bot), `ψ_M = paramsEquivFlat ∘ packM ∘ shearM` where
`shearM` is the `coreShear` skew-product (the rational `Λ₀` top-row shift, MP for any widths via the GENERAL
brick `measurePreserving_coreShear_measurable`), `R_M = pivotBlowupOn` (the sole Jacobian `|z|^{minAdm−1}`),
`U_M = ‖P₁H̄‖²` a genuine polynomial (`Λ₀` cancels). FLAG-1 (the `packM` opaque-width cast) handled via the
`Equiv.apply_symm_apply` / flat-index readback pattern (the `paramsEquivFlat` `FlatIdx` ordering align).

## Pre-staged API contracts (the bricks this build consumes — pinned as `example`s)

The durable contracts (skill: pre-stage uncertain API). These confirm the brick signatures compile at the
shapes the L = 2 build needs, BEFORE the cast-heavy fill.
-/

open MeasureTheory
open scoped ENNReal BigOperators

namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-! ### Brick 1 — the general `coreShear` skew-product is measure-preserving (any widths) -/

example (a b c : ℕ) (shift : (Fin a → ℝ) × (Fin c → ℝ) → (Fin b → ℝ)) (hsh : Measurable shift) :
    MeasurePreserving
      (fun q : (Fin a → ℝ) × ((Fin b → ℝ) × (Fin c → ℝ)) =>
        (q.1, (q.2.1 + shift (q.1, q.2.2), q.2.2)))
      volume volume :=
  measurePreserving_coreShear_measurable a b c shift hsh

/-! ### Brick 2 — `paramsEquivFlat M` is a measure-preserving `MeasurableEquiv` (the outer reshape) -/

example (M : Fin (L + 1) → ℕ) :
    MeasurePreserving (paramsEquivFlat M) (volume : Measure (Params M)) volume :=
  measurePreserving_paramsEquivFlat M

-- the inverse reshape `(paramsEquivFlat M).symm` is the generic `packM` (a `MeasurableEquiv`, MP);
-- its MP is `(measurePreserving_paramsEquivFlat M).symm …` — pinned at build time, not here.

/-! ### Brick 3 — the contract this build feeds (`routeMCore_box_diverges_smearedContract`) -/

example (M : Fin (L + 1) → ℕ)
    (ψ R : (Fin (routeMAmbient M) → ℝ) → (Fin (routeMAmbient M) → ℝ))
    (D : (Fin (routeMAmbient M) → ℝ) → (Fin (routeMAmbient M) → ℝ) →L[ℝ] (Fin (routeMAmbient M) → ℝ))
    (p : Fin (routeMAmbient M)) (h : ℕ)
    (hmp : MeasurePreserving ψ (volume : Measure (Fin (routeMAmbient M) → ℝ)) volume)
    (hemb : MeasurableEmbedding ψ) (c' : ℝ) (ε : ℝ)
    (S : Set (Fin (routeMAmbient M) → ℝ)) (hSmeas : MeasurableSet S)
    (hSpre : S ⊆ (fun u => ψ (R u)) ⁻¹' (cubeBox (routeMAmbient M) ε))
    (hRderiv : ∀ u ∈ S, HasFDerivWithinAt R (D u) S u) (hRinj : Set.InjOn R S)
    (hRdet : ∀ u ∈ S, |(D u).det| = |u p| ^ h)
    (hSdiv : (∫⁻ u in S, ENNReal.ofReal (|u p| ^ h)
      * ENNReal.ofReal (|routeMCore M (ψ (R u))| ^ (-c'))) = ⊤) :
    ∫⁻ x in cubeBox (routeMAmbient M) ε,
      ENNReal.ofReal (|routeMCore M x| ^ (-c')) = ⊤ :=
  routeMCore_box_diverges_smearedContract M ψ R D p h hmp hemb c' ε S hSmeas hSpre hRderiv hRinj hRdet
    hSdiv

/-! ### Sub-tide 1 — general matrix-inverse entrywise measurability (the `shiftM`/Λ₀ foundation)

The (2,3,1) `lam231_measurable` uses an explicit `2×2` cofactor inverse (no transport to opaque widths).
The GENERAL route, valid at any width: `A⁻¹ i j = (det A)⁻¹ • adjugate A i j` (`Matrix.inv_def`), with
`adjugate`/`det` continuous (hence measurable) in the entries and `(·)⁻¹` measurable. This unblocks the
opaque-width `Λ₀ = (P₁ᵀP₁)⁻¹P₁ᵀP₂` shift measurability (FLAG-1, resolved). -/

/-- **General matrix-`det` entrywise measurability.** For a matrix-valued map with measurable ENTRIES,
`det (A x)` is measurable in `x`. Via `det_apply'` (`det = ∑_σ ε σ · ∏_i A (σ i) i`) + `Finset` sum/prod
measurability — avoids the `Matrix` `MeasurableSpace` instance (works entrywise, like `lam231`). -/
theorem measurable_matrixDet {X : Type*} [MeasurableSpace X] {n : ℕ}
    (A : X → Fin n → Fin n → ℝ) (hA : ∀ i j, Measurable (fun x => A x i j)) :
    Measurable (fun x => (Matrix.of (A x)).det) := by
  simp only [Matrix.det_apply']
  refine Finset.measurable_sum _ (fun σ _ => ?_)
  refine (measurable_const).mul (Finset.measurable_prod _ (fun i _ => ?_))
  exact hA (σ i) i

/-- **General matrix-`adjugate` entrywise measurability.** Each `adjugate (A x) i j = (updateRow j (e i)).det`
(`adjugate_apply`), a `det` of an entry-measurable matrix — measurable by `measurable_matrixDet`. -/
theorem measurable_matrixAdjugate {X : Type*} [MeasurableSpace X] {n : ℕ}
    (A : X → Fin n → Fin n → ℝ) (hA : ∀ i j, Measurable (fun x => A x i j)) (i j : Fin n) :
    Measurable (fun x => (Matrix.of (A x)).adjugate i j) := by
  simp only [Matrix.adjugate_apply]
  -- (updateRow (A x) j (Pi.single i 1)).det — entries measurable (updateRow swaps row j for a constant)
  refine measurable_matrixDet (fun x => (Matrix.of (A x)).updateRow j (Pi.single i 1)) (fun a b => ?_)
  by_cases haj : a = j
  · subst haj
    simp only [Matrix.updateRow_self]
    exact measurable_const
  · simp only [Matrix.updateRow_ne haj, Matrix.of_apply]
    exact hA a b

/-- **General matrix-inverse entrywise measurability (the `shiftM`/Λ₀ foundation).** For a matrix-valued
map with measurable ENTRIES, each inverse entry `(A x)⁻¹ i j` is measurable. Via `Matrix.inv_def`
(`A⁻¹ = (det A)⁻¹ • adjugate A`) + `measurable_matrixDet`/`measurable_matrixAdjugate` + `Measurable.inv`.
The opaque-width replacement for the `(2,3,1)` explicit-`2×2`-cofactor `lam231_measurable` (FLAG-1). -/
theorem measurable_matrixInv_entry {X : Type*} [MeasurableSpace X] {n : ℕ}
    (A : X → Fin n → Fin n → ℝ) (hA : ∀ i j, Measurable (fun x => A x i j)) (i j : Fin n) :
    Measurable (fun x => (Matrix.of (A x))⁻¹ i j) := by
  have hentry : ∀ x, (Matrix.of (A x))⁻¹ i j
      = (Matrix.of (A x)).det⁻¹ * (Matrix.of (A x)).adjugate i j := by
    intro x; rw [Matrix.inv_def]; simp [Matrix.smul_apply, smul_eq_mul]
  simp only [hentry]
  exact (measurable_matrixDet A hA).inv.mul (measurable_matrixAdjugate A hA i j)

end DLNFibre.DLN.RLCT
