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

end DLNFibre.DLN.RLCT
