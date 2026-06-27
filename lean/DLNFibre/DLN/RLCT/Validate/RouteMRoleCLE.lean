import DLNFibre.DLN.RLCT.Validate.RouteMBridgeCLE
import DLNFibre.DLN.RLCT.Validate.RouteMChartSlots
import Mathlib.Topology.Algebra.Module.Equiv

/-!
# `RouteMRoleCLE` — brick (a): the per-role flat-block-split CLE engine

The ARCH-1 achiever-chart factors are `cleConjFactor (bridgeCLE M) (conjBlockMap S g) …` where
`S : Params M ≃L Block × Rest` exposes one role block (the radial pivot / the Schur frame `K/X/N/E` /
the LDU diagonal / the lift `W`) of the Params space (`codex/brick-a-*`). This module banks the
reusable ENGINE that builds such role-block-split CLEs from the banked `chartIdxEquiv` role-slot
coordinatization, validated to elaborate against the v4.29 pin.

The construction chain (all `ContinuousLinearEquiv`, so the conjugated factor's det is read at the
block via `conjBlock_abs_det`):

* `flatToChartIdxCLE` — `(Fin N → ℝ) ≃L (ChartIdx M t → ℝ)` via `ContinuousLinearEquiv.piCongrLeft`
  over the banked `chartIdxEquiv` (the disjoint role-slot bijection on `Fin N`).
* `roleSplitCLE` — given a reindex `ChartIdx ≃ Block ⊕ Rest`, `(ChartIdx → ℝ) ≃L (Block → ℝ) × (Rest →
  ℝ)` via `ContinuousLinearEquiv.sumPiEquivProdPi`.
* `flatBlockSplitCLE` — their composite `(Fin N → ℝ) ≃L (Block → ℝ) × (Rest → ℝ)` — the flat-level
  role-block split. Composing with `bridgeCLE.symm = paramsEquivFlatCLE` lifts it to a `Params M`
  split (the `S` the factors conjugate by).

The genuine per-role REINDEX `ChartIdx ≃ Block ⊕ Rest` (e.g. pulling the boundary-`k` Schur `K`-slot
to the front) is the role-specific input these consume; the radial-pivot split is the first instance.

Axiom-clean `[propext, Classical.choice, Quot.sound]` (finite equivalences + the pi-CLE combinators).
-/

namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-- **The flat → ChartIdx CLE** `(Fin N → ℝ) ≃L (ChartIdx M t → ℝ)` — `piCongrLeft` over the banked
disjoint role-slot bijection `chartIdxEquiv`. The first step of every per-role block split. -/
noncomputable def flatToChartIdxCLE (M : Fin (L + 1) → ℕ) (t : ℕ → ℕ)
    (h0 : t 0 = M 0) (hc : ∀ k, t (k + 1) ≤ (Wext M) (k + 1)) (hL : 0 < L) :
    (Fin (routeMAmbient M) → ℝ) ≃L[ℝ] (ChartIdx M t → ℝ) :=
  ContinuousLinearEquiv.piCongrLeft ℝ (fun _ : ChartIdx M t => ℝ) (chartIdxEquiv M t h0 hc hL)

/-- **The role-block split CLE** `(ChartIdx → ℝ) ≃L (Block → ℝ) × (Rest → ℝ)` — reindex `ChartIdx` to
`Block ⊕ Rest` (the role-specific `ρ`), then `sumPiEquivProdPi`. -/
noncomputable def roleSplitCLE {ChartIdxT Block Rest : Type*}
    (ρ : ChartIdxT ≃ Block ⊕ Rest) :
    (ChartIdxT → ℝ) ≃L[ℝ] (Block → ℝ) × (Rest → ℝ) :=
  (ContinuousLinearEquiv.piCongrLeft ℝ (fun _ : Block ⊕ Rest => ℝ) ρ).trans
    (ContinuousLinearEquiv.sumPiEquivProdPi ℝ Block Rest (fun _ => ℝ))

/-- **The flat-level role-block split** `(Fin N → ℝ) ≃L (Block → ℝ) × (Rest → ℝ)` — `flatToChartIdxCLE`
then `roleSplitCLE ρ`. The flat block split; precompose `paramsEquivFlatCLE` for the Params split. -/
noncomputable def flatBlockSplitCLE (M : Fin (L + 1) → ℕ) (t : ℕ → ℕ)
    (h0 : t 0 = M 0) (hc : ∀ k, t (k + 1) ≤ (Wext M) (k + 1)) (hL : 0 < L)
    {Block Rest : Type*} (ρ : ChartIdx M t ≃ Block ⊕ Rest) :
    (Fin (routeMAmbient M) → ℝ) ≃L[ℝ] (Block → ℝ) × (Rest → ℝ) :=
  (flatToChartIdxCLE M t h0 hc hL).trans (roleSplitCLE ρ)

/-- **The Params-level role-block split** `Params M ≃L (Block → ℝ) × (Rest → ℝ)` — `paramsEquivFlatCLE`
then `flatBlockSplitCLE ρ`. The `S` the ARCH-1 factors conjugate by (`conjBlockMap S …`); its det is
read at the block via `conjBlock_abs_det`. -/
noncomputable def paramsBlockSplitCLE (M : Fin (L + 1) → ℕ) (t : ℕ → ℕ)
    (h0 : t 0 = M 0) (hc : ∀ k, t (k + 1) ≤ (Wext M) (k + 1)) (hL : 0 < L)
    {Block Rest : Type*} (ρ : ChartIdx M t ≃ Block ⊕ Rest) :
    Params M ≃L[ℝ] (Block → ℝ) × (Rest → ℝ) :=
  (paramsEquivFlatCLE M).trans (flatBlockSplitCLE M t h0 hc hL ρ)

/-! ## Non-vacuity: the engine elaborates and composes (the `(2,2,2)` radial split shape)

The role split is parametric in the reindex `ρ : ChartIdx ≃ Block ⊕ Rest`. For the radial pivot the
block is the single slot carrying the radial coordinate; `Equiv` provides the singleton split
`ChartIdx ≃ (designated slot) ⊕ rest` (e.g. via `Equiv.optionSubtype` / a `decide`-d `Fin`-table on a
concrete case). The composite `paramsBlockSplitCLE` is then a genuine `Params M ≃L Block × Rest`. -/

/-- Non-vacuity: for ANY reindex `ρ`, `paramsBlockSplitCLE` is a genuine CLE (its forward map composes
`paramsEquivFlatCLE`, `piCongrLeft`, `sumPiEquivProdPi`) — the engine fires. -/
noncomputable example (M : Fin (L + 1) → ℕ) (t : ℕ → ℕ)
    (h0 : t 0 = M 0) (hc : ∀ k, t (k + 1) ≤ (Wext M) (k + 1)) (hL : 0 < L)
    {Block Rest : Type*} (ρ : ChartIdx M t ≃ Block ⊕ Rest) (P : Params M) :
    (Block → ℝ) × (Rest → ℝ) :=
  paramsBlockSplitCLE M t h0 hc hL ρ P

end DLNFibre.DLN.RLCT
