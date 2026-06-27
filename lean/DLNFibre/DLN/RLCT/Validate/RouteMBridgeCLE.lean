import DLNFibre.DLN.RLCT.Validate.RouteMFlatStructV
import DLNFibre.DLN.RLCT.Validate.RouteMCLEConj
import DLNFibre.DLN.RLCT.Foundations.ParamsFlatLinear

/-!
# `RouteMBridgeCLE` — brick (a) foundation: the ONE collapse CLE + Params-level decoder (ARCH-1)

The OPTION-1 bridge `composeFold fs = phiFlatStructV` collapses (via `composeFold_eq_cleConj_foldr`) to
a `Params`-level layer equality, PROVIDED every factor uses the SAME CLE. Per the decorrelated Codex
brick-(a) consult (`codex/brick-a-*`), the right single CLE is

  `bridgeCLE M := (paramsEquivFlatCLE M).symm : (Fin N → ℝ) ≃L[ℝ] Params M`.

Then `cleConjMap (bridgeCLE M) g = paramsEquivFlat.symm ∘ g ∘ paramsEquivFlat` for layer-ops
`g : Params M → Params M`, and `composeFold_eq_cleConj_foldr` gives
`composeFold fs = paramsEquivFlat.symm ∘ (gs.foldr) ∘ paramsEquivFlat` — wait, `bridgeCLE.symm =
paramsEquivFlatCLE`, so it is `composeFold fs = paramsEquivFlat ∘ (gs.foldr) ∘ paramsEquivFlat.symm`,
matching `phiFlatStructV = paramsEquivFlat ∘ chartParamsGen ∘ genBlkFlatStruct` once
`(gs.foldr) ∘ paramsEquivFlat.symm = chartParamsGen ∘ genBlkFlatStruct`.

The **alignment is absorbed by CLE cancellation**, not a per-index proof: the Params-level decoder
`genBlkParamsStruct M t ha P := genBlkFlatStruct M t ha (paramsEquivFlat P)` satisfies
`genBlkParamsStruct M t ha (bridgeCLE M x) = genBlkFlatStruct M t ha x` because `bridgeCLE M x =
paramsEquivFlat.symm x` and `paramsEquivFlat (paramsEquivFlat.symm x) = x`.

This module banks the CLE + the Params-level decoder + the cancellation lemmas (the brick-(a) spine);
the layer-ops + the `funext s` bridge build on it.

Axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/

namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-- **The bridge collapse CLE** `bridgeCLE M := (paramsEquivFlatCLE M).symm : (Fin N → ℝ) ≃L Params M`
— the single CLE every achiever-chart factor conjugates by (so `composeFold_eq_cleConj_foldr` fires). -/
noncomputable def bridgeCLE (M : Fin (L + 1) → ℕ) :
    (Fin (routeMAmbient M) → ℝ) ≃L[ℝ] Params M :=
  (paramsEquivFlatCLE M).symm

/-- `(bridgeCLE M).symm P = paramsEquivFlat P` (the Params → flat flatten; `(·.symm).symm = ·` is
`rfl` for `ContinuousLinearEquiv`). -/
@[simp] theorem bridgeCLE_symm_apply (M : Fin (L + 1) → ℕ) (P : Params M) :
    (bridgeCLE M).symm P = paramsEquivFlat M P := by
  show (paramsEquivFlatCLE M) P = paramsEquivFlat M P
  exact congrFun (paramsEquivFlatCLE_coe M) P

/-- `bridgeCLE M x = paramsEquivFlat.symm x` (the flat → Params reshape). Both invert the same forward
function (`bridgeCLE.symm = paramsEquivFlat`), so they agree. -/
@[simp] theorem bridgeCLE_apply (M : Fin (L + 1) → ℕ) (x : Fin (routeMAmbient M) → ℝ) :
    bridgeCLE M x = (paramsEquivFlat M).symm x := by
  apply (paramsEquivFlat M).injective
  rw [MeasurableEquiv.apply_symm_apply, ← bridgeCLE_symm_apply,
    ContinuousLinearEquiv.symm_apply_apply]

/-- **The Params-level structured decoder** `genBlkParamsStruct M t ha P := genBlkFlatStruct M t ha
(paramsEquivFlat P)` — reads the role data from the flattening of the Params point. -/
noncomputable def genBlkParamsStruct (M t : Fin (L + 1) → ℕ) (ha : StructAdm M t) (P : Params M) :
    GenBlk M t :=
  genBlkFlatStruct M t ha (paramsEquivFlat M P)

/-- **The decoder cancels through `bridgeCLE`**: `genBlkParamsStruct M t ha (bridgeCLE M x) =
genBlkFlatStruct M t ha x` (the `paramsEquivFlat ∘ paramsEquivFlat.symm = id` cancellation — the
alignment absorbed). -/
@[simp] theorem genBlkParamsStruct_bridgeCLE (M t : Fin (L + 1) → ℕ) (ha : StructAdm M t)
    (x : Fin (routeMAmbient M) → ℝ) :
    genBlkParamsStruct M t ha (bridgeCLE M x) = genBlkFlatStruct M t ha x := by
  rw [genBlkParamsStruct, bridgeCLE_apply, MeasurableEquiv.apply_symm_apply]

/-- The radial scalar read from a Params point: `(paramsEquivFlat P) p` (`p = ⟨0,hN⟩`). -/
noncomputable def radialParams (M : Fin (L + 1) → ℕ) (hN : 0 < routeMAmbient M) (P : Params M) : ℝ :=
  paramsEquivFlat M P (structPivot M hN)

/-- The radial scalar cancels through `bridgeCLE`: `radialParams M hN (bridgeCLE M x) = x p`. -/
@[simp] theorem radialParams_bridgeCLE (M : Fin (L + 1) → ℕ) (hN : 0 < routeMAmbient M)
    (x : Fin (routeMAmbient M) → ℝ) :
    radialParams M hN (bridgeCLE M x) = x (structPivot M hN) := by
  rw [radialParams, bridgeCLE_apply, MeasurableEquiv.apply_symm_apply]

/-- **The monolithic Params-level chart op** `phiParamsStruct M t ha hN P := chartParamsGen
(radialParams P) M t (genBlkParamsStruct P) hle`. The achiever chart's TARGET in `Params`-space;
the genuine factored layer-ops will compose to this (the brick-(a) bridge), and it cancels through
`bridgeCLE` to `chartParamsGen (x p) M t (genBlkFlatStruct x) hle`. -/
noncomputable def phiParamsStruct (M t : Fin (L + 1) → ℕ) (ha : StructAdm M t)
    (hN : 0 < routeMAmbient M) (P : Params M) : Params M :=
  chartParamsGen (radialParams M hN P) M t (genBlkParamsStruct M t ha P) (hleStruct M t ha)

/-- **`phiParamsStruct` cancels through `bridgeCLE`** to the flat chart's `chartParamsGen` argument:
`phiParamsStruct M t ha hN (bridgeCLE M x) = chartParamsGen (x p) M t (genBlkFlatStruct M t ha x) hle`.
The Params-level target of the bridge, in terms of the flat decoder. -/
@[simp] theorem phiParamsStruct_bridgeCLE (M t : Fin (L + 1) → ℕ) (ha : StructAdm M t)
    (hN : 0 < routeMAmbient M) (x : Fin (routeMAmbient M) → ℝ) :
    phiParamsStruct M t ha hN (bridgeCLE M x)
      = chartParamsGen (x (structPivot M hN)) M t (genBlkFlatStruct M t ha x) (hleStruct M t ha) := by
  rw [phiParamsStruct, radialParams_bridgeCLE, genBlkParamsStruct_bridgeCLE]

/-! ## The monolithic-op bridge (the ARCH-1 spine, validated end-to-end)

A SINGLE `cleConjFactor (bridgeCLE M) phiParamsStruct …`-style factor reproduces `phiFlatStructV` via
the CLE cancellation — this validates the ARCH-1 collapse MECHANISM (the `bridgeCLE` cancellation +
`composeFold_eq_cleConj_foldr`) end-to-end, before the genuine Schur/LDU layer-op decomposition. The
factored chart replaces the monolithic op with the dependency-ordered layer-ops; this lemma is the
spine they slot into. -/

/-- **The ARCH-1 collapse spine**: for ANY list of layer-ops `gs : List (Params M → Params M)` whose
`cleConjMap (bridgeCLE M)`-conjugated factors are `fs`, `composeFold fs = paramsEquivFlat ∘ (gs.foldr)
∘ paramsEquivFlat.symm` (from `composeFold_eq_cleConj_foldr`). The bridge then needs only the
Params-level `(gs.foldr) ∘ bridgeCLE = phiParamsStruct ∘ bridgeCLE`. -/
theorem composeFold_bridge_eq (M : Fin (L + 1) → ℕ) (fs : List (ChartFactor (routeMAmbient M)))
    (gs : List (Params M → Params M))
    (hfs : fs.map (·.f) = gs.map (cleConjMap (bridgeCLE M))) :
    composeFold fs = fun x => paramsEquivFlat M ((gs.foldr (· ∘ ·) id) ((paramsEquivFlat M).symm x)) := by
  rw [composeFold_eq_cleConj_foldr (bridgeCLE M) fs gs hfs]
  funext x
  rw [bridgeCLE_symm_apply, bridgeCLE_apply]

end DLNFibre.DLN.RLCT
