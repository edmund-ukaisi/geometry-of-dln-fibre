import DLNFibre.DLN.RLCT.Foundations.S1NodeBlowup
import DLNFibre.DLN.RLCT.Validate.NodeHomogeneity

/-!
# `DLNFibre.DLN.RLCT.Foundations.S1NodeFlatHomog` — the flat node loss is layer-0 homogeneous (R1 item i)

The flat-ambient shadow of `dlnLoss_homogeneous_layer`, the seam that feeds `node_loss_pivot_factor`
(the flat chart identity `flatNodeLoss (pivotBlowupOn active p x) = (x p)²·flatNodeLoss (hardPivotAt p x)`)
WITHOUT a hand-written flat-loss polynomial (the `myF222` route): we work with `flatNodeLoss M :=
dlnLoss M 0 ∘ (paramsEquivFlat M).symm` abstractly and transport the layer-0 homogeneity across the
flattening.

## The seam (the load-bearing identity)
Scaling the layer-0 flat coordinates (`layer0Coords M`, the `FlatIdx` entries whose layer is `0`) by `c`
corresponds, under `(paramsEquivFlat M).symm`, to scaling matrix layer `0` by `c` (`scaleLayer M c 0`):

  `(paramsEquivFlat M).symm (scaleActiveBy c (layer0Coords M) x) = scaleLayer M c (⟨0,hL⟩) ((paramsEquivFlat M).symm x)`.

Both sides read entrywise: the flat `symm` is `rfl` per entry (`x` evaluated at the flat index of
`(s,i,j)`), and `i ∈ layer0Coords ⟺ layer(i) = 0`, so the `scaleActiveBy` branch matches the
`scaleLayer` branch exactly. Then degree-2 homogeneity (`dlnLoss_homogeneous_layer`) gives `hhomog`,
and `node_loss_pivot_factor` (`NodeHomogeneity`) gives the flat chart identity for free.

Axiom-free target (only `propext`/`Classical.choice`/`Quot.sound`).
-/

open MeasureTheory Matrix
open scoped BigOperators
namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-- The flat-ambient coordinate indices of the deepest layer (`layer 0`): the `Fin (flatDim M)`
indices `i` whose underlying `FlatIdx` entry `(equivFin.symm i)` has layer `0`. The blow-up's `active`
set; `(layer0Coords M).card = mk` (`layer0Coords_card`, below, via `flatIdx_layer0_card`). -/
noncomputable def layer0Coords (M : Fin (L + 1) → ℕ) : Finset (Fin (flatDim M)) :=
  Finset.univ.filter (fun i : Fin (flatDim M) =>
    (((Fintype.equivFin (FlatIdx M)).symm i).1.1 : ℕ) = 0)

/-- Membership in `layer0Coords`: `i ∈ layer0Coords M ⟺ layer(i) = 0`. -/
theorem mem_layer0Coords (M : Fin (L + 1) → ℕ) (i : Fin (flatDim M)) :
    i ∈ layer0Coords M ↔ (((Fintype.equivFin (FlatIdx M)).symm i).1.1 : ℕ) = 0 := by
  simp [layer0Coords]

/-- **The layer-0 active block has `m·k` coordinates.** `(layer0Coords M).card = M 0 * M 1` —
via the `FlatIdx` layer-0 fibre count (`flatIdx_layer0_card`). The blow-up's `active.card`, giving the
Jacobian power `active.card − 1 = mk − 1` (`pivotBlowupOnDeriv_det`). -/
theorem layer0Coords_card (M : Fin (L + 1) → ℕ) (hL : 0 < L) :
    (layer0Coords M).card = M ((⟨0, hL⟩ : Fin L).castSucc) * M ((⟨0, hL⟩ : Fin L).succ) := by
  classical
  rw [layer0Coords, ← Fintype.card_subtype]
  rw [← flatIdx_layer0_card M hL]
  exact Fintype.card_congr
    (Equiv.subtypeEquiv (Fintype.equivFin (FlatIdx M)).symm (fun i => Iff.rfl))

/-! ## The seam: flat `scaleActiveBy` (layer-0) = matrix `scaleLayer` (layer 0) -/

/-- **The homogeneity seam.** Scaling the layer-0 flat coordinates by `c` corresponds, under
`(paramsEquivFlat M).symm`, to scaling matrix layer `0` by `c`. Entrywise `rfl` on the flat `symm`
read, with the `scaleActiveBy`/`scaleLayer` branch agreement from `i ∈ layer0Coords ⟺ layer(i) = 0`.
The flat shadow of `scaleLayer`; feeds `dlnLoss`'s layer-0 homogeneity to the flat node loss. -/
theorem symm_scaleActive_layer0 (M : Fin (L + 1) → ℕ) (hL : 0 < L) (c : ℝ) (x : Fin (flatDim M) → ℝ) :
    (paramsEquivFlat M).symm (scaleActiveBy c (layer0Coords M) x)
      = scaleLayer M c (⟨0, hL⟩ : Fin L) ((paramsEquivFlat M).symm x) := by
  funext s
  rw [scaleLayer]
  -- case on the LAYER (where `Function.update` is clean): `s = ⟨0,hL⟩` or not.
  by_cases hs : s = (⟨0, hL⟩ : Fin L)
  · -- layer 0: `Function.update … = c • (symm x) s`; match entrywise via the flat reads.
    subst hs
    rw [Function.update_self]
    funext i j
    -- the flat index of the matrix entry `(⟨0,hL⟩, i, j)`
    set idx : Fin (flatDim M) :=
      (Fintype.equivFin (FlatIdx M)) (⟨⟨(⟨0, hL⟩ : Fin L), i⟩, j⟩ : FlatIdx M) with hidx
    have hread : ∀ (v : Fin (flatDim M) → ℝ),
        (paramsEquivFlat M).symm v (⟨0, hL⟩ : Fin L) i j = v idx := fun v => rfl
    rw [hread]
    show (scaleActiveBy c (layer0Coords M) x) idx = (c • (paramsEquivFlat M).symm x ⟨0, hL⟩) i j
    rw [Matrix.smul_apply, smul_eq_mul, scaleActiveBy]
    have hidxmem : idx ∈ layer0Coords M := by
      rw [mem_layer0Coords, hidx, Equiv.symm_apply_apply]
    rw [if_pos hidxmem]
    rfl
  · -- layer ≠ 0: `Function.update … = (symm x) s`; match entrywise (idx ∉ active).
    rw [Function.update_of_ne hs]
    funext i j
    set idx : Fin (flatDim M) :=
      (Fintype.equivFin (FlatIdx M)) (⟨⟨s, i⟩, j⟩ : FlatIdx M) with hidx
    have hread : ∀ (v : Fin (flatDim M) → ℝ), (paramsEquivFlat M).symm v s i j = v idx := fun v => rfl
    rw [hread]
    show (scaleActiveBy c (layer0Coords M) x) idx = (paramsEquivFlat M).symm x s i j
    rw [scaleActiveBy]
    have hidxnmem : idx ∉ layer0Coords M := by
      rw [mem_layer0Coords, hidx, Equiv.symm_apply_apply]
      exact fun h => hs (Fin.ext h)
    rw [if_neg hidxnmem]
    exact (hread x).symm

/-! ## The flat node loss and its layer-0 homogeneity (`hhomog`) -/

/-- The flat node loss `flatNodeLoss M := dlnLoss M 0 ∘ (paramsEquivFlat M).symm` — the true loss in
flat coordinates (NOT a hand-written polynomial; the abstract pullback). -/
noncomputable def flatNodeLoss (M : Fin (L + 1) → ℕ) : (Fin (flatDim M) → ℝ) → ℝ :=
  fun x => dlnLoss M 0 ((paramsEquivFlat M).symm x)

/-- **The flat node loss is degree-2 homogeneous in the layer-0 active block** (`hhomog`, the
`node_loss_pivot_factor` input). `flatNodeLoss M (scaleActiveBy c (layer0Coords M) x) = c²·flatNodeLoss
M x`: the seam (`symm_scaleActive_layer0`) turns the flat scaling into the matrix `scaleLayer`, then
`dlnLoss_homogeneous_layer` gives the `c²`. -/
theorem flatNodeLoss_homog (M : Fin (L + 1) → ℕ) (hL : 0 < L) (c : ℝ) (x : Fin (flatDim M) → ℝ) :
    flatNodeLoss M (scaleActiveBy c (layer0Coords M) x) = c ^ 2 * flatNodeLoss M x := by
  unfold flatNodeLoss
  rw [symm_scaleActive_layer0 M hL c x, dlnLoss_homogeneous_layer]

/-- **The flat chart identity (the per-chart `F∘φ = y₀²·core`).** Pulling the flat node loss back
through the layer-0 blow-up chart `pivotBlowupOn (layer0Coords M) p` factors out the pivot square:
`flatNodeLoss M (pivotBlowupOn (layer0Coords M) p x) = (x p)²·flatNodeLoss M (hardPivotAt p x)`. From
`node_loss_pivot_factor` + `flatNodeLoss_homog`. The `(x p)²` is the exceptional `y₀²`; the residual
`flatNodeLoss M ∘ hardPivotAt p` is the `core = ‖Â·B‖²` the cover descends on (`Â p = 1`). -/
theorem flatNodeLoss_pivot_factor (M : Fin (L + 1) → ℕ) (hL : 0 < L) (p : Fin (flatDim M))
    (hp : p ∈ layer0Coords M) (x : Fin (flatDim M) → ℝ) :
    flatNodeLoss M (pivotBlowupOn (layer0Coords M) p x)
      = (x p) ^ 2 * flatNodeLoss M (hardPivotAt p x) :=
  node_loss_pivot_factor (layer0Coords M) p hp (flatNodeLoss M)
    (fun c y => flatNodeLoss_homog M hL c y) x

end DLNFibre.DLN.RLCT
