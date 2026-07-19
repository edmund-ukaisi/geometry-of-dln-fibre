import DLNFibre.DLN.RLCT.Engine.CenterIndices
import DLNFibre.DLN.RLCT.Foundations.ParamsFlatLinear
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# `DLNFibre.DLN.RLCT.Engine.QNodeChart` — the parametric center-split Homeomorph (carrier remainder)

The blow-up chart's ambient coordinate split: `qOfCenter` takes an INJECTIVE center selector
`c : Fin d → Fin (flatDim M)` (the flat coordinates of a blow-up center — `resBlockCenterIndices` for
the residual/d-family, or the `u`-pivot's birth-corner coordinate for case-1(1)) and produces the
`Homeomorph` splitting `Params M` into the `d` center coordinates × the `flatDim M − d` rest. It is
PARAMETRIC in `c` (elder-gate9: the arithmetic selector is banked in `CenterIndices`; the `u`-pivot
coordinate enters as part of `c` at the call site, so this piece does not block on the `divBirthCoord`
field). The per-edge wrapper `qEdgeOf` computes `d = dCenterOfEdge` and instantiates `c`.

**PER-EDGE keying** (coverage seam Q4 / elder-gate9 amendment 1): `d_center` is the per-EDGE count
(`dCenterOfEdge`), not the node sum — coverage's per-edge `β_e`/`pivotChart` index `Fin d_center_edge`
matches `qOfCenter`'s `Fin d` factor directly, with no node-sum slicing (the gate partitions per-edge).

Traps (carrier-remainder-spec §1): B — the permutation from the injective selector, via range +
complement (`Equiv.ofInjective` + `Equiv.sumCompl`, the `Fintype.card` complement bookkeeping in
`centerPerm`); C — stay on the CLE (`paramsEquivFlatCLE`), do the split on the flat `Fin (flatDim M) →
ℝ` side (never on `Params M` directly, dodging the `Matrix.module`/`NormedSpace` diamond); D —
`arrowCongr` continuity via the banked finite-pi Homeomorph combinators.
-/

namespace DLNFibre.DLN.RLCT.Engine

open DLNFibre.DLN.RLCT

variable {L : ℕ}

/-- **The center permutation** (trap B): from an injective center selector `c : Fin d → Fin (flatDim M)`,
the equiv `Fin (flatDim M) ≃ Fin d ⊕ Fin (flatDim M − d)` splitting the flat coordinates into the `d`
center coordinates (the range of `c`) and the `flatDim M − d` rest (its complement). The complement
card is `flatDim M − d` (`card (range c) = d` by injectivity; `Fintype.card_subtype_compl`). -/
noncomputable def centerPerm (M : Fin (L + 1) → ℕ) {d : ℕ} (c : Fin d → Fin (flatDim M))
    (hinj : Function.Injective c) : Fin (flatDim M) ≃ Fin d ⊕ Fin (flatDim M - d) := by
  classical
  have hcardR : Fintype.card {x : Fin (flatDim M) // x ∈ Set.range c} = d := by
    have h := Fintype.card_congr (Equiv.ofInjective c hinj)
    rw [Fintype.card_fin] at h
    exact h.symm
  have hcardC : Fintype.card {x : Fin (flatDim M) // x ∉ Set.range c} = flatDim M - d := by
    rw [Fintype.card_subtype_compl, Fintype.card_fin, hcardR]
  exact (Equiv.sumCompl (· ∈ Set.range c)).symm.trans
    (Equiv.sumCongr (Equiv.ofInjective c hinj).symm (Fintype.equivFinOfCardEq hcardC))

/-- **The center-split Homeomorph** (the intricate remainder): `Params M ≃ₜ (Fin d → ℝ) × (Fin
(flatDim M − d) → ℝ)`, splitting off the `d` center coordinates named by an injective `c`. Composed
`paramsEquivFlatCLE.toHomeomorph` (Params ≃ₜ flat, trap C: on the CLE instance) ∘ `piCongrLeft
(centerPerm)` (reindex the flat coords, trap D) ∘ `sumArrowHomeomorphProdArrow` (⊕ → ×). -/
noncomputable def qOfCenter (M : Fin (L + 1) → ℕ) {d : ℕ} (c : Fin d → Fin (flatDim M))
    (hinj : Function.Injective c) :
    Params M ≃ₜ (Fin d → ℝ) × (Fin (flatDim M - d) → ℝ) :=
  ((paramsEquivFlatCLE M).toHomeomorph.trans
      (Homeomorph.piCongrLeft (Y := fun _ : Fin d ⊕ Fin (flatDim M - d) => ℝ)
        (centerPerm M c hinj))).trans
    Homeomorph.sumArrowHomeomorphProdArrow

/-- **Per-edge center dimension** (elder-gate9 amendment 1; the count the `geometricLeafPaths` fan-out
uses). case-1(1) = `1` (the `u`-pivot chart); case-1(2) = `runLen · resCols` (the d-family, NOT
resRows); case-2 = `resRows · resCols`; rollover = `0` (chartless). -/
def dCenterOfEdge (node : StepData M) (e : Edge M) : ℕ :=
  match e.case with
  | StepCase.case11 => 1
  | StepCase.case12 => e.subst.runLen * node.resCols
  | StepCase.case2 => node.resRows * node.resCols
  | StepCase.rollover => 0

end DLNFibre.DLN.RLCT.Engine
