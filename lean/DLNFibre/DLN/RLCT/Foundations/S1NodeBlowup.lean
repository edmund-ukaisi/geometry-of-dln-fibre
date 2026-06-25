import DLNFibre.DLN.RLCT.Foundations.S1G5Charts
import DLNFibre.DLN.RLCT.Foundations.ParamsFlat
import DLNFibre.DLN.RLCT.Validate.LossHomogeneity

/-!
# `DLNFibre.DLN.RLCT.Foundations.S1NodeBlowup` — the node blow-up chart `F∘φ = y₀²·core` (R1 item 1)

The per-node single-pivot blow-up chart and its two load-bearing facts, for the per-node cover atom
(cert-104b §4; the R1 transport-producer lane, item 1 — de-risks the chart before the cover assembly).

## The chart (matrix level)
At the deepest layer (layer `0`, an `m × k = H 0 × H 1` matrix), the single-pivot blow-up scales the
whole layer-`0` block by a pivot scalar `y₀`. At the matrix level this is `scaleLayer M y₀ 0` — and
the square-Frobenius loss at the deepest point is degree-2 homogeneous in layer `0`
(`dlnLoss_homogeneous_layer`), so

  `dlnLoss M 0 (scaleLayer M y₀ 0 Â) = y₀² · dlnLoss M 0 Â`.

With `Â` carrying the unit pivot (`Â`-layer-0 `(0,0) = 1`), `core := dlnLoss M 0 Â = ‖Â·B‖²` is the
post-pivot residual (independent of `y₀`), giving the `F∘φ = y₀²·core` factorisation the cover
consumes.

## The Jacobian (flat level)
On the flat ambient `Fin (flatDim M) → ℝ`, the single-pivot blow-up acts as `pivotBlowupOn (layer-0
coords) p` (identity on the deeper-layer / `B` coords), whose Jacobian determinant is
`(x p)^{(#layer-0 coords) − 1} = y₀^{mk−1}` (`pivotBlowupOnDeriv_det`, the exceptional-divisor power
of the blow-up of the codim-`mk` center `{layer 0 = 0}`).

This file delivers (1) the matrix-level loss factorisation (the genuinely-new packaging over the
existing `dlnLoss_homogeneous_layer`) and (2) the flat layer-0 active-coordinate count `= mk` (so the
Jacobian power `active.card − 1 = mk − 1`), the two facts the cover assembly composes with the
box-product-min (`S1BoxProductMin`).

Axiom-free target (only `propext`/`Classical.choice`/`Quot.sound`).
-/

open MeasureTheory Set Matrix
open scoped BigOperators ENNReal
namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-! ## 1. The matrix-level loss factorisation `F∘(scale layer 0 by y₀) = y₀²·core` -/

/-- **The node blow-up loss factorisation (matrix level).** Scaling the deepest layer (`layer 0`) by a
pivot scalar `y₀` scales the square-Frobenius loss at the deepest point by `y₀²`:
`dlnLoss M 0 (scaleLayer M y₀ 0 Â) = y₀² · dlnLoss M 0 Â`. The `F∘φ = y₀²·core` identity the per-node
cover consumes, with `core = dlnLoss M 0 Â` the post-pivot residual (`Â` carrying the unit pivot). A
direct restatement of `dlnLoss_homogeneous_layer` at `s = 0` (requires `0 < L`, i.e. a non-leaf node
with a deepest layer). -/
theorem dlnLoss_nodeBlowup_factor (M : Fin (L + 1) → ℕ) (hL : 0 < L) (y₀ : ℝ) (Â : Params M) :
    dlnLoss M 0 (scaleLayer M y₀ ⟨0, hL⟩ Â) = y₀ ^ 2 * dlnLoss M 0 Â :=
  dlnLoss_homogeneous_layer M y₀ ⟨0, hL⟩ Â

/-! ## 2. The flat layer-0 active-coordinate block has `m·k` coordinates

The blow-up acts (on the flat ambient) as `pivotBlowupOn active p` with `active` the deepest layer's
flat coordinates; its Jacobian power is `active.card − 1 = mk − 1` (`pivotBlowupOnDeriv_det`). The
content here is that the deepest-layer block carries exactly `mk` coordinates — proved at the
`Fintype` level via the layer-`0` `FlatIdx` fibre. -/

/-- **The layer-0 `FlatIdx` fibre has `m·k` entries.** The `FlatIdx M` entries whose layer is `0`
(`(j.1.1 : ℕ) = 0`) biject with `Fin (M (⟨0,hL⟩.castSucc)) × Fin (M (⟨0,hL⟩.succ))` — the deepest
layer's matrix coordinates — which has `M (⟨0,hL⟩.castSucc) · M (⟨0,hL⟩.succ)` elements (`= mk` after
`castSucc = 0`, `succ = 1`). The blow-up's `active.card`, giving the Jacobian power `active.card − 1`.
Stated against the per-layer widths `M (⟨0,hL⟩.castSucc/succ)` (NOT yet collapsed to `M 0`/`M 1`) so
the equiv is cast-free; the `castSucc = 0 ∧ succ = 1` collapse is the trivial `Fin.ext` step the
consumer applies. -/
theorem flatIdx_layer0_card (M : Fin (L + 1) → ℕ) (hL : 0 < L) :
    Fintype.card { j : FlatIdx M // (j.1.1 : ℕ) = 0 }
      = M ((⟨0, hL⟩ : Fin L).castSucc) * M ((⟨0, hL⟩ : Fin L).succ) := by
  classical
  rw [show M ((⟨0, hL⟩ : Fin L).castSucc) * M ((⟨0, hL⟩ : Fin L).succ)
      = Fintype.card (Fin (M ((⟨0, hL⟩ : Fin L).castSucc)) × Fin (M ((⟨0, hL⟩ : Fin L).succ))) by
        rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]]
  apply Fintype.card_eq.mpr
  refine ⟨{
    toFun := fun j =>
      (Fin.cast (by rw [show j.1.1.1 = (⟨0, hL⟩ : Fin L) from Fin.ext j.2]) j.1.1.2,
       Fin.cast (by rw [show j.1.1.1 = (⟨0, hL⟩ : Fin L) from Fin.ext j.2]) j.1.2)
    invFun := fun p =>
      ⟨⟨(⟨(⟨0, hL⟩ : Fin L), p.1⟩ : FlatRowIdx M), p.2⟩, rfl⟩
    left_inv := ?_
    right_inv := ?_ }⟩
  · rintro ⟨⟨⟨s, row⟩, col⟩, hj⟩
    have hse : s = (⟨0, hL⟩ : Fin L) := Fin.ext hj
    subst hse
    rfl
  · rintro ⟨a, b⟩
    rfl

end DLNFibre.DLN.RLCT
