import DLNFibre.DLN.RLCT.Validate.DeepestSchurShift

/-!
# `DLNFibre.DLN.RLCT.Validate.DeepestFramedProduct` — the gauge-sliced framed product `∏C` (#44c)

The shared concrete object both PIN 1 (`Ereg`, the regular residual) and PIN 2 (`loss_squeeze`, the
frame bridge) consume: the **framed product** `∏C_s`, where each layer
`C_s = fromBlocks (1 + X_s) Y_s Z_s T_s` is the gauge-sliced normal-form deviation (the `block_elimination`
frame puts `w0` at `blockdiag[I_r,0]`; the deviation reads the gauge blocks `(X_s, Y_s, Z_s)` off the
reg+spec slots via `gaugeSlotRead`/`regGaugeSlotEquiv` and the reduced `T_s` off the core slot).

Per the #92 producer contract: `∏C` is the CLEAN product of the per-layer normal forms (the interior
`block_elimination` frames are trivial — #77 (iii), interior layers already block-normal — so the
per-layer framing telescopes; only the two boundary frames carry units, absorbed by the endpoint
conjugation `conjugation_frobenius_comparable`). The framed product is `prod H C` for the reconstructed
gauge-sliced tuple `C : Params H` — no new fold; `prod`/`prodAux` are reused.

## Status

SCAFFOLD (decision-independent piece): the per-layer framed reconstruction `framedLayer`
(`fromBlocks` reindexed to a `Params H` layer via `rThresholdSplit`) + the framed tuple `framedParams`.
The `∏C` residual (`Ereg`) extraction + the `dlnLoss = ‖∏C − D‖²` bridge are the coupled pieces
(gated on the #77 (iii) decl-confirm + the `Ereg = E_pivot` (B)-ruling); built once confirmed.
-/

open Matrix
open scoped BigOperators
namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-- **The per-layer framed normal-form matrix** `C_s = fromBlocks (1 + X_s) Y_s Z_s T_s`, reindexed
from the block split `Fin r ⊕ Fin (H_s − r)` to the layer dimension `Fin (H_s)` (via `rThresholdSplit`),
so it types as a `Params H` layer `Matrix (Fin (H s.castSucc)) (Fin (H s.succ)) ℝ`. The gauge blocks
`(X_s, Y_s, Z_s)` are the regular/spectator gauge entries (off `gaugeSlotRead`); `T_s` is the reduced
core block. -/
noncomputable def framedLayer (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (s : Fin L)
    (X : Matrix (Fin r) (Fin r) ℝ) (Y : Matrix (Fin r) (Fin (H s.succ - r)) ℝ)
    (Z : Matrix (Fin (H s.castSucc - r)) (Fin r) ℝ)
    (T : Matrix (Fin (H s.castSucc - r)) (Fin (H s.succ - r)) ℝ) :
    Matrix (Fin (H s.castSucc)) (Fin (H s.succ)) ℝ :=
  Matrix.reindex (rThresholdSplit r (H s.castSucc) (hr s.castSucc)).symm
    (rThresholdSplit r (H s.succ) (hr s.succ)).symm
    (Matrix.fromBlocks (1 + X) Y Z T)

/-- **The framed parameter tuple** `C : Params H` reconstructed from a `DeepestSplit` point: each layer
is `framedLayer` of the gauge blocks `(X_s, Y_s, Z_s)` (read off the reg+spectator slot via
`readX/readY/readZ`) and the reduced core `T_s` (read off the core slot via `paramsEquivFlat (deepestM)`).
The framed product `∏C = prod H (framedParams q)` is the shared object; `dlnLoss = ‖∏A − B‖²` relates to
`‖∏C − D‖²` through the endpoint conjugation (the #77 (iii) telescoping). Decision-independent (the
product `∏C` is well-defined regardless of (iii)/(B); those affect how it relates to `dlnLoss`/`Ereg`). -/
noncomputable def framedParams (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (q : DeepestSplit H r (deepestNGauge H r)) : Params H :=
  fun s =>
    framedLayer H r hr s
      (readX H r hr hL (q.1, q.2.2) s) (readY H r hr hL (q.1, q.2.2) s)
      (readZ H r hr hL (q.1, q.2.2) s)
      ((paramsEquivFlat (deepestM H r)).symm q.2.1 s)

end DLNFibre.DLN.RLCT
