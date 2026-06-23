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

/-! ## PIN 2 frame bridge — the telescoping (#80, next chunk)

The geometric bridge `dlnLoss H B (paramsSymm w) ≍ ‖∏(framed C) − D‖²` reduces to: the **endpoint-frame
telescoping** `prod H A = P_0⁻¹ · (prod H C) · Q_{L-1}⁻¹` (under #95-(I): interior frames `= I` via
`deepestPoint_interior_eq_corM`, boundary-inner `= I` via `deepestPoint_layer{0,Last}_*_vanish`, so the
interior interfaces `Q_s⁻¹·P_{s+1}⁻¹ = 1` collapse) → `conjugation_frobenius_comparable` (the endpoint
conjugation, banked) → `fullProduct_loss_squeeze` (the block split, banked) + the gauge-read identities.

**The statement SHAPE is solved** (the cast obstacle): state it with EXISTENTIAL endpoints —
`∃ (P0 : Matrix (Fin (H 0)) (Fin (H 0)) ℝ) (QL : Matrix (Fin (H (Fin.last L))) (Fin (H (Fin.last L))) ℝ),
IsUnit P0 ∧ IsUnit QL ∧ prod H C = P0 * prod H A * QL`, with hypotheses: per-layer frames
`P : (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ`, `Q : … (Fin (H s.succ)) …`,
`hframe : ∀ s, C s = P s * A s * Q s`, `hunit : ∀ s, IsUnit (P s) ∧ IsUnit (Q s)`, and the
INTERFACE-VANISHING conditions `Q s * P s' = 1` for adjacent `s + 1 = s'` (the #95-(I) frame-triviality
makes the interfaces `I`). Existential `P0, QL` are naturally typed where `prod` lives (`H 0`, `H (last)`)
— this DODGES the `H 0` vs `H ⟨0,_⟩.castSucc` cast that breaks an explicit-endpoint statement (probed,
typechecks). The PROOF is the cast-heavy `prodAux` induction: invariant `prodAux H C k = P0 *
prodAux H A k * (frame at k)`, interior interfaces cancelling by the `Q s * P s' = 1` conditions. The
endpoint conjugation + block split are banked (`conjugation_frobenius_comparable`,
`fullProduct_loss_squeeze`); only this induction remains for PIN 2's bridge. -/

end DLNFibre.DLN.RLCT
