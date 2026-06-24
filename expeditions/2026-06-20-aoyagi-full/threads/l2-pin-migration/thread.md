# l2-pin-migration tide (rThresholdSplit → pivotThresholdSplit J)

Target: close L2 PIN1 (b) `deepestEPivot_regSlice_fderiv` + PIN2 (c) `framedParams_split_eq_frame_raw`
via the shared-J migration, on the verified `DeepestPivotFrame` foundation.

## Outcome: GREEN partial (no smuggle). Architecture validated; bedrock banked; both PINs remain
correctly-stated honest `sorry`s (unchanged from entry — NO regression).

The migration is genuinely 1500-2500 LoC of coupled, single-writer-sensitive work (Codex `xhigh`
decorrelated estimate), of which the PIN1 value-fold (~350-700 LoC of never-written strict-derivative
geometry against the frame-conjugate `framedLayer` shape) and the PIN2 bridge (~500-900 LoC) are the
bulk. An in-place API migration leaves the whole `deepestEPivot` chain red until the value-fold lands,
plus a multi-cycle `finCongr (H_lastLayer_succ)` cast bridge. Per the binding soundness gate (honest
partial > smuggle; do not leave a smuggled green), I landed the validated-architecture bedrock GREEN
rather than force a large red-incomplete state this tide.

## Delivered (green, axiom-clean `[propext, Classical.choice, Quot.sound]`)
- `DeepestRegBlockInvertible.lean` (new, 87 LoC): the F-invertibility consumer bricks —
  `mulRightUnitCLE` (`Y ↦ Y·M` a `≃L` from `IsUnit M` — the `Y·B₂₂` arm) and `shearCLE`
  (`(u,v)↦(u+g v,v)` a `≃L` — shears the `Y·B₂₁` cross term). These + a `·A`-conjugation assemble the
  linear part `F(X,Y,Z)=(A₁₁X+A₁₂Z+Y·B₂₁, Y·B₂₂, A₂₁X+A₂₂Z)` into the `≃L` that
  `regStraightenTotalCLM_equiv_of_regBlock_isUnit` consumes. The "no new geometry" PIN1 piece.

## Architecture VALIDATED (Codex ×2 + a sorry-free Lean discriminating check that BUILT GREEN)
- **L1 (last-layer-only pivot twist), NOT L2.** L2 ("twist only `deepestEPivot`'s final read") is
  UNSOUND: yields the MIXED block `Y·(reindex rThreshold eJ Q)₂₂`, not the certified
  `Y·(reindex eJ eJ Q)₂₂`. The last layer's `.succ`-side reindex AND the final-read codomain split must
  BOTH use `eLast := pivotThresholdSplit r (H last) J`. First/interior layers keep `rThresholdSplit`
  (their `.succ` side is only the corner at the gauge-zero slice) ⟹ `framedParamsReg_regSlice_{first,
  interior}`, `readX/Y/Z_regSlice_*` survive; only `framedParamsReg_regSlice_LAST` needs a pivot variant.
  `regResidualPack` stays FROZEN `:= regPivotFinEquiv` (the cancellation lemmas read the DOMAIN slot).
- **Discriminating identity (verified green):**
  `(reindex eR eJ ((reindex eR.symm eJ.symm (fromBlocks 0 Y 0 0)) * Q)).toBlocks₁₂
   = Y * (reindex eJ eJ Q).toBlocks₂₂`. Idiom: split at the middle index `eJ` via `submatrix_mul_equiv`,
  then `fromBlocks_toBlocks` + `fromBlocks_multiply`. So `B₂₂ = (reindex eJ eJ (Qf last))₂₂` — the block
  `exists_deepest_lastLayer_pivotFrame` certifies `IsUnit`.
- **Cast caveat:** `J` from the frame fact lives on `Fin (H ((lastLayer hL).succ))`; the codomain split
  is on `Fin (H (Fin.last L))`. EQUAL by `H_lastLayer_succ` (a `congr`, not defeq) ⟹ thread needs a
  `finCongr (H_lastLayer_succ H hL)` bridge on `J` (the same cast `readY_regSlice_last` already carries).

Full notes are inlined at the two `sorry`s in `DeepestGaugeConstruction.lean` (PIN1 ~line 550, PIN2
~line 850) so the next tide executes the atomic single-writer write deterministically.

## Codex artefacts
`codex/scoping-{prompt,answer}.md`, `codex/localize-{prompt,answer}.md`.
