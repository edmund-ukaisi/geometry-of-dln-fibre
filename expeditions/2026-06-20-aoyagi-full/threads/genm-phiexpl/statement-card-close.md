# genm-phiexpl-close — the L=2 headline crux CLOSED (sorry-free, unconditional-except-S2)

Charged to close the L=2 crux `d1ge_L2_hAtV_explicit` sorry-free by assembling the banked germ +
reindex foundation (TIDE-7 runway) into the banked consumer `d1ge_L2_hAtV_of_explicit_chart`.

## Outcome — CLOSED

`d1ge_L2_hAtV_explicit` (`D1L2ExplicitCoreProducer`) was an honest `sorry`; it is now **closed
sorry-free** by the new drop-in `d1ge_L2_hAtV_explicit_close`. The L=2 headline
`aoyagi_learning_coefficient_L2` is **sorry-free**, forced-`#print axioms` footprint (deleted oleans +
recompiled):

    [propext, Classical.choice, Quot.sound, DLNFibre.DLN.RLCT.monomial_rlct]

— the mission-target clean-four. **NO `sorryAx`, NO `native_decide`, NO `hbox`.** The only citation is
`monomial_rlct` (the bare weighted-monomial-integral fact = S2). Pushed to `origin/genm-phiexpl-close`.

## Files

- **NEW** `lean/DLNFibre/DLN/RLCT/Validate/D1L2ExplChartClose2.lean` (~700 lines) — the germ + `qₑ` +
  slice + wiring.
- **EDITED** `lean/DLNFibre/DLN/RLCT/Validate/D1L2ExplicitCoreProducer.lean` — the crux `sorry`
  REMOVED, now `:= d1ge_L2_hAtV_explicit_close H r B v hopt hB hpos`; import added.
- Controller to wire `D1L2ExplChartClose2` into the aggregator `DLNFibre.lean` (single-writer) + add
  `aoyagi_learning_coefficient_L2` to `AxCheck.lean` (its forced footprint is now the clean-four).

## Theorems delivered (all sorry-free, in `D1L2ExplChartClose2.lean`)

- `splitHomeoL2` (+ `_apply`/`_zero`, `measurePreserving_splitHomeoL2`, `measurableEmbedding_…`,
  `contDiff_splitMP_symm`, `continuous_splitMP`, `splitMP_symm_apply`) — the `Homeomorph` version of
  the banked `splitMP` with a `C^∞` inverse, so `rlctAtOn_comp_homeomorph` (wants `≃ₜ`) applies.
- `reg_readback` (+ `reg_entry_M11/M12/M21`, `e_idx_reg`) — `∑ p² = ∑M21²+∑M11²+∑M12²`: the regular
  flat coords ARE the three raw `blockFlatEquiv_L2` reg-block entries (pure reindex, shifts zero).
- `qResid` / `qResidMat` + `contDiff_qResid` — the explicit `₂₂` Schur residual (bump-globalised
  inverse `G`), globally `ContDiff ℝ 1`. Helpers `contDiff_matrixEntry`/`_of_entries`/`_mul_entry`,
  `qBlock`, `contDiff_bChart`, `qResid_apply`/`_sq_sum`, `qBlock_splitMP`.
- **`schurReadout_germ_eq`** (the WALL) — `F =ᶠ[𝓝 0] fun x => ∑(splitMP x).1² + ∑ qResid(splitMP x)²`:
  the block-chart Frobenius readout splits into `∑p²` (reg readback, shifts zero) + `∑qₑ²` (the
  `M11⁻¹ → G` swap valid near the base). The `hchart` germ.
- **`qResid_slice_value`** — at `p=0` the reg residuals vanish (reg block `=0`) and the Schur complement
  `Br₂₁ Br₁₁⁻¹ Br₁₂ − Br₂₂ = 0` (`Core.schur_complement_zero_of_rank_le`), leaving `qResidMat =
  prod (H−r) (coreParams + coreShiftParam)`. The `hfact` value. Helpers `reg_zero_of_slice`,
  `mul_toBlocks₁₁/₁₂/₂₁`, `bChart_slice_reg_zero`, `coreShiftParam`.
- **`d1ge_L2_hAtV_explicit_close`** — the crux drop-in (identical signature to `d1ge_L2_hAtV_explicit`):
  `∃ P : Params (H−r), nRegL2 H r / 2 + rlctAtOn (dlnLoss (H−r) 0) P ≤ rlctAt H (dlnLoss H B) v`.
  Assembles the germ (`hchart`), the slice value (`hfact`, `u ≡ 1`), the core-nonvanishing (`hRne`, via
  `MvPolynomial.ae_eval_ne_zero`/`corePoly` + `quasiMeasurePreserving_fst.ae` + `e`-MP transport), and
  a measure-preserving core-translation `e` into the banked `d1ge_L2_hAtV_of_explicit_chart`.

## How the close is genuine (no laundering)

Every hypothesis the consumer `d1ge_L2_hAtV_of_explicit_chart` needs is CONSTRUCTED, not re-assumed:
`hchart` from the germ theorem (not an unproven interface); `hfact` from the real Schur-complement
slice value; `hRne` from the real polynomial non-vanishing; `u ≡ 1`; `e` a genuine measure-preserving
translation absorbing the reduced-core shift `(A0red₀, A1red₀)`. The `rlctAtOn (dlnLoss (H−r) 0) P` in
the conclusion is a genuine reduced-core RLCT; the Aoyagi Theorem-4 domination is downstream
(`core_zero_le_of_params`, already PROVEN), not inside this crux.

## Axiom footprint (forced `#print axioms`, oleans deleted + recompiled)

- `aoyagi_learning_coefficient_L2` : `[propext, Classical.choice, Quot.sound, monomial_rlct]` — clean-four.
- `d1ge_L2_hAtV_explicit` (the crux) : sorry-free, same footprint.

## Status

sorry-free, forced-axiom clean-four, pushed to `origin/genm-phiexpl-close`. Fidelity review requested.
