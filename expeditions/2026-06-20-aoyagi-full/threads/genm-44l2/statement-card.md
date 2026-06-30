# Statement card — the #44-at-L=2 normal form (taint-clean conditional value)

> **Claim.** At `L = 2`, for a rank-`r` target `B` with strict widths (`r < H s ∀ s`), the local RLCT
> of the DLN loss at the constructed deepest point equals the closed form `nReg/2 + ofReal(lambdaCore M)`
> (`nReg = r(H⁰+Hᴸ−r)`, `M = H − r`) — the EXACT conclusion of the Skeleton's #44
> `deepest_regular_core_normal_form`, at `L = 2`, CONDITIONAL on three named-open hypotheses.
>
> - **Lean:** `DLNFibre.DLN.RLCT.deepest_regular_core_normal_form_L2`
>   (`lean/DLNFibre/DLN/RLCT/Validate/DeepestNormalFormFrontPivotL2.lean` @ `6e38ba3d`)
>   — supporting: `deepest_regular_core_reduces_frontPivot_L2` (value-free L2 reduction) +
>   `deepest_gauge_chart_construct_L2` (the L2-clean chart producer, the taint-kill).
> - **Signature (conclusion, verbatim = Skeleton #44):**
>
>       rlctAt H (dlnLoss H B) (deepestPoint H r B hB hr hL)
>         = ((r * (H 0 + H (Fin.last L) - r) : ℕ) : ℝ≥0∞) / 2
>           + ENNReal.ofReal (lambdaCore (fun s => H s - r) : ℝ)
>
>   Hypotheses: `hB : B.rank = r`, `hr : ∀ s, r ≤ H s`, `hL : 1 ≤ L`, `hL2 : 2 ≤ L`,
>   `hpos : ∀ s, r < H s`, `hLlt : L < 3`, plus the three named-open `hJfront`, `htop`, `hRValue`.
> - **Gloss.** The L=2 deepest-point local RLCT is the regular gauge shift `nReg/2` (the `r(H⁰+Hᴸ−r)`
>   nondegenerate gauge directions, Fubini-additive) plus the singular core value `ofReal(lambdaCore M)`
>   on the reduced widths. Built by the gauge-slice squeeze chart (L=2-clean), its measure-preserving
>   transport + smooth-block split (the value-free reduction to `nReg/2 + rlctAtOn(dlnLoss M 0) 0`),
>   then R1's core value `hRValue` substitutes `rlctAtOn(dlnLoss M 0) 0 = ofReal(lambdaCore M)`.
> - **Proved.** The full L2 chain `deepest_gauge_chart_construct_L2 → ..._reduces_frontPivot_L2 →
>   ..._normal_form_L2`, all sorry-free + **axiom clean-three** `[propext, Classical.choice, Quot.sound]`
>   (forced `#print axioms`, verified post-edit). The `hGne` reduced-core germ-nonvanishing is DISCHARGED
>   here from `hpos` via the banked `dlnLoss_deepest_core_ae_ne_zero` (`r < H s ⟹ 1 ≤ H s − r`).
>   **Taint-kill:** re-pointing the chart producer off the GENERAL `deepest_gauge_construction` (whose
>   unexecuted `L ≥ 3` branch carries the #120 `sorry`s, inherited as `sorryAx` even at `L = 2`) onto
>   `deepest_gauge_construction_L2` removes the taint — the old `deepest_gauge_chart_construct` /
>   `deepest_normal_form_of_value_frontPivot` carry `sorryAx`; the `_L2` chain does NOT.
> - **Assumed (named-open hypotheses, carried not discharged).**
>   - `hJfront` — the deepest-point frame-pivot `.choose` embedding equals `frontEmbed` (the front
>     `k ↦ k`). **OPEN** (GATE-0 verdict, genm-44l2): the WLOG transfer from front-pivot to the general
>     `deepestPoint` is NOT closed. The #100/#154 column/row WLOG (`headline_frontRowColPivot_exists`,
>     sorry-free) operate at the `⨅ optimalSet` level and give front-COLUMN-rank + top-ROW-rank facts;
>     nothing bridges those to the abstract-`.choose`-`frontEmbed` identity at the single `deepestPoint`.
>   - `htop` — `B`'s top `r` rows full rank (the row-alignment, KC1). OPEN, the row-WLOG dual of `hJfront`.
>   - `hRValue` — R1's resolution core value `rlctAtOn(dlnLoss M 0) 0 = ofReal(lambdaCore M)` (R1's lane,
>     in flight).
> - **Cited.** none (all internal: the banked `deepest_gauge_construction_L2` clean-three assembly, the
>   transport/smooth-split `deepest_squeeze_transport`/`deepest_regular_smooth_split`, the hGne glue
>   `dlnLoss_deepest_core_ae_ne_zero`).
> - **Deferred.** (1) The `hJfront` bridge (the true remaining obstacle to the UNCONDITIONAL L2 value —
>   also gates the D1 ≥-leg `hDeepest`). (2) Wiring `deepest_regular_core_normal_form_L2` into the
>   Skeleton's #44 bare `sorry` at cone-merge (controller, single-writer on `Skeleton.lean`); the extra
>   hyps `hL2`/`hLlt` come from `L = 2`, and `hJfront`/`htop`/`hRValue` stay named-open at the headline.
>   (3) The `L ≥ 3` analogue (the #120 grouped-diffeo wall, out of scope).
> - **Route.** Re-home the front-pivot value chain (`DeepestNormalFormFrontPivot`) onto the L2-clean
>   `deepest_gauge_construction_L2` (a new `_L2`-suffixed parallel chain in a NEW file, no edits to the
>   single-writer `Skeleton.lean`/`DeepestL2Wiring.lean` theorems); discharge `hGne` from `hpos`.
> - **Status.** sorry-free + axiom clean-three (forced `#print axioms`); pending fidelity review +
>   cone-merge wiring into Skeleton #44.

---

## hJfront re-architecture — COMPLETE (phases A+B+C, the value side is now headline-closeable)

> **Result.** The `#44`-at-`L=2` normal form holds CONDITIONAL on `htop` + `hcolfront` (BOTH
> headline-WLOG-supplied — `#154` row-WLOG + `#100` column-WLOG) + `hRValue` (R1) — and **NOT** on the
> unprovable `hJfront`. So the value-side leg (`#44`, and the D1 ≥-leg that inherits it) is now
> closeable by the headline.
>
> - **Lean:** `DLNFibre.DLN.RLCT.deepest_regular_core_normal_form_L2_front`
>   (`lean/DLNFibre/DLN/RLCT/Validate/DeepestFrontGauge.lean` @ `3ab44e9f`) — clean-three.
> - **Conclusion:** identical to `deepest_regular_core_normal_form` (#44) at `L = 2`. Hypotheses:
>   `hB`, `hr`, `hL`, `hL2`, `hpos`, `htop`, `hcolfront`, `hLlt`, `hRValue` (no `hJfront`; `hGne`
>   discharged from `hpos`).
> - **Route X (parameterize, bedrock).** `DeepestL2Wiring` gains `deepest_gauge_construction_L2_ofBundle`
>   (the L2 gauge body with the triangular bundle as explicit args, byte-verbatim) +
>   `deepest_gauge_construction_L2` refactored to a thin wrapper (obtains the ARBITRARY bundle, applies
>   the core). **Guardrail verified:** the existing `deepest_gauge_construction_L2` stays clean-three
>   `[propext, Classical.choice, Quot.sound]`, behavior unchanged (the banked rung-1 L2 witness). The
>   FRONT bundle (`deepestPoint_frame_pivot_triangular_front_exists`) feeds the SAME core — no
>   duplication. Full `lake build DLNFibre` green (8644 jobs).
> - **Status.** sorry-free + clean-three; pending the controller's A+B+C review + cone-merge.

## hJfront re-architecture (follow-on, phases A+B+C — banked)

The `hJfront` discharge (the value-side gap that also gates the D1 ≥-leg). The arbitrary-`.choose`
identity `(deepestPoint_frame_pivot_exists ...).choose.trans finCongr = frontEmbed` is **unprovable**
(Codex-confirmed: `exists_pivot_cols_of_rank` picks an arbitrary maximal-independent column subfamily,
not the front). The sound route REPLACES it with a PROVABLE precursor `hcolfront` (`B`'s front `r`
columns full rank — the column-WLOG `headline_frontRowColPivot_exists` supplies it at the headline ⨅,
the dual of `htop`).

> - **Banked (phase A, `DeepestPivotFrame.lean`, additive, clean-three @ `035c1c7d`):**
>   `exists_pivotFrame_lastBlock_isUnit_of_pivot` (the deterministic pivot-frame core — `J`/`hJ` as
>   inputs; the Codex factorization) + `exists_frontPivotFrame_lastBlock_isUnit` (the front variant:
>   when `V`'s front `r` cols are full rank, `J = frontEmbed` deterministically). The legacy
>   `exists_pivotFrame_lastBlock_isUnit` refactored to DELEGATE — statement unchanged, all consumers +
>   `AxCheck` unaffected (verified, full `lake build DLNFibre` green).
> - **Banked (phase B, `DeepestLastBlock.lean`, NEW, clean-three @ `035c1c7d`):**
>   `deepestPoint_lastBlock_front_rank` — the COLUMN-dual of `DeepestLeadingBlock`'s
>   `deepestPoint_leadingBlock_isUnit`: from `hcolfront` (`B`'s front `r` cols rank `r`), the deepest
>   point's LAST layer has a full-rank top-left `r×r` block. Via `prod = B` + the back-peel
>   `prod_eq_prodAux_mul_last` + `deepestPoint_layerLast_rows_vanish` + a rank-squeeze. NO
>   `deepestPoint_exists` edit. This is the `hfront` input to the front frame builder.
> - **Banked (phase C, `DeepestFrontGauge.lean`, NEW, clean-three @ `48162ab4`/`3ab44e9f`):** the front
>   frame stack — `exists_deepest_lastLayer_frontPivotFrame`, `deepestPoint_frame_pivot_front_exists`,
>   `deepestPoint_frame_pivot_triangular_front_exists` (SAME output signature as the arbitrary
>   triangular bundle, `J.trans finCongr = frontEmbed` by construction via `frontJsucc_trans_eq_frontEmbed`)
>   — then the front feeder `deepest_gauge_construction_L2_front` + `deepest_gauge_chart_construct_L2_front`
>   + the value lemma `deepest_regular_core_normal_form_L2_front` (above). Route X parameterization replaced
>   the feared ~450-line body copy (`deepest_gauge_construction_L2_ofBundle` shared by both paths).
>   `deepest_layer0_blockLower_frame` un-privated (behavior-preserving visibility; reused verbatim).
