# Statement card — general-`L` interior-chart ANALYTIC LEAF facts (`genm-glift` task (b))

> **Claim.** For every depth `L > 0`, dimension vector `M : Fin (L+1) → ℕ`, achiever descent path
> `tach M` with `ha : StructAdm M (tach M)` (plus `0 < Text M (tach M) L`, `0 < Wext M L`), the four
> analytic-leaf facts the `NodeAchieverChart` bundle needs for the general-`L` LIVE-leaf ∘ kLDU interior
> achiever chart `interiorLivePhiGen` / its unit `interiorLiveUnitGen` all hold at arbitrary `L`:
> **(1)** the chart contracts a small source box `[0,δ]^N` into `cubeBox N ε`; **(2)** the unit is
> measurable; **(3)** the unit is bounded on `[0,δ]^N` and a.e.-positive there (given a.e.-positivity);
> **(4)** the unit is a.e.-positive on all of `ℝ^N`, given `InteriorDrop M`. This lifts the
> `Fin (2+1)`-pinned `ldu_image` / `ldu_Umeas` / `ldu_Ubound` / `interiorLiveUnit_ae_pos` to every depth.
>
> - **Lean:** `DLNFibre.DLN.RLCT.ldu_imageGen` (1), `ldu_UmeasGen` (2), `ldu_UboundGen` (3),
>   `interiorLiveUnit_ae_posGen` (4)
>   (`lean/DLNFibre/DLN/RLCT/Validate/RouteMInteriorLiveGenAnalytic.lean`),
>   with the supporting `continuous_interiorLiveUnitGen`, `ldu_Uval_le_on_boxGen`,
>   `UPolyLiveGen` + `UPolyLiveGen_ne_zero` + `eval_UPolyLiveGen`, `interiorLiveUnitGen_wInt_ne_zero`,
>   `kLDU_wIntGen`, `interiorLivePhiGen_zero`, and the depth-generic engine piece
>   `continuous_Hmat0_gen` (+ `continuous_suffix_gen` / `continuous_Hmat_gen`)
>   @ `<pending — genm-glift push SHA onto 45124eda>`.
> - **Gloss.**
>   (1) `∀ ε>0, ∃ δ>0, interiorLivePhiGen M ha hL h0r h0c '' [0,δ]^N ⊆ cubeBox N ε` — the chart maps a
>       small nonneg box near the origin into the ε-cube (continuity + `φ 0 = 0`).
>   (2) `Measurable (interiorLiveUnitGen M ha hL h0r h0c)` — the radial-quotient unit is measurable.
>   (3) `∀ δ, ∃ B>0, (∀ u∈[0,δ]^N, interiorLiveUnitGen u ≤ B) ∧ (∀ᵐ u ∂(vol.restrict [0,δ]^N), 0 <
>       interiorLiveUnitGen u)`, GIVEN `hpos : ∀ᵐ u, 0 < interiorLiveUnitGen u`.
>   (4) `∀ᵐ u, 0 < interiorLiveUnitGen M ha hL h0r h0c u`, GIVEN `hInt : InteriorDrop M`.
> - **Proved.** UNCONDITIONALLY (∀`L`, modulo the named hypotheses):
>   (1) continuity of `interiorLivePhiGen` (banked `interiorLive_diffGen.continuous`) + `interiorLivePhiGen
>       0 = 0` (`interiorLivePhiGen_zero`: `kLDU 0 = 0` via `kLDU_zeroGen`, then the banked ∀L
>       `chartParamsGen_live_zero` + `paramsEquivFlat_deepest`) + generic `cubeBox_subset_of_isOpen`.
>   (2)/(3) continuity of the unit, via `VvalGen_eq_sqSumHmat0` (unit `= ∑∑ (Hmat 0)²`) + the NEW
>       depth-generic `continuous_Hmat0_gen` (downward induction on `L−s` over `suffix`/`Hmat`, reusing the
>       banked ∀L `continuous_toChain_A/B/E` — the depth-2-hardcoded `continuous_Hmat0_L2` did not lift) +
>       `genBlkContinuous_liveGen` (block-continuity of the live decoder). Measurable = `continuous.measurable`;
>       the box bound is `IsCompact.exists_isMaxOn` on `[0,δ]^N`.
>   (4) `interiorLiveUnitGen u = eval u UPolyLiveGen` for a NAMED polynomial `UPolyLiveGen` (`eval_UPolyLiveGen`,
>       via `chainOfMt_map` + `genBlkFlatLiveGen_genBlkMap_of` glued from `kLDUGen_eval`/`rfinFixedPivotGen_map`
>       + `sqSumHmat0_map`); `UPolyLiveGen ≠ 0` (`UPolyLiveGen_ne_zero`, from `interiorLiveUnitGen_wInt_ne_zero`)
>       ⟹ its zero set is Lebesgue-null (`MvPolynomial.ae_eval_ne_zero`); `interiorLiveUnitGen_nonneg`
>       (sum of squares) upgrades `≠ 0` to `> 0`.
> - **Assumed.** `StructAdm M (tach M)`; `0 < L`; `0 < Text M (tach M) L`, `0 < Wext M L` (leaf-pivot
>   well-definedness, all four); for (3) the a.e.-positivity `hpos` (threaded in — it is exactly (4)); for
>   (4) `InteriorDrop M` (`0 < Wext M L ∧ ∃ p, 1≤p<L, Text(p+1)<Text(p) ∧ ∀ b∈[p,L), Text(b+1)<Wext(b)` — the
>   interior-drop cert supplying the pivot `p`, the strict row-drop, the tail column-drops, the leaf width).
> - **Cited.** `MvPolynomial.ae_eval_ne_zero` (the polynomial-zero-set-is-null brick,
>   `Core.MeasureTheory.PolynomialZeroSet`; itself axiom-clean `[propext, Classical.choice, Quot.sound]`).
> - **Deferred.** none for the analytic-leaf facts. (These are the `Umeas`/`Ubound`/`image_subset`
>   `NodeAchieverChart` slots + the a.e.-positivity soundness pin; the DET half of the interior atom —
>   `DtotGen_abs_det` / `eihd_hD_gen` in `RouteMInteriorLiveGenDet`, factor1's Route-B — is SEPARATE, still
>   open, and NOT part of this card. The `NodeAchieverChart` bundle assembly that consumes these four slots
>   is downstream, controller-wired.)
> - **VERIFY-FIRST (nonvanishing, task (4)'s flagged risk).** SETTLED — NONVANISHING HOLDS, no wall.
>   `UPolyLiveGen` is NOT identically zero at general `L`: `interiorLiveUnitGen_wInt_ne_zero` exhibits a
>   surviving `Hmat 0 (ρ,0) = 1` entry at the interior-drop witness `wInt p`, built ENTIRELY from ∀L-generic
>   machinery (`Hmat_pivot` / `Hmat_row_thread` / `suffix_carrier` + `genBlk_Bmat_succ_bot` /
>   `genBlk_Rmat_pivot` / `genBlk_Bmat_zero_top` / `genBlk_Bmat_succ_top` / `genBlk_Rmat_succ_zero` +
>   `readK_wInt` / `readW_wInt` / `survRowVal` / `rhoAt` / `liftRow`, all already stated at `Fin (L+1)`). The
>   surviving entry reads only `Bmat`/`Nblk`/`Wblk`/`Rmat` — `Rfin L`-blind and scalar-`u`-blind — so it is
>   `1` for ANY interior-drop config at ANY depth. The `InteriorDrop` cert docstring records validation
>   285/285 over the `1..3` / `L∈{2,3,4}` grid (i.e. L=3 already banked). Verdict = a LIFT of the L=2
>   `interiorLiveUnit_wInt_ne_zero` (`2 → L`), not new math.
> - **Route.** Lift the four `Fin (2+1)`-pinned atoms `ldu_image`/`ldu_Umeas`/`ldu_Ubound`/
>   `interiorLiveUnit_ae_pos` (`RouteMInteriorLiveAnalytic` + `RouteMUPolyLive`) to `Fin (L+1)`, reusing the
>   banked ∀L infra directly (co-import clash-free after the `readK_pbo_all → readK_pbo_allGen` rename on the
>   ∀L side, base `45124eda`). Only ONE genuinely-new engine piece: `continuous_Hmat0_gen`, the depth-generic
>   `Hmat 0` continuity by downward induction (the banked `continuous_Hmat0_L2` telescopes depth 2 by hand and
>   does not generalize). Everything else is a substitution `2 → L`, `by norm_num → hL/InteriorDrop`.
> - **Status.** sorry-free. Forced `#print axioms` (elaboration-forced, base `45124eda`): `ldu_imageGen`,
>   `ldu_UmeasGen`, `ldu_UboundGen`, `interiorLiveUnit_ae_posGen`, `UPolyLiveGen_ne_zero`,
>   `interiorLiveUnitGen_wInt_ne_zero`, `continuous_Hmat0_gen`, `ldu_Uval_le_on_boxGen` — ALL
>   `[propext, Classical.choice, Quot.sound]` (no `sorryAx` / `native_decide` / `monomial_rlct` / S2). All 18
>   new top-level names verified clash-free against the codebase. `scripts/lb GenAnalytic` GREEN. Fidelity
>   review: pending (controller-commissioned).

## Files

- `lean/DLNFibre/DLN/RLCT/Validate/RouteMInteriorLiveGenAnalytic.lean` (NEW, 582 LoC) — the four ∀L
  analytic-leaf facts + supporting continuity/poly lemmas.

Import direction: imports `RouteMInteriorLiveGenHmap` (∀L chart + `interiorLive_diffGen` +
`differentiable_kLDUGen`), `RouteMInteriorLiveAnalytic` (∀L `GenBlkContinuous` / `continuous_toChain_*` /
`continuous_bmatStack` / `continuous_rmatPad` / `chartParamsGen_live_zero`), `RouteMUPolyLive` (∀L
`kLDUGen` / `kLDUGen_eval` / `genBlkFlatLiveGen` / `rfinFixedPivotGen` / `sqSumHmat0_map` /
`genBlkFlatLiveGen_genBlkMap_of` / `kLens_one`; and, transitively, `RouteMAchieverWitnessInterior`'s ∀L
witness machinery). The co-import of the ∀L chart side and the `Fin (2+1)`-Contract side is clash-free
after genm-glift's `readK_pbo_all → readK_pbo_allGen` rename (base `45124eda`). Downstream-only sorries
in `RouteMInteriorLiveGenDet` (factor1's open det residuals) are in the import closure but NOT touched by
any theorem here — the forced `#print axioms` confirms no `sorryAx` leaks into the four deliverables.

FOLLOW-UP (bedrock simplification, optional, controller): none needed — the module already reuses one
canonical infra source (no duplication). `continuous_Hmat0_gen` could be relocated UP into
`RouteMInteriorLiveAnalytic` next to `continuous_Hmat0_L2` if a second ∀L consumer appears (lift-on-second-use).
