# Statement card — the ∀M-L2 boundary factor `B` (RouteMLeafBData)

> **Claim.** For the REAL ∀M-L2 `genBlkFlatLive` + leaf-pivot achiever chart `phiFlatLiveAt M ha hL p₀`
> (radial axis at the leaf pivot `p₀ = leafSlot 0 0`), there is a CONCRETE `u`-free boundary factor
> `B = BchartLeaf ha` with `phiFlatLiveAt = B ∘ pivotBlowupOn activeM p₀` (the map identity `hmap`) and
> `B` differentiable (`hasDB`), so the chart Jacobian abs-det is
> `|det Dφ| = |u p₀|^(minAdm M − 1) · ∏_{s:Fin 2} engine_s`
> against `DB := fderiv ℝ B (pivotBlowupOn activeM p₀ u)`, GIVEN the engine reading
> `|det DB| = ∏_s engine_s` (the per-boundary Schur·LDU value).
>
> - **Lean:** `DLNFibre.DLN.RLCT.interiorDet_leaf_headline_Bchart`
>   (`lean/DLNFibre/DLN/RLCT/Validate/RouteMLeafBData.lean` @ `26834bc3`); with `hmap_leaf`,
>   `hasDB_leaf`, `chartParamsGen_match` the load-bearing sub-results.
> - **Gloss.** The achiever chart factors as `boundary factor ∘ radial blow-up`. The boundary factor
>   `BchartLeaf ha y := paramsEquivFlat M (chartParamsGen 1 M (tach M) (genBlkFlatLive M (tach M) ha
>   (rfinDirect ha y) y) hle)` reads the residual coordinates as ORDINARY `y`-values (radial scalar
>   hardwired to `1`, leaf entries read directly via `rfinDirect`), so it carries no radial axis. The
>   chart's Jacobian determinant then splits as the radial monomial `|u p₀|^(minAdm−1)` (from the
>   blow-up's `pivotBlowupOnDeriv_det`, `activeM.card = minAdm`) times the boundary-factor determinant
>   `|det DB|`, which the caller reads as the per-boundary engine product.
> - **Proved.**
>   - `hmap_leaf` — `phiFlatLiveAt M ha (by norm_num) (leafPivot …) = BchartLeaf ha ∘ pivotBlowupOn
>     (activeM M ha) (leafPivot …)`. The design doc's stated BOTTLENECK (the opaque-width per-layer
>     reindex), discharged via Cgen-block matching (`Agen_congr` + `Cgen1_match`/`Cgen2_match`), with
>     NO explicit `chainA` reindexing over the dependent `Fin (Text/Wext)` widths.
>   - `hasDB_leaf` — `HasFDerivAt (BchartLeaf ha) (fderiv …) (pbo u)`. `BchartLeaf` is differentiable
>     everywhere (the chain is polynomial in `y`: radial `1`, linear block reads); assembled from the
>     banked chain-diff atoms (`diffAt_bmatStack`/`diffAt_rmatPad`/`diffAt_chainA`/`diffAt_read*`) via
>     `diffAt_Cgen_live` / `diffAt_Agen_live` / `Bchart_differentiableAt`.
>   - `interiorDet_leaf_headline_Bchart` — the headline above, with `B`, `hmap`, `hasDB` ALL concrete /
>     discharged; only the `hdet` engine reading remains a hypothesis.
>   - Supporting kernel (all axiom-clean): `rmatPad_smul` (`rmatPad` ℝ-linear in `E`),
>     `schurFrameProd_u_to_E` (the radial `u` of the chart's E-term moves into the residual coordinate
>     of the `u`-free `B`), `Agen_congr` (`Agen` depends only on `Nblk`/`Wblk`/`Cgen(k+1)`),
>     `activeSlotE_mem_activeM` / `leafSlot_mem_activeM` (E-slots and leaf-slots ∈ `activeM`),
>     `boundary0_notMem_activeM` + `readK/X/N/W_pbo` (the spectator reader slots are fixed by the
>     blow-up), `readE_pbo` (the E reader scales by `u p₀`).
> - **Assumed.** `StructAdm M (tach M)` (the achiever-path admissibility), `0 < Text M (tach M) 2`,
>   `0 < Wext M 2` (the leaf block nonempty, so the fixed pivot is realised) — all needed by the
>   informal claim too. `L = 2` (the single-interior-boundary case).
> - **Cited.** none new. (The downstream `rlct = ½·codim` reading still rests on the cited Aoyagi
>   equality, off this chart-Jacobian-level result.)
> - **Deferred.** The `hdet` engine reading `|det DB| = ∏_s engine_s` with `engine` the EXPLICIT
>   per-boundary Schur·LDU value (`engine_0 = |det K|^(r+c)·∏_i|q_i|^{2(t−1−i)}`, `engine_1 = 1`
>   leaf) is the SINGLE remaining hypothesis. This is the heavy `BFactors`/coordinate-split determinant
>   assembly (the pending `nodeChartGeneral` det piece, task #89) — Codex-confirmed NO honest shortcut
>   (the per-layer det is NOT a free product: `N` feeds both the layer-0 Schur frame and the chaining).
>   It is NOT proved here; the headline states it as a named input, and the determinant is taken
>   against the canonical `DB := fderiv ℝ (BchartLeaf ha) (pbo u)`.
> - **Structure & ideas observed.** The cheap hmap route (Cgen-block matching) sidesteps the explicit
>   `Agen0`/`Agen1` matrix derivation the (2,2,2) template used: since `Agen k = chainA(Nblk k, Wblk k,
>   Cgen(k+1))` and the radial `u` enters only through `Cgen`, two `(u, decoder)` configs with matching
>   `Nblk`/`Wblk`/`Cgen(k+1)` produce the SAME `Agen` (`Agen_congr`) — so the dependent-Fin reindex
>   never has to be unfolded. The E-block radial scaling is captured by the single algebraic identity
>   `schurFrameProd … u K X N E = schurFrameProd … 1 K X N (u•E)` (`rmatPad` linearity) plus the slot
>   fact `readE (pbo x) = (x p₀)·readE x` (the E-slot is in `activeM`). The reader/slot disjointness
>   (`boundary0_notMem_activeM`) was the main grind, as Codex predicted, but is bounded.
> - **Route.** (formaliser) The decoder-match design: `BparamsLeaf = chartParamsGen 1 …
>   (rfinDirect)`, then `hmap` by funext + per-layer `Agen_congr` over the two Cgen-block matches;
>   `hasDB` by mirroring the banked `phiFlatLiveR1_differentiableAt_of_Agen` for the `genBlkFlatLive`
>   chain. Decorrelated Codex (gpt-5.5, high) red-teamed the route and confirmed soundness +
>   flagged the slot-disjointness grind + `rmatPad_smul` as the bricks to bank first.
> - **Status.** sorry-free + reviewed; axiom-clean `[propext, Classical.choice, Quot.sound]` (forced
>   `#print axioms` with the olean deleted). Reviewer fidelity audit (decorrelated-Codex-corroborated)
>   PASSED all six questions — non-vacuous, faithful, `B` genuinely `u`-free, the `hdet` gap honestly
>   named; the one defect found (an overclaiming module docstring) is fixed.
