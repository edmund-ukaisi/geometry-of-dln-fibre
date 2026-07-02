# genm-dr0build — statement cards

Thread: the general-`L` `deepRank = 0` interior box-divergence handler (re-pivot of the DONE
general-`L` `interiorLiveGen` staircase from the leaf pivot to an interior E-active slot). Module:
`lean/DLNFibre/DLN/RLCT/Validate/RouteMInteriorDeepRank0Gen.lean` (additive; branched from canonical
`origin/expedition/aoyagi-full` @ `ba7ecaf5`).

## CAREFUL SPOT — the pivot-generic `kLDU` / `pbo` commute (DONE, verdict: THREADS)

> **Claim.** For any radial pivot `p₀ ∈ activeMGen M ha`, `pivotBlowupOn (activeMGen) p₀` and `kLDU`
> commute: `pbo (kLDU x) = kLDU (pbo x)`.
>
> - **Lean:** `DLNFibre.DLN.RLCT.kLDU_pbo_commuteGen_at`
>   (`lean/DLNFibre/DLN/RLCT/Validate/RouteMInteriorDeepRank0Gen.lean` @ `5050afeb`)
> - **Gloss.** Casework on the coordinate `q`: at `q = p₀` (an active slot) the `kLDU` E-role identity
>   arm `kLDU_eq_on_activeMGen` gives `kLDU (pbo x) p₀ = (pbo x) p₀` directly (cleaner than the leaf
>   case, which needed `kLDU_leafPivotGen`); at other active `q` likewise; at spectator `q` the K-arm
>   agrees by `readK_pbo_allGen_at` (K-slots ∉ activeMGen ⟹ ≠ p₀), the identity arm by `pbo` fixing it.
> - **Proved.** The commute unconditionally for every `p₀ ∈ activeMGen`.
> - **Cited.** none. **Deferred.** none.
> - **Status.** sorry-free; axiom-clean `[propext, Classical.choice, Quot.sound]`.

The decorrelated adjudications (`dr0adj` pen-and-paper + Codex-xhigh) predicted this THREADS and is the
one place to build carefully; confirmed — it is cleaner than the leaf-pivot case.

## The re-pivot chart Jacobian abs-det (DONE)

> **Claim.** The `deepRank = 0` E-radial chart `eDeepRank0PhiGen` has Jacobian abs-det the single-axis
> monomial `∏_j |u_j|^{eDeepRank0_leafHGen p₀ j}`, where `p₀ = eBlockPivotGen k` is an interior E-active
> slot carrying the radial exponent `minAdm − 1`, and the K-diagonal slots carry the frame+LDU exponents.
>
> - **Lean:** `DLNFibre.DLN.RLCT.eDeepRank0_abs_detGen`
>   (`lean/DLNFibre/DLN/RLCT/Validate/RouteMInteriorDeepRank0Gen.lean` @ `5050afeb`)
> - **Gloss.** The chart factors (MAP) `eDeepRank0PhiGen = (BchartLeafGen ∘ kLDU) ∘ pbo p₀`
>   (`eDeepRank0PhiGen_factor`, via `hmap_EfpGen` + the commute); the pivot-generic radial split
>   `radialComp_abs_det_at` at `p₀` gives `|u p₀|^{minAdm−1} · |det D(BchartLeafGen ∘ kLDU)(pbo u)|`; the
>   boundary factor monomializes to the SAME K-diagonal product as the leaf-pivot case
>   (`interiorLive_BdetMonomialGen_at` — the pivot-generic reuse of the `Dtot_factor1` × `kLDU_ambient`
>   factors at any `p₀`, NOT the L=2 `|det DB| = 1` shortcut, which is FALSE at general `L`).
> - **Proved.** The det identity unconditionally (∀u). Also `eDeepRank0_diffGen` (differentiability).
> - **Cited.** none (pure calculus + finite products; the S2 `monomial_rlct` is NOT reached — no integral
>   yet). **Deferred.** none for the det.
> - **Structure & ideas observed (dr0adj).** `radialComp_abs_det_at` is fully pivot-generic and the base
>   Jacobian exponent `liveLeafHOnIdxGen` is `0` at every E-role slot, so the `minAdm − 1` radial override
>   on an E-slot is clean and the boundary-factor det is unchanged from the leaf-pivot case.
> - **Route (controller synthesis, attributed).** Route B: pivot-generic refactor of the done staircase
>   (Codex-xhigh confirmed over Route A from-scratch duplication).
> - **Status.** sorry-free; axiom-clean `[propext, Classical.choice, Quot.sound]`.

## Remaining gate (NOT done in this thread) — injectivity → cov → the box-divergence atom

> **Target (deferred).** `routeMCore_box_diverges_eDeepRank0Gen` (∀L): `InteriorDrop M ∧ deepRank M = 0`,
> `1 ≤ minAdm M` ⟹ the box integral `= ⊤` for `c' ≥ ½·minAdm M`, `ε > 0`; + the `deepRank = 0` consumer
> form `∀ _ : 2 ≤ L, InteriorDrop M → deepRank M = 0 → BoxDiverges M c' ε`.
>
> - **Deferred.** The `NodeAchieverChart.cov` field needs
>   `Set.InjOn (eDeepRank0PhiGen …) {u | u p₀ ≠ 0 ∧ ∀ j, u j ≠ 0}`. Via the factorization this reduces to
>   `BchartLeafGen ∘ kLDU` injective on the blowup image — the SAME per-boundary Schur-frame recovery as
>   the leaf-pivot `BchartLeafGen_injOn_recover` (`RouteMInteriorLiveGenInjRec`). Its recovery bricks
>   (`Cgen_succ_eq_of_BchartLeafGen_eq`, `frameReaders_eq`, `frameRecoverGen`, …) take the domain
>   hypothesis `hymem : y ∈ kLDU '' (pbo (leafPivot …) '' injDom)` ONLY to feed `detK_ne_zero_gen`
>   (`det (readK y k) ≠ 0`). At `deepRank = 0` `leafPivot` does not exist, so the leaf-pivot `hymem`
>   cannot be formed, and the private helpers (`frameTuple` / `Bof` / `readN_eq_of_frameTuple_eq` /
>   `Nblk_eq_of_readN_eq`) block a same-file-free re-derivation.
> - **UNBLOCK (precise).** Canonical-side hypothesis-weakening: re-state `detK_ne_zero_gen` + the recovery
>   bricks to take `hdetK : ∀ k, (Matrix.of (readK y k)).det ≠ 0` in place of `hymem` (strictly weaker —
>   the leaf case supplies it from `hymem`; this module supplies it from `readK_pbo_allGen_at` + the
>   all-nonzero domain). Alternatively make `frameTuple` / `Bof` / the two `readN` helpers non-private.
>   Once injectivity lands, the cov / `NodeAchieverChart` / the atom / the consumer form follow
>   mechanically (mirroring `RouteMInteriorDeepRank0Atom` at general `L`, feeding the M-agnostic
>   `routeMCore_box_diverges_of_nodeChart`); analytics (unit continuity / bound / ae-pos / measurable /
>   image_subset) do not need injectivity and mirror the L=2 module.
> - **Status.** NOT proven in this thread (no `sorry` in the module — the target theorem is simply not
>   yet stated, pending the unblock). The module is sorry-free.
