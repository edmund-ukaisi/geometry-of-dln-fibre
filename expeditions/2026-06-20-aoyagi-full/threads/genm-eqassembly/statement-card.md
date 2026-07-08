# Statement card — `hstep2` (D1 #120 "=" side gauge diffeo), general `L ≥ 3`

> **Claim.** For a deep-linear network with widths `H`, target `B` of rank `r`, at the deepest
> point of the fibre, the *regularized-score* local RLCT equals the *absorbed-core* local RLCT:
> `rlctAtOn Φscore wstar = rlctAtOn Φcore wstar`, where
> `Φscore x = ∑ᵢ (regStraighten (split x)).reg² + Score x`,
> `Φcore x = ∑ᵢ (regStraighten (split x)).reg² + deepestCoreF (coreAbsorb (split x)).core`,
> `wstar = paramsEquivFlat (deepestPoint …)`, `coreAbsorb = deepestCoreAbsorb`. This is the second
> step (the joint-move diffeo bridge `Ψ_conj ∘ Θ`) of the route-B ROUTE-B close; composed with the
> banked `hstep1` it discharges the `loss_squeeze` RLCT-equality, closing `deepest_gauge_construction`'s
> `L ≥ 3` arm.
>
> - **Lean:** `hstep2` — the local `have` at `DLNFibre/DLN/RLCT/Validate/DeepestL2Wiring.lean:1070`,
>   inside `DLNFibre.DLN.RLCT.deepest_gauge_construction`
>   (`lean/DLNFibre/DLN/RLCT/Validate/DeepestL2Wiring.lean`, branch `genm-eqassembly`, base
>   `2439023d` + 1 uncommitted change — controller pins the integration SHA).
> - **Gloss.** The score-energy `∑reg² + Score` and the absorbed-core energy `∑reg² + coreF(coreAbsorb)`
>   have the same real log-canonical threshold at the deepest point, because they agree up to a smooth
>   local diffeomorphism `psi` fixing the basepoint with derivative `id` there (so `rlctAtOn` is
>   diffeo-invariant). `psi` is the cutoff-flattened split-side joint move `psiSplitRawGen` (a core
>   Schur untwist + a reg/gauge fibre correction that keeps `deepestEFull` exactly invariant).
> - **Proved.** The full equality, unconditionally on the `L ≥ 3` arm's in-scope data (the triangular
>   pivot bundle from `deepestPoint_frame_pivot_triangular_exists`, `htop`, `hJfront`). Assembled from
>   banked, independently-reviewed leaves: diffeo triple (`deepestPsiFlatCut` + `psiSplitRawGen_zero`
>   / `hasStrictFDerivAt_psiSplitDeltaGen_zero` / `hcd_psiSplitRawGen`), `hsub3reg_gen_germ`, the
>   `hsub4core` germ (keystone `deepestCoreF_coreAbsorbConj_psiSplitRawGen_eq_score_at_chart` +
>   `coreAbsorbConj_reindex_eq_blockSchur_movedC_decode` for `hC` + the eventual corner-invertibility
>   germs + the eventual cutoff-ball), `deepBlkA_isUnit_gen` / `deepBlk_boundary_gen`, and
>   `deepest_diffeo_bridge_gen_assembled` (LINK-1 Ψ_conj + LINK-2 Step Θ).
> - **Assumed.** Only the hypotheses of `deepest_gauge_construction` itself (`hJfront` front-pivot WLOG,
>   `htop` row-alignment WLOG, `hpos`, `hL2 : 2 ≤ L`) — the same the headline discharges via the banked
>   row/col-permutation WLOG hub. No extra hypothesis is introduced by `hstep2`.
> - **Cited.** none. (No `cited_aoyagi_dln`, no `monomial_rlct` in the transitive closure of this arm.)
> - **Deferred.** none for the "=" side. NOTE (scope, per `genm-critpathmap`): closing `hstep2` closes
>   the D1 "=" side only; the D1 "≤" side (`Skeleton:1177`, needs the general-`L` IFT-chart-at-`v`
>   producer) is a separate, uncovered wall — not part of this card.
> - **Route.** Port the sorry-free `L = 2` arm (`DeepestL2Wiring` lines ~480–648) to general `L`:
>   remove the `subst hL2eq`, generalize the boundary/endpoint casts (`(lastLayer hL).succ = Fin.last L`
>   via `omega`; per-layer triangularity via `hInterior` on interior layers), swap the L2-specific
>   `deepBlkA_isUnit_of_L2` / `deepBlk_boundary_of_L2` for the general `deepBlkA_isUnit_gen` /
>   `deepBlk_boundary_gen`, and build the one genuinely-new piece — the `hsub4core` germ lifting the
>   pointwise keystone over the basepoint neighbourhood (eventual cutoff-ball from
>   `hderiv0 ⟹ ContinuousAt 0` + `psiSplitRawGen_zero`; `IsUnit → Invertible` on the corner germs;
>   per-`x` `hC` via the banked decode). Pick the flat-cut bump χ small-radius (`rIn=ε/4, rOut=ε/2`)
>   so `tsupport χ ⊆` the `eventually_psiInvBundle` region (`ContDiffBump.tsupport_eq`).
> - **Status.** sorry-free + reviewed.

## Fidelity review (decorrelated reviewer + Codex xhigh, 2026-07-08) — PASS (all 4 dims)

- **Goal fidelity — PASS.** `hstep2` type is the genuine `rlctAtOn Φscore wstar = rlctAtOn Φcore wstar`
  RLCT-equality; `Score` and `deepestCoreF(coreAbsorb …)` are visibly distinct (not a defeq restatement);
  no hypothesis smuggled into the `have` type.
- **Assembly fidelity — PASS.** `psi = deepestPsiFlatCut … psiSplitRawGen …` is the real `movedC` Schur
  repack (not `id`); `hsub4core` applies the keystone with `hC` discharged by the banked decode (not
  assumed); `hq`/`hLayer`/`hPart`/`hMid` from genuine `nhds`-eventual germs; χ non-vacuous
  (`tsupport ⊆` invertibility region); `hDA`/`hbdy` general-`L`. Faithful two-link reduction, no laundering.
- **Axiom footprint — PASS.** `deepest_gauge_construction`, `aoyagi_learning_coefficient_frontPivot` both
  `[propext, Classical.choice, Quot.sound]`; no `sorryAx`/`cited_aoyagi_dln`/`monomial_rlct`.
- **Scope honesty — PASS.** Correctly the "=" side only; "≤" side named as a separate wall; no overclaim.
- **Non-blocking note (for controller):** `DeepestDiffeoBridgeGenConj.lean:26,40` carries a now-stale
  docstring ("the `hstep2` sorry is therefore LEFT UNTOUCHED") — accurate when authored (germs were
  hypotheses there), superseded now that the caller discharges the germs. Documentation only.

## Downstream consequence (verified by forced `#print axioms`, fresh olean)

- `deepest_gauge_construction` — `[propext, Classical.choice, Quot.sound]` (was: 1 open `sorry` = `hstep2`).
- `aoyagi_learning_coefficient_frontPivot` (`DeepestNormalFormFrontPivot:125`) —
  `[propext, Classical.choice, Quot.sound]`. So the front-pivot chain
  (`… → deepest_gauge_chart_construct → deepest_gauge_construction`) is axiom-clean; the D1 "=" side
  `Skeleton:1131` is now closeable by the controller's skeleton-assembly tide (route via `_frontPivot`,
  NOT the DEAD `DeepestGaugeChart:357` stub).

## Build

- `scripts/lb DLNFibre.DLN.RLCT.Validate.DeepestL2Wiring` — green, 0 sorries (`scripts/sorries` clean).
- Full `scripts/lb DLNFibre` — **Build completed successfully (8780 jobs)**, incl. `AxCheck` (the
  forced-axioms gate). No new top-level names (all local `have`s), no import cycle; 10 Gen-module
  imports added to `DeepestL2Wiring.lean`.
