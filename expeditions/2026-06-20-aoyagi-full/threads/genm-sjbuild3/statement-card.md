# Statement card — R1-UPPER `genm-sjbuild3`: joint-resolution reduction + decoration row-mix

Thread `genm-sjbuild3` (formaliser). Branch `genm-sjbuild3` (pushed to `origin`). Base
`expedition/aoyagi-full @393f3ec3`. Two new modules, both isolated force-recompiled green
(`scripts/lb`), NOT wired into the `DLNFibre.lean` aggregator (controller wires). Every result
forced-`#print axioms` = clean-three `[propext, Classical.choice, Quot.sound]`; S2-FREE (no
`monomial_rlct`, no `cited_aoyagi_dln`). `scripts/sorries` = 0 in both modules.

## Module 1 — `RouteMSJJointReduce.lean` (the conditional close of `sjJointResolution`)

> **Claim.** The per-`(t,ρ,κ)`-chart peeled integral is dominated by the full layer-product box
> integral of the SAME chain; hence `sjJointResolution` closes immediately from standalone
> `RouteMBoxThresholdFinite M`.
>
> - **Lean.**
>   - `gammaPeelIntegral_le_boxIntegral : gammaPeelIntegral M t ρ κ c' ≤ routeMLayerBoxIntegral M c' 1`.
>   - `sjJointResolution_of_boxThresholdFinite : RouteMBoxThresholdFinite M → … → gammaPeelIntegral M t ρ κ (c':ℝ) < ⊤`.
> - **Gloss.** Both integrals are the tail-outer iterated front-factor integral
>   (`routeMLayerBoxIntegral_front_split`, banked); the chart restricts the inner leading-layer domain
>   to `matBox ∩ pivotChart ρ κ ⊆ matBox`, so `lintegral_mono_set` + `lintegral_mono` give the `≤`;
>   the close is `lt_of_le_of_lt` with `hM`.
> - **Proved.** Both, unconditionally, sorry-free.
> - **Fidelity caveat (decorrelated-Codex-confirmed).** Correct and non-circular ONLY as
>   `RouteMBoxThresholdFinite M → gammaPeelIntegral < ⊤`. It must NOT be used to discharge
>   `sjJointResolution` INSIDE the induction step (whose available IH is only for SHORTER chains) via a
>   same-chain box-finiteness that itself sits downstream of the `sjJointResolution` sorry — that would
>   launder the target. Combined with `sjBoundaryPeel` (box ≤ ∑ gammaPeel) it gives only the vacuous
>   `box ≤ (#charts)·box`; it does NOT reduce `gammaPeel` to a shorter chain. `sjBoundaryPeel` itself
>   stays a valid cover inequality.

## Module 2 — `RouteMSJDecoratedRowMix.lean` (piece 5, the clear-first (a) half)

> **Claim.** The clear-first scalar Schur elimination, lifted from the generator carrier to a whole
> `SJDecoration`, mixes the generators at constant support without touching the resolution state.
>
> - **Lean.**
>   - `SJDecoration.rowMix (D) (R : ι' → D.ι → ℝ) (s : Fin D.d → ℕ) : SJDecoration M` — mixes generators
>     by `R` onto fresh constant support `s`; only `ι ↦ ι'` and `carrier ↦ carrier.rowMix R (fun _↦s)`
>     change.
>   - `SJDecoration.rowMix_decLoss` — at a fresh block (`hconst : ∀ i, carrier.supp i = s`):
>     `(D.rowMix R s).decLoss u z = ∑ⱼ (∑ᵢ Rⱼᵢ · genᵢ)²` (banked `SJLinGenState.loss_rowMix`; the
>     support-homogeneity side condition discharged FOR FREE by `hconst`, unconditional in `R`).
>   - `rowMix_d` / `rowMix_jac` / `rowMix_dom` — the resolution-state invariants (`rfl`): `d`, `jac`,
>     `dom` (hence `carrierThreshold M`) preserved.
> - **Proved.** All, sorry-free; non-vacuity example on the trivial `(3,3,4)` decoration.
> - **Fidelity.** States the generators MIX (monomial prefix factoring cleanly out), NOT that the loss
>   is preserved (only det-1 absorbing units do, `frobSq_step3_absorb`; not asserted). Sits beside the
>   banked (b) `radialAttach`. Does NOT discharge `hsh` for the ACTUAL analytic Schur matrix at a
>   non-fresh block, does NOT compose (a)+(b)+regime into `decorated_peel_step`, does NOT reach
>   `RouteMBoxThresholdFinite M`.

## Status of `sjJointResolution` — UNTOUCHED (the standing monument)

`sjJointResolution` (`RouteMSJResolution.lean:803`) stays the single named analytic sorry. It did NOT
close this tide, and this is NOT a one-tide task. Closing it reduces (Module 1) to standalone
`RouteMBoxThresholdFinite M` for all `M`, whose only route is the full decorated recursion
(`decorated_peel_step` → `decorated_base` → well-founded recursion) — the explicit
**resolution-of-singularities chart-tree**, a **multi-module SIZE barrier (~65–75% genuinely-new
construction), NOT a math wall**. Confirmed convergently by: a fresh decorrelated Codex verdict
(`codex/scope-answer.md`, this thread), the prior scope-answer (`genm-sjcarrier4`), the design cert
(`genm-sjjoint-design`: at the binding cut `minAdm M = pq + minAdm(redChain t* M)` the residual exponent
EXACTLY saturates the reduced-chain IH threshold — Hölder-infeasible — so the strong `hIH` is
insufficient as a black box), the `RouteMSJFreedPeel` header (outer `(S,J)` descent unbuilt), and the
direct obstruction: regime-A shift `matBox_corank_residual_absZ_le` needs the deeper core `W z > 0`
STRICTLY, which fails on the vanishing / rank-deficient-`Q_b` locus, requiring further blow-up; and
`gen_rowMix`'s support-homogeneity `hsh` "does NOT hold for an arbitrary `R`", both deferred to the same
recursion.
