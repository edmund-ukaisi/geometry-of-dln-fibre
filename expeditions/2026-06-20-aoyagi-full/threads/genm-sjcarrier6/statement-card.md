# Statement card — `genm-sjcarrier6` (R1-UPPER Phase-2 piece 2-rest: the Schur-split weld)

Thread: `genm-sjcarrier6` (formalisation tide). Branch: pushed to `genm-sjcarrier6` (off
`expedition/aoyagi-full` @ `8ffe1ed4`). Module:
`lean/DLNFibre/DLN/RLCT/Validate/RouteMSJChartWeld.lean`.

This tide welds the banked pointwise **Schur block split** (`frobSq_schur_toBlocks_split`,
`RouteMSJChartAlgebra`) onto the banked **block-reindex transport** (`chartInner_blockReindex_eq_of_emb`,
`RouteMSJBlockReindex`, thread `genm-sjcarrier5`). The output: the raw front-factor chart integral (the
inner fibre of `gammaPeelIntegral`) equals the cross-coupled Schur block integral over the chart, with
the corank block `Γ` **exposed inside the integrand**. `sjJointResolution`
(`RouteMSJResolution.lean:803`) is **UNTOUCHED** (still the named sorry). Honest-partial multi-tide
progress: mission item 1 (the weld) lands; items 2 (the `(S,J)` descent) and 3 (the `redChain t` IH
wiring) do NOT land — they are the documented ~65–75% genuinely-new construction (the outer
`A'`-integral), reported precisely below.

---

> **Claim 1 (pointwise — the block loss IS the cross-coupled Schur loss, `⁻¹` form).** For a
> block-indexed front factor `M' : Matrix (Fin t ⊕ Fin a) (Fin t ⊕ Fin b) ℝ` whose pivot block
> `M'.toBlocks₁₁` is a unit, `frobSq (M' * Q) = schurLoss M' Q`, where `schurLoss` is the pivot energy
> `frobSq (P·Q̃ₚ')` plus the corank energy `frobSq (C·Q̃ₚ' + Γ·Q_b)`,
> `P = M'.toBlocks₁₁`, `C = M'.toBlocks₂₁`, `Γ = M'.toBlocks₂₂ − C·P⁻¹·M'.toBlocks₁₂`,
> `Q̃ₚ' = Q.submatrix Sum.inl id + P⁻¹·M'.toBlocks₁₂·Q.submatrix Sum.inr id`.
>
> - **Lean:** `DLNFibre.DLN.RLCT.frobSq_schur_split_inv` (+ the def `schurLoss`).
> - **Gloss.** On the chart the banked `⅟`-form Schur split (`frobSq_schur_toBlocks_split`) reads in
>   `Matrix.inv` (`⁻¹`) form, so the loss is a plain function of `M'` (no per-point `Invertible` instance)
>   — the form a `lintegral` integrand can take.
> - **Proved.** The equality, via `IsUnit.invertible` (the instance) + `invOf_eq_nonsing_inv` (`⅟ = ⁻¹`)
>   + unfolding `schurCompl`.
> - **Assumed / Cited / Deferred.** none.
> - **Status.** sorry-free (clean-three `[propext, Classical.choice, Quot.sound]`).

> **Claim 2 (measurability of the chart domain).** `genBox α β T` (finite index) and
> `{B | IsUnit (Matrix.toBlocks₁₁ B)}` are measurable.
>
> - **Lean:** `DLNFibre.DLN.RLCT.measurableSet_genBox` (finite intersection of `Icc`-preimages),
>   `DLNFibre.DLN.RLCT.measurableSet_isUnit_toBlocks₁₁` (preimage of `{0}ᶜ` under the continuous
>   `B ↦ det B.toBlocks₁₁`, via `Matrix.isUnit_iff_isUnit_det` + `isUnit_iff_ne_zero`).
> - **Proved.** Both, unconditionally.
> - **Status.** sorry-free (clean-three).

> **Claim 3 (the Schur-split chart-integral rewrite, abstract block level).** Over
> `genBox ∩ {IsUnit toBlocks₁₁}`,
> `∫⁻ B, ofReal (frobSq (Matrix.of B · Q̃))^{−c'} = ∫⁻ B, ofReal (schurLoss (Matrix.of B) Q̃)^{−c'}`.
>
> - **Lean:** `DLNFibre.DLN.RLCT.chartInner_schurSplit_eq` (`setLIntegral_congr_fun` on the measurable
>   chart domain, pointwise `frobSq_schur_split_inv`).
> - **Status.** sorry-free (clean-three).

> **Claim 4 (the composed weld — the RAW chart integral IS the Schur block integral).** For an arbitrary
> `t`-element `(ρ, κ)` pivot and a fixed tail product `Q`,
> `∫⁻ A₀ in matBox p n T ∩ pivotChart ρ κ, ofReal (frobSq (rmatMul A₀ Q))^{−c'}`
> `= ∫⁻ B in genBox (Fin t ⊕ Fin (p−t)) (Fin t ⊕ Fin (n−t)) T ∩ {B | IsUnit (toBlocks₁₁ B)},`
> `    ofReal (schurLoss (Matrix.of B) (Q.submatrix (blockSplitEquiv κ).symm.symm id))^{−c'}`.
>
> - **Lean:** `DLNFibre.DLN.RLCT.chartInner_schurWeld_eq_of_emb`
>   (composes `chartInner_blockReindex_eq_of_emb` (transport) + `chartInner_schurSplit_eq` (split)).
> - **Gloss.** This is the inner fibre of `gammaPeelIntegral M t ρ κ c'` (with `p = M₀`, `n = M₁`,
>   `q = M(last)`, `Q = prod (tailChain M) A'`): the corank block
>   `Γ = B.toBlocks₂₂ − B.toBlocks₂₁·(B.toBlocks₁₁)⁻¹·B.toBlocks₁₂` is now EXPOSED inside the integrand,
>   the shape the shear + corank radial peel integrate. Stated abstractly (on the chart integral, NOT on
>   `gammaPeelIntegral`) so it is upstream-usable — a future `RouteMSJResolution` imports this module and
>   rewrites the inner integral of `gammaPeelIntegral` via `lintegral_congr` in `A'`.
> - **Assumed / Cited / Deferred.** none (all four claims are unconditional).
> - **Status.** sorry-free (clean-three, forced `#print axioms` confirmed for all five load-bearing
>   results).

---

## What is NOT closed (the standing mountain — reported precisely)

`sjJointResolution` is **UNTOUCHED**. The Schur form is EXPOSED but not yet INTEGRATED. The precise
remaining items, in dependency order:

1. **The shear `D ↦ Γ`** — decompose the `genBox` integral over the block coordinates `(P, B₁₂, C, Γ)`
   (a Fubini + `measurePreserving_shearSub`), freeing `Γ` as a variable over its shear-image domain.
2. **The corank radial peel of `Γ`** — `corankBlock_morsePeel_lt_top` (`RouteMSJCorankPeel`, banked)
   integrates the freed `Γ`, contributing the Gram Jacobian `det(Q_b Q_bᵀ)^{−p/2}` and the exponent
   shift `c' ↦ c' − pq/2`. **BLOCKER: it requires the deeper core strictly positive (`w > 0`)** — the
   pivot energy `frobSq (P·Q̃ₚ')` can vanish, so `w > 0` is NOT available at the front factor alone. The
   positivity is supplied by the OUTER tail-parameter `A'`-integral.
3. **The `(S,J)` `Nat`-measure descent of the OUTER `A'`-integral** to the monomial terminal
   (`sjLoss_terminal_lintegral_lt_top`, `RouteMSJLedger`, banked), carrying the accumulated Gram residual
   and the shifted core through the `SJLinGenState` carrier (`gen_rowMix_const` block-elim + `loss_radialStep`
   radial, `RouteMSJLinGen`, banked), wiring the reduced coupling to the strong IH (`redChain t M`,
   `RouteMLayerSplit`). This is the ~65–75% genuinely-new construction (decorrelated-Codex-scoped in
   `genm-sjcarrier4/codex`); no pointwise brick shortcuts it. The subordination `sjSubordination`
   (`a/2 ≤ ½·minAdm(tailChain M)`) keeps the coupling exponents at or below threshold.

The `(a)`-BOUNDED verdict is robust; the barrier is SIZE (this descent is genuinely a multi-module build).

## Build / hygiene

- Isolated module force-recompiled green (`touch` + `scripts/lb DLNFibre.DLN.RLCT.Validate.RouteMSJChartWeld`,
  8.6 s, fresh — not a first-exit-0 stale-cache artifact).
- Forced `#print axioms` (olean-bypassing scratch importer) on all five load-bearing results
  (`frobSq_schur_split_inv`, `chartInner_schurSplit_eq`, `chartInner_schurWeld_eq_of_emb`,
  `measurableSet_genBox`, `measurableSet_isUnit_toBlocks₁₁`): `[propext, Classical.choice, Quot.sound]` —
  clean-three, no `sorryAx`, S2-free (no `monomial_rlct`).
- Wired into the worktree aggregator `DLNFibre.lean` (import at end, after `RouteMSJBlockReindex`);
  `rg` name-clash scan against siblings: 0 clashes. Controller wires the same import into the integration
  checkout's `DLNFibre.lean`.
- `scripts/sorries`: 20 sorry / 0 #exit / 0 native_decide / 1 axiom — **unchanged from baseline**
  (this tide adds a sorry-free module; `sjJointResolution` untouched).
- LoC: +~150 (`RouteMSJChartWeld.lean`) + aggregator import.
