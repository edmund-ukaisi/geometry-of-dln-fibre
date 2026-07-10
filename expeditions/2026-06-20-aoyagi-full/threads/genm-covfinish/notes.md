# genm-covfinish — CoV transport finish + the (S,J) recursion contract

Target handed off: close `sjJointResolution` (`RouteMSJResolution.lean:803`),
`gammaPeelIntegral M t ρ κ c' < ⊤` for `c' < minAdm M / 2`, given box-finiteness for every
one-shorter chain (`hIH`). Base `5d276748` (all covmount ck1-9 banked).

## VERDICT (grounded + decorrelated Codex xhigh): 803 is the unbuilt (S,J) recursion, NOT labour

The covmount handoff framed the remaining work as "labour, no wall" via transport + good/deeper cover
+ `hIH`. That is **over-scoped**. Three independent findings:

1. **The naive fibre route fails the threshold.** Bounding the pivot chart by the full box and running
   the banked fibre engine (`fibre_lintegral_mul_le`) caps at `c' < M₀/2`, but `minAdm M > M₀` in 417
   of the L=3..5 width-≤4 chains (e.g. `M=(1,2,2)`: `minAdm=2`, `M₀=1`). The pivot chart is essential —
   discarding it loses the threshold room. So the peel genuinely needs the Schur reduction, not fibres.

2. **The banked endpoint closes only the "good" (dimensionally-cooperative) branch.**
   `sjGoodChartLoss_endpoint_lt_top` (and `sjGoodMap_loss_matBox_lt_top`) require the pivot `P`
   LEFT-invertible (always, on the chart) AND the corank map `W : (M₁−t)×M₂` and the deep factor
   `A₂ : M₂×M_last` BOTH RIGHT-invertible. Right-invertibility of `W`, `A₂` is dimensionally
   IMPOSSIBLE when `M₁−t > M₂` or `M₂ > M_last` (more rows than columns → no full row rank), and on a
   positive-measure rank-deficient set otherwise. `RouteMSJGoodLoss`'s own docstring: the multi-block
   `E_T` (L ≥ 4) case is "DEFERRED to the recursion assembly."

3. **The deeper (rank-deficient) branch does NOT close via `hIH` on a shorter chain.** After the corank
   Γ-blowup (`corankBlock_morsePeel_eq`, needs `Q_b Q_bᵀ` PosDef = full row rank), the OUTER
   tail-parameter `A'`-integral carries the **anisotropic Gram weight** `det(Q_b Q_bᵀ)^{−(M₀−t)/2}`
   times a shifted core. That is NOT a plain `routeMLayerBoxIntegral` of a shorter chain — the Gram
   weight blows up exactly on the rank-deficient locus, which is where `hIH` is needed. `sjChargeBudget_le`
   is a threshold INEQUALITY (`minAdm M ≤ (M₀−t)(M₁−t) + minAdm(redChain t M)`), NOT the analytic
   reduction. `RouteMSJCorankPeel`: "discharge the OUTER A'-integral carrying the Gram residual
   det(Q_bQ_bᵀ)^{−p/2} and the shifted core — that is the (S,J) double induction, the standing gap."
   `RouteMSJDecorated`: "the full well-founded recursion discharging sjJointResolution ... is ~65-75%
   genuinely-new, UNBANKED, multi-tide ... sjJointResolution stays the single named analytic sorry,
   UNTOUCHED, until the recursion genuinely lands." Codex (xhigh, decorrelated): "None — it is the
   recursion. The missing mechanism is a rank-stratified Schur/fibre recursion for the decorated
   residual integral, i.e. the (S,J) engine itself."

This is Aoyagi's ESTABLISHED mathematics (§5, the (S,J) simultaneous resolution) — substantial
multi-tide LABOUR to formalise, not a research wall. The controller adjudicates & commissions.

## Why a bare-inequality contract is CIRCULAR (justifies the decorated structure)

A tempting contract is `gammaPeelIntegral M t ρ κ c' ≤ ∑ᵢ Cᵢ · routeMLayerBoxIntegral (M'ᵢ) dᵢ 1` with
each `M'ᵢ` strictly shorter and `dᵢ < minAdm(M'ᵢ)/2`. Proving `803` from it is one line (`ENNReal`
sum/mul finiteness + `hIH`). **But this contract is circular**: if `gammaPeelIntegral < ⊤`, one can
always pick a shorter `M'`, small `d`, and `C = gammaPeelIntegral / routeMLayerBoxIntegral M' d 1`
(finite, positive) to satisfy `≤`. So the bare inequality is EQUIVALENT to `gammaPeelIntegral < ⊤`
itself — it carries no reduction content. This is exactly why the codebase encodes the contract as an
inductive DECORATED PREDICATE (a structured CoV), not an inequality.

## THE CRISP CONTRACT (already encoded — name the one missing lemma)

The contract skeleton is `RouteMSJDecorated`, sorry-free and validated:

- **`SJDecoration M`** — the buildable decorated carrier: `SJLinGenState` (shared-divisor support +
  linear residual) + accumulated Jacobian-exponent `jac` + deeper-param domain. Faithful (NOT a
  detached `Wπ(u)·frobSq` weight; the anisotropy `Γ·Q_b` lives in the carrier).
- **`SJDecoration.integral D c'`** = `∫_{dom} ∫_{unitBox d} (∏ℓ |uℓ|^{jacℓ}) · (decLoss u z)^{−c'}`.
- **`DecoratedBoxThresholdFinite D`** := `∀ c' < carrierThreshold M (= ½·minAdm M), D.integral c' < ⊤`.
- **`decoratedBoxThresholdFinite_trivial_iff` (PROVED)**: `DecoratedBoxThresholdFinite (trivial M) ↔
  RouteMBoxThresholdFinite M`. So the decorated recursion, once it lands
  `DecoratedBoxThresholdFinite (trivial M)`, delivers `RouteMBoxThresholdFinite M` with NO residual gap
  — bypassing the sjBoundaryPeel/sjJointResolution decomposition entirely (both are alternative routes
  to the same `RouteMBoxThresholdFinite M`).
- **`SJDecoration.radialAttach` (PROVED, the (b) radial half)**: prepend a fully-shared exceptional
  divisor (`d↦d+1`, `carrier↦radialStep`, `jac↦Fin.cons j₀`); multiplies `decLoss` by `u₀²`.

**THE ONE UNBUILT ANALYTIC LEMMA + the recursion (the whole gap):**

1. **`decorated_peel_step`** (named, unbuilt): the full single decorated peel =
   (a) **clear-first scalar Schur elimination** `rowMix R` at constant support — carries the chart's
       analytic matrix `R = P⁻¹B` (the `radialAttach` above is only the (b) radial half; this (a) half
       with `rowMix R` is the deferred analytic content);
   (b) `radialAttach` (built);
   (c) **block split + regime A/B** (INCLUDING the `c' = pq/2` boundary ε-argument), reducing the
       decoration on `M` to a decoration on `redChain u M` (strictly shorter) at threshold shifted by
       `½·peelCharge M u`, soundly (banked cast `carrierThreshold_shift`:
       `carrierThreshold M − ½·peelCharge M u ≤ carrierThreshold (redChain u M)`).
2. **The well-founded recursion**: descend the decoration's remaining chain (finite, strictly shorter
   each `decorated_peel_step`) to the pure-monomial terminal (`terminal_monomial_mul_unit_lintegral_lt_top`,
   banked), yielding `DecoratedBoxThresholdFinite (trivial M)` ∀M. The Gram weight
   `det(Q_bQ_bᵀ)^{−p/2}` of finding (3) is ABSORBED into the decoration's shared-divisor support (never
   materialised as a detached weight) — that is the design point of the carrier.

Kill-condition for the contract being genuine (not vacuous): `decorated_peel_step` must land the
reduced decoration at threshold `carrierThreshold M − ½·peelCharge`, and `carrierThreshold_shift`
(banked, 0/171) certifies that stays below `carrierThreshold (redChain u M)`.

## What this tide BANKED (sorry-free, clean-three `[propext, Classical.choice, Quot.sound]`)

Transport bedrock for the complementary ENDPOINT route's good branch (reusable regardless of route):

- **`RouteMSJRowSplit.lean`** — transport step (b), the ONLY un-banked transport atom from covmount:
  - `rowSplitEquiv κ n` : MP `(Fin m → Fin n → ℝ) ≃ᵐ (Fin t → Fin n → ℝ) × (Fin (m−t) → Fin n → ℝ)`
    (row-reindex by `blockSplitEquiv κ`, then `sumPiEquivProdPi`), `measurePreserving_rowSplitEquiv`,
    `rowSplitEquiv_reindex` (reassembly = row-reindexed matrix), `rowSplitEquiv_preimage_box`.
  - `rowSplit_lintegral_eq`: `∫_{U∈matBox m n 1} F(fun I => U(blockSplitEquiv κ I))
      = ∫_{(Upiv,W)∈matBox t n 1 ×ˢ matBox (m−t) n 1} F(Sum.elim Upiv W)`.
- **`RouteMSJTransport.lean`** — transport step (a), fully composed:
  - `eFrontTail_symm_zero`: leading tail layer of the Pi-split reassembly = first factor.
  - `gammaPeelIntegral_piSplit_eq` (EQUALITY): `gammaPeelIntegral M t ρ κ c'` = the triple integral with
    `A'` split into leading layer `p.1` + deeper `p.2`, deep factor `= sjDeepFactorCore M p.2`
    (`A'0`-independent), front factor `= p.1.submatrix (blockSplitEquiv κ) id`. Pure `lintegral_congr`
    under the MP Pi-split; no measurability.

Together with the banked step (c) `sjGoodChartLoss_pivotRows_translate_eq` (covmount) and the banked
endpoints (`sjGoodChartLoss_endpoint_lt_top`, `corner_block_lt_top_of_pos`), the ENDPOINT route's
transport is complete at the atom level. The remaining GOOD-BRANCH assembly (iterated row-split via
`setLIntegral_prod` + Tonelli reorder to bring `Upiv` innermost + the pivot→v translation + δ-good cover
+ uniform ball-domination bound) is BOUNDED plumbing — but it closes only the good branch; the deeper
branch is the recursion above. `sjJointResolution` (803) LEFT UNTOUCHED (its sorry, as all prior threads).

## Files
- `lean/DLNFibre/DLN/RLCT/Validate/RouteMSJRowSplit.lean` (step b, clean-three)
- `lean/DLNFibre/DLN/RLCT/Validate/RouteMSJTransport.lean` (step a composed, clean-three)
- `codex/scope-{prompt,answer}.md` (decorrelated recursion verdict)
