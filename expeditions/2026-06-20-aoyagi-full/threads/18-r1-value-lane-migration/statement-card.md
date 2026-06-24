# Statement card — R1 value-lane migration onto the layer-collapsing atlas (#18)

The R1 value/recursion lane migrated off the fixed-arity `ChainDimSplit`/`routeStep` carrier (whose
general `branch` arm is the documented `sorry` in `RouteMRecursion.lean`) onto the prior tide's PROVEN
layer-collapsing atlas `routeLayerAtlas`. PARALLEL migration (approach (a)): the old inductive is
untouched; this thread exposes the layer atlas's chart family in the `(ι, d, k, h)`-tuple shape
`routeM_rlctAtOn_eq_iInf`/`resolution_charts` consume, and re-points the value lane onto it.

Module: `lean/DLNFibre/DLN/RLCT/Validate/RouteMLayerValue.lean` @ `26124397` (worktree branch
`r1-migration-layersplit`, off `expedition/aoyagi-full` @ `8afeedc0`). NOT yet wired into the
single-writer aggregator `DLNFibre.lean` — controller integration step.

---

## The orthogonality finding (the scope decision, Codex-confirmed)

`resolution_charts` is `rlctAtOn(core) = ⨅ monomialThreshold`. Its VALUE (`= ½·minAdm = lambdaCore`) is
this lane; its `rlctAtOn = ⨅` equality is the ANALYTIC COVER — the two measure-theoretic legs of
`IsRouteMCover` (`cover_le` finiteness, `cover_ge_div` divergence). The two lanes are ORTHOGONAL: the
value lane carries no measure-theoretic information about the loss, so it CANNOT close the gate. A
decorrelated Codex consult (xhigh) confirmed: the only path that would close `resolution_charts` from
the value alone is an independent `rlctAtOn(core) = ofReal(lambdaCore)` identity or a general
`IsRouteMCover`-from-`routeLayerAtlas` — neither exists; both need the unbuilt cover analysis. So this
thread delivers the value lane sorry-free + the gate REDUCED to exactly the layer-family cover; it does
NOT close `resolution_charts` (which stays a `sorry`, blocked on the separate cover lane #104).

## 1. `routeLayerAtlas_isResolutionAtlas` — the layer atlas IS a resolution atlas (sorry-FREE)

> **Claim.** For a non-degenerate chain (`1 ≤ minAdm M`), the layer-collapsing chart family
> `routeLayerAtlas M` satisfies the two `IsResolutionAtlas` value clauses: every leaf threshold is
> `≥ ½·minAdm M` (no undershoot) and some leaf achieves `= ½·minAdm M` (no over-estimate).

- **Lean:** `theorem routeLayerAtlas_isResolutionAtlas (M : Fin (L+1) → ℕ) (hpos : 1 ≤ minAdm M) :`
  `IsResolutionAtlas M (routeLayerAtlas M).ι (layerD M) (layerK M) (layerH M)`
- **Gloss.** `layerD/layerK/layerH` are the per-leaf `(d, k, h)` accessors of the atlas's
  `data : ι → MonoData`. `threshold_ge` chains the banked `routeLayerAtlasAcc_leaf_singleton` (each
  leaf's single divisor `≥ minAdm`) + `monomialThreshold_singleton` (`= c/2`); `achiever` uses the
  banked `routeLayerAtlasAcc_achiever` (the path-min is attained) + `layerLeafMin M 0 = minAdm M`.
- **Proved.** Both clauses, sorry-free, from the prior tide's layer-recursion lemmas. `ι` is genuinely
  `Nonempty` (`instNonemptyLayerIota`, lifted from the atlas field) — NOT a vacuous atlas over empty `ι`.
- **Assumed.** `hpos : 1 ≤ minAdm M` (non-degeneracy; the threshold is finite only off the `minAdm = 0`
  leaf). The `m₀ = ((Adm M).inf' Mval).toNat` of `IsResolutionAtlas` is `minAdm M` definitionally.
- **Cited.** S2 (`monomial_rlct`) — via `monomialThreshold_singleton`. `#print axioms` =
  `[propext, Classical.choice, Quot.sound, monomial_rlct]`, NO `sorryAx`.
- **Deferred.** none (this lane is complete).
- **Status.** sorry-free + reviewed.

## 2. `routeLayerAtlas_value_eq_lambdaCore` — the migrated value (sorry-FREE)

> **Claim.** The `⨅` over the layer-collapsing chart family of the per-leaf `monomialThreshold` equals
> `ofReal(lambdaCore M)` (the singular-core RLCT value), for `1 ≤ minAdm M`.

- **Lean:** `theorem routeLayerAtlas_value_eq_lambdaCore (M) (hpos : 1 ≤ minAdm M) :`
  `(⨅ i : (routeLayerAtlas M).ι, monomialThreshold (layerD M i) (layerK M i) (layerH M i))`
  `= ENNReal.ofReal (lambdaCore M : ℝ)`
  (also `_eq_half_minAdm`: the same value as `(minAdm M : ℝ≥0∞)/2`.)
- **Gloss.** `resolution_value_of_atlas ∘ routeLayerAtlas_isResolutionAtlas`; `lambdaCore = ½·minAdm`.
- **Proved.** The value, sorry-free. Replaces the `sorryAx`-tainted `routeMGeneralValue`/`routeM_value_eq`
  (which fold over `routeMIota M`, whose value reduces through the open `routeStep` branch).
- **Cited.** S2 (`monomial_rlct`). NO `sorryAx`.
- **Status.** sorry-free + reviewed.

## 3. `resolution_charts_of_layerCover` — the gate reduced to the layer-family cover (sorry-FREE)

> **Claim.** GIVEN an `IsRouteMCover` for the flat core over the bounded box with the layer atlas's
> chart family, the `resolution_charts` existential holds.

- **Lean:** `theorem resolution_charts_of_layerCover (M)`
  `(hcover : IsRouteMCover (routeMCore M) (routeMBaseNbhd M) (routeLayerAtlas M).ι`
  `  (layerD M) (layerK M) (layerH M)) :`
  `∃ (ι : Type) (_ : Fintype ι) (d : ι → ℕ) (k h : (i : ι) → Fin (d i) → ℕ),`
  `  rlctAtOn (fun A : Params M => dlnLoss M 0 A) (fun _ => 0) = ⨅ i, monomialThreshold (d i)(k i)(h i)`
- **Gloss.** The conclusion is verbatim the `resolution_charts` gate body. Proof:
  `routeM_rlctAtOn_eq_iInf` (the proven bridge) ∘ `rlctAtOn_routeMCore_transport` (flat ↔ params,
  measure-preserving). The chart family is `routeLayerAtlas`'s `(ι, layerD, layerK, layerH)`.
- **Proved.** The CONDITIONAL reduction: the gate holds once the layer-family cover is supplied.
  Reviewer-confirmed the conclusion matches the gate body exactly (same LHS/RHS).
- **Assumed.** `hcover` — a genuine, un-discharged `IsRouteMCover` (its two legs `cover_le`/`cover_ge_div`
  are measure-theoretic facts about the actual loss, NOT vacuously true; the only repo instance,
  `isRouteMCover_222`, is keyed to a different family `F=myF222, ι=Fin 1, d=8`, so it does NOT discharge
  `hcover` even at `(2,2,2)`).
- **Cited.** none — `#print axioms` = `[propext, Classical.choice, Quot.sound]` (clean-three, NO
  `sorryAx`, NO `monomial_rlct`): the reduction is pure cover-plumbing; the S2 citation enters only when
  the cover (or the value `⨅ = ½·minAdm`) is asserted.
- **Deferred (the SEPARATE cover lane, NOT done).** the general-`M` `IsRouteMCover` over the layer
  family — the analytic blow-up/Jacobian cover (#104, only `(2,2,2)` hand-built). This is what closes
  `resolution_charts`; it is out of scope for this thread (the 2nd lane). The reduction PINS this
  residual to the exact `(ι, d, k, h)` the cover proof must target (anti-interface-drift, Codex-flagged).
- **Status.** sorry-free + reviewed (the reduction); the gate `resolution_charts` itself stays a `sorry`.

## 4. `routeLayerAtlas_value_eq_lambdaCore_M222` — non-vacuity anchor (sorry-FREE)

> **Claim.** The migrated value lane folds `(2,2,2)` to `3/2` (`= ½·minAdm(2,2,2) = lambdaCore(2,2,2)`).

- **Lean:** `theorem routeLayerAtlas_value_eq_lambdaCore_M222 : (⨅ i, monomialThreshold (layerD ![2,2,2] i)`
  `(layerK ![2,2,2] i) (layerH ![2,2,2] i)) = 3 / 2`
- **Proved.** The concrete fold (via `_eq_half_minAdm` + `minAdm ![2,2,2] = 3` by `decide`). Non-vacuity
  witness shown in-file. **Cited.** S2 (`monomial_rlct`).
- **Status.** sorry-free + reviewed.

---

## Review verdict — SURVIVED (fidelity, 2026-06-24)

Independent reviewer (decorrelated Codex): **SURVIVED** on all five fidelity checks. (1) the
`IsResolutionAtlas` instance is non-vacuous, both clauses honestly derived, `ι` genuinely nonempty;
(2) the value is correct (`lambdaCore = ½·minAdm`) and sorry-free; (3a) `resolution_charts_of_layerCover`'s
conclusion is verbatim the gate body; (3b) `hcover` is a load-bearing, genuinely un-dischargeable residual
(the cover's `cover_ge_div` premise is not vacuous; `cover_le`'s `C < ⊤` cannot be smuggled; the only
repo `IsRouteMCover` is keyed to a different family); (3c) it does NOT close `resolution_charts` itself.
Axiom prints machine-confirmed the Proved/Cited/Deferred split. Prior-tide results unchanged
(`minAdmRec_eq_minAdm` clean-three, `routeLayerAtlas_value` + monomial_rlct); full `DLNFibre` build green
(3707 jobs). Codex independently judged the reduction a genuine conditional, not a disguised non-result.

## Fidelity notes

- **No fabrication (trap-iii clean).** The value lane is sorry-free (only `monomial_rlct`); the gate
  reduction is clean-three. The residual is the cover hypothesis, named and un-discharged — NOT smuggled.
- **Anti-drift.** The chart family is exposed in the exact `(ι, d, k, h)` shape the bridge consumes, so
  the future cover proof plugs in with zero interface drift (the explicit Codex directive).
- **Approach (a) PARALLEL chosen over (b) IN-PLACE.** The old `RouteStep.branch`/`routeStep`/`routeAtlas`
  (`ChainDimSplit`-indexed) are untouched — re-pointing their index types to `LayerSplit` would break the
  ~17 consumers, while the value lane consumes `routeLayerAtlas` directly with no consumer breakage. The
  old machinery is not in the aggregator green-gate; deprecating it is a later step.
