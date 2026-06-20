# synthesis.md — Aoyagi-Full controller's integrative read

(Internal ledger; assumes repo context. Flushed every tick; read on re-ground. Not a deliverable.)

## Current read (2026-06-20): CONTRACT IS BEDROCK — structural-proof phase OPEN

`rv-2` delivered the **BEDROCK** verdict on the contract (`Skeleton.lean` @86eb0a9, headline @a4d00e1):
green-gate green (`lake build DLNFibre`, 2851 jobs), 13 sorry / 1 axiom, headline assembles, `#print axioms`
= `[propext, sorryAx, Classical.choice, Quot.sound]`, **S2 (`monomial_rlct`) the only cited line and it does
NOT leak into the headline**. All 6 statement bugs the green build had hidden are fixed; `deepestPoint` is
honest (geometric `IsDeepLayers` choice — never mentions `rlctAt`, so D1 is a genuine claim; real provable
existence obligation; sound `Classical.choice` route). The one residual is A2's weak existential (accepted
**secondary θ-seam**, see below) — not a regression.

→ The bedrock gate is cleared. The structural-proof phase is dispatched (below).

## Structural-phase dispatch (2026-06-20) — 3 tracks, collision-free by file ownership

The 10 rung sorries all live in **Skeleton.lean**; only the measure infra (`ParamsFlat.lean`) and the
(1,1,1) bridge (`Case111*.lean`) are split out — and Skeleton does NOT import those. So:

- **MEASURE track — `fm-2` [thread 15]**, owns `ParamsFlat.lean` + `Case111*.lean`:
  - U1 (keystone): `paramsEquivFlat : Params H ≃ᵐ (Fin N → ℝ)` (Route A++: banked `measurePreserving_piCurry`
    + scoped `letI` fiber instance + `.comp`; correct the stale "not rfl-equal" docstring — it IS `rfl`).
  - U2: close the (1,1,1) bridge `case111_rlct_eq_monomialThreshold` (#13) → first fully axiom-free+sorry-free
    end-to-end. Unblocks S1.1's use-site.
- **ALGEBRA track — `fm` [thread 14]**, owns `Skeleton.lean` (measure-free rungs only):
  - A1 `lambdaCore_eq_clean` + `clean_eq_printed` (pure arithmetic; balanced-split min + finite ℚ identity,
    rv-2-verified 9324 cases) → L1 `block_elimination` (block/Schur normal form) → `deepestPoint_exists`
    (r=0 origin; general r consumes L1's factorization; feasible under hB:B.rank=r alone).
- **DESIGN track — `pp` [thread 16]** (read-only): design R1 (the mountain) — explicit blow-up charts,
  monomial exponents (k,h), cover, R1↔Adm match (via the proven `codim S(t)=Mval`), decorrelated Codex —
  so R1 is formalise-ready when paramsEquivFlat lands.
- **`rv-2`** decorrelated standby: per-rung honesty audit as each closes green (statement unchanged, no
  cheat/vacuity, axioms clean). I green-gate + commit + push, THEN ping rv-2 with target + SHA.

Build discipline: module-scoped builds during iteration (`lake build DLNFibre.DLN.RLCT.<Module>`); controller
runs full `lake build DLNFibre` at commit; controller is sole committer. Per-rung Skeleton split done
opportunistically when a proof gets heavy (the build-time lesson), not big-bang now (avoids disturbing the
just-certified contract; the import-ordering around deepestPoint deserves care, not a phase-boundary scramble).

## Tracked obligations / open scope decisions

- **A2 / θ-order — deferred tightening, NOT dropped.** `aoyagiTheta_eq` is still the weak existential
  (dischargeable by d=1,ℓ=0,a=0). Tighten to bedrock by binding its `(d,k,h)` data to R1's resolution
  geometry — downstream of R1. λ (the headline) does not depend on A2.
- **θ-scope question (resolve when tightening A2):** the order routes through S2's order-half (the
  meromorphic pole-order, scoped to `∃j kⱼ≠0`). Whether that sits inside the operator's "only cite that the
  normal-crossing form gives the RLCT statement" boundary depends on reading "RLCT statement" as Watanabe's
  full (λ AND multiplicity) theorem vs λ-only. Flag, don't block.

## WIN — λ-citation ELIMINABLE (banked @22f5dfe)
Monomial threshold-half directly provable from Mathlib (Fubini + `intervalIntegral.integrableOn_Ioo_rpow_iff`);
demonstrated axiom-free for (1,1,1). General = labour, no wall. So λ can beat the one-citation target; only
the θ-order-half stays the genuine analytic seam.

## Measure-side architecture — DECIDED: ROUTE A++ (pp, 10 compiled probes + Codex)
Matrix-instance wall is NOT systemic — paid ONCE + contained by interface discipline. `Params.volume` = nested
`Measure.pi` is **rfl**; fiber instance = scoped one-line `letI` inside `paramsEquivFlat` (not a global Matrix
instance); banked `piCurry` covers per-layer + across-layers (no 2nd gap); downstream (S1.1, bridge, R1) state
measure facts on `Fin N → ℝ` and pull back via `integrableOn_comp_preimage` — never re-touch Matrix.

## Rung map (scoped, post-bedrock)
- Measure-free, ready now: **A1, L1, deepestPoint_exists** (fm, thread 14).
- Keystone infra: **paramsEquivFlat** (fm-2) → unblocks (1,1,1) bridge (#13/#12), S1.1 use-site, R1 measure facts.
- Measure-dependent (after paramsEquivFlat): **S1.1** transport (heavy) + S1.3/S1.4 + **S1.5** smooth-block;
  **L2** (needs L1+S1.5); **D1** `deepest_point_reduction` (needs S1 monotonicity); **R1** (the mountain;
  pp designing now, thread 16).
- Assembly: **T** `aoyagi_learning_coefficient` already assembles from D1+L2 (headline proven modulo those two).
- Two hard Lean builds remain: S1.1 + R1.

## Next tick
Process whichever lands first: a "module green" from `fm` (A1) or `fm-2` (paramsEquivFlat). On each: pull,
full green-gate, commit+push, ping `rv-2` to audit, update synthesis. On `pp`'s R1 design: read it, decide the
R1 formalisation plan (and whether to extract R1 into its own file). Watch for collision reports (shouldn't
happen — disjoint files). Keep rv-2 decorrelated. Don't stop in a blocked state (hero-task autonomy).
