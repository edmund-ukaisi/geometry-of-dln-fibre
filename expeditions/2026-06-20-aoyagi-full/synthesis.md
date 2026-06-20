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

## R1 design BANKED (pp, thread 14) + R3b DECISION

pp mapped the mountain (`threads/14-r1-design/r1-design.md`; decorrelated Codex, one correction adopted).
- **Value/atlas split.** Separate the RLCT VALUE from the explicit CHART ATLAS the statement names.
  - VALUE: `rlctAt(‖∏C‖²) = ½·min_t Mval(t)`, pinned by codim S(t)=Mval (thread-03, proven gen-L) +
    {∏C=0}=⋃S(t) + the per-branch binding divisor (residual-block center, codim Mval). No chart enumeration
    needed for the value.
  - ATLAS (ι,φᵢ,k,h): Aoyagi's iterated affine blow-ups (coordinate-subspace; explicit substitutions).
- **Codex correction (adopted, bedrock-sharpening):** prefix-stratum partition is right for the VALUE but
  TOO COARSE for a literal atlas — center {rank≤t} is singular along {rank≤t−1}; the smooth resolution
  refines strata by the FULL rank-pattern r_{ab}=rank(C^a···C^b), not just prefix ranks. ⇒ "each minimizing
  chart ↔ one prefix stratum" is TOO STRONG; the R1↔Adm match is VALUE-level only (min-chart-ratio = ½ min
  Mval). Corrects design-spec §9.3 + thread-03 (pp patching as wind-down).
- **Lean-tractability reversal (adopted):** Aoyagi's affine recursion is the MOST tractable atlas (vs
  flag/quiver determinantal-resolution + SNC — far heavier). Anti-treadmill-safe: value from §3-codim, NOT
  the bookkeeping.
- **Binding-divisor mechanism (reusable core, verified; pp self-corrected its own "telescoping" framing):**
  the divisor-ratio lemma — smooth codim-c center ⇒ F (sum of squares) vanishes to order 2 ⇒ k=1, Jacobian
  u^{c−1} ⇒ h=c−1, ratio c/2 — applies to the BINDING divisor per branch: after the regular pivot split
  exposes the RESIDUAL BLOCK (whose vanishing IS the stratum S(t)), ONE blow-up of that residual-block-zero
  center (codim EXACTLY Mval(t)) gives the binding divisor (k,h)=(1, Mval(t)−1), ratio ½·Mval(t). NOT
  per-rank-drop telescoping — that gives ½·min(cᵢ) = TOO SMALL ((2,2,2) t=1: min(1,2)/2=1/2≠λ=3/2). The
  `Mval = Σ rank-drop codims` is the codim ARITHMETIC; geometrically it is ONE codim-Mval binding center per
  branch. min over branches = ½·min_t Mval = λ. (2,2,2) verified: binding divisor ρ (residual {δ=u=v=0})
  codim-3-in-one-step, (k,h)=(1,2)→3/2=λ.
- **No hidden hypotheses** (Codex §4): char-0 auto, positive widths, r≤min M⁽ˢ⁾ from hB; no genericity, no
  width inequality. Frobenius → any PD form. Toric/Newton route DEAD (Codex torus-zero counterexample).

**DECISION (controller, within standing authority): R3b — self-contained, one-citation.** R3a (cite
Lehalleur–Rimányi `rlct=codim/2`, arXiv:2411.19920) is OUT: violates (1) the one-citation scope (codim is
THE new content, must be PROVEN) AND (2) the Aoyagi-independence constraint. No operator gate (R3b is the
default); surfaced to operator as informational, override-able. R1's value PROVEN via atlas + telescoping + S2.

**R1 formalisation ladder (pp):** 1. (1,1,1) [=fm-2 bridge #12]. 2. divisor-ratio lemma (reusable core).
3. codim S(t)=Mval (thread-03). 4. atlas (Aoyagi affine branches) + assembly [THE mountain, general-L].
5. cover. Steps 1–3 tractable+reusable; step 4 is the heavy lift; small cases = validation gate.

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
