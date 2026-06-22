# Full-result spine audit — core → aoyagi headline (crux2, #40, 2026-06-22)

Audit of the assembly spine ABOVE the R1 core (`routeM_rlctAtOn_eq_lambdaCore`, reduced widths) up to the
hero headline `aoyagi_learning_coefficient` (general M). Done-vs-open + the conditional-assembly trace.
Decorrelation: crux2 audits/assembles the spine; does NOT co-produce fm3's `RouteMAtlas` (the geometry).

## The spine (Skeleton.lean) — rung-by-rung status

| Rung | Loc | Status | What it is |
|---|---|---|---|
| **T headline** `aoyagi_learning_coefficient` | 1505 | **PROVEN** | `⨅ optimalSet rlctAt = ofReal(aoyagiLambda H r)`. Body = `rw [deepest_point_reduction]; exact product_reduction`. |
| **D1** `deepest_point_reduction` | 988 | **PROVEN mod 1 sorry** | `⨅ optimalSet rlctAt = rlctAt (deepestPoint)`. `≤` proven (`iInf₂_le`, deepestPoint ∈ fibre); `≥` = `le_iInf₂` of the per-point obligation below. |
| **D1 ≥-leg** `rlctAt_deepest_le_of_optimal` | 978 | **sorry** | The fibre-monotonicity: `rlctAt(deepest) ≤ rlctAt(v)` ∀ optimal v. L2-gated (needs the homogeneous normal form). |
| **L2** `product_reduction` | 951 | **sorry** | `rlctAt (dlnLoss B) (deepest) = ofReal(aoyagiLambda H r)` = regular `[−r²+r(H⁰+Hᴸ)]/2` shift + singular core `lambdaCore` on `M = H−r`. |
| **R1 core** `resolution_charts` | 1017 | **sorry** | `rlctAtOn (dlnLoss M 0) (0:Params M) = ⨅ᵢ monomialThreshold (d i)(k i)(h i)`. ← crux2's `routeM_rlctAtOn_eq_iInf` (given RouteMAtlas) + the Params↔flat bridge. |
| **A1** `lambdaCore_eq_clean` | 4025 | **PROVEN** | `lambdaCore M = cleanCore` at the achiever (the `⨅=lambdaCore` value side; Karamata engine, green). |
| **A2** `aoyagiTheta_eq` | 1493 | **sorry** | `∃ … monomialOrder = aoyagiTheta`. The θ-count — **OFF the λ critical path** (secondary, seam-flagged). |
| **S2** `monomial_rlct` | 120 | **axiom** (cited) | The monomial-integral extraction (Aoyagi/Watanabe). The one allowed citation. |

**Critical path for the λ headline:** T ← D1 (+ `rlctAt_deepest_le_of_optimal`) ← L2 `product_reduction` ←
{R1 core `resolution_charts`, A1 `lambdaCore_eq_clean` (PROVEN), the `n/2` Fubini shift}. A2 `aoyagiTheta_eq`
is the θ count — NOT on the λ headline path (it's the separate order-count deliverable).

## Conditional assembly — GIVEN the core, does the headline compose?

YES, the chain assembles cleanly; the genuinely-open pieces are named + each has its machinery green:

1. **R1 core `resolution_charts`** ⟸ crux2's `routeM_rlctAtOn_eq_iInf` (PROVEN given a `RouteMAtlas`) +
   the `Params M ≃ₜ (Fin (flatDim M) → ℝ)` bridge. **The bridge is GREEN**: `paramsEquivFlat`
   (`ParamsFlat.lean:80`), measure-preserving (`measurePreserving_paramsEquivFlat`) + continuous both ways
   (`continuous_paramsEquivFlat`/`_symm`). So `rlctAtOn (dlnLoss M 0) (0:Params M)` transports to the flat
   core via `rlctAtOn_comp_homeomorph` (the lemma crux2 already used), and crux2's bridge gives `= ⨅`.
   **OPEN = the `RouteMAtlas` existence** (fm3's G1 geometry) — NOT crux2's; the only genuinely-open
   geometry on the critical path. Everything else here is green.

2. **`⨅ = ofReal(lambdaCore M)`** ⟸ A1 `lambdaCore_eq_clean` (PROVEN) folded through cover's
   `resolution_value_of_atlas` (S-min, rv3-blessed). Already bundled in crux2's
   `routeM_rlctAtOn_eq_lambdaCore` (#38). So R1 core + A1 give `rlctAtOn(core) 0 = ofReal(lambdaCore M)`.

3. **L2 `product_reduction`** ⟸ the core (step 1+2) + the regular `n/2` additive shift. **The shift is
   GREEN**: `rlct_additive_smooth_block` (`Skeleton:235`, `= n/2 + rlctAtOn(core)`, proven). The OPEN work
   in `product_reduction` is the WIRING: transport `dlnLoss H B` at the deepest point into the
   `(regular n/2 block) × (singular core dlnLoss M 0)` product form (the `B`-of-rank-`r` block-elimination
   `block_elimination` (L1, green) → the `n/2`-many regular generators + the `M = H−r` core), then
   `rlct_additive_smooth_block` + the core. Ingredients green; the assembly is the lift.

4. **D1 `rlctAt_deepest_le_of_optimal`** (the `≥` fibre-monotonicity) — OPEN, L2-gated (needs the
   homogeneous normal form `product_reduction` supplies, under which the deepest point's core pointwise
   dominates). Scoping question (Skeleton:978 docstring): provable from L1 `block_elimination` + deepest
   structure alone, or needs the resolution value? — a pp-hall/controller call.

## Net — what's open on the λ critical path (3 rungs), each with green machinery

- **`resolution_charts`** (R1 core): OPEN only on **fm3's `RouteMAtlas` existence**; crux2's bridge +
  `paramsEquivFlat` close the rest. The moment fm3's RouteMAtlas lands, this rung closes (crux2 wires it).
- **`product_reduction`** (L2): the `n/2`-shift + core wiring. Ingredients green (`rlct_additive_smooth_block`,
  `block_elimination`, `paramsEquivFlat`); needs the block-elimination → product-form lift.
- **`rlctAt_deepest_le_of_optimal`** (D1 ≥-leg): the fibre-monotonicity, L2-gated; a scoping call on its
  dependency.

A2 `aoyagiTheta_eq` (θ) is OFF the λ path — close it separately for the order-count deliverable.

So the headline `aoyagi_learning_coefficient` (PROVEN modulo these) assembles the moment the three
critical-path rungs close, and the deepest of them (R1 core) is one fm3-`RouteMAtlas` away. The spine
above the core is in good shape: headline proven-conditional, A1 + all the transport/shift machinery green,
the open rungs named with their (green) ingredients.

## Recommendation (parallel close, in crux2's lane vs others')
- crux2 (spine assembly, NOT fm3's geometry): once fm3's RouteMAtlas lands, WIRE `resolution_charts`
  (`routeM_rlctAtOn_eq_iInf` + `paramsEquivFlat` transport) — small, mine. THEN `product_reduction` (the
  `n/2`-shift + core product-form lift — the L2 wiring, mine to attempt; `block_elimination` is green L1).
- `rlctAt_deepest_le_of_optimal` (D1 ≥-leg) — needs the scoping call (L1+deepest vs resolution-value);
  flag to controller/pp-hall before attacking.
- A2 `aoyagiTheta_eq` — separate (θ count), off the λ headline.
