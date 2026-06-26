# R1 route adjudication — cover (A) vs squeeze (B) for `resolution_charts`

**Seat:** `pen-and-paper` (obstruction-leaning adjudication). **Date:** 2026-06-24.
**Gate:** R1 `resolution_charts` — `rlctAtOn(dlnLoss M 0)(0) = ⨅ᵢ monomialThreshold(dᵢ,kᵢ,hᵢ)`.
**Brief:** `theory/aoyagi-2023-reproduction/verify-r1-route-adjudication.md`.
**Method:** exact sympy (symbolic Schur identities, exact pullback orders), Newton-LP RLCT,
exact `minAdm` census, + one decorrelated `local-codex-consult` (gpt-5.5, xhigh; frame-in /
facts-in / hypothesis-out — my conclusion withheld). Artefacts: `/tmp/hnode_*.py`,
`/tmp/q2_assembly_trace.py`, `/tmp/q3_corank_census.py`; Codex prompt+answer in
`codex/squeeze-assembly-{prompt,answer}.md`.

---

## VERDICT (one line)

**Route B's `hnode` is SOUND-BUT-NARROW, not general-M: it is unprovable at corank-≥2 binding
branches (≈22% of 3-width vectors), where the rank-1 Schur cross term `bcol⊗Erow` cannot
represent the genuine rank-2 `Δ`-coupling.** Recommend **Route A (cover)** as the general-M
spine — its residual atoms are hard but *honestly general*; build **`hdiv` (the box-divergence
lower bound)** first, via the squeeze restricted to the achiever path as the value input.

---

## Q1 — is `hnode` provable for the general-M DLN loss? **NO (corank-≥2), YES (corank-≤1).**

`hnode` (`GeneralR1Recursion.lean:620-623`) asserts the per-node core is, near the deepest point,

    flatCore w = (∑_j w₁ⱼ²) + ∑_{i,j} (bcolᵢ · w₁ⱼ + SΓᵢⱼ)²,   G(w₂)² = ∑_{i,j} SΓᵢⱼ²,   ∑ᵢ bcolᵢ² ≤ T²

with `w₁` = the `nReg` regular coords (= the pivot-row product `Erow`), `bcol` a single pivot
COLUMN, `SΓ` the residual. The cross term `bcolᵢ·w₁ⱼ` is a **rank-1 outer product** `bcol⊗Erow`.

**Worked case A — the hard-1-pivot Schur (exact, `/tmp/hnode_structure.py`).** With ONE pivot
cleared (block `A₁ = 1×1 = 1`), the lower rows of the product factor EXACTLY as
`lowerᵢⱼ = bcolᵢ·Erowⱼ + (S·Γ)ᵢⱼ` (a `CommRing` identity — this is `schur_row_decomp`, banked).
So at a **corank-≤1 peel the cross term IS the rank-1 `bcol⊗Erow`** and `hnode` is faithful.

**Worked case B — `(2,2,2,2)` rank-1 peel, t=(1,0,0) (exact, `/tmp/hnode_2222_rank1.py`).** After
the layer-1 incidence chart + one blow-up of `{δ=u=v=0}`, `F = α²ρ²·U` with
`U = ‖[[ξ,η],[bξ+r,bη+s]]·C³‖²`. Exact: **`U` vanishes to order 4** at the deepest point — NOT a
unit. The residual is a *fresh `(2,2,2)` core*; the recursion must continue (it does not terminate
in one blow-up). For the rank-1 chain this fresh core IS a width-chain `(2,2,…)` loss, so `hnode`'s
`redCore_eq` (`G² = dlnLoss(redChain)`) can be honestly met node-by-node.

**Worked case C — `(3,3,4)`, the binding corank-2 obstruction (exact, `/tmp/hnode_geometry_careful.py`).**
The unique `minAdm`-achiever is `t=(1,0)`, `Mval=8`, true `rlct=4`. The layer-1 peel gives
`F ∼ ‖T‖² + ‖Δ·S‖²` with `T` a clean `1×4` row (the `nReg=4` regular coords, `nReg/2=2`) and `Δ`
a **FREE 2×2** residual block, `S` free `2×4`. The matrix product `Δ·S` is generically **rank 2**.
Two exact facts kill `hnode` here:

- The "extra" coupling beyond a smooth reduced core, `(Δ−I)·SC`, has `det ≢ 0` ⟹ **rank 2** —
  it is **NOT** a rank-1 `bcol⊗Erow` (`/tmp/hnode_structure.py`, Test B). The rank-1 cross term
  cannot represent it.
- If instead the whole `Δ·S` is pushed into `G²`, then `G² = ‖Δ·S‖²` is a **`(2,2,4)` PRODUCT
  singularity** (rlct 2 by a genuine radial resolution of a determinantal variety), whereas the
  recursion's reduced chain `redChain 1 (3,3,4) = (1,4)` is a **smooth 4-square leaf** (rlct 2 as
  a Morse block). `minAdm(1,4)=minAdm(2,2,4)=4` — the rlct **values coincide (2=2)** but the
  **germs are not measure-preservingly homeomorphic** (one is a smooth quadratic, the other a
  product singularity). So `redCore_eq` + `redEmbed` (a measure-preserving homeo onto
  `Params(redChain)`) **cannot be honestly discharged**. A value-correct `redEmbed` here would be
  exactly the forbidden degenerate fill (germ ≠ germ, only the number matches).

This is the *same boundary* the design certificates (`verify-r1-light-recursion.md`,
`verify-r1-diagb-334.md`, tasks #26-#30) already mapped: a per-row / threshold-only resolution
(which `hnode`'s rank-1 form IS) computes `3` at `(3,3,4)`, the true value is `4`. The obstruction
**binds** because `(3,3,4)`'s unique minimiser is corank-(2,2).

**Decorrelated Codex (gpt-5.5, xhigh) independently reached the identical verdict** (conclusion
withheld in the prompt): Q-A "No; at corank ≥ 2, hnode cannot honestly satisfy both the rank-1
Schur form and `redCore_eq`"; it caught the value-vs-germ distinction unprompted ("the shared RLCT
value 2 is only a value coincidence, not a measure-preserving germ identification"). No rubber
stamp — it constructed the rank argument from the setup.

**Scope (named by true content):** `hnode` holds **iff every binding peel has
`min(M₀−t, M₁−t) ≤ 1`** (Codex's sharpening of "corank ≤ 1": the residual block has at most one
free row or column, so no genuine ≥2×2 `Δ`). This covers the rank-1 chains `(2,2,…,2)`, the
`c₁=0` full-rank peels, and corank-1 partial drops like `(3,3,2,2)` `t=(2,1,0)`. It **excludes**
the RRR-type cores `(n,n,p)`, `n≥3` — `(3,3,4)`, `(2,2,4)`, `(3,4,5)`, … (census below).

---

## Q2 — is the squeeze-assembly a SOUND closure of `resolution_charts = ½·minAdm`?

**The connective shape (`/tmp/q2_assembly_trace.py`).** `resolution_charts`'s RHS is
`⨅ᵢ monomialThreshold` = a **min over leaves**; its value is already proven `= ½·minAdm`
(`routeLayerAtlas_value_eq_half_minAdm`, PROVEN). Route A's cover bridge
(`routeM_rlctAtOn_eq_iInf`) supplies BOTH inequalities (the upper via `cover_le` finiteness, the
lower via `cover_ge_div` divergence), reading the `⨅` off the leaf exponents.

Route B would instead compute `rlctAtOn` **directly and additively**:
`rlctAtOn(flatCore)(0,0) = nReg/2 + rlctAtOn(G²)(0)` per node. There is a *potential shortcut*:
if the squeeze computes `rlctAtOn(dlnLoss M 0)(0)` EXACTLY along the achiever decomposition
(`= ½·minAdm`), the gate closes by **transitivity** with the value lane
(`rlctAtOn = ½·minAdm = ⨅ monomialThreshold`), **bypassing `IsRouteMCover` entirely**. This is the
genuine attraction of Route B. But the closure has four named gaps:

- **GAP 1 (carrier re-home).** `GeneralR1Recursion` is on the *fixed-arity* `ChainDimSplit`
  carrier (`drop+red = M`, same arity); the gate routes through `LayerSplit` (`redChain t M =
  (t,M₂,…)`, **one fewer layer**). `RouteMLayerSplit`'s docstring + the `SOUNDNESS NOTE` record
  that the fixed-arity carrier *structurally cannot* express the layer-collapsing recursion (it
  was the documented sorry). So the per-node squeeze must be **fully re-homed** onto `LayerSplit`
  — not cosmetic.
- **GAP 2 (`redEmbed`).** The brief's hope `redEmbed := id` (taking `Y := Params S.red`) discharges
  the measure-preserving homeo *only* when `G² = dlnLoss(redChain)` holds as a germ — which is
  exactly what Q1 shows FAILS at corank-≥2 (the geometric reduced core is a product singularity,
  not the width-chain loss). So `redEmbed = id` is sound only on the corank-≤1 scope.
- **GAP 3 (the binding gap).** The transitivity shortcut needs the squeeze to compute `rlctAtOn`
  EXACTLY along the achiever — which requires `hnode` at EVERY achiever node. By Q1, the `(3,3,4)`
  achiever `t=(1,0)` HAS a corank-2 node; `hnode` is unprovable there. **This is the load-bearing
  gap, not a connective nicety.**
- **GAP 4 (the S2 analytic import — Codex Q-C).** Even on the corank-≤1 scope, the per-node step
  uses `rlct_additive_smooth_block` (S1.5 Fubini/smooth-block split — an analytic fact) and the
  recursion's *leaf* rlct must ultimately be a `monomialThreshold`, which needs `monomial_rlct`
  (the S2 citation). Codex Q-C: "squeeze proves equality of RLCTs under comparability; it does not
  compute singular RLCTs … any passage from `(dᵢ,kᵢ,hᵢ)` to `monomialThreshold` imports the
  normal-crossing monomial RLCT theorem." So Route B **does not avoid** the S2 import; it relocates
  it to the leaves. That is acceptable (S2's job) **provided it is not smuggled into `hnode`** —
  and `hnode` as written does not smuggle it (it asserts only the algebraic Schur form, no rlct
  value). The soundness gate is respected by the *interface*; the problem is that the interface is
  *false* at corank-≥2.

**Q2 verdict:** the squeeze-assembly is a **sound closure on the corank-≤1 sub-family** (rank-1
chains, `c₁=0` peels) — there `hnode` holds, `redEmbed=id` discharges, and transitivity with the
value lane closes the gate without the cover. It is **NOT a sound closure for general M**: GAP 3
(the corank-≥2 binding node) blocks it, and no honest `hnode` exists there.

---

## Q3 — net: which route, and the single load-bearing residual atom?

**Census (exact, `/tmp/q3_corank_census.py`).** Of 3-width vectors with widths 2..5: **14/64
(≈22%)** have ALL `minAdm`-achieving branches corank-≥2 (no clean reach) — e.g. `(2,2,4)`,
`(3,3,4)`, `(3,4,5)`, `(4,4,4)`. **50/64** are clean-reachable. So the corank-≥2 obstruction is
**not rare** — it is the whole RRR-core family `(n,n,p)`, `n≥3`. Route B's sound scope excludes
a substantial, structurally-natural slice of the headline's domain.

**Decisive consideration (the soundness gate).** The brief forbids a value-correct degenerate
fill and prefers an honest residual. Route B's `hnode`, pushed to general M, *is* that degenerate
fill at corank-≥2: a `redEmbed` that matches the rlct value while the germs differ. Route A's
atoms (`hfin`, `hdiv`) are GLOBAL and hard, but they are **honestly general-M** — the cover never
pretends to a per-node structure the loss lacks. **An honest hard atom beats a false easy one.**

**A crucial de-risking fact (`Case334RouteStep.lean`).** The **value lane is already sound
general-M** and sidesteps the corank obstruction entirely: the committed `RouteStep`/`PivotWitness`
datum reads `Mval M₀ T` from the *closed Aoyagi form* anchored at the ROOT — it does NOT re-derive
the per-row resolution, so `(3,3,4)` folds to the correct `4` (not the per-row `3`). The
obstruction bites **only the analytic `rlctAtOn = ⨅` content** — which is exactly the cover's two
atoms. So the residual is cleanly isolated to Route A's `hfin`/`hdiv`.

**RECOMMENDATION: build Route A (the cover), `hdiv` first.**

`hdiv` is the lower bound (`cover_ge_div`): for `c'` at-or-above a leaf threshold, the box integral
`∫_{cubeBox N ε} |routeMCore|^{−c'} = ⊤` for all `ε>0`. It is more tractable than `hfin`
(completeness/no-missing-strata, a global combinatorial cover) because it needs only **one
diverging leaf** (the achiever path), not a full cover. **The squeeze is the right instrument for
`hdiv`** — restricted to the achiever path it lower-bounds `rlctAtOn`, and the achiever-path
divergence transcribes to box-integral divergence. This is precisely the "squeeze-to-box-integral
bridge" the `RouteMLayerCover` header names as the open lower-bound content; the squeeze's
single-path additive computation is the *correct* shape for `cover_ge_div` (one leaf suffices),
whereas it was the *wrong* shape for the per-node `=⊤` over all branches.

### The single most load-bearing residual atom (precise statement)

**Atom `hdiv_achiever` — achiever-path box-integral divergence.** For the layer atlas of `M`, let
`i⋆ : (routeLayerAtlas M).ι` be the achiever leaf (`routeLayerAtlasAcc_achiever`, banked) with
`monomialThreshold (layerD M i⋆) (layerK M i⋆) (layerH M i⋆) = ½·minAdm M`. Then for every
`c' : NNReal` with `½·minAdm M ≤ (c':ℝ≥0∞)` and every `ε > 0`,

    ∫⁻ x in cubeBox (routeMAmbient M) ε, ENNReal.ofReal (|routeMCore M x| ^ (-(c':ℝ))) = ⊤.

This is the achiever specialization of `routeMLayerCover_of_atoms`'s `hdiv` hypothesis (which then
discharges `cover_ge_div` via `routeM_coverGeDiv_of_boxDiverges`, banked). Building it gives the
**lower bound** `rlctAtOn(routeMCore M) 0 ≤ ½·minAdm M`. Combined with the value lane and (the
separate) `hfin` upper bound, it closes the gate.

**Why this atom and not `hnode`:** `hdiv_achiever` needs the loss to *vanish fast enough along ONE
path* (the achiever) — a lower bound, robust to the corank coupling (the coupling only makes the
loss vanish FASTER, helping divergence). It does NOT need the per-node rank-1 Schur form, so it is
immune to the corank-≥2 obstruction that kills `hnode`. The squeeze's achiever-path computation
`rlctAtOn(achiever core) = ½·minAdm` (sound *as a single-path upper estimate* even where the
per-node `redCore_eq` germ-equality fails, because along the achiever the squeeze only needs the
SANDWICH inequality, not the reduced-loss germ identification) is the right driver.

---

## Soundness verdict (binding gate)

- The retracted measure-preserving-chart route stays retracted; **not** re-introduced.
- `hnode` as currently stated is **not** a degenerate fill *as an interface* (it asserts only the
  algebraic Schur form, importing no rlct value) — but it is **unsatisfiable at corank-≥2 binding
  branches**, so building the general-M recursion on it would force a degenerate `redEmbed` (germ ≠
  germ, value-only). That is the forbidden fill; the recommendation avoids it.
- The S2 monomial→RLCT extraction (`monomial_rlct`) is correctly the leaf citation in BOTH routes;
  it is **not** smuggled into `hnode`. Route B does not avoid it (Codex Q-C); Route A imports it via
  the bridge `routeM_rlctAtOn_eq_iInf` (already proven, axioms = the single S2 `monomial_rlct`).

## Scope, caveats, what would break this

- **Levels kept separate.** This adjudicates the *analytic* `rlctAtOn = ⨅` mechanism. The *value*
  `½·minAdm` is established (value lane) and is corank-robust (reads the closed `Mval` form). The
  `rlct = ½·codim` reading still rides the cited S2 bound — unchanged here.
- **Verified exact:** the hard-1-pivot rank-1 cross term (CommRing identity); the `(2,2,2,2)`
  order-4 residual; the `(3,3,4)` rank-2 `Δ·S` coupling + `det((Δ−I)·SC) ≢ 0`; the value-vs-germ
  split (`minAdm(1,4)=minAdm(2,2,4)=4`); the corank census (14/64).
- **Inference (structural):** that `hdiv_achiever` is strictly more tractable than `hnode`
  general-M and than `hfin`. The squeeze-to-box-integral bridge along the achiever is itself
  unbuilt — it is the recommended *next* construction, not yet a certificate.
- **The one thing most likely to break the recommendation:** if `hfin` (completeness) turns out to
  REQUIRE the same corank-≥2 chart structure that kills `hnode` (i.e. the "no missing strata"
  cover cannot be assembled without the coupled `diag(b)` charts), then Route A's *upper* bound is
  as hard as Route B's mechanism, and the honest move is to commit to Aoyagi's coupled `diag(b)`
  recursion (controller's prior Decision, option (ii)) as the chart producer for BOTH bounds. The
  next construction after `hdiv_achiever` should probe whether `hfin` is corank-sensitive.
