# routeStep dispatcher cert — the certified rank-pattern → RouteStep recipe + 3 correctness arguments (pp-hall, 2026-06-22, #68)

**The R1 combinatorial core**: the formalization-ready recipe for the single sorry `routeStep M : RouteStep M`
in fm3's `RouteMRecursion.lean`, generalizing the `(2,2,2)` hand-build (`Case222Resolution.lean`). The
target is fm3's CERTIFIED type (g161/g162 + Codex vacuity-trap): a raw `routeStep` with arbitrary splits is
**worse than `sorry`** (type-checks, terminates, encodes wrong combinatorics, no connection to `dlnLoss M 0`).
This cert pins the recipe AND the per-cell certificate fields (`ValidRouteStep`) so the three correctness
obligations — COVER, VALUE+CONSISTENCY, CODIM — are dischargeable, and names the load-bearing conditions
(decorrelated Codex confirmed each).

## §0 — the target (fm3's certified type, g162)
`routeStep : (M : Fin (L+1) → ℕ) → RouteStep M` with each `branch` cell carrying a `ValidRouteStep` certificate
(crux2's `schur_straighten_squeeze_of_data` consumed data: `nReg`, reduced ambient `Y`, `flatCore`, `G`,
`redEmbed : Y ≃ₜ Params S.red`, `c₁ c₂`, the `IsSchurStraightenSqueeze` datum, the node-loss identification,
the cover fact). The fold theorem (fm3) reconstructs `rlctAtOn (dlnLoss M 0) 0 = ⨅ᵢ monomialThreshold (dᵢ)(kᵢ)(hᵢ)`
from the certified branches; the value side feeds `RouteMState.foldDivisors`/`appendDivisor` (banked).

## §1 — the recipe (`classify M`): the dispatch logic
Read ranks **relative to the active prefix image** (#138 Fix 1). At node `M`:

1. **LEAF** — iff the residual core is a **UNIT** (Codex #5, the corrected condition; NOT "no C1 applies").
   Concretely: after the accumulated pivot monomials are factored out, the residual core ideal is a unit
   (`monomialThreshold = ⊤`, `leafMonoData`, `leafMonoData_threshold`). The Lean predicate is
   `Leaf → IsUnit residualCore`, carrying the unit certificate (`residual ≥ a > 0`, the `step2E_unit_ge_one`
   / `step3_unit_ge_one` shape). **This is load-bearing** (Codex #5): "no rank-defect coupling remains" is
   too weak — scalar/rank-1 remnants, post-C2 downstream products, and unresolved C4/C5 cores can be
   non-units misclassified as leaves, silently dropping a binding divisor.
2. else **separating** (a width-1 / rank-1 inner pinch, or forced `s=0`) → **C4** (Fubini product split, two
   children `leftState`/`rightState`, `L` drops). The C4-terminal proviso (empty-Schur/width-1 → C4, not C1)
   is the no-stall guard.
3. else on the active factor's rank on the incoming prefix image (`t_{s-1}`):
   - drops to coupled/0 → **C1** (blow up the rank-defect center, Schur-descend, recurse, `ΣM` drops by 2);
   - full rank `= t_{s-1}` (later-factor drop) → **C2** (pass-through, `L` drops);
   - partial `t_{s-1} > t_s > 0` → **C5** (block-column split: complement via C1, survivor via C2).
4. **C3** (NC-completion, `k ≥ 2` divisors) is a per-leaf `(d,k,h)` post-pass, NOT a tree node.

**C1 node mechanism** (triply-converged, g138/g140/g152/g153): `pivotBlowupOn active p` (core∘φ = x_p²·Q,
Jac `(x_p)^{card−1}`, `k=1` weight, `ΣM` unchanged) + the **det-1 triangular Schur peel** `w := D − ba`
(the #37 ΣM-2 drop, `measurePreserving_lemma2` / MP, no Jacobian) → `schurState M'` (`M'_0 = M_0−1`,
`M'_1 = M_1−1`, `M'_{s≥2} = M_s`) + recurse. Precondition `M_0, M_1 ≥ 2` (else width-1 → C4).

## §2 — THE LOAD-BEARING CONDITION (the C1-condition): codim = geometric codim = Mval, with an admissible witness
**This is the single seam that makes the dispatcher CERTIFIED vs green-but-wrong (Codex #1, #4, my #138).**
`pivotBlowupOn` only knows "blow up this coordinate subspace" — it does NOT know the subspace is the strict
transform of an admissible rank-pattern stratum. A type-checking dispatcher can record `c = card pivotCoords`
or a Jacobian/Hessian rank and get a divisor codim that is **not any admissible `Mval(T)`** (the `(4,3,2)`
thin-product trap). So **every C1/C5 pivot cell MUST carry**, in its `ValidRouteStep` certificate:
- a **rank-pattern witness** `T` with `Adm M T` (`Adm`/`Mval` from `RouteMState`/design-spec §3);
- a proof that the pivot center is the smooth strict-transform / normal slice of the rank-pattern stratum
  `S_T`, with the selected pivot coordinates a regular parameter system for its ideal, so
      **`codim(center) = height(S_T) = Mval(M, T)`**   (the geometric codim, NOT the raw Jacobian rank);
- a proof the exceptional multiplicity is exactly one pivot square: the axis is `(k,h) = (1, c−1)`,
  `c = Mval(M,T)` (ratio `c/2`), the `appendDivisor c` shape (`RouteMState.appendDivisor`).

This is the field the `ValidRouteStep` certificate threads (co-designed with fm3, g162): `codim : cells → ℕ`
must come paired with `witness : (c : cells) → {T // Adm M T ∧ codim c = Mval M T}` (and the multiplicity-1
proof), NOT a bare `ℕ`. **Without this, C≥ is unprovable** (Codex #2: a bogus axis — non-admissible T,
non-Mval codim, or an over-broad center creating a falsely small `c` — is the only way the cover `⨅` dips
below `minAdm/2`).

## §3 — the three correctness arguments

### (1) COVER — the cells cover the node locus
The pivot cells of `pivotBlowupOn active p` are its affine charts (`argmaxCellOn` cover + `aedisjoint`,
banked `g5_pivotNode`/`argmaxCellOn_cover`/`_aedisjoint`). Per-cell change-of-variables
(`node_loss_pivot_factor` + `node_jacobian_det` composed down the path) lands `monomial · unit` on
`chartDomOn [−1,1]^d`; normalization (signed box → bare-monomial `[0,1]^d`) via crux2's
`monomialIntegrand_abs_invariant` + `integrableOn_monomial_mul_unit_iff` (banked). The cover obligation is
`IsRouteMCover` (crux2's bridge consumer); the recursion glues child covers (each `S.red` recursion's cover
lifts through the parent chart). **Validated** `(2,2,2)`: the 8 unit leaves + 16 block leaves = 24 cells
cover the cube (`Case222Resolution`, `cover_le`/`cover_ge_div` route, the `phiUnit` binding leaf for `≤`).

### (2) VALUE + CONSISTENCY — the ⨅-min = aoyagiLambda AND matches fm3's foldDivisors achiever
The leaf threshold = `monomialThreshold (foldDivisors cs)` = `ratioMinFold cs` = `min over the path of c/2`
(`RouteMState.monomialThreshold_foldDivisors`, banked). The dispatcher's per-node codim contributions ARE
the `appendDivisor c` codims (§2: `c = Mval(M,T)`), so the leaf-monomials match fm3's `foldDivisors` achiever
exactly (obligation #2 satisfied **by construction**, since both fold the same per-node codims). Then:
- **(C≥)** `∀ i, ½·minAdm(Mval) ≤ monomialThreshold (dᵢ)(kᵢ)(hᵢ)`: every divisor codim is some `Mval(T) ≥
  minAdm` (§2 witness), so `ratioMinFold ≥ minAdm/2` (`monomialThreshold_appendDivisor_ge` /
  `ratioMinFold_ge_of_all_ge`, banked). **Holds ONLY given §2's certification** (Codex #2). The mult-control
  `m·k ≤ h+1` (`monomialThreshold_ge_of_mult'`, banked) is C3-robust (`k≥2` NC divisors:
  `k_E = Σk_i`, `h_E+1 = Σ(h_i+1)`, the ratio is a weighted average, cannot undershoot).
- **(C=∃)** `∃ i₀, monomialThreshold (dᵢ₀)(kᵢ₀)(hᵢ₀) = ½·minAdm(Mval)`: the achiever path `i₀` (pp2 g147/g148,
  delivered) resolves each factor to its `T*`-rank, the minimiser; its binding divisor has codim
  `= Mval(T*) = minAdm` (`monomialThreshold_appendDivisor_le_binding` / `_le_regularSeq`, banked). **Needs a
  reachability lemma** (Codex #3, see §4).
- `⨅ᵢ = ½·minAdm(Mval) = ofReal(lambdaCore M)` by `le_antisymm` (the `(S-min)` form, #134; replaces per-path
  `threshold_eq`). The achiever wiring is `of_mult_and_achiever` (g148/g154: `eq_half_of_binding` bundles the
  multi-axis `le_antisymm` at `j₀` + the within-chart mult-bound).

### (3) CODIM — per-node codims accumulate to C
Each C1/C5 node's `appendDivisor c` (`c = Mval(M,T)`) accumulates along the path
(`RouteMState.foldDivisors`); the cover's binding (minimal-codim) divisor controls the `⨅`. The total
geometric codim `C = minAdm(Mval)` is realized at the achiever path's binding divisor. (`C` the codim, `θ`
the component count, `rlct = ½·codim` are separate levels — this cert is the R1 chart `⨅`, the `½·codim`
reading rides the cited Aoyagi bound, NOT proved here.)

## §4 — the reachability obligation (C=∃, Codex #3 — name it, it's a theorem not a freebie)
"Resolve each factor to its `T*`-rank by iterated rank-defect blow-ups" is NOT automatic: it needs
**for every minimiser `T*`, a legal C1/C2/C4/C5 chart path whose transformed target stays admissible after
each peel/pass/split, with binding C1/C5 center exactly `S_{T*}` of codim `Mval(T*)`.** This is the
realizability seam (pp2 g147/g148): `T*` is realizable via `Core.OrbitKostant` / `Orbit.baseChange_normalForm`
(Gabriel normal form hits `T*`; `RealizableRank M = range rankFn`), and **only the minimiser need be reached**
(weaker than full `stratum_surjective`). The nodeC1/C5 branch at each step picks the `T*`-rank pivot cell.
**Validated** (g147): `(2,2,2)→T*=(1,0)` codim 3; `(3,2,3)→(1,0)` codim 5; `(2,2,2,2)→(1,0,0)` codim 3 (one
of 3 achievers — only one need be reached); `(4,3,2)→(2,0)` codim 6; `(2,1,2)→(1)` codim 1. No
forced counterexample to reachability if the route tree covers all admissible strata — but that COVERAGE IS A
THEOREM (the realizability lemma), not a consequence of termination.

## §5 — validation (the recipe is right on (2,2,2) + a second case + depth-3, not just (2,2,2))
QIP ground-truth (`g183_qip_minAdm.py`, exact): `minAdm(Mval)` and achievers —
| M | minAdm | λ=minAdm/2 | achiever T* | reached? |
|---|---|---|---|---|
| (2,2,2) | 3 | 3/2 | (1,0) | ✓ (codims {4,3}, binding 3) |
| (3,2,3) | 5 | 5/2 | (1,0) | ✓ (binding codim 5) |
| (2,2,2,2) | 3 | 3/2 | (1,0,0) [3 achievers] | ✓ (reach one) |
| (4,3,2) | 6 | 3 | (2,0) | ✓ (binding codim 6) |

`(2,2,2)` tree (`Case222Resolution`, the anchor): step-1 A-pivot `pivotBlowupOn {0,1,2,3} 0` card 4 =
`Mval(t=(0,0))=4` (ratio 2); Lemma-2 (det ±1, no divisor); step-2 `pivotBlowupOn {1,2,3} 1` card 3 =
`Mval(t=(1,0))=3` = **the achiever binding** (ratio 3/2); δ-branch step-3 card 4 (ratio 2). Binding leaf
codims `{4,3}` → `ratioMinFold = min(2, 3/2) = 3/2 = λ(2,2,2)` ✓; all 24 leaves give `3/2`
(`g179`/`g180`/`g181`). `(3,2,3)`, `(2,2,2,2)` (`g182`): rank-descent reaches the minimiser, C≥/C=∃ hold.

The codim-sequence reads as a **rank-descent**: each C1 node crosses one rank stratum, its divisor codim =
that stratum's `Mval`; the path traces `t_root → … → 0`; the MIN codim on the achiever path = `minAdm`. The
`(4,3,2)` trap is the witness that codim MUST be the geometric `Mval`, not the coordinate cardinality / raw
Jacobian rank (there they diverge — §2).

## §6 — what fm3 transcribes (the ValidRouteStep field list, co-designed)
`ValidRouteStep M step` per `branch` cell carries: `nReg`, reduced ambient `Y` + instances,
`flatCore`/`G`/`redEmbed`/`c₁ c₂`/`IsSchurStraightenSqueeze` (crux2's consumed data), the node-loss
identification (`flatCore = dlnLoss M 0` in blow-up coords), the cover fact, AND the §2 certification:
`witness : (c : cells) → {T // Adm M T ∧ codim c = Mval M T}` + the multiplicity-1 proof `(k,h)=(1,c−1)`.
LEAF carries `IsUnit residualCore` (§1.1). The generic fold theorem (fm3) reconstructs the `⨅`-identity from
the certified fields; the achiever (`of_mult_and_achiever`, pp2 g148) + threshold_ge supply VALUE; the cover
supplies COVER; the appendDivisor accumulation supplies CODIM.

## §7 — most likely thing to break this (the green-but-wrong risk, Codex #4)
**Computing `codim` from local coordinate cardinality / raw rank data instead of threading the admissible-`T`
witness + `codim = Mval`.** It type-checks, terminates, passes small symmetric tests `(2,2,2)`/`(3,3,3)`, and
FAILS thin/mixed cases `(4,3,2)`. The guard: `codim` is NOT a bare `ℕ` field — it is paired with the
admissible-rank-pattern witness and the `codim = Mval` proof (§2). The second risk: LEAF as "no C1 applies"
(must be `IsUnit residualCore`, §1.1). The third: C=∃ reachability assumed instead of proved (§4) — it rides
`Core.baseChange_normalForm`, the realizability seam. All three are NAMED `ValidRouteStep` obligations here,
not silent assumptions.

## §8 — decorrelation
pp-hall exact algebra (`g183_qip_minAdm.py` the QIP ground-truth; `g179`/`g180`/`g181` the (2,2,2) trace +
codim=Mval reading; `g182` the depth-3 reachability) + decorrelated Codex (gpt-5.x xhigh,
`g183-dispatcher-codex-answer.md`) — CONVERGED on the load-bearing C1-condition (codim=Mval, not Jacobian
rank — Codex #1/#4 = my #138 C1-condition, independently re-found) and SHARPENED three obligations: the
admissible-`T` witness on every pivot (§2), the reachability lemma for C=∃ (§4), and the `IsUnit residualCore`
LEAF condition (§1.1). Builds on #26/g138 (the node taxonomy), g147/g148 (the achiever i₀, re-spelled in
fm3's encoding), `Case222Resolution` (the (2,2,2) anchor), `RouteMState` (the value-side foldDivisors,
banked), fm3 g161/g162 (the certified-not-raw type + the co-design). No Lean — fm3 transcribes against §6.

---

## VALUE-TARGET (#68 follow, pp-hall, 2026-06-22) — fm3's machine-checked contract (a)+(b) → foldFamily_* (the two conditions, named)

fm3 banked (`@bef5ba5`, `RouteMState.lean`, green) the consistency contract as TWO checkable conditions on
the dispatcher's per-leaf codim-lists `codimsOf : ι → List ℕ` (the exceptional-divisor `Mval`-codims along
each path, §VALUE-CONSISTENCY — NOT the `nReg` smooth dims, which are spectators / the additive transport).
Let `m₀ = (Adm M).inf' Mval` (`lambdaCore M = ½·m₀`):
- **(a) NO path undershoots:** `∀ i, ∀ c ∈ codimsOf i, m₀ ≤ c`  ⟹  `foldFamily_threshold_ge` (the C≥ atlas fact);
- **(b) the minimiser realises m₀:** the min-stratum leaf `i₀` has `(∀ c ∈ codimsOf i₀, m₀ ≤ c) ∧ m₀ ∈ codimsOf i₀`
  ⟹  `foldFamily_achiever` (the C=∃ atlas fact).

`(a)+(b)` ⟹ `IsResolutionAtlas` (threshold_ge + achiever) ⟹ `⨅ᵢ monomialThreshold = lambdaCore`, via fm3's
banked `foldDivisors` lemmas. **The dispatcher's leaf monomials then AGREE with the value-side BY
CONSTRUCTION — no separate consistency proof.** These two ARE this cert's VALUE+CONSISTENCY obligation, in
fm3's exact names:
- **(a) = §2** (the C1-condition): every pivot codim is a geometric codim `= Mval(T)`, hence `≥ minAdm = m₀`
  by definition of the min. The §2 `witness : {T // Adm M T ∧ codim = Mval M T}` field discharges (a)
  directly — every `codimsOf i` entry is some `Mval(T) ≥ m₀`. **No path can undershoot precisely because
  the codim is the geometric `Mval`, not the coordinate cardinality** (the green-≠-right guard, §7).
- **(b) = §4** (the achiever reachability): the path resolving to the minimiser `T*` crosses `S_{T*}`, whose
  pivot codim is `Mval(T*) = m₀`, so `m₀ ∈ codimsOf i₀`. The reachability lemma (rides
  `Core.baseChange_normalForm`; only the minimiser need be reached) discharges (b).

**Verified `(a)+(b)` on all validation cases** (`g186_foldFamily_contract.py`): `(2,2,2)` m₀=3
[Case222: unit-leaf `codimsOf=[4,3]`, block `[4,3,4]`; all ≥3, 3∈[4,3] ✓]; `(3,2,3)` m₀=5; `(2,2,2,2)` m₀=3;
`(4,3,2)` m₀=6 [`Mval` set {6,8,12}, all ≥6 ✓ — the thin-product case where (a) needs codim=Mval, not
cardinality]; `(2,3,2)` m₀=4; `(3,3,3)` m₀=7. The `(2,2,2)` `codimsOf` reproduces Case222Resolution's
step-1(card4)/step-2(card3)/step-3(card4) exactly.

So the cert's value-target is literally `foldFamily_threshold_ge` (needs (a) = §2 witness) +
`foldFamily_achiever` (needs (b) = §4 reachability). fm3 builds the certified `RouteStep` type + the generic
fold against these names; the dispatcher populates `codimsOf` with the `Mval`-witnessed codims; (a)+(b) hold
by §2/§4; `⨅ = lambdaCore` follows. The additive `nReg/2` (per-cell transport, `schur_recursion_step`)
stays separate from this min-fold value — it justifies each cell's split factorises the loss (cover_le), not
the leaf-codim value.

---

## DATUM-WEIGHT CORRECTION (#68 follow, pp-hall, 2026-06-22) — R1's per-cell datum is the LIGHT monomial pullback, NOT the heavy IsSchurStraightenSqueeze

**§6 over-specified the per-cell datum as crux2's heavy additive `IsSchurStraightenSqueeze`. fm3's numerics
caught it (controller-relayed): R1's per-cell consequence is the LIGHT monomial pullback, MIN-folded — the
heavy squeeze is the OFF-PATH / L2 datum, not R1's blow-up node.** The combinatorial recipe + codim-design
(§1, §2, §4, §VALUE-TARGET) are datum-weight-INDEPENDENT — unchanged; only §6's datum field corrects.

**The light per-cell datum (verified, `g188_light_datum.py`):** a C1/C5 node is `pivotBlowupOn active p`,
whose G2 factorization (`node_loss_pivot_factor`, fm3 banked) gives
    `core ∘ φ = x_p² · (core ∘ hardPivotAt)`,    Jacobian `(x_p)^{card−1}` (`node_jacobian_det`).
So on the chart the pulled-back integrand is `|x_p|^{2·(−c)} · |x_p|^{card−1} · |reduced∘φ|^{−c}` — a
`monomialIntegrand` on the `x_p` axis (`k=1`, `h=card−1`, ratio `card/2 = codim/2`) times the reduced
pullback. The per-cell rlct = `MIN(codim/2, rlct(reduced))`, recursing → the `foldDivisors` MIN-fold. **NO
squeeze constants `c₁ < c₂`, NO additive `nReg/2`.** The per-cell DATUM field is just
`node_loss_pivot_factor` (the `x_p²·reduced` monomial pullback) + `node_jacobian_det` (the `(x_p)^{card−1}`
Jacobian) — both fm3's banked G2, light.

**Why §6's heavy datum was wrong (the additive/min confound, sharpened):**
- **LIGHT (R1 core, this dispatcher):** `pivotBlowupOn` monomial pullback `x_p²·reduced`, MIN-folded
  (`foldDivisors`). Datum = `node_loss_pivot_factor` + `node_jacobian_det`. This is what the (2,2,2) leaves
  use (`Case222`: `myF222_step1A` = `y0²·Q`, `step1A_det` = `y0³` — monomial, not a squeeze).
- **HEAVY (off-path / L2):** `IsSchurStraightenSqueeze` (`c₁Φ ≤ flatCore ≤ c₂Φ`, additive `nReg/2 +
  rlctAtOn(reduced)`). This is the DEEPEST-GAUGE chart / L2 regular-shift datum (the g150/g175
  `core_comparability_squeeze`, #54) — a DIFFERENT node (the full-B reduction, the regular `n/2` shift),
  NOT R1's blow-up node. §6 conflated the two.

**The corrected §6 datum field** (pending crux2's precise lemma confirmation): per branch cell carries the
LIGHT monomial-pullback witness — `node_loss_pivot_factor` (`core∘φ = x_p²·(core∘hardPivotAt)`) +
`node_jacobian_det` (`(x_p)^{card−1}`) + the cover fact + the `codim = Mval(M,T)` witness (§2, unchanged).
The reduced core recurses (the `red = schurState M'`). NO `IsSchurStraightenSqueeze` / `c₁ c₂` / additive
`nReg/2` on R1's path — that bundle is the L2 datum. (If crux2 confirms a residual additive piece at some
node type, it's a thin wrapper; the value MIN-folds regardless, §VALUE-TARGET unchanged.)

**Datum-weight-independent content (build-now, unchanged):** §1 (the classify recipe), §2 (the
`codim = Mval` witness, the C1-condition), §4 (the achiever reachability), §VALUE-TARGET (the (a)+(b) →
`foldFamily_*` contract). These are the actual combinatorial content; they hold whether the per-cell datum
is the light pullback or (off-path) the heavy squeeze. The datum field is a thin wrapper either way —
likely the light `node_loss_pivot_factor` for R1.

---

## TRANSCRIPTION-READY (#68 final, pp-hall, 2026-06-22) — fm3's exact types confirmed; the witnessed-codim form + the banked bridges

fm3 sent the concrete types (RouteMRecursion.lean working tree + RouteMState.lean banked); g183/g187/g188
already designed against them. Final tightening (fm3's ask): pin the witnessed-codim form + the exact
banked bridge names + flag the transport-field as crux2-pending.

**The codim field is the witnessed form (fm3 confirmed §2 is the target).** The current
`codim : cells → ℕ` (in `RouteStep.branch`) is the STUB; the certified `ValidRouteStep` carries

    witness : (c : cells) → { T : Fin L → ℕ // T ∈ Adm M ∧ codim c = (Mval M T).toNat }    (+ the mult-1 proof (k,h)=(1, codim−1)).

Note `(Mval M T).toNat`: `Mval : … → ℤ`, but `Mval M T ≥ 0` on `T ∈ Adm M` (each summand
`(t_{j-1}−t_j)(M_j−t_j) ≥ 0` by admissibility — weakly-decreasing `t` and `t_j ≤ M_j`; verified
`g189_mval_nonneg.py` across (2,2,2)/(3,2,3)/(2,2,2,2)/(4,3,2)/(2,3,2)/(3,3,3)/(2,1,2)/(3,1,3)/(4,4,4)),
so `.toNat` is faithful. **Design every per-cell `codim c` as `(Mval M T).toNat` for an admissible `T`** —
which §2 already mandates.

**The VALUE+CONSISTENCY obligation maps to fm3's EXACT banked bridges (cleaner than §VALUE-TARGET's (a)+(b)):**
- **(C≥)** `foldFamily_threshold_ge_of_admWitness`: IF every leaf's codims are `(Mval M T).toNat` with
  `T ∈ Adm M`, THEN every leaf threshold `≥ ½·minAdm`. **The §2 witness feeds this DIRECTLY** — no
  separate "all codims ≥ m₀" step; the admissible-`T` witness IS the hypothesis. (Uses `minAdm_le_Mval_toNat`:
  `T ∈ Adm ⟹ minAdm ≤ (Mval M T).toNat` — the no-undershoot, automatic, banked.)
- **(C=∃)** `foldFamily_achiever` / `monomialThreshold_foldDivisors_eq_of_binding`: the minimiser path `i₀`
  has `minAdm ∈ codimsOf i₀` (the §4 reachability: it crosses `S_{T*}`, `Mval(T*) = minAdm`).
- `(C≥) + (C=∃) ⟹ IsResolutionAtlas ⟹ ⨅ = lambdaCore` (`= ½·minAdm`). BY CONSTRUCTION — no separate
  consistency proof, once `codimsOf` carries the `(Mval M T).toNat` witnessed codims.

So obligation #2 (VALUE+CONSISTENCY) is discharged by: design `codimsOf i = [(Mval M T_node).toNat : node
along path i]` (§2 witness per node) + the achiever reaches `T*` (§4). The two banked bridges
(`foldFamily_threshold_ge_of_admWitness`, `foldFamily_achiever`) then deliver `IsResolutionAtlas` with NO
new lemma. This is the transcription target.

**The per-cell TRANSPORT field is crux2-pending (the light/heavy fork, g188).** fm3's g164 independently
found (converging with my g188): the `(2,2,2)` leaf is min-fold/monomial, NOT additive `+nReg/2`, so the
heavy `IsSchurStraightenSqueeze` (additive) is likely OFF-PATH; R1's per-cell transport is the LIGHT G2
`node_loss_pivot_factor` (`core∘φ = x_p²·(core∘hardPivotAt)`) + `rlctAtOn_reduced_transport`. **The
transport-field's exact shape (light G2 vs heavy squeeze) is the ONE thing pending crux2's lemma-mapping
confirmation** — but it is the analytic WRAPPER, it does NOT change the recipe / codims / the 3 correctness
arguments. Design the combinatorics (done: §1 recipe + §2 witnessed codims + §3/§4 args + the foldFamily
value-target); the transport-field is a thin wrapper, likely the light pullback.

**FIRM (design to these):** `ChainDimSplit` (drop/red/hsum/hdrops, `L` fixed, `red = M'`); `M : Fin(L+1)→ℕ`
(reduced widths, `T : Fin L → ℕ` the rank pattern, `T ∈ Adm M`); `MonoData`/`appendDivisor (1,c−1)`/
`foldDivisors`; the value-side achiever + the family/§2 bridges. **MOVING:** `codim : cells → ℕ` →
codim + §2 witness (the `(Mval M T).toNat` form). **crux2-PENDING:** the transport-field (light G2 vs heavy
squeeze) — wrapper only.

**Transcription-ready.** §1 (recipe), §2 (witnessed `(Mval M T).toNat` codim), §4 (reachability), the
foldFamily value-target, the (2,2,2)/(3,2,3)/(4,3,2) validation, the light-datum (g188). The dispatcher
populates `codimsOf` with `(Mval M T).toNat` witnessed codims; `foldFamily_threshold_ge_of_admWitness` +
`foldFamily_achiever` deliver the value; the light G2 transport (crux2-confirm) wraps each cell. No open
combinatorial question.

---

## C5 REDUCTION EXERCISED (#68 follow, pp-hall, 2026-06-22) — the mixed partial-drop node reduces to main-Schur, NO new lemma

**crux2's fast-veto question (via fm3): does the C5 mixed partial-drop node (`t_{s-1} > t_s > 0`) reduce to
the main coupled-rank-defect Schur node, or need a distinct existence lemma?** §1.3/§4 read as "C5 reduces"
(block-column split: complement via C1, survivor via C2) — but the §5 validation set
(2,2,2)/(3,2,3)/(2,2,2,2)/(4,3,2) has NO genuine partial-drop (all full-rank-to-coupled C1 or thin C4). So
"C5 reduces" was DESIGN-only. **EXERCISED now (g191/g192/g193_c5_schur_present.py):** the answer is **C5
REDUCES to main-Schur on the complement, NO new lemma.**

**The genuine partial-drop:** `M = (3,3,2)`, stratum `T = (2,0)` (`tt = (3,2,0)`, partial-drop
`t_0 = 3 > t_1 = 2 > 0` at `s=1`). `C1 : 3×3` rank-2 at the basepoint, `C2 : 3×2`, core `‖C1·C2‖²`. The
block-column split:
- **SURVIVOR** (rows 0,1 of `C1 ≈ I_2`, the rank-`t_1 = 2` block): `P_0, P_1` have independent linear parts
  in `b` (`b0,b1,b2,b3`) — **4 SMOOTH regular generators = the `∑Erow²` block** (the C2 pass-through). Straighten
  them (solve `{E=0}` for `b0..b3`).
- **COMPLEMENT** (row 2, `C1`'s rank-defect row, the rank-`(t_0−t_1) = 1` drop): `P_2` has ZERO linear part.
  On `{E=0}` (survivor straightened), `P_2 = (S·b4, S·b5)` where
      `S = a8 − a6·(survivor)⁻¹·(coupling0) − a7·(survivor)⁻¹·(coupling1)`
  — **exactly the per-layer Schur complement `T − Z(I+X)⁻¹Y`** (`T = a8`, the complement corner; the g172
  `S_s` object). Leading term `a8·(b4,b5)` — a single coupled rank-1 defect (pivot `a8`, coupling `(b4,b5)`).

So the complement residual `= ‖S·Γ‖²` with `S` the Schur complement, `Γ = (b4,b5)` — the **CLEAN main-Schur
hnode form** `flatCore = ∑Erow² + ‖S·Γ‖²`, `G² = ‖S·Γ‖²`. crux2's `schur_straighten_squeeze_exists` applies
to the complement's C1 (a single coupled-rank-defect node, pivot `a8`). **C5 = C2-survivor (rows 0,1) ⊕
C1-complement (row 2, main-Schur). NO distinct existence lemma.** ✓

**HONEST CAVEAT (the scope of the exercise):** this exercises the MINIMAL genuine partial-drop — ONE
partial-drop step, complement rank 1. The multi-partial-drop cases (`(3,3,2,2,2)` `T=(3,2,1,0)` with
partial-drops at steps 2,3; crux2's depth-6 `t=(3,3,2,2,2,0)`) compose the SAME reduction ITERATIVELY (each
partial-drop step = one C2-survivor ⊕ C1-complement, recursing on the survivor's later kill-layer) — NOT yet
run explicitly. The single-step per-node reduction (the thing crux2's existence lemma consumes) IS exercised
+ clean; the iteration over multiple partial-drop steps is design (the recursion applies the same node op
per step). If a multi-step exercise is wanted, run `(3,3,2,2,2)`. But the per-node C5 reduction — each
partial-drop step's complement presents as a clean main-Schur node — is exercised, closing crux2's
transport-field question: the transport datum for every node type (C1, C2, C5-complement) is the SAME
`schur_straighten_squeeze_exists` / light G2 monomial pullback; C5 needs no new lemma.
