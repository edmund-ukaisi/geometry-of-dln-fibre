# Cert — the stranded-divisor dichotomy (analytic vs full ledger at reachable terminals)

*Seat: `pen-and-paper` (pnp-fold, adjudication), follow-up charge. Adjudicates which of STRONG / WEAK /
FALSE holds for the geometric fold's full ledger vs `leafOfState`'s analytic (t̃=0) ledger at every
`conOracle`-reachable-from-`conRoot` terminal. Exhaustive simulation of the actual FIX-A recursion +
a hand-verified minimal witness. Decorrelated Codex leg (`codex/stranded-dichotomy-{prompt,answer}.md`).
Pinned to `leafOfState`/`t0Indices`/`ConState.divTilde`/`leaf_mem_Adm_single` (`EngineConstruction.lean`),
`LeafData` (analytic `numDiv`/`divExp`/`divCoord` vs full `fullNumDiv`/`fullDivExp`/`fullDivProfile`,
`ResolutionTree.lean:133-173`), `geoAtlas_fold_det` (`GeoLeafJacobian.lean:39`), and this thread's
`cert-ledger-accumulation.md` (whose §1 headline this cert CORRECTS).*

---

## VERDICT: **FALSE.** A reachable terminal routinely carries a stranded (t̃>0) divisor with `divExp > 1`.

The STRONG form (`(t0Indices s).length = s.numDiv` — no stranding) and the WEAK form (every stranded
divisor has `divExp = 1`) both FAIL. **Minimal witness: `M = (2,3)`, `L = 1`** — the reachable terminal
carries the full ledger `{ divisor A: divExp 6, t̃ 0 ; divisor B: divExp 2, t̃ 1 }`; the geometric fold
blows up BOTH, so

    |det D chartMap w| = |z_A(w)|^{6−1} · |z_B(w)|^{2−1} = |z_A|^5 · |z_B|^1,

while `geoAtlas_fold_det`'s analytic-filtered RHS (`leafOfState` keeps only the t̃=0 divisor A) is
`|z_A|^5`. They differ by the stranded factor `|z_B|` (nonzero exponent, `divExp(B) − 1 = 1`).

**Consequence.** `geoAtlas_fold_det` as stated (RHS over the ANALYTIC ledger `c.numDiv = (t0Indices).length`)
is FALSE. The honest identity is the **FULL-LEDGER form** (below). This is EXACTLY the form my
`cert-ledger-accumulation` cocycle already proves (`L(s)` sums over `s.numDiv`); the headline assembly in
that cert's §1 ("`c.divExp = s.divExp`") silently assumed no stranding and is corrected here.

---

## §1 The recursion semantics (why stranding is unavoidable)

`ConState.divTilde k = tildeOf (divProfile k) = min` of the divisor's rank-pattern (`EngineConstruction:66`).
A divisor is born (case-2 / case-1(2), `stepAppendAdvance`) with its tail set to the current `cleared` `J`
and a head; `t̃ = min(head, J)`. `conOracle`'s terminal is `L ≤ layer` (`EngineConstruction:2118`). Between
birth and a terminal, a divisor's `t̃` is lowered ONLY by a case-1(1) merge that RE-CLEARS it to the then-
current `J` (`stepCase11` `setTail`); an untouched divisor keeps its birth `t̃`.

So a divisor born at `J > 0` and never subsequently merged reaches the terminal with `t̃ = min(head, J) > 0`
— **stranded** — while its `divExp` (set at birth to `resRows·resCols` for case-2, and `> 1` whenever the
residual block is non-trivial) is unchanged. `leaf_mem_Adm_single`'s docstring records this explicitly:
"the t̃ > 0 stranded/non-live divisors fold into the residual core, so `leaf_mem_Adm`'s ∀ k form is too
strong at a terminal that carries residuals" (`EngineConstruction:1336-1340`). The `∀ k, t̃=0` hypothesis
of `leaf_mem_Adm` (`:1323`) is exactly the STRONG form — assumed, not derived.

**Hand trace of the witness `M=(2,3)`, `L=1`** (against `stepUpdate`/`conOracle`):
- `conRoot` (layer 0, cleared 0): not terminal, not rollover (`widthMinUpto 1 = min(2,3)=2 > 0`), occ empty ⟹
  **case-2**. Births A: `resRows = widthMinUpto 0 − 0 = 2`, `resCols = M₁ − 0 = 3`, `divExp = 6`;
  `divBirthCoord (0,0)` (diagonal); profile tail `:= 0` ⟹ `t̃ = 0`. `cleared → 1`.
- (layer 0, cleared 1): occ empty (A has t̃=0 ≠ target range) ⟹ **case-2**. Births B: `resRows = 2−1 = 1`,
  `resCols = 3−1 = 2`, `divExp = 2`; `divBirthCoord (0,1)`; profile tail `:= 1` ⟹ `t̃ = 1`. `cleared → 2`.
- (layer 0, cleared 2): `widthMinUpto 1 = 2 ≤ 2` ⟹ **rollover**. `layer → 1`, ledger carried.
- (layer 1, cleared 0): `L = 1 ≤ layer = 1` ⟹ **terminal**. Full ledger `{A: 6, t̃0 ; B: 2, t̃1}`;
  analytic (`t0Indices`) `= {A}`.

The geometric fold has a chart per node: `geoChartMapNorm(node_A) ∘ geoChartMapNorm(node_B) ∘ (rollover = id)`,
so `|det D chartMap| = |z_A|^{6−1}·|z_B|^{2−1}` — the stranded B is blown up (it is a case-2 node on the
path), so its factor is present. ✓ FALSE.

## §2 Exhaustive adjudication (`battery/hunt_stranded.py`, exit-0)

The FIX-A (runMinWidth head-reset = the Lean) recursion, swept over small `M` families, classified every
reachable terminal's every divisor. Counts (STRONG / WEAK-not-strong / FALSE families):

| family | STRONG | stranded-all-`divExp=1` | **FALSE (stranded `divExp>1`)** |
|---|---|---|---|
| `L=1, M∈[1..3]²` (9) | 5 | 1 | **3** |
| `L=2, M∈[1..3]³` (27) | 15 | 2 | **10** |
| `L=3, M∈[1..3]⁴` (81) | 45 | 5 | **31** |
| `L=4, M∈[1..3]⁵` (243) | 135 | 14 | **94** |
| `L=2, M∈[1..4]³` (64) | 28 | 2 | **34** |
| `L=3, M∈[1..4]⁴` (256) | 112 | 6 | **138** |

FALSE is pervasive (310 families total). Clean higher-`L` witnesses: `M=(2,2,3)` `L=2` (stranded profile
`(2,1)`, `divExp 2`, t̃ 1); `M=(2,2,2,3)` `L=3` (profile `(2,2,1)`, `divExp 2`, t̃ 1); `M=(2,2,4)` `L=2`
(`divExp 3`). The recursion (FIX-A `runmin`) matches the Lean; the sim is validated against the known t̃=0
atlases at `(2,2,2),(3,3,4),(2,2,2,2)` (the `08-atlas-probe` provenance).

## §3 The honest statement (FULL-LEDGER form)

The geometric fold blows up EVERY born divisor (each case-2/case-1(2) node carries a chart; case-1(1)
re-merges and rollovers add no divisor). So the honest Jacobian identity is:

    |det D c.chartMap w| = ∏ k : Fin c.fullNumDiv, |z_{fullDivCoord k}(w)| ^ (c.fullDivExp k − 1)

over the FULL ledger (`fullNumDiv`/`fullDivExp`, `ResolutionTree.lean:150-152`), NOT the analytic
`c.numDiv`/`c.divExp`. Equivalently, the **analytic × stranded factorization**:

    |det D c.chartMap w| = (∏ k : Fin c.numDiv, |z_{c.divCoord k}(w)|^{c.divExp k − 1})        -- analytic
                          · (∏ over stranded j, |z_{fullDivCoord j}(w)|^{c.fullDivExp j − 1})   -- stranded

**This is my `cert-ledger-accumulation` cocycle's ACTUAL conclusion** — `L(s) = ∏_{k:Fin s.numDiv}
|z_{diagCell(s,k)}|^{divExp k − 1}` sums over the full `ConState.numDiv`. So the cocycle needs NO change;
only the leaf headline must be stated over the full ledger (see §5 correction).

**Missing field.** `LeafData` carries `fullNumDiv`/`fullDivExp`/`fullDivProfile` but only an ANALYTIC
`divCoord` (`:170`); there is no `fullDivCoord`. The full-ledger headline needs the flat cell of EVERY
divisor (analytic + stranded) — the diagonal `flatCoordOf (divBirthCoord k)` for all `k : Fin s.numDiv`
(the `birthFlatCoord` construction, already used for the analytic `divCoord`, applied to the full index
set). So the honest form needs a `fullDivCoord := birthFlatCoord ∘ (full index)` field / read.

## §4 The stranded factors are RLCT-INERT (why the payoff is unaffected)

The downstream consumer is the RLCT integral `∫_{srcBox} F(w)^{−λ} |det D chartMap(w)| dw` (smallest
pole in `λ`). Its pole location is unchanged by the stranded factors, PROVIDED the binding
hypothesis below. With `F = (∏_{analytic} |z_a|²)·G`,

    F^{−λ}·|det D chartMap| = G^{−λ} · ∏_{analytic} |z_a|^{E_a − 1 − 2λ} · ∏_{stranded} |z_s|^{E_s − 1}.

- Each stranded factor contributes `∫_{−R}^{R} |z_s|^{E_s − 1} d z_s = 2R^{E_s}/E_s < ∞` (`E_s ≥ 1`), with
  NO `λ`-dependence — a finite amplitude, no pole.
- So the poles come only from the analytic factors `∫₀ r^{E_a − 1 − 2λ} dr`, converging iff `λ < E_a/2`;
  `λ_RLCT = min_a E_a/2` (binding at `minAdm`). The stranded factors change the finite amplitude, not the
  pole. **RLCT-inert.**

**Binding hypothesis (Codex-sharpened).** Inertness requires `G` uniformly bounded BELOW on `srcBox`
(`0 < c ≤ G ≤ C`) AND the stranded coordinate `z_s` disjoint from the residual — i.e. `z_s` does NOT
appear in `G`. The bare fact "`F` does not vanish identically on `{z_s = 0}`" is NOT sufficient: the
counterexample `F = x² + y²`, `J = |y|^{E−1}` has `F|_{y=0} = x² ≠ 0` yet `∫(x²+y²)^{−λ}|y|^{E−1} ∼
∫ r^{E − 2λ} dr` shifts the threshold to `(E+1)/2` — because `y` is entangled in the Morse core, not
disjoint from it. In the construction the stranded `z_s` IS disjoint: (i) `ChartBridge` requires
`Disjoint (range divCoord) (range resCoord)`, so `z_s ∉ resCoord` (a Morse-residual leaf's `G = ‖z_resCoord‖²`
does not contain `z_s`); (ii) for a fully-diagonalised leaf (`resRank = 0`), `G = 1 + Σ(non-terminal
monomials)² ≥ 1`, floored by the `1+` regardless of `z_s` (`cert-loss-factorization` §II, kill-c). Either
way `G` is uniformly positive as `z_s → 0`, so the stranded factor is inert. The full-ledger `fullDivCoord`
must therefore stay disjoint from `resCoord` (an extension of `ChartBridge`'s disjointness clause to the
full ledger).

Consequence: the ANALYTIC ledger remains the correct read for the LOSS (`LeafPullback`'s `∏ divCoord²`),
the C-agreement (`divExp ∈ terminalExponents`), and the RLCT pole; the FULL ledger is needed ONLY for the
Jacobian IDENTITY (`LeafJacobian`'s β-det), and the stranded factors ride into the RLCT integral's bounded
amplitude. The three consumers read DIFFERENT ledgers — by design, now made explicit (Codex Q4).

## §5 Correction to `cert-ledger-accumulation` §1 / §6 (this cert supersedes)

That cert's §1 "Headline" step wrote `c.divExp = s.divExp`, `c.divCoord = diagCell M s k` — conflating
the analytic `leafOfState` ledger `c` with the full state ledger `s`. That equality holds ONLY under the
STRONG form (no stranding), which is FALSE (this cert). The correct reading: the cocycle proves
`|det D chartMap w| = L(s)(w)` over the FULL `s.numDiv` ledger; the leaf headline `geoAtlas_fold_det` must
therefore be stated with the FULL-ledger RHS (`fullDivExp`/`fullDivCoord`), and the current analytic RHS
is FALSE. Everything else in `cert-ledger-accumulation` (the threaded invariant, the four maintenance
identities, the base) is over `s.numDiv` and stands verbatim — it was already the full-ledger cocycle.

## §6 Transcription notes (for t14 — the leaf instantiation t14's provability check flagged)

- **Restate `geoAtlas_fold_det`** to the full-ledger RHS `∏ k : Fin c.fullNumDiv, |z_{fullDivCoord k}(w)|^{c.fullDivExp k − 1}`
  (§3). The current `GeoLeafJacobian.lean:39` analytic RHS is FALSE (witness §1).
- **Add `fullDivCoord`** to `LeafData` (or read the state's `divBirthCoord` over the full index at the
  leaf): `fullDivCoord k := birthFlatCoord M s (fullIndex k)`, the diagonal of `divBirthCoord k` for ALL
  `k : Fin s.numDiv`. The `(β)` coherence `birthFlatCoord_eq_flatCoordOf` applies to the full index set
  unchanged (it is stated for an arbitrary `k : Fin s.numDiv`, not only the analytic sublist).
- **The cocycle instantiates directly**: `Inv(chartMap, leafState)` gives `|det D chartMap w| = L(leafState)(w)`
  = the full-ledger RHS. No stranded/analytic case split inside the induction — the induction is already
  full-ledger; only the leaf STATEMENT changes from analytic to full.
- **LeafJacobian (the ChartBridge clause)**: its β-det clause (`EngineDefs.lean:62-64`) reads `l.divCoord`/
  `l.divExp` (analytic). Either (i) point it at the full ledger `l.fullDivCoord`/`l.fullDivExp`, or (ii)
  keep it analytic and add the stranded factor as a separate bounded-positive term — (i) is cleaner and
  matches the cocycle. The RLCT read (area formula) is unaffected either way (§4: stranded = RLCT-inert).
- **Do NOT** try to prove the STRONG or WEAK form as a reachability lemma — both are FALSE (§2). The
  honest route is the full-ledger statement, not a no-stranding invariant.

## §7 Codex decorrelation (`codex/stranded-dichotomy-{prompt,answer}.md`, xhigh, conclusions withheld)

Given the setup + the witness (my verdict/statement withheld), Codex independently: Q1 FALSE (same
`z_A ≠ 0, z_B = 0` separation); Q2 the full-ledger form `∏_{k∈L} |z_k|^{E_k−1}` (= analytic × stranded);
Q3 RLCT-inert **under the uniformly-positive residual core**, with the exact `∫ r^{E−1−2λ}` pole analysis
AND the sharpening counterexample `F = x²+y², J = |y|^{E−1}` (threshold shifts to `(E+1)/2` when the
stranded coord is entangled in the Morse core) — establishing that disjointness / the uniform lower bound,
not mere non-vanishing, is what secures inertness (§4); Q4 the three-ledger split (Jacobian → full; loss → analytic;
RLCT pole → analytic pairs, stranded folded into the bounded amplitude). Two decorrelated derivations agree.

## Close

- **Firmest (exhaustive + hand-verified + Codex-decorrelated):** FALSE. Stranded divisors with
  `divExp > 1` are pervasive at reachable terminals (310 families; minimal `M=(2,3)` `L=1` hand-verified
  against `stepUpdate`).
- **The honest statement:** the full-ledger Jacobian identity (§3), which my `cert-ledger-accumulation`
  cocycle already proves; the analytic headline in `GeoLeafJacobian.lean:39` must be restated to it, and a
  `fullDivCoord` added.
- **Payoff unaffected:** stranded factors are RLCT-inert (§4) — the analytic ledger stays the read for the
  loss / C-agreement / RLCT pole; only the Jacobian identity goes full-ledger.
- **Most likely to bite the builder:** forgetting that `LeafData` has no `fullDivCoord` yet (§3), or
  keeping the analytic RHS on `geoAtlas_fold_det` (FALSE). No new paper adjudication owed — §3/§4 pin the
  honest statement and its RLCT-inertness exactly.
