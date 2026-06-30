# D1 ≥-leg endgame — scoping map (genm-d1scope, READ-ONLY)

Canonical: `expedition/aoyagi-full` @ `e61a1683` (main checkout `/home/ubuntu/workspace/geometry-of-dln-fibre`).
Mission (A): the fully general `aoyagi_learning_coefficient`. This maps the D1 ≥-leg only.

All paths below are in the main checkout, not my worktree (the worktree is on a different branch).

---

## Q1 — Which producer is LIVE for `rlctAt_deepest_le_of_optimal` (Skeleton:1172)?

**Neither.** `rlctAt_deepest_le_of_optimal` (`Skeleton.lean:1172`) is a **bare `sorry`** in canonical
(general-L, no L=2 specialisation in its statement). Nothing in canonical discharges it.

The headline path (DATA, from the Lean):

- `aoyagi_learning_coefficient` (`Skeleton.lean:1725`)
  `→ rw deepest_point_reduction` (`Skeleton.lean:1187`)
    `→ le_iInf₂ ... rlctAt_deepest_le_of_optimal` (`Skeleton.lean:1172`) — **the bare `sorry`**.

Both candidate producers (`deepest_le_of_optimal_secondPeel_discharged`,
`deepest_le_of_optimal_of_iftResidual`) appear in source **only** in:
- `AxCheck.lean` (`#print axioms` smoke tests, lines 200/226), and
- `DLNFibre.lean` (import-narrative comments, lines 596/611).

There is **no `exact`/`have` in any canonical theorem** that consumes a producer to close the Skeleton
`sorry`. The producers are sorry-free *standalone L=2 lemmas modulo named hyps*; they are **not plumbed
into the headline.** A glue lemma is missing on BOTH routes:
`rlctAt_deepest_le_of_optimal (L:=2) ⟵ producer` (subst `L=2`, supply named hyps).

Intended discharger: the docstring at Skeleton:1166-1171 says D1≥'s obligation (a) "is the SAME
constant-rank chart machinery as `deepest_regular_core_normal_form` (#44)". The producers are the L=2
realisation of that, but the wire to the general-L `sorry` (specialised to L=2) does not exist yet.

---

## Q2 — Exact named hypotheses of each producer + current state

### Route A — `deepest_le_of_optimal_secondPeel_discharged` (`D1SecondPeelAssembly.lean:50`)
Standalone sorry-free; calls `secondPeel_hchart_residual` then delegates to Route B. Named hyps:

| Hyp | What it is | State |
|---|---|---|
| `hcoreDeepest` | `coreDeepest = ofReal(lambdaCore (square m))` — definitional | discharged (rfl-shaped) |
| `hDeepest` (#44) | `rlctAt deepest = nRegL2/2 + coreDeepest` | **open**: this is #44 `deepest_regular_core_normal_form`, a bare `sorry` at `Skeleton.lean:1124` (general-L). The L=2 discharge route is `deepest_diffeo_bridge_L2_impl` (`DeepestDiffeoBridgeL2.lean:3058`) — **2 sorries remain** there; wiring tasks #149/#153 in flight. So #44-at-L2 is **open-but-near**, NOT banked. |
| first-peel `hchart`+`q`+`hq`+`t0`+`hRne` | the DLN bounded-unit IFT chart-transfer + C¹ residual | **PRODUCIBLE & sorry-free**: `dln_hchart_residual` (`D1HChartResidual.lean:343`) builds exactly this, given a nonzero `jacFlatL2` minor `hminor`. `D1HChartResidual.lean` is **0 sorries**, clean-three. The remaining gap is using it (the minor-existence at general v) — but the producer itself is built. |
| `hslice`/`hslice0`/`eh`/`ec`/`heh`/`hec` | second-peel selected-minor scaffold (C² slice, vanishes, injective selectors) | data hyps, dischargeable from the first residual's structure |
| `hminor₂` | `det of the extra×extra Jacobian minor of q(0,·) ≠ 0` | **open analytic non-degeneracy** — a Jacobian-rank condition on the residual VECTOR (NOT a Hessian). The verify-first gate (#208) verdict: this is BOUNDED, off the L≥3 wall. Not yet discharged as a theorem; it is the genuine open analytic premise of the second peel. |
| `hInterface` (= `R1ResolutionInterface` at the degraded core `M'`) | `∀ M' (0<M'), rlctAtOn(dlnLoss M' 0) 0 = ofReal(lambdaCore M')` | **GATED on R1**. Def: `D1ChartProducerL2Build.lean:320`. Discharged by `r1_interface_discharges_degraded` (same file :329) **from R1's general-width resolution**: `resolution_charts` (Skeleton:1228, a bare `sorry`) + `resolution_value_of_atlas`. This is the R1-LOWER `cover_ge_div` dependency. **Binding constraint recorded** (`D1ChartProducerL2Build.lean:308`): R1's `resolution_charts` MUST stay general-width to cover the rectangular `M'`. |

### Route B — `deepest_le_of_optimal_of_iftResidual` (`D1IFTResidualProducer.lean:84`)
Standalone **0 sorries**. The delegate Route A calls. Same obligations re-stated as bare hyps:
`hDeepest` (#44), first-peel `hchart`+`q` (← `dln_hchart_residual`), `hchart₂`+`q₂` (the second peel),
and `hDegraded` (= the R1 interface value at `M'`, the same R1 gate as Route A's `hInterface`).
The difference from Route A: Route B takes `hchart₂` and `hDegraded` as **bare hyps**; Route A
**builds** `hchart₂` from `hminor₂` (via `secondPeel_hchart_residual`) and packages `hDegraded` via
`hInterface`. So **Route A is strictly more assembled** — it discharges the second-peel chart from
selected-minor data rather than positing it.

### #225/#231 — the eihd-det `hchart` wiring (the iftResidual route's first-peel `hchart`)
Tasks #225 ("land iftResidual's hchart via `rlctAtOn_eq_of_contDiff_chart`") and #231 ("wire to
iftResidual hchart") are both **in_progress**, but the LANDING is already done by a DIFFERENT atom:
`dln_hchart_residual` (`D1HChartResidual.lean`, 0 sorries) IS the assembled first-peel `hchart`, built
on the generic engine `rlctAtOn_eq_of_contDiff_chart` (Foundations) + the `jacFlatL2` selected minor.
It does **NOT** route through `interiorDet_leaf_headline_eihd`. `D1HChartWire.lean` (the #231 germ
building blocks) is sorry-free; its docstring lists the remaining #231 work as "partition + bump +
reindex" — but `dln_hchart_residual` already performs exactly that and is closed. So the #225/#231
"eihd-det hchart" framing is **stale**: the first-peel hchart is produced WITHOUT the eihd det.

---

## Q3 — The eihd-orphan question: RESOLVED

`interiorDet_leaf_headline_eihd` (`RouteMHDtotEihd.lean:1029`, clean-three, ∀M-L2 interior Jacobian)
has **NO live downstream consumer as a term** anywhere outside (i) its own file, (ii) `AxCheck`
(`#print axioms`), (iii) the `DLNFibre.lean` import comment. Grep confirms empty.

**It is NOT the iftResidual route's `hchart`.** The iftResidual `hchart` is produced by
`dln_hchart_residual`, whose chart-transfer atom is the generic `rlctAtOn_eq_of_contDiff_chart`
(an IFT bounded-unit chart from a `jacFlatL2` minor) — a different object from the eihd staircase det.

**Verdict: the eihd det is an R1-LOWER/upper INTERIOR-DET asset, not a D1 asset.** Per AxCheck:236 and
`DLNFibre.lean:628`, `interiorDet_leaf_headline_eihd` is "the cov-field input to the R1-LOWER
`cover_ge_div` / `NodeAchieverChart`" — i.e. it feeds R1's resolution (the |det Dφ| Jacobian-monomial
side), which is the in-flight R1-LOWER build (#157/#158). It is a real clean-three 23-file build that
is **awaiting its R1-LOWER consumer wiring**, NOT a dropped D1 route. Plainly: D1 never needed it; R1
does. The "intended iftResidual consumer" in the commission brief is a mis-attribution — the actual
iftResidual hchart consumer was always `dln_hchart_residual`, which is already closed and eihd-free.

---

## Q4 — Recommendation: what is commissionable NOW

The D1 ≥-leg has FOUR distinct open pieces. Their gating:

1. **The producer→Skeleton glue** (`rlctAt_deepest_le_of_optimal (L:=2) ⟵ secondPeel_discharged`):
   UN-GATED on R1 structurally, but its inputs include #44 + R1-interface, so the *green* wire waits.
   The glue lemma SHAPE (subst L=2, thread the 4 named hyps) is bounded + writable now as a
   `sorry`-carrying reduction (turns the bare Skeleton `sorry` into 4 named hyps) — a precision win
   that makes the remaining D1 debt legible. **Commissionable now (low-risk plumbing).**

2. **#44-at-L2** (`deepest_diffeo_bridge_L2_impl`, 2 sorries; #149/#153 in flight): UN-GATED on R1,
   the heavy gauge-slice geometry. Already an active build. **Not idle — being worked.**

3. **`hminor₂`** (second-peel Jacobian-minor non-degeneracy): UN-GATED on R1, BOUNDED (verify-first
   #208 verdict). A `pen-and-paper` witness-seat / `lean-formaliser` target: exhibit the nonzero
   extra×extra minor of the first residual's Jacobian at the basepoint. **Commissionable now, in
   parallel with R1-LOWER** — does not touch R1 at all.

4. **`hInterface` / `hDegraded`** (R1 resolution value at rectangular `M'`): **GATED on R1-LOWER**.
   This is `R1ResolutionInterface` ← `resolution_charts` general-width (Skeleton:1228 `sorry`) ←
   `cover_ge_div` — exactly the in-flight interior+smeared R1-LOWER build. **D1's only hard R1
   coupling. Waits on R1-LOWER landing.**

**Crisp next-D1 call:** charge **#3 (`hminor₂`)** and **the #1 glue reduction** NOW, in parallel with
R1-LOWER. #2 (#44-at-L2) is already moving (close it). Do NOT charge #4 — it gates on R1-LOWER's
`resolution_charts` general-width close. Once R1-LOWER lands `R1ResolutionInterface` and #44-at-L2
closes, the only remaining D1 piece is `hminor₂` + the L=2 glue — so derisk those two now so D1 is a
pure assembly the day R1-LOWER lands.

**Eihd note (plainly):** the eihd det is banked R1 infrastructure awaiting `cover_ge_div` wiring; it is
NOT in the D1 critical path and NOT a dropped route. If R1-LOWER's interior-cov branch (#158) is the
live R1 resolution route, eihd is its det-side input and should be wired there — confirm with the
R1-LOWER thread (genm-r1lower) that #158 is the eihd consumer, else flag eihd as a stranded R1 asset.

---

## Reflection (registers)
- **Claim (most likely to advance):** the D1 ≥-leg is, post-R1-LOWER, a 2-piece assembly (`hminor₂` +
  L=2 glue); de-risking `hminor₂` now removes D1 from the critical path entirely. Kill-condition: if
  `hminor₂` turns out to require the full constant-rank split (i.e. is secretly #44-hard), then D1≥
  collapses back onto the gauge-slice wall and is NOT independent.
- **Most likely to break:** the assumption that `dln_hchart_residual`'s `hminor` (a nonzero `jacFlatL2`
  minor at general optimal v) is dischargeable WITHOUT new geometry — it is stated as a hypothesis, and
  minor-existence at an ARBITRARY optimal v (not just front-pivot) is the H_indep question (#226
  resolved "general-v", but the minor-selection at v is the residual analytic content).
- **Next computation to clarify:** read `D1HChartResidual`'s use-site (does any canonical lemma supply
  `hminor` at a general v, or is it always threaded as a hyp?) — that decides whether the first-peel
  hchart is truly "produced" or still posits a minor. This is the same question for `hminor₂`.
