# DecoratedStepHyp (#5) formalization build-plan — the cert→Lean lemma DAG (banked vs owed)

**Seat:** pen-and-paper (forward-scope build-plan — genm-sj5-cover). **Date:** 2026-07-11. **NO Lean.**
**Charge (team-lead):** bridge the now-settled StepHyp soundness cert → Lean as a lemma DAG, each node
banked-vs-owed; consume the banked spine (BUILT-INDEX + the RouteMSJ scaffold). Forward-scope; DROP the
moment desc3 lands #148 (the #3 audit is higher priority).

**Consumed:** `stephyp-intersection-cert` (+ §8 correction), `transversality-recursion` (§8–§10), dmcheck
`cert.md` (the settled invariant), `BUILT-INDEX.md`, the RouteMSJ spine (grep'd). **Settled soundness
statement (canonical, controller-stamped):** per-cell threshold `½(M₀ρ + min(M₀q, D_q))`; the QIP identity
`min_ρ(cCodim(deeper;ρ)+M₀ρ)=minAdm`; `m=1` per direction; `D_q≤M₀q` at binding; the 3 misread-traps avoided.

**Legend:** [BANKED] in-repo sorry-free · [ADJ] banked-adjacent (small lemma off a banked one) · [OWED] genuine
new build · [DRIVER] the abstract spine already landed.

---

## ★ The DAG (top = the #5 goal; edges = "consumes")

```
                       DecoratedStepHyp adm  (#5 goal: adm D at arity L, decorated IH at L-1 ⟹ D finite)
                          │
     ┌────────────────────┼───────────────────────────┬────────────────────────┐
   (N4) peelOp +        (N2) per-cell            (N3) σ_min(A₂)≥ε          (N5) adm entry
   corner-ADD +          estimate                sector cover +            (peel-preservation
   reduced-IH compose    ½(M₀ρ+min(M₀q,D_q))     rank-drop split           + IH closing)
     │        │             │        │              │       │                 │
  [DRIVER] [BANKED]     (N2a)     (N2b)          [ADJ]   (N3-term)         = #144 peel-closure
  decoratedBox  carrier  QIP-id   tube=cCodim   RouteMSJ  finite rank        [BANKED: RouteMSJ
  ThresholdFin  Thresh   [BANKED] [ADJ #127]    SigMin    strata (minor-cut)  Transversality
  _of_decStep   _shift   minAdm_          RouteMSJ        [ADJ RankLocus       + BackPeel #1
  [DRIVER]     [BANKED]  eq_backPeel      ProductTube     Closed]              + CorankSurvival #2b]
                        + cCodim_eq_qipMin                                     parameterized on #3
                                    │
                              (N1) m=1 normal slice  ◄── THE ONE OWED GEOMETRIC INPUT
                              [OWED, ADJ normalSlice_transfer #109]
```

---

## N1 — [OWED] the `m=1` reduced full-rank first-order normal slice (the one geometric input owed to Lean)

**Statement to build (precise).** At a generic point of a top-dimensional rank-`ρ` component of the deeper
product `P = A₁···A_{L-1}` (`M₁×M_L`), the transverse first-order normal slice is REDUCED and the
smallest active singular value vanishes to order exactly 1: `σ_{ρ+1}(P)² ≍ dist(·, {rank≤ρ})²`, i.e. the
`(ρ+1)`-minor ideal has a generator of transverse order 1 (`m=1`). Equivalently: the compression directions
de-rank at FIRST order at the generic tube point.
- **What #109 (`normalSlice_transfer`) gives [BANKED]:** the unit-Jacobian CoV / normal-slice IDENTITY
  `{rank(A₁···A_{L-1})≤q} ⟺ Σ⁰(reduced)` — the change-of-variables straightening the tube, NOT the order.
- **The exact GAP [OWED]:** the FIRST-ORDER reducedness (`σ² ≍ dist²`, `m=1`) — that the normal slice is a
  reduced full-rank-`q` matrix, so each collapsing direction is order 1 (the corank-2-cert per-direction
  `σ₂²≍t²`, verified symbolically by dmcheck). This is banked-ADJACENT to #109 (same CoV, add the order-1
  transversality). **The single genuinely-geometric owed node** — everything else is arithmetic/measure.
- **Guard (T-a):** state it PER DIRECTION with `σ_min²` (order 2 in the squared loss = `m=1`), NEVER the
  aggregate `det(PPᵀ)` (order `2q` → spurious `m=q`). The corank-`q` case is the per-direction iterated
  corner (`corank2-cert §2` joint two-scale density), not one aggregate `U₀`.

## N2 — [BANKED core + OWED assembly] the per-cell estimate `½(M₀ρ + min(M₀q, D_q))`

The cell-`q` (corank `q`, `ρ=r−q` survive) RLCT threshold, feeding `min_q = ½minAdm`.
- **N2a QIP identity `min_ρ(cCodim(deeper;ρ)+M₀ρ)=minAdm` — [BANKED].** = `minAdm_eq_backPeel` (`RouteMSJBackPeel`,
  #1) with `t=M₀`, composed with `cCodim_eq_qipMin` (`cCodim = qipMin`, banked Core). The `D_q≤M₀q`-at-binding
  is `minAdm_redChain_succ_ge` (banked convexity, `RouteMSJTransversality`) + the back-peel (my §8/dmcheck P3).
- **N2b tube-codim `= cCodim(deeper;ρ)` — [ADJ #127].** The product-pushforward tube codim = the geometric
  `cCodim` (dmcheck P1, Jacobian-verified incl. bottlenecks). `RouteMSJProductTube` (#127) banked the tube
  leading power `D = cCodim(reduced)`; the pushforward-density = cCodim is banked-adjacent (the coarea/Jacobian
  of the rank map). Guard (T-b): the tube is `Zdeep`'s rank drop, NOT the corank block (`transversality §1`).
- **N2-assembly [OWED]:** the per-cell lemma `cell_q threshold = ½(M₀ρ + min(M₀q,D_q))`. The `min` is the
  coupled-corner cap: the front charge `M₀q` (front `A₀`-box, `RouteMSJFrontSpectral`/`CornerBound`) vs the
  tube `D_q`; the coupled blow-up ADDS `M₀ρ` (the surviving front) to `min(M₀q,D_q)`. Consumes the corner
  scaffold (`RouteMSJSphereBlowup`, `RouteMSJTwoBlockRadial`, `RouteMSJCorner*`, `loss_radialStep`). Guard
  (T-c): the cell VALUE is `½(M₀ρ+min(M₀q,D_q))`, NOT `½(D_q+d_q)` (over-claims on narrow fronts, still
  `≥½minAdm`).

## N3 — [ADJ] the `σ_min(A₂)≥ε` quantitative sector cover + rank-drop split + termination

- **The sector `{σ_min(A₂) ≥ ε}` [ADJ `RouteMSJSigMin`].** On it, `U₀,U₁ ≥ c(ε) > 0` UNIFORMLY (T4 — the
  no-collapse gate, `stephyp-cert §7-Q2`): the coupled corner has RLCT `½minAdm`. `RouteMSJSigMin` banks the
  `σ_min` machinery; the uniform units bound `σ_min(A₂)≥ε ⟹ ZZᵀ≽c·I` is the banked units bridge (#147,
  `RouteMSJUnitsBridge`).
- **The rank-drop split `{σ_min(A₂)<ε}` → recursive branch [ADJ RankLocusClosed].** The complement is assigned
  to a deeper branch (NOT null-deleted). The strata `{rank A₂ = ρ}` are minor-cut (banked `Core.RankLocusClosed`).
- **N3-termination [OWED, small]:** the `σ_min(A₂)`-rank-stratification terminates — `rank A₂` strictly
  decreases down the branches (finite ranks `0..min`), so finitely many strata; each deeper stratum is a
  higher-`Mval` branch with threshold `≥½minAdm` (dmcheck P3 per-branch). Owed: the finite-stratum induction
  + the per-branch `≥½minAdm` (= N2 applied to the branch).

## N4 — [DRIVER + BANKED shift + OWED peelOp] the peel + reduced-IH composition

- **The abstract driver [DRIVER, banked].** `decoratedBoxThresholdFinite_of_decoratedStep` +
  `routeMBoxThresholdFinite_of_decoratedDescent` (`RouteMSJDecoratedRec`) — the arity strong-induction wrapper
  consuming `DecoratedStepHyp adm`. Already landed (clean-three). #5 = supply `DecoratedStepHyp adm`.
- **The threshold shift [BANKED].** peel at cut `t` shifts `c' ↦ c'−½peelCharge`; `carrierThreshold_shift` +
  `half_minAdm_sub_half_peelCharge_le` (banked) give `c'<½minAdm ⟹ c'−½peelCharge < ½minAdm(redChain)`, so the
  reduced integral is inside the IH range. BANKED.
- **peelOp (the coupled corner blow-up + diag(b) ledger) [OWED — the #5 centerpiece].** The
  `SJDecoration → SJDecoration` transform: front Γ-block blow-up (`RouteMSJDecoratedPeelStep`/`PeelCore`),
  the coupled corner (`RouteMSJSphereBlowup`/`Corner*`), the diag(b) ledger threading (`RouteMSJLedger`,
  `RouteMSJLinGen`, `loss_radialStep`). Scaffold mostly banked; the peelOp AS the decoration transform + its
  measurability (`RouteMSJDecoratedMeas`/`PeelMeas`) is the OWED assembly. **Composition:** peelOp D (charge
  `½peelCharge`, N2 per-cell) → reduced decoration D' on `redChain` at `c'−½peelCharge` → decorated IH (D'
  finite). Charges ADD (N2 corner) to `½minAdm`.

## N5 — [BANKED, parameterized] where `adm` (#3) enters

**Parameterize on the abstract `adm` (robust to #3's exact form B):** #5 assumes `adm` satisfies the three
interface facts, and consumes them — it does NOT hard-code #3's def.
- **(i) input:** `adm D` (the hypothesis on the peeled decoration).
- **(ii) peel-preservation `adm D → adm(peelOp u D)` [BANKED = #144]:** the new peel divisor has `p=0` by
  `RouteMSJTransversality` (rank `≥ b` via `minAdm_eq_backPeel` #1 + convexity) + `corank_survival_ae` (#2b,
  the corank block survives full-row-rank `b`, `p=0`); old divisors inherit. Needs `genuineCarrier` (D.ctx =
  the real reduced product) — an `adm`-clause hypothesis (#3), consumed here.
- **(iii) IH-closing:** the reduced integral handed to the IH is over an `adm`-decoration (peel-preservation),
  so the decorated IH applies. **Parameterization:** state #5 as `∀ adm, (adm contains trivial ∧ adm
  peel-closed via #144 ∧ genuineCarrier) → DecoratedStepHyp adm` — so #5 is robust whether #3 lands as the
  valuation-predicate (B) or any equivalent; the peel-closure it needs is the #144 theorem, chain-geometric.

## N6 — the 3 misread-traps as explicit "do NOT" guards (bake into the Lean statements)

- **T-a [N1, N2b]:** DO NOT use `U₀ = det(PPᵀ)` (order `2q`) as the per-direction unit — use `σ_min²` (order
  2, `m=1`) per direction; corank-`q` via the iterated corner (joint density), not one aggregate.
- **T-b [N2b]:** DO NOT read the tube as the corank block `A₁,cor·Zdeep` (prepends the FREE front layer →
  spurious low codim) — the tube is the DEEPER PRODUCT `Zdeep`'s rank drop (`transversality §1` licenses it;
  the corank block is full-row-rank there, its drop is inside the front `½ab` charge).
- **T-c [N2-assembly]:** DO NOT assert `½(D_q+d_q)` as the per-cell VALUE (over-claims on narrow fronts
  `M₀q<D_q`) — the true cell is `½(M₀ρ+min(M₀q,D_q))`, `≥½minAdm` (so (□) survives; `min_q` still `=½minAdm`).

---

## Owed-node summary (what #5 genuinely needs to BUILD, in dependency order)

1. **[OWED, geometric] N1 `m=1` normal slice** (`σ_{ρ+1}²≍dist²`, reduced full-rank slice) — banked-adjacent
   to `normalSlice_transfer` #109; the ONE geometric input dmcheck flagged. Smallest-risk to state, but the
   only non-arithmetic owed node.
2. **[OWED, assembly] N2-assembly** the per-cell `½(M₀ρ+min(M₀q,D_q))` from banked N2a (QIP id) + N2b (tube),
   corner-ADD + front-cap.
3. **[OWED, small] N3-termination** finite `σ_min(A₂)`-stratification + per-branch `≥½minAdm`.
4. **[OWED, centerpiece] N4 peelOp** the `SJDecoration→SJDecoration` corner-blow-up + ledger transform + its
   measurability (scaffold banked; assembly owed).
5. **[BANKED] N5 peel-preservation** = #144 (`RouteMSJTransversality` + #1 + #2b), parameterized on #3.

Everything else — the driver (`decoratedBoxThresholdFinite_of_decoratedStep`), the threshold shift
(`carrierThreshold_shift`), the QIP identity (`minAdm_eq_backPeel`+`cCodim_eq_qipMin`), the units bridge
(#147), the terminal (`sjLoss_terminal_lintegral_lt_top`), the corank survival (#2b) — is BANKED.

**The crux owed piece is N4 (peelOp), with N1 the one geometric input.** N2/N3 are assembly of banked pieces.
N5 is #144, banked (parameterized on #3). When desc3 reaches #5, this DAG is the build order: N1 (or cite it
as the owed geometric lemma) → N2 → N3 → N4 (peelOp) → wire via the driver + shift + N5.

## Firmest / most-likely-to-break / next
- **Firmest.** The DAG is mostly banked: the driver, shift, QIP identity, units bridge, terminal, corank
  survival, peel-preservation (#144) are all in-repo. #5 = build peelOp (N4) + assemble N2/N3 + cite/build N1.
- **Most likely to break.** N4 peelOp measurability + the ledger threading (the `frobSq → carrier.loss`
  base-connection post-corner, `transversality §10`/#141-Q2's decorated-IH obligation) — the fiddliest
  assembly. And N1's `m=1` if the normal slice is NOT reduced at some width (dmcheck verified generic tubes;
  descendant angular loci are the recursion's job, N3).
- **Next.** Hand this DAG to desc-#5 when it reaches the crux. I audit N4/N1 hardest (the owed nodes) + the
  N5 parameterization against #3's landed form. DROPPING NOW for the #3 audit when desc3 reports #148.