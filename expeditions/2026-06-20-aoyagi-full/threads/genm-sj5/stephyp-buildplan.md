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

---

## §5′ — the FaithfulSJAt-frame REFINEMENT of N4/N5 (post-`faithfulsj-design.md`, the resolved invariant)

The base-fork resolution (OPT-A) made `adm := genuineCarrier ∧ (a=0 ∨ b=0 ∨ FaithfulSJAt D)`. So #5 is now
exactly: **`peelOp` PRESERVES `FaithfulSJAt`.** The DecoratedStepHyp is the peel-closure of this ONE invariant
(#4 consumes it, #5 preserves it). Refined N5/N4:

### N5′ — [the #5 GOAL] `DecoratedStepHyp`: `FaithfulSJAt D → FaithfulSJAt (peelOp u★ D)` (+ finiteness via IH)

Statement: at a binding cut `u★` of `M`, given the decorated IH (`∀ D' : SJDecoration (redChain u★ M),
FaithfulSJAt D' → DecoratedBoxThresholdFinite D'`), for `D : SJDecoration M` with `FaithfulSJAt D`: the peel
`peelOp u★ D : SJDecoration (redChain u★ M)` satisfies `FaithfulSJAt (peelOp u★ D)`, and `D`'s integral is
finite (via the IH on `peelOp u★ D` at the `½peelCharge`-shifted threshold). **Each clause preserved (cert-tied):**
- **α (pSimultaneous preserved) — [BANKED].** `peelOp` = `radialAttach` (+ chart); the fresh divisor `u₀` has
  `sharedDivisorExp`-exponent `1` shared by ALL generators (`sharedDivisorExp_prependColumn_one_zero`, banked
  `RouteMSJLedger`), and old divisors are preserved (`sharedDivisorExp_prependColumn_succ`). So the
  dehomogenised `i₀` persists (the corank generator stays a unit at every divisor). `p=0` preserved
  (transversality-recursion §144).
- **β (threshold ≥ ½minAdm preserved) — [BANKED arithmetic, my certs].** `peelOp` adds `peelCharge = ab` to the
  `u`-monomial (jac/sharedDivisorExp) and lands on `redChain u★ M`; `minAdm M = peelCharge + minAdm(redChain)`
  (`minAdm_le_peelCharge_add_redChain`, `exists_binding_cut`), so the shifted `monomialThreshold` stays
  `≥ ½minAdm(redChain)` (`carrierThreshold_shift`, `half_minAdm_sub_half_peelCharge_le`, banked). The nD-homogeneous
  corner `½Σ(block dims)` (dmcheck's `½(M₀ρ+min(M₀q,D_q))`, no-undershoot) is the per-peel realisation. **THE
  charges-ADD content lives HERE** (β preservation), NOT at #4 (§4-settled: #4 consumes β separably).
- **γ (coercive residual preserved) — [my stephyp/dmcheck certs + #147; the SUBSTANTIAL owed analytic content].**
  `peelOp` operates on the `σ_min(A₂) ≥ ε` QUANTITATIVE UNITS SECTOR (T4), on which the units bound
  `Z·Zᵀ ≽ c·I` (`#147`) makes the peeled residual coercive (bounded below). The rank-drop complement
  `{σ_min(A₂) < ε}` SPLITS to a higher-`Mval` recursive branch (dmcheck P3, threshold `≥ ½minAdm` per-branch
  via `D_q ≤ M₀q`). ★ This is the deepest #5 content — the intersection COUPLED estimate, NOT a codim freebie
  (the `x²(x²+y^{2N})` correction). **AUDIT FOCUS:** γ-preservation must be the QUANTITATIVE-sector +
  per-branch joint-tube (my `stephyp-intersection-cert` §7/§8), never "higher codim ⟹ slack".

### N4′ — [OWED centerpiece] the `peelOp : SJDecoration M → SJDecoration (redChain u★ M)` construction

The transform that realises N5′. **Exact shape (banked-vs-owed):**
- **[BANKED scaffold]** `radialAttach` (`d+1`, jac-prepend, `carrier.radialStep`, keeps `ζ/ν/ι/Z`); the corner
  chart `Γ = u·M(s,t,v)` (`RouteMSJSphereBlowup`/`Corner*`, `|dΓ|=u^{ab−1}`); the `diag(b)` row-mix
  (`gen_rowMix_const`, `RouteMSJLinGen`); the measure-preserving flatten / `MeasurePreserving e`.
- **[OWED assembly]** (1) the chain re-type `M → redChain u★ M` with `Z : Params M → Params(redChain u★ M)`
  (the reduced-product re-index) **keeping `ν = product-type FIXED** (FLAG-2: record the row-elimination in
  `coeff`/`supp`, do NOT shrink `ν`, else `genuineCarrier` preservation fails — cover #3-audit); (2) the
  `decLoss → carrier.loss` base-connection post-corner (the `frobSq → SJLinGenState.loss` faithful CoV, the
  `P⁻¹`-free pivot form — `transversality §10`/#141-Q2 decorated-IH obligation); (3) measurability
  (`RouteMSJDecoratedMeas`/`PeelMeas`). **This is the fiddliest owed piece; desc3 builds it, I audit the
  fidelity (FLAG-2 `ν`-fixed + the CoV faithfulness).**

### N1′ — [OWED, the one geometric input] exact Lean statement (banked-adjacent `normalSlice_transfer` #109)

`m = 1` reduced full-rank first-order normal slice — the residual-coercivity (γ) source. Exact target:
> at a generic point of a top-dim rank-`ρ` component of the deeper product `P = A₁···A_{L−1}`, the smallest
> active singular value satisfies `σ_{ρ+1}(P)² ≍ dist(·, {rank ≤ ρ})²` (`m=1`), and the transverse first-order
> normal slice is reduced (contains a full-rank-`q` matrix).
`#109 normalSlice_transfer` gives the CoV/normal-slice IDENTITY (`{rank ≤ q} ⟺ Σ⁰(reduced)`); the OWED GAP is
the ORDER-1 transversality (`σ² ≍ dist²`) — banked-adjacent, per-direction `σ_min²` (NOT `det(PPᵀ)`, dmcheck
T-a). Feeds γ (the coercive residual on the units sector).

### Net (FaithfulSJAt frame)
`DecoratedStepHyp = peelOp preserves FaithfulSJAt`, clause-by-clause: **α banked, β banked arithmetic
(charges-ADD, my certs), γ the substantial analytic content (my stephyp/dmcheck/#147, the units-sector +
per-branch joint-tube).** Owed builds: **N4′ peelOp** (scaffold banked, the re-type + CoV + measurability owed;
FLAG-2 `ν`-fixed) + **N1′ `m=1` slice** (banked-adjacent #109). My audit of #5 = the γ-preservation against
`stephyp-intersection-cert` (the units-sector, per-branch `½minAdm`, no codim-slack) + `dmcheck` (the
invariant `½(M₀ρ+min(M₀q,D_q))`) + β against `#144`/`carrierThreshold_shift`. [Codex NOT fired — the
preservation of α/β/γ is my already-certified content; the peelOp Lean CONSTRUCTION is desc3's formalization,
audited on landing.]
---

## §6″ — POST-§7 REFRESH (2026-07-12, UPDATE-965): #5 = the ROUTE-B decorated descent / coupled `diag(b)`; §6/§7 naive corner SUPERSEDED

The §7 independent-hunt refutation + the minAdm perm-invariance proof + (□)-soundness settling (theorem
modulo Aoyagi ∀ width) re-shape the #5 plan. **This section is the CURRENT #5 plan; where it conflicts with
§5′/N-nodes above, this wins.** (Refs: `joint-corner-cert.md §8` refutation+pivot, `minadm-perminv-cert.md`,
`offsector-independent-hunt.md`, `verify-r1-diagb-334.md`, `scripts/deepshare.py`.)

**1. The off-sector IS the decorated descent (route B), NOT a separate cover.** DROP §6/§7's naive-corner /
corank-of-Z stratification (superseded — the Eckart–Young "single matrix m=1" was a category error;
"charges ADD to ½Σ" was units-only). The #5 mechanism is **route B**: at the binding cut, integrate the freed
corank block `Γ` FIRST (freed Morse, exponent shift `½·peelCharge`), then the BLACK-BOX decorated IH on the
reduced chain at `c'−½peelCharge < ½minAdm(redChain)` (`carrierThreshold_shift`). This IS Aoyagi's coupled
`diag(b)` (R1, task #122) — same mechanism, `min(freed-divisor Morse, inner) + disjoint Watanabe-ADD`.

**2. ★ THE fidelity requirement: the carrier carries `supp`+`coeff` = the `diag(b)` symbolic support.** This
is the precise difference between the SOUND route and the refuted ones: threshold-only (multiplicity) →
R1-refuted (under-counts (3,3,4) as 3); the naive corner (my §7) → over-counts; the DECORATED carrier
(`SJLinGenState.supp` = which exceptional divisor weights which generator, `coeff` = the shear/coupling e) →
carries exactly the shared-divisor data, giving the correct `½minAdm`. **#5 must build peelOp so the reduced
decoration's `supp`+`coeff` faithfully record the diag(b) support** (FLAG-2: keep `ν`=product-type fixed;
record row-elimination in coeff/supp, don't shrink ν).

**3. Well-foundedness = the DRIVER's arity recursion (`decoratedBoxThresholdFinite_of_decoratedStep`), NOT
§7-C.** Each peel strictly reduces arity (`redChain`, one fewer layer), bottoms at width-2 (#4). No separate
corank-of-Z well-foundedness. The value is a TRUE statement ∀ width (minAdm perm-invariance + minAdm=cCodim
+ Aoyagi ⟹ RLCT=½minAdm, NO collapse — de-risked, so route B targets a true target).

**4. Owed pieces (the #5 checklist):**
- **N4′ peelOp** [OWED centerpiece] — `SJDecoration → SJDecoration` on `redChain`, carrying `supp`+`coeff`
  faithfully (the diag(b) support), measurability. Scaffold banked (`radialAttach`, `gen_rowMix_const`,
  `freedSchurLoss`, `Corner*`).
- **Owed piece A: UNIFORM transversality** [OWED, geometric] — route B's units sector needs
  `σ_{ρ+1}(Z)² ≍ dist²` UNIFORM on compact charts (not merely generic m=1; the [[1,t],[t,0]] tangency shows
  generic-immersion is insufficient). Banked-adjacent `normalSlice_transfer` #109.
- **ρ-Equiv PRODUCTION obligation** [OWED, fidelity] — peelOp must produce the bijection `ι ≃ (Fin a × Fin
  Dt)` (one generator per resolved-corner entry, `|ι|=a·Dt`, no spurious/omitted) — the fidelity requirement
  the #4 consumes as a hypothesis.
- **β (charges-ADD via the shift)** [BANKED] `carrierThreshold_shift` + `minAdm=peelCharge+minAdm(redChain)`.
- **α / p=0 preservation** [BANKED #144], **corank survival** [BANKED #2b].

**5. DEEP-SHARING de-risk (folded in, `scripts/deepshare.py`).** Through DEEP (≥2) peels the freed blocks
SHARE the deeper product; the hunt's mechanism — the **shared peel-radial's Jacobian `r^{#shared}` ADDS the
charges** (route B: the outer radial carries `peelCharge + minAdm(redChain)`) → the ratio is RAISED to
`½minAdm`, STRICTLY ≥ the naive independent-MIN (the collapse). Verified: this persists through deep peels
(nested radials pile onto the outer), and `minAdm` is perm-invariant on deep chains ((5,5,5,5)→17,
(3,3,3,4)→7, (4,4,2,2)→4 — all `=minAdm(sort)`). **#5-mechanism check for the formaliser:** confirm the
peelOp's `supp`+`coeff` record the shared peel-radial at each deep peel (so the Jacobian's `r^{#shared}` is
present) — this is what realizes "sharing raises," NOT a naive per-peel disjoint-Watanabe assumption (the
blocks are NOT disjoint in the deeper product; they share it, and the shared-radial Jacobian is the ADD).
The precise per-block bookkeeping is R1's `diag(b)` (`verify-r1-diagb-334.md`: `min(a-divisor, inner) +
disjoint T`); the carrier's `supp`+`coeff` carry it.

**6. The remaining CITED-Aoyagi residual (what route ii, #97 build-don't-cite, turns into a built one).** The
resolution-EXHAUSTIVENESS at arbitrary width (disjoint/shared block-elimination closes at every peel, no
missed divisor, RLCT = ½minAdm) is the Aoyagi content the descent BUILDS. #5 = route B realizing it natively.
Aoyagi stays the sole Cite for the payoff equality; the native descent replaces the opaque rlct=½codim axiom
for (□).

**Net #5 plan (current):** build peelOp (route B, carrying `supp`+`coeff` = diag(b)) + N1-uniform-transversality
+ the ρ-Equiv production; well-foundedness = the driver's arity recursion; β/α/#144/#2b banked. The soundness
(no-collapse, ∀ width) is SETTLED (theorem modulo Aoyagi); #5 is the native DISCHARGE. Audit focus (mine):
the peelOp `supp`+`coeff` fidelity (does it carry the diag(b) support faithfully) + the uniform transversality.
