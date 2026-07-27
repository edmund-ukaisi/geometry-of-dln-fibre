# Navigator pass #10 — follow-up spine pricing (route i confirmed TELESCOPES)

Authored by navigator-7 (content delivered via message, homed here by the controller per the
navigator read-only/leaf-executor boundary). Two-channel grounded: pnp-ideal
cert-ideal-reduction-depth3 §1–8 + the banked Lean infra (file:line). This is the pricing side
of the operator's follow-up decision package. Companion: journal tick 416 (verdict verified),
tick 417 (elder's shallow-instance sharpening), compass fork-16 addendum (838033059).

## Headline
Route i is **M-class, not the L** the navigator earlier flagged: the telescoping drops the
reduction from L (naive one-shot, walls) to a clean depth-INDUCTION (single-layer peel, corner a
unit at every depth, cert §1–3). The follow-up is a focused **M** research expedition for the
(2,2,2,2)/all-widths-≤2 **CLEAN** scope; **+L** for the general coupled reach.

## The LeafPullback-salvage finding (refines #8/#9) — a candidate, verify-at-open
Cert §2 gives `∏C∘chart = m·U`, m a monomial, `U[0,0]=1` (unit), so
`frobSq(∏C∘chart) = m²·‖U‖²` with `‖U‖² ≥ U[0,0]² = 1`. That is LeafPullback's content
(`residualCore = ‖U‖² ≥ lo=1`, EngineDefs.lean:43-48) **without diagonalizing**. #3a killed the
DIAGONALIZATION realization (InvVal3 demands prod exactly diagonal → det-0 projection);
LeafPullback only needs a bounded-below cofactor norm, which the UNIT CORNER gives. So #8's
"LeafPullback refuted-as-stated" is: refuted over the DIAGONALIZING α; **ACHIEVABLE over the
a-shear/peel α** (a valid det-1 chart, cert §1). This forks the spine:
- **ROUTE i-a** (factorization → discharge LeafPullback): build the peel identity, extract
  `residualCore = ‖U‖² ≥ 1`, discharge the EXISTING LeafPullback clause over the corrected
  (a-shear) α. Engine + ChartBridge UNCHANGED — less surgery.
- **ROUTE i-b** (Lemma 1 + monomial rule): the ideal equality `⟨∏C∘chart⟩=⟨m⟩` → Lemma 1 →
  monomial rule. Aoyagi's actual method (elder's fidelity preference); re-routes the engine's
  finiteness input.

Both stand on the SAME peel identity (cert §1–2 gives both). **THE ONE CHECK i-a needs**: does
the a-shear α give `residualCore ≥ 1` EVERYWHERE (all charts / all widths — unlike interior-α,
which pnp-full §4 found hits 0)? The cert's (2,2,2,2) `U[0,0]=1` says yes locally; the
all-charts/all-widths version is the confirm. Navigator recommends the follow-up **open** by
settling i-a-viable-or-i-b, since it sets the engine-surgery cost.

**Controller flag (verify-before-relying, carried from the navigator's own hedge).** i-a is the
navigator's INFERENCE from the (2,2,2,2) `U[0,0]=1`; the all-charts `residualCore ≥ 1` confirm is
the gate that makes i-a real vs collapses it to i-b. Additionally, the i-a/i-b settle must
confirm i-a delivers exactly what `hbox`/the lower bound needs (the direction: `frobSq ≥ m²` and
what it yields for the RLCT is subtle — the same direction-care the Lemma-1 typo exposed). Do
NOT commit the "less surgery" cost estimate before that settle. First-class opening gate, not a
settled route.

## Charge 1 — critical path (Lean to discharge hbox at L≥3 via route i)
- (i) RESOLUTION **[BANKED, KEPT]**: leaf-first geoAtlas tree → b_i divisors, cover,
  o5_realization, minAdm_eq_cCodim. No change.
- (ii) THE PEEL IDENTITY / depth recursion **[NEW — shared core of i-a and i-b]**:
  `∏C∘chart = α·ρ·(fresh lower-depth core)`, corner-unit each depth, telescoping over the
  geoAtlas tree. Cert proved it exact at (2,2,2,2); the Lean is the induction over the tree + the
  per-node single-layer peel. **THE TALLEST POLE for scope A.** (M)
- (iii-a) [i-a] extract `residualCore = ‖U‖² ≥ 1` + discharge LeafPullback [rides the peel
  identity]. (S–M)
- (iii-b) [i-b] LEMMA 1 ideal-domination [rides banked `rlctAt_mono` Rlct.lean:93] + the
  ideal-membership→pointwise-domination step [explicit cofactors from the peel]. (S–M)
- (iv) MONOMIAL RULE [BANKED `monomialThreshold` Skeleton.lean:88 + the RouteMState family] →
  ½·min = minAdm/2. (S)

Sequence: [banked resolution] → PEEL IDENTITY (tallest) → {i-a: LeafPullback discharge | i-b:
Lemma1+monomial} → hbox. The peel-identity induction is the tallest pole; everything downstream
rides banked infra.

## Charge 2 — reuse vs new
- **INHERITED UNTOUCHED**: engine/ledger/oracle/tree/DivBirthInv, buildTree, conOracle,
  ConState, the leaf-first geoAtlas cocycle/fold_det/leafJacobian (KEPT — leaf-first correct,
  #3b), the cover (geoAtlas_imageCover), o5_realization, minAdm_eq_cCodim,
  monomialThreshold+family, rlctAt+rlctAt_mono, the #8 generic engine
  (region_glue_of_chartBridge assembly).
- **GENUINELY NEW-MODULE**: (a) the b-chain (bChain/bExp — NOT built, grep-empty; R4-small, ~1
  module); (b) the peel identity / depth recursion (the core); (c) EITHER i-a's
  residualCore=‖U‖² extraction + LeafPullback discharge over the a-shear α, OR i-b's Lemma 1 +
  ideal-equality + engine finiteness re-route.
- **RETIRED**: the diagonalizing α completion (#21/#22), the InvVal3 diagonalization machinery
  (its CONTENT survives as the b-chain target; the DIAGONALIZATION realization retires — that was
  the category error).

## Charge 3 — width scope (both boundaries priced, razor held)
- **SCOPE A — (2,2,2,2) / all-widths-≤2 CLEAN**: every branch clean-disjoint (t₁=1 or c₁=0;
  coupling needs a layer min≥3, cert §4). The clean disjoint depth recursion is COMPLETE at the
  ideal level (cert §1–3). Cost = the M critical path. A genuine, self-contained landing
  (Aoyagi's mechanism faithfully, for the width-≤2 class).
- **SCOPE B — GENERAL incl. coupled** (any layer min≥3, e.g. (3,3,2,2)): partial-rank branches
  need Aoyagi's coupled diag(b) — non-toric bilinear coupling (`δ²‖R·C³‖²` sharing C³, cert §5).
  MONOMIALIZES, does NOT wall (value certified via verify-r1-shortcut), but HEAVIER: the
  ideal-level coupled monomial endpoint is HELD/stubbed (cert §5a — a 3-step Gröbner endpoint;
  kill = a non-toric obstruction surviving the C³ blow-up, no sign of it). Cost = A + L.
- **RAZOR HELD**: Lemma 1 / the peel identity is the load-bearing CORE — sequence FIRST, NOT
  scope-out. Scope = the general RLCT-ideal library (the reduction + Lemma 1 + monomial rule),
  with SCOPE A the near-term landing and the coupled diag(b) + θ-order + analytic-pole as the
  declared IN-SCOPE reach (sequenced later). Present as "A now, B+θ+analytic as the library's
  staged reach," never "B scoped out."

## Charge 4 — parallelization (follow-up opening)
- **RISK-FREE PRE-STAGE** (needed under either scope/sub-route, cannot be wasted): (1) the
  b-chain (A) — independent, R4-small, front-load; (2) the i-a-vs-i-b settle (does the a-shear α
  give residualCore≥1 everywhere) — a pen-and-paper confirm that sets the engine-surgery cost;
  (3) pin Lemma 1's exact statement/direction (fidelity flag).
- **SERIAL SPINE**: b-chain → peel identity (tallest pole) → {i-a discharge | i-b
  Lemma1+monomial} → engine (i-a: unchanged | i-b: re-route Hleaf) → hbox.
- **PARALLEL once the peel identity lands**: the monomial-rule connection (∑b²/⟨m⟩ →
  monomialThreshold, rides banked) ∥ the b-chain finalization ∥ (i-b) the Lemma-1 domination
  wiring (rides rlctAt_mono). The coupled endpoint (scope B) is a SEPARATE lane, only if width≥3
  is scoped in — gate it on the operator's scope call, do not pre-spend (cert §5a stub is a cold
  pick-up).

## Fidelity flag (corroborated)
Cert §6 independently confirms navigator #9's flag: worked.tex:156 states Lemma 1 as `≥`; the
correct direction is `≤` (three derivations + banked `rlctAt_mono` agree). Harmless for the
equality use (both inclusions), but pin the statement before building i-b.

## Reachability + recommended scope
The follow-up is reachable as a focused **M-class research expedition for SCOPE A** — the
make-or-break (depth-≥3 telescoping) is RESOLVED favorably, the tallest pole (the peel identity)
is proven-at-(2,2,2,2) and rides a clean induction, and everything downstream rides banked infra.
**RECOMMEND**: launch SCOPE A (widths ≤2, clean disjoint recursion) as the near-term deliverable,
declare B+θ+analytic in-scope-staged. Open with the i-a/i-b settle + the b-chain (both
risk-free). **Decision the operator owns**: A-now vs A+B-committed (the +L coupled cost); and the
launch itself (operator-gated).

## Disposition table
1. Route i → CONFIRMED tractable (M, telescopes). ACCEPT.
2. Tallest pole → the peel-identity depth induction (proven at (2,2,2,2); clean induction).
3. Sub-route → settle i-a (discharge LeafPullback, less surgery) vs i-b (Lemma1+monomial,
   Aoyagi-faithful) at the follow-up's OPEN; sets engine-surgery cost. (Controller: verify-at-open.)
4. Scope → A (widths≤2) near-term M; B (coupled) +L, operator-gated; θ/analytic staged in-scope
   (razor: core sequenced first, nothing scoped out).
5. b-chain (A) + i-a/i-b settle + Lemma-1 direction → RISK-FREE PRE-STAGE at launch.
6. Banked engine → REUSED; i-a keeps ChartBridge/engine unchanged, i-b re-routes only the
   finiteness input.
7. #8 conditional spine → stands as the durable close; the follow-up discharges LeafPullback
   (i-a) or the ideal clause (i-b) into it.

Next trigger: (a) operator's scope + launch call (A-now vs A+B); (b) the i-a/i-b settle →
navigator #11 finalizes the concrete spine once sub-route + scope are chosen.
