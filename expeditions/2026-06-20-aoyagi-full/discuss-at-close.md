# Discuss-at-close — items for operator review (charge-ahead by default)

Per operator (2026-06-24): "record design decisions / things to discuss at the end of the expedition in
a doc; by default charge ahead." This is that doc. Controller decides autonomously now; these are flagged
for an eventual operator sanity-check at close (not blockers).

## 1. L2-PIN soundness reconciliation (DECISION I'm making autonomously)
`fm2/split-reindex` carries soundness CORRECTIONS the integration base lacks (the base took `fold3-close`'s
versions): "#120 CORRECT deepestEPivot `_deriv` spec =fst→shear-CLE (name=content)" + "DeepestGaugeChart
correct dE(0)=id overclaim (g163)" + frame-as-DATA. `sub34` has the bulk PIN modules split-reindex lacks.
**Plan:** at L2-wiring, cherry-pick split-reindex's corrections onto the chosen base PIN modules, per-file,
verifying name=content (NOT a blind merge). **For close:** sanity-check the final reconciled `_deriv` spec
is the shear-CLE (not =fst) and the dE(0)=id is not overclaimed — these gate L2 soundness.

## 2. θ analytic seam (KNOWN at-risk, brief standing decision 6)
The combinatorial order `θ=a(ℓ−a)+1` (A2) is landable from the same `(ℓ,a)` data. The ANALYTIC identity
"combinatorial count = pole multiplicity" needs meromorphic continuation Mathlib lacks. **Plan:** land
combinatorial θ fully; the analytic=combinatorial step rides inside the S2 interface for λ, but as an
independent θ statement it needs the order-tracking monomial rule. **For close:** decide whether to (a)
land combinatorial θ + flag the analytic seam honestly, or (b) attempt the analytic bridge. Default (a).

## 3. RRR general-L-first API (design caveat)
RRR-Lean (#17) defines the L=2 model + Thm-1; the headline `aoyagiLambda` API must stay general-L-first,
with RRR exposed as the L=2 INSTANCE — NOT RRR-first. **For close:** confirm RRR is a thin instance of the
general theorem, not a parallel API.

## 4. hMid / non-degeneracy carve-out (#70, audit-corrected to non-strict)
Headline is non-strict (`∀s, r ≤ H_s`, paper-faithful); the degenerate boundary (some reduced width =0)
routes via a direct-Morse lemma (#70), not the decomposition (which gives ⊤ there). **For close:** confirm
the degenerate-boundary handling is sound + the carve-out is named honestly ("DLNs mildly singular" caveat).

## 5. The one cited axiom (S2) — confirm at close
`monomial_rlct` (normal-crossing→RLCT) is the ONLY permitted citation. **For close:** `#print axioms
aoyagi_learning_coefficient` shows only `[propext, Classical.choice, Quot.sound, monomial_rlct]` (no
sorryAx, no native_decide) — the closing criterion.

(Append items as they arise during the autonomous charge.)

## 6. R1 is the LONG POLE — two mountains (controller charging ahead; for awareness)
The R1 gate (`resolution_charts` / general-M `routeStep`) is the genuine long pole. `routestep-read`
(triple+Codex) found the existing `ChainDimSplit` carrier is fixed-arity and cannot express the
layer-collapsing minAdm recursion `minAdm(M₀,…,M_L)=min_t[(M₀−t)(M₁−t)+minAdm(t,M₂,…,M_L)]` —
r1-135-design's "bounded construction" was over-optimistic. The MATH is validated (layer-collapsing =
Aoyagi's layer-peeling + the #18 depth-recursion); the Lean CARRIER needs re-architecting. TWO lanes:
(1) the **LayerSplit re-architecture** (layer-collapsing carrier + routeAtlas recurse on (L',red) + the
descent cert generalised to the collapsed chain) — BUILDING (`layersplit-rearch`, validate-first);
(2) the **general-M `IsRouteMCover`** (only the (2,2,2) atoms exist) — separate, not yet started. The
headline `aoyagi_learning_coefficient` stays honest-conditional on R1. I'm driving both lanes; flagging
because R1 closing is the main remaining effort and may take significant time. NOT a wall — a precise
re-arch path; each prior R1 dead-end (per-node Morse, §8 one-shot, threshold-only-corank≥2, ChainDimSplit
carrier) was caught honestly before building on it.

### Item 1 — L2-PIN reconciliation ASSESSED (heartbeat 2026-06-24 ~09:43)
The #120 EPivot shear-CLE correction + the dE(0)=id overclaim fix span BOTH `DeepestGaugeChart` and
`DeepestSplitReindex` (split-reindex also adds `deepestSplitHomeo` + MP/basepoint theorems). FIVE base
modules consume these: DeepestSchurShift, DeepestFramedProduct, DeepestGaugeChart, DeepestGaugeConstruction,
DeepestTelescoping. So this is NOT a clean cherry-pick — replacing the base's (fold3-close) versions risks
breaking the 5 consumers. PLAN: do it as a DELIBERATE controller-supervised step during the L2 gate-drive
(an active gauge-chart build surfaces what the proof needs), verifying name=content (the _deriv spec is the
shear-CLE, not =fst) + that all 5 consumers still build. NOT rushed in parallel with the R1 long-pole.

### Item 1 — RESOLVED (2026-06-24 ~12:10): #120 merge LANDED, soundness-POSITIVE.
l2-branch-mapper's decorrelated map found the base PIN1 (`deepestEPivot_regSlice_fderiv_id = id`) is
FALSE-as-stated ("id only up to an opaque relabel"; the repo's own 2c9c492f/12846aae + Codex confirm).
Merged `fm/deriv-frame-resume` (the #120 shear-CLE family): ONE conflict (DeepestTelescoping → took incoming
sorry-free FOLD3), the consumers merged clean (shared base `7e1ab44c` is an ancestor of HEAD — a near-
ancestor, not the divergent rewrite the 5-consumer assessment feared). @ab4fc740, builds green (3752). L2 is
re-based onto the CORRECT frame-sandwich statements (`deepestEPivot_regSlice_fderiv : ∃ F : ≃L, …`, invertible
frame factor, not id); remaining = the gauge-chart sorries (PIN1 443 / PIN2 624 / frame-endpoint 831-832 /
GaugeChart 365 / NormalFormWiring), being closed by the `l2-gauge-close` tide. NO operator action; resolved.

### Item 6 — R1 ROUTE ADJUDICATED (2026-06-24 ~12:30): Route A (cover) is the spine; `hfin` corank-risk is THE R1 watch-item.
Decorrelated pen-and-paper (+ Codex gpt-5.5 xhigh) adjudicated the two R1 routes. Route B (the per-node
squeeze `hnode`) is corank-≥2-UNPROVABLE: at the RRR cores `(n,n,p)` n≥3 (14/64 ≈22%, e.g. (3,3,4)) the
reduced core is a *product singularity*, not the width-chain smooth leaf — the rlct VALUES coincide but the
GERMS are not measure-preservingly homeomorphic, so a general-M `hnode` would force the forbidden value-only
degenerate `redEmbed`. (This corrected the controller's own earlier lean toward Route B — the decorrelation
earned its keep.) So R1 closes via Route A (cover): `hdiv_achiever` (lower bound, achiever-path box
divergence, corank-IMMUNE — BUILDING via the proven squeeze on one leaf) + `hfin` (completeness / upper
bound). **KEY OPEN RISK for R1 from-scratch completability:** if `hfin` ALSO needs the coupled-`diag(b)`
corank-≥2 chart structure, the upper bound is as hard as the refuted route — the honest move is then to
commit to Aoyagi's coupled-`diag(b)` recursion as the chart producer for BOTH bounds (the prior Decision
option ii; still S2-only, from-scratch, but a larger build). The next R1 probe (after `hdiv` lands) tests
`hfin`'s corank-sensitivity. NOT a wall — a named risk on the long pole, flagged for operator awareness.

### Item 6 — VERDICT (2026-06-24 ~13:30): the `hfin` risk is CONFIRMED. R1's long pole = the full coupled-`diag(b)` resolution; hdiv build-ready at L=2.
The wedge-design adjudication (pen-and-paper + decorrelated Codex) settled both R1 legs:
- **hdiv (lower bound, `cover_ge_div`) is BUILD-READY at L=2** — a single weighted radial blow-up gives
  `F∘φ = u²·U` (sympy-exact), Jacobian `u^{minAdm−1}`, binding axis `(1,minAdm−1)` feeding
  `monomialIntegrand_lintegral_box_eq_top`; covers the binding corank-2 `(3,3,4)`; corank-IMMUNE. The L=2
  case is BUILDING (`r1-hdiv-l2-wedge`). L≥3 = a recursive gauge chain (heavier; ship L=2 first).
- **hfin (upper bound, `cover_le`, `rlctAtOn ≥ ½·minAdm`) is CORANK-SENSITIVE — CONFIRMED.** It must control
  EVERY stratum incl. corank-≥2; a threshold-only cover mis-resolves `(3,3,4)` (codim 3 not 8). The only
  honest from-scratch route is **the full coupled-`diag(b)` resolution atlas covering U up to null** — "as
  hard as the route that refuted `hnode`" (prior Decision option ii). `F ≥ dist²` just relocates to the
  determinantal codim. **This is THE R1 long pole and the dominant remaining difficulty of the whole
  expedition.**
- **CITATION DECISION (OPERATOR'S — I hold the constraint as binding):** the alternative to the full
  resolution is citing `rlct ≥ ½·codim_min` (Aoyagi/Watanabe) — but that is a SECOND citation, forbidden by
  the one-citation brief (S2 only), and is exactly the "cites away the new content" move `lessons.md`
  rejected. **I am NOT relaxing this.** Flagging for the operator: the realistic path to the FULL general-L
  headline requires building the full coupled-`diag(b)` resolution for hfin from scratch — a large effort
  (prior design exists: `verify-r1-diagb-334.md`, tasks #26–#30, the coupled resolution = 4 at (3,3,4)).
  Options the operator may want to weigh at close: (i) commit to the full resolution (large, from-scratch,
  honest); (ii) bank an L=2/RRR milestone (hdiv L=2 + L2 gauge + D1 give the L=2 headline, with general-L
  hfin as a named Deferred); (iii) — only if the operator chooses — relax the one-citation constraint for
  hfin specifically (cite the upper bound, prove the geometric codimension = the new content). Default
  (mine, until the operator says otherwise): pursue (i), banking (ii) as the guaranteed milestone.

## 7. Process: an unattributed edit to `.agent-team/roles/controller.md` appeared + was reverted (2026-06-24)
A working-tree modification to `.agent-team/roles/controller.md` appeared (1 line, an on-message elaboration:
"Holds the executive position. Holds the *vision*… meditatively let the sea rise. Responsible for breaking
problems into dissolvable chunks, but also meticulous in asking teammates to check whether details and
project design are viable at each stage. Responsible for maintaining project hygiene."). Provenance unknown —
most likely the stopped in-main wedge tide (a12ac) overreaching while reading role files; NOT made by me.
Per discipline (don't silently accept unauthorized edits to role/config files of unknown provenance), I
REVERTED it to the committed version. The content is benign + aligned with the disposition. **Operator: if
this edit was yours (or you want it), re-apply it deliberately — I preserved the text here.** Related: the
in-main wedge tide also left transient `lean/.codex-consult/` scratch (untracked, not committed) — harmless.

## 8. R1 re-assessment (2026-06-24): the (3,3,4) hdiv "milestone" had a DEGENERATE chart; BOTH R1 legs need the resolution.
**Correcting Item 6's "hdiv build-ready at L=2".** The (3,3,4) hdiv wedge I integrated as a reviewed milestone
(@c1bf8ba4) had a DEGENERATE chart: `phi334` dropped 2 coords ⟹ Jacobian `det ≡ 0`, null image ⟹ the c-o-v
field asserted `0 = ⊤` (FALSE). The factorization + assembly are sound + reusable; the box-divergence STATEMENT
is plausibly true; only the chart's measure-change-of-variables is broken. The honest fix (b free + Schur shear
back to flat) hits the **a=0 obstruction** — the achiever curve passes through the blow-up center where the
shear is singular — which is **genuine resolution geometry**. So `hdiv` is NOT a "light wedge": **both R1 legs
(hdiv chart + hfin cover) need the coupled-`diag(b)` resolution.** Net: R1 is harder than the milestone
suggested; the dominant difficulty is the resolution geometry, shared by both bounds. **Key open question (fed
to `r1-hfin-designer`): does ONE coupled resolution serve BOTH bounds?** If yes, one hard construction (not two)
— this is the central input to the **operator R1 scope decision** (Item 6: pursue the full general-L resolution
vs bank the L=2/RRR milestone). Process note: this surfaced because I over-claimed a milestone on a
factorization-only review; corrected promptly (the soundness vigilance held — the next tide + Codex caught it).

## 9. hfin MAGNITUDE VERDICT (2026-06-24): BOUNDED — the full general-L R1 is REACHABLE (decision refined).
`r1-hfin-designer` + decorrelated Codex (independent agreement): the unified hdiv+hfin resolution is
**BOUNDED-and-formalizable — person-weeks of toric/monomial-principalization combinatorics, NOT a multi-month
AG resolution-of-singularities**. Completeness is BANKED (the recStep equality, step-by-step); termination is a
lexicographic measure bounded by Adm(M); the one crux is the monomial-sum refinement (toric, exact). The
dominant cost is the per-node measure-change-of-variables, front-loaded on the (3,3,4) genuine-diffeo chart
(task #44, being spec'd). **So the R1 scope decision is now better-informed:**
- **Option (i) — full general-L (my default):** REACHABLE + bounded (person-weeks / several focused threads),
  S2-only, from scratch. Risk is formalisation surface, not conceptual.
- **Option (ii) — bank the L=2/RRR milestone:** clean, sound, S2-only; sidesteps the entire hfin recursion (at
  L=2 the single Schur+blow-up node IS the leaf — no monomial-sum refinement, no termination induction). The
  guaranteed floor.
Both are honest + citation-clean. **Operator: pick (i) drive the full resolution, or (ii) bank the milestone +
defer general-L.** Default until you say otherwise: pursue (i), with (ii) as the banked floor. The earlier
"hfin = the dominant difficulty, possibly multi-month" fear is RETIRED — it's bounded.

## 10. Item 8 RESOLVED (2026-06-24): the degenerate (3,3,4) chart is FIXED — honest genuine-diffeo chart banked.
The degenerate-chart soundness issue from Item 8 is RESOLVED @172f16a8: an honest genuine-diffeo (3,3,4)
chart replaces phi334 (Codex's b=a·β clears the a⁻¹ shear pole polynomially — one chart does both Layer 1
and the Layer-2 origin reach), with the genuine-diffeo VALIDATION done first + sorry-free + REVIEWER-PASSED
(det Dφ = −u₀⁷·u₁² ≠ 0, independently recomputed, matching the bundle weight — the new cov is a TRUE
statement). routeM334_box_diverges went 3 sorries (one FALSE) → 1 honest sorry (the Jacobian c-o-v / the
paramsEquivFlat-as-linear-iso measure-plumbing, being closed by r1-cov-cov). No operator action; the
self-correction (catch → unification → honest chart) is the soundness discipline working as intended. The
honest chart is also the reusable shared hfin per-node atom (the unification's single hard construction).

## 11. Scope magnitude datum (2026-06-24): the L2 gauge-chart close is ~1500-2500 LoC — needed by BOTH options.
Codex-xhigh estimate (matching the prior tides' notes): the L2 PIN1+PIN2 close is ~1500-2500 LoC of coupled,
single-writer geometry (PIN1 value-fold ~350-700 unwritten strict-derivative geometry + PIN2 bridge ~500-900 +
the API thread). The MATH is settled + the foundation is banked + reviewer-verified (bricks, keystone, the
reviewer-SURVIVED frame fact, the consumer bricks, the validated last-layer-only architecture); what remains is
the large coordinated write. **Both scope options need this** — the L=2/RRR milestone floor uses the L2 gauge
chart (product_reduction → deepest_regular_core_normal_form, 2≤L), so the L2 value-fold is required either way;
it is NOT a cheap floor. **Honest realistic remaining (either option): person-weeks of formalisation, no
conceptual walls** — L2 value-fold (~1500-2500) + R1 cov (~400-600) + L=1 smooth base + wiring + D1 (L2-gated);
general-L additionally needs the R1 hfin tree (which reuses the banked general-M per-node atom). This refines
Items 6/9: "bounded" is correct, but the bound is person-weeks of grinding, front-loaded on the L2 value-fold.

### Item 11 — REFINED (2026-06-24 ~20:50): the L2 PIN1 real bottleneck is the deepest-point-frame PIVOT RE-ARCHITECTURE.
A decorrelated (Codex-xhigh) finding sharpened the L2 PIN1 picture, with no false progress (zero Lean edits). The
frame fact `exists_deepest_lastLayer_pivotFrame` — banked + reviewer-SURVIVED, and which I'd reported above as the
"reviewer-SURVIVED frame fact" foundation — certifies an ABSTRACT pivot frame; it is **not connected** to the actual
deepest-point frame (`deepestPoint_frame`, which is rThreshold-aligned). The PIN1 close therefore needs a
**deepest-point-frame pivot re-architecture** (re-target the last-layer arm to the pivot-aligned Q so the normal-form
lands the pivot corner) BEFORE the J-migration + value-fold are mechanical. **Operator-relevant honesty:** this is the
dominant L2 effort (7 chip-tides banked components but not the coupled core); the math is settled + the foundations
banked, and the re-architecture is now correctly targeted + decomposed (Stage A additive/green-bankable = the
connection itself; Stage B = the coupled migration). It does NOT change the magnitude (~1500-2500 LoC) or the option
(i)/(ii) decision — both still need the L2 gauge chart — but it is the realistic L2 bottleneck to weigh when picking
scope. No operator action required mid-flight; flagged for the close. The self-correction (over-credited abstract fact
→ named for what it is → re-targeted) is the precision discipline working.

## 12. Headline RE-SCOPED to all-widths-positive (2026-06-24 @9c96786a): a genuine over-claim caught + fixed.
The L=1 base tide caught (Codex-corroborated) that `deepest_regular_core_normal_form` — hence `product_reduction`,
`aoyagi_learning_coefficient` (the headline T), and `aoyagi_rrr` (the L=2 RRR deliverable) — was **mathematically
FALSE at a degenerate zero-width layer** (`H s = 0`, reachable at `r = 0` under the stated `hr`): there the loss is
identically `0`, so the local RLCT is `⊤` (`rlctAtOn_zero_eq_top`) while the closed form `aoyagiLambda` is finite.
**Fix (controller, banked):** added `(hpos : ∀ s, 0 < H s)` to all four lemmas + threaded the call sites + caveat in
the docstrings. **This is a STATEMENT change to the deliverable** the operator should be aware of, but it is the
honest, expected scoping: at `r ≥ 1`, `hpos` is automatic from `hr` (so no real restriction); it bites ONLY the
degenerate `r = 0` zero-width corner, which is not a DLN. Aoyagi's result is for positive-width networks. The headline
now reads "for any rank-`r` `B` with every width positive and `≥ r`". No soundness debt remains here; full build green
(3719). The self-correction (tide catches over-claim → controller re-scopes before proofs lock in) is the precision
discipline working — and a reason the headline statement was worth pinning down NOW, not at assembly.

**STRENGTHENED (2026-06-24 @15fc3913): `hpos` is `∀ s, r < H s` (STRICT), not `0 < H s`.** A read of
`resolution_charts` (Skeleton:1228) — which the L2 core reduction routes through — showed it requires `hMid : 0 < M s`
(all layers), with its own docstring stating "the headline supplies it in H-form (`∀ s, r < H s`)". The earlier
`0 < H s` fixed only the `L = 1` loss-empty case; it MISSED the `L ≥ 2` CORE degeneracy: at `r = H s` (zero reduced
width `M s = H s − r = 0`) the reduced core `dlnLoss M 0` has `prod ≡ 0` so `rlctAtOn = ⊤`, while `aoyagiLambda` is
finite — `deepest_regular_core_normal_form`'s split is FALSE there. Strengthened `hpos` to `r < H s` (subsumes
`0 < H s`) across `deepest_regular_core_normal_form` / `product_reduction` / `aoyagi_learning_coefficient` /
`aoyagi_rrr`. D1 (`deepest_point_reduction`) deliberately UNCHANGED — the deepest point stays the minimizer (finite
RLCT) at `r = H s`; only the L2 split-value formula breaks, so only the L2 chain carries `hpos`. This refines the
paper's non-strict `r ≤ min H` to the realisable non-degenerate domain (the `resolution_charts` carve-out; sound
within it, not a verbatim Aoyagi assumption). **Operator: the deliverable's domain is `r < H s` (strict).** Net of
the two re-scopings: the headline is now correctly scoped; the over-claim is closed.

## 13. R1 STATE + hero-task feasibility (2026-06-24): hdiv design-closed; hfin = the largest build + ONE feasibility risk.
A decorrelated adjudication (pp-r1-genM, exact + Codex) settled R1's remaining shape:
- **hdiv (R1 lower bound, rlctAtOn ≤ ½·minAdm): DESIGN-CLOSED** — the #135 uniform closed-form φ_M (verified on 5
  witnesses incl the codim-0 boundary). Being formalised (r1-node-bundle: the NodeAchieverChart bundle + (4,4,2,2)).
- **hfin (R1 upper bound, rlctAtOn ≥ ½·minAdm): REACHABLE from scratch (S2-only) but the LARGEST remaining R1 build.**
  The combinatorial `routeLayerAtlas` (single-divisor leaves) does NOT supply it; hfin needs the unit bounded BELOW on
  the whole chart (normal-crossing), but the #135 φ_M's unit VANISHES on a deeper in-chart corank sublocus {V=0}. So
  hfin needs a RECURSIVE coupled cover (generalising the (2,2,2) Lean `Case222CoverGETail`, which already does it for
  (2,2,2)) — per-cell = #135 φ_M (top stratum) + coupled diag(b) sub-charts resolving {V=0} for corank-≥2 cells. Smooth
  (corank-≤1) cover suffices only for near-trivial M; almost all width-≥3 M need the coupled resolution.
- **THE ONE FEASIBILITY RISK (operator-relevant):** hfin's per-cell upper c-o-v on a corank-≥2 cell needs {V=0} resolved
  recursively. pp-r1-genM is hard-validating (on (3,3,4) + a corank-≥2 case) whether that recursion TERMINATES with
  **S2-only** normal-crossing leaves. **If YES** → R1 is fully provable from scratch, hero-task feasible (the S2-only
  constraint holds), and hfin is "just" the largest build. **If NO** → R1's upper bound needs a non-S2 cite (the
  rlct≥½·codim / Aoyagi–Watanabe bound), and the hero task's "everything from scratch except S2" is INFEASIBLE for the
  full headline — the operator would then choose: relax S2-only to allow the Aoyagi/Watanabe upper bound (R1-upper
  becomes cited-conditional), or accept the headline as honest-conditional on the unbuilt recursive cover.
- **Scope-decision impact:** hfin (the recursive cover) is needed for resolution_charts at ANY L, so BOTH options
  (i full general-L, ii L=2/RRR milestone) need it; the (2,2,2) hfin is done but the general is the long pole. The
  headline is honest-conditional on hfin until the recursive coupled cover is built. **No operator action required
  mid-flight** — pp-r1-genM's validation (in progress) resolves the feasibility risk; flagged here for the close.

  **RESOLVED (2026-06-24 @a194f1e4) — FEASIBLE, no infeasibility flag.** The decisive validation came back **S2-only
  YES**: the corank-r determinantal core's {V=0} recursion (radial Δ=a·R → rank-stratified Morse-block ⊕ lower-core)
  TERMINATES at bounded depth (≤ corank) with leaves that are monomial divisors (S2) + Euclidean Morse blocks (S2-FREE,
  Mathlib `radial_ball_iff` — the same terminal the existing (2,2,2) Lean hfin already uses). The recursion threshold
  λ_{r,p} reproduces ½·minAdm EXACTLY (10/10, incl corank-3). So R1's upper bound is provable from scratch, S2-only —
  the Aoyagi/Watanabe cite is NOT required and the **hero-task S2-only constraint is FEASIBLE for the full headline**.
  (Decorrelated Codex red-team caught + repaired an over-clean first pass — the intermediate-rank strata genuinely bind;
  the conclusion survives the stratified repair, cross-checked.) **Net: no operator scope/citation decision is forced
  by feasibility.** The remaining R1 hfin work is the bounded Lean build of the recursive coupled cover (the long pole),
  with the explicit per-cell recipe now in hand (radial Δ=a·R + rank-stratified Schur + Morse/monomial leaves + the
  radial disjoint-sum lemma) — pp-r1-genM is spec'ing it build-ready for the formaliser.

## 14. L2 PIN2 needs a COMPARABILITY re-architecture (2026-06-25): the cert's exact-equality statement is FALSE.
A decorrelated finding (l2-pin2-final + reviewer + Codex, with a numerical counterexample) established that the L2
gauge-chart's PIN2 (`framedParams_split_eq_frame_raw` + `deepest_loss_squeeze`'s `hSreg_eq`) is **false as stated**: it
asserts EXACT equalities for the regular blocks read off the T-core-ZEROED `framedParamsRegPivot`, but the actual
telescoped loss is full-T and the T-core leaks into the off-diagonal regular blocks (`(C0·C1)₁₂ = (1+X0)Y1 + Y0·T1`;
counterexample L=2 H=[2,2,2] r=1 → y·t ≠ 0). **Operator-relevant honesty:** my earlier "L2 gate is close / one wire
from done" updates were PREMATURE — PIN2 is the open geometric heart, and three successive PIN2 attempts each found a
deeper issue (split-genericity → frame-genericity → this T-core leak).
- **The MATH is unaffected.** The RLCT formula (the headline) holds; rlctAt is invariant under two-sided comparability,
  and the squeeze `deepest_loss_squeeze` is built for comparability. Only the cert's *exact-equality phrasing* of the
  regular blocks was over-claimed. This is a FORMALISATION re-architecture, NOT a math obstruction or a hero-task-feasibility
  risk. The repair (comparability — `Sreg ≍ ∑deepestEPivot²`, leak folded into γ₁/γ₂) is exactly what the cert ALREADY
  does for the core blocks; PIN2 just needs to do it for the regular blocks too. It changes the cert's public signature
  (exact → comparability) — a controller-level statement re-architecture, being designed (pp-pin2-rearch) before any build.
- **No operator action required mid-flight** — flagged for the close + as an honest correction to the optimistic L2-close
  framing. The L2 gauge chart's true remaining work: the PIN2 comparability re-architecture (the open heart) + the
  L=1/2≤L case-split wire + product_reduction. PIN1 (closed) + the L=1 base + the PIN2 route-step bedrock are all banked
  and unaffected.

## 15. L2 PIN2 RESOLVED at the design level (2026-06-25): full-reg repair, NOT comparability — supersedes Item 14's plan.
The Item-14 "comparability re-architecture" plan (weaken the regular blocks to `Sreg ≍ ∑deepestEPivot²`, fold the leak
into γ) was itself **REFUTED** (pp-pin2-rearch, decorrelated Codex + exact): the `Y0·T1` leak is DEGREE-2 (same order as
the kept terms, exact cancellation), so comparability fails both directions and `deepest_loss_squeeze` is false as typed.
The SOUND repair is **full-reg `regStraighten`**: the chart's regular OUTPUT reads the FULL product core
(`E_pivot:R×S→R` → `E_full:R×(C×S)→R`), so `∑(regStraighten·).1² = Sreg` EXACTLY (no leak, no comparability slack on the
regular blocks). Adjudicated GREEN: (a) **PIN1 survives verbatim** — `D(E_full)(0) = [F | 0 | G]` (the leak is degree-2 ⟹
zero first-order core contribution), reg-in F = the same invertible `regBlockCLE`, re-used via a 1-line bridge; (b) the
transfer is a SIMPLIFICATION of the banked `_isUnit` lemma (`W := C×S` unsplit), not a new generalization; (c) it **closes
the open rlct-risk gamble** — the squeeze is now the BANKED leaf lemma `dlnLoss_two_sided_of_frame`'s TRUE comparability
`dlnLoss ≍ Sreg+Score`, so the headline rlct no longer rests on an unverified `rlct(Φ_struct)=rlct(dlnLoss)`. **Operator
note:** PIN2 went false-statement → sound-repair under the precision discipline (three deepening tide catches, then a
decorrelated design that refuted even the controller's own option-2 lean). The math (the RLCT formula) was never at risk —
only the cert's phrasing — and is now on a verified path. Building (l2-pin2-fullreg); no operator action required.

## 16. STRAY cross-expedition dir in the aoyagi-full working tree (2026-06-25) — needs homing, NOT banked here.
`expeditions/2026-06-23-fibre-codim/` (a separate expedition: Jacobian-rank / geometric-codimension, the Lehalleur-Rimányi
track — thread `25-jacobian-rank-cert` with sympy/Gröbner scripts + Codex consults) appeared **untracked** in the main
checkout while it is on `expedition/aoyagi-full`. I have **deliberately NOT committed it** to aoyagi-full's history (wrong
expedition/branch) and **NOT deleted it** (it is someone's work). It persists untracked across checkouts. **Operator
action:** home it on its own branch / the fibre-codim expedition, or confirm it should be dropped. (Also gitignored the
transient `**/.codex-consult/` scratch this tick.)

## 17. FALSE prose in a committed docstring found + corrected (2026-06-25): g156 `R − ∏S ∈ ideal(E)` is FALSE.
S5c adjudication (pp-pin2-rearch + decorrelated Gröbner Codex) found `fullProduct_core_split`'s docstring
(`DeepestGaugeBlocks.lean:126`) asserted in PROSE that the global Schur complement `R` and the per-layer Schur product
`∏S_s` differ by an element of `ideal(E)` (the regular blocks) — so they "squeeze the same" via ideal membership. **That
mechanism is FALSE** (`num(R − ∏S) mod ideal(A−1, P12, P21) = −Y1·Z0 ≠ 0`). The THEOREM itself is sound (its statement +
proof, `frobenius_fromBlocks` + `schur_P11_decomp`, never used the false claim — it lived only in the explanatory prose).
The CONCLUSION (R, ∏S squeeze the same) is TRUE, but via an exact **unit-rescaling** `R = u·∏S`, `u = ∏(1+X_s)/P00` a
bounded unit. **Corrected the docstring this tick** (cite s5c-cert; added the build-ordering consequence: feed the squeeze
the global `R`, not `∏S`). No operator action — flagged as the conceptual-slop catch + correction.

## 18. r≥2 / matrix-core S5c is NOT exact-proven — the headline NEEDS it (2026-06-25).
The S5c core comparability `∑R² ≍ ∑(∏S)² = deepestCoreF(coreAbsorb)` (via the unit rescaling `R = u·∏S`) is **EXACT for
r=1, all L** (rank-1 determinant identity, L=2/3 symbolically verified). For **r≥2 / matrix core (M>1)** the scalar unit `u`
becomes a bounded invertible SIMILARITY — only **MC-supported** (`H=[3,3,3]` r=1 2×2-core: `∑R²/∑(∏S)² → [0.99,1.02]`), NOT
exact-proven. **The full L2 headline (rank-`r` reduced core) DEPENDS on this matrix case.** pp-pin2-rearch flagged it +
recommends a short r≥2 cert before the body build relies on it; I've dispatched it onto the r≥2 adjudication (probably
routine sub-multiplicativity, but not free). **Operator-relevant:** until the r≥2 matrix-core comparability is proven, the
L2 gate closes only for r=1 cores; the general-r headline carries this as a named open dependency. Driving it now, not deferring.
- **UPDATE (2026-06-25, same day): ADJUDICATED — TRUE but GERM-scoped (a decorrelation win).** The exact matrix identity is a
  middle-factor `R = S0·W·S1·…`, `W_s = I − Z_{s+1}A⁻¹Y_s → I` at the deepest point. Codex caught a real confound the first MC
  missed: the two-sided BOX ratio `∑‖R‖²≍∑‖∏S‖²` is **FALSE for M>1** off-germ (rank-deficient `S0=εE12,S1=εE21` ⇒ R=0≠∏S),
  because the rank-≤1 `W` gives no rank protection. BUT on a true germ (all deviations→0) `R−∏S = O(ε⁴)` vs `∏S = O(ε²)`, so the
  in-sum germ bound `|∑‖R‖²−∑‖∏S‖²| ≤ C·∑E²` HOLDS — and `rlctAt` is a germ invariant, so the germ form is the right (and only
  safe) scope. **The build atom MUST be the germ form (`schur_core_germ_comparability`), not a `[m,M]` box bound** — a box bound
  would be unsound. Verified r=1,M=2 symbolically; the LDU is general in L,M. **One residual** (dispatched): a short r≥2
  matrix-PIVOT (a_s an r×r block) LDU symbolic confirm before the body build hard-relies on r≥2. No operator action — the
  dependency is closed germ-scoped; the precision (germ-not-box) is captured in the g156 docstring + s5c-r2-cert.
