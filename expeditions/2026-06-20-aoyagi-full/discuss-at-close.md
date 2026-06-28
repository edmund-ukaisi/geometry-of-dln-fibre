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

## 19. L2 body: a GENERAL-L interior-frame dependency (VACUOUS at L=2) + the hS1' option-α soundness catch (2026-06-25).
Building the framedParams body (`framedParams_split_eq_frame_raw`) surfaced two items:
- **hS1' option-α was REFUTED** (pen-and-paper + decorrelated Codex): the cert's "clean" last-layer round-trip
  `framedParamsPivot (split w) last = Pf last · paramsSymm w last · Qf last` is FALSE for a non-front pivot `J` — the last
  layer carries a column-permutation `π_J` (threshold-encoded reads at pivot columns). The cert (framedbody-cert) + the lemma
  were corrected in-place to the permuted statement (a correct-statement sorry); hS2/hS3b were re-architected onto the sound
  `w0` deepest-gauge instance, NOT the false general form (reviewer-confirmed). The third L2 statement-correction catch (after
  the PIN2 false-equality + the framedParams under-hypothesization) — the precision discipline holding.
- **A GENERAL-L-only gap (operator-relevant for the scope decision):** the body's 2 interior-frame sorries (DeepestGaugeConstruction
  ~2412/2417) are **VACUOUS at the L=2 headline** (guarded empty branches — `1 ≤ s ∧ s+1 < 2` empty) but bind for L≥3: they need
  the `deepestPoint_frame_pivot_exists` bundle to CHOOSE identity interior frames (the generic rank-normal-form interior frames
  are not identity for L≥3). Closing them is an off-tide `DeepestPivotFrame` refinement. **Net for scope:** the L=2/RRR milestone
  body needs only hS1' + hproducer (the 2 interior gaps don't bind); the FULL general-L headline additionally needs the
  identity-interior-frame bundle choice. Signature note: framedParams/loss_squeeze/gauge_construction now carry `hL2 : 2 ≤ L`,
  `hpos : ∀ s, r < H s`, and an explicit `hinterface` — wired from the headline (which holds hpos/hL2) at squeeze-exists connect time.

## 20. Two more soundness catches (2026-06-25) + a latent `minAdm_M4422` name duplicate (cleanup at final wiring).
- **4th L2 catch — hproducer (d)/(e) MULTIPLICATIVE comparability FALSE for M>1.** The framedParams cert's core conjuncts
  asserted a uniform two-sided `∑Rcore² ≍ coreΦ`; a decorrelated Codex + a tilted-kernel germ counterexample (`W=I+ηE₁₂` ⟹
  `Rcore=0` while `∏S≠0` arbitrarily near the deepest point) refuted it (same shape as the earlier germ-vs-box S5c finding).
  RESTATED to the regular-energy-FOLDED form `Sreg+‖Rcore‖²≍Sreg+coreΦ`; `deepest_loss_squeeze`'s PUBLIC conclusion preserved.
  The S5c germ atom `schur_core_germ_comparability` is now BUILT (axiom-clean) and the folded (d')/(e') reduce to it.
- **5th catch — a CONTROLLER-recipe error (mine).** My r1-n4 commission told the formaliser to peel `‖T‖²` via the crude
  `radial_morse_dominates_lt_top`, which caps at the Morse threshold 2 and discards the core's rlct — UNDERSHOOTING the additive
  (3,3,4) target `c'<4` by 2. The tide + pp-r1-genM-2 + decorrelated Codex caught it and built the correct
  `radial_morse_residual_power_le` (the residual-power convolution, S2-free). The decorrelated review catching the controller's
  own recipe, not just a cert's — worth noting the controller is not exempt from the soundness loop.
- **Latent name duplicate (cleanup):** `minAdm_M4422` is defined in BOTH `Case334RouteStep.lean` and `RouteM4422.lean` (same
  namespace `DLNFibre.DLN.RLCT`); importing both together fails. Pre-existing, not introduced by these tides; `RouteM334Hfin`
  avoids it by not importing `RouteM4422Hfin`. **Must be de-duplicated before the final aggregator wiring** that pulls the R1
  hfin modules together. Operator-relevant only as a wiring-time cleanup, not a soundness issue.

## 21. The DEEPEST L2 catch (2026-06-25): the gauge chart needs a front-pivot WLOG (or a comparability restatement).
The 6th L2 soundness catch (l2-hproducer, triply confirmed: exact index algebra + numeric witness `17.98 ≠ 23.65` + 2
decorrelated Codex): `hproducer` conjunct (b), the reg-energy IDENTITY `∑ deepestEFull(split w)² = Sreg`, is **FALSE for a
non-front pivot J** — and a non-front J is the GENERIC headline case (B's rank-r pivot columns are wherever B's rank lives, not
forced to `{0..r−1}`). Root cause: `deepestEFull` (from PIN1) reads the residual *threshold-effectively* (via `pivotThr J`),
while `Sreg`/the `hconj` blocks are *pivot-aligned*; the column permutation `π_J` moves the `−1` deepest-corner between the
P00/P01/P11 blocks, so the two residual energies genuinely differ. The cheap "assert threshold-Sreg = pivot-Sreg" repair is
unsound. **This is the deepest L2 architecture catch — the gauge chart, as built, only closes for a front pivot.**
- **Controller decision (autonomous, per the charge-ahead mandate), being spec'd by pp-pin2-rearch:** the most-contained sound
  repair. (A) IF the COMPARABILITY `∑deepestEFull² ≍ Sreg` holds uniformly on a 𝓝 (the squeeze only needs `≍`, not `=`) →
  restate (b) as `≍`, no headline restructure. (B) ELSE R2 — the front-pivot WLOG: `rlctAt(dlnLoss B) = rlctAt(dlnLoss B·π)`
  (a column permutation realized by `A_{L-1} → A_{L-1}·π`, a linear MP param change), invoke the chart for the front-pivot `B·π`
  where (b) holds. Neither touches PIN1. **Operator-relevant:** this adds a repair step before the L2 body closes; the L2 gate
  is NOT "one piece (hproducer) away" until (A)/(B) lands. No math is at risk (the RLCT formula is invariant under the column
  permutation / the comparability); it is a gauge-chart-architecture correction. Not blocking the operator — driving it now.
- **RESOLVED (same day) — option A (comparability) is SOUND, the contained repair.** pp-pin2-rearch + decorrelated Codex (exact
  PD certificate, generalized eigenvalues [0.52,1.93] ∋ the 0.76 witness): the comparability `∑deepestEFull²≍Sreg` HOLDS (both
  energies vanish at w0 ⟹ PD Gram forms differing by the invertible kernel-preserving reindex `π_J·QL`). Restate (b) from `=` to
  `≍` — which `deepest_loss_squeeze` ALREADY folds (it never needed the equality). No headline restructure, no PIN1 touch, no R2
  WLOG (B validated as fallback only). Build resumed (l2-hprod-comp). **Net for the operator: the 6th catch cost a statement
  restatement, not an architecture change; the L2 gate is again hproducer → body → final wire.** Scope: the comparability's PD
  cert is exact at r=1/H0=1/H2=2; the structural argument is convention-uniform (general-H unverified symbolically — pp-pin2-rearch
  on-call if the Lean general-H operator-norm bound snags).

## 22. The L2 producer's LAST piece is RESEARCH-GRADE in Lean (the frame-stripping bridge) + an 8th soundness catch (2026-06-25).
The L2 gauge-chart producer (the geometric heart) is built end-to-end EXCEPT one germ charge: the **frame-stripping bridge**
`Rcore = P11−P10·⅟P00·P01` (the framedParamsPivot product's global Schur, front pivot) `= S0·(1−K)·S1` with the SAME per-layer
Schur cores `S_s` as the deepestCoreAbsorb core, DESPITE the per-layer `Pf,Qf` frames. **The algebra is sympy + Codex VERIFIED**
(`two-layer-ldu-verify.py` ALL ZERO; `K=Z1·⅟P·Y0`, `P=(1+X0)(1+X1)+Y0·Z1`) — so it is TRUE, not a math wall. But l2-core-de +
Codex flag it **research-grade in Lean**: 3 inverses (⅟A0,⅟A1,⅟P), no clean ring proof, and the per-layer Schur does NOT telescope
cleanly (the middle `R0⁻¹·L1⁻¹` is a full matrix). pp-pin2-rearch is pinning the Lean route (asked to flag honestly if it is a
multi-tide grind). **Operator-relevant:** this is the single hardest-to-formalise remaining piece of the L2 body; the L2 gate is
gated on it + the final wire (WLOG/squeeze-exists/case-split). If pp reports it is a deep multi-tide build, the L2-close timeline
extends here — a candidate point for the operator's scope call (full general-L vs the L=2/RRR milestone).
- **8th soundness catch (fixed, l2-core-de):** the prior producer witness bound γ₁=γ₂=1, under which (d')/(e') demanded the
  standalone equality `Score=coreΦ` — FALSE for M>1 (the kill-condition germ witness). Rebound to γ=1+C (the correct in-sum fold)
  + made the charge a genuine germ (∀ᶠ, not ∀). lemma-1 decode (coreΦ=‖∏S‖²) + the γ=1+C composition banked sorry-free.
- **DOWNGRADED (same day): NOT research-grade — a MODERATE 2-3 tide contained build (~200-350 LoC).** pp-pin2-rearch + Codex's
  honest effort re-read: the "frames" worry resolves — frame-stripping is ALREADY DONE (the banked (b)-exact `hconj` strips Pf,Qf →
  the frame-free ∏C_s); only the frame-free 2-layer LDU `Rcore=S0·(1−K)·S1` is new, and it's the `hR` the banked S5c atom already
  defers. Mathlib's `SchurComplement` API (block-LU + triangular inverses + inverse-cancel) is the toolkit; a bounded 4-lemma
  directed sequence (schur_P11_decomp style), one watch-item (the `⅟P` bookkeeping). **Commissioned as a contained build
  (l2-framestrip), NOT an operator wall.** So the L2 close is NOT blocked here — it's a moderate build + the final wire.
- **RE-ESCALATED (2026-06-25, l2-framestrip build report — the MODERATE downgrade was OPTIMISTIC).** The build banked the genuinely-new
  lemma (`schur_product_ldu`, the frame-free LDU) + a conditional bridge (`germ_charge_of_schur_factorization`), both axiom-clean and
  integrated (HEAD `dfcfeb82`), PIN1 re-verified clean. BUT l2-framestrip + decorrelated Codex(xhigh) + the reviewer all honestly
  corrected the cert's "the ONLY new piece is the LDU": the producer germ charge ALSO needs three named unbuilt obligations —
  **h1** (the per-layer block decomposition / interior-frame telescope at the BLOCK level — the HEAVIEST, ~300+ LoC), **h2** (match
  lemma-1's cores to the LDU's), **h3** (the `‖Y0‖,‖Z1‖≤√Sreg` reg-block estimate ⟹ quadratic remainder). Multi-tide (~300-1500 LoC).
  **The L2 body is NOT complete for front pivot.** This is the SECOND re-scope of this piece (MODERATE-downgrade → re-escalate); the
  producer keeps revealing the next layer. Net: real layer-filling (each banked piece is solid; the gap is now three attackable
  obligations, not a vague bridge), but the L2-close timeline extends here. **Driving h1 (design-first) now** under the charge-ahead
  mandate; flagged as a genuine scope-decision point below.
- **GENERAL-L FINDING (2026-06-25, the h1/h2/h3 formaliser, Codex xhigh-confirmed).** The banked bridge is a TWO-FACTOR Schur-LDU.
  The germ charge is stated for `2≤L`. h1(hR) lifts to general L by grouping (first L−1)·(last); but **h2 is NOT clean for L≥3** — it
  needs a RECURSIVE multi-factor Schur-core-of-product identity (absorbing the off-diagonal leaks of the first L−1 layers), which is
  research-grade. At L=2 it is trivially two-factor (h2 clean) ⇒ the germ charge CLOSES at L=2. The pen-and-paper cert's "h2 CLEAN" was
  correct **at L=2**; the general-L recursion is the refinement. **DECISION (controller): option (a)** — close L=2 fully via the bridge,
  leave L≥3 a precisely-stated guarded sorry (the established 3169/3174 / Item-19 pattern), keeping the L=2 path axiom-clean. Rejected (b)
  general-L recursive induction (research-grade AND insufficient alone — general R1/hdiv/D1 are also held general-L) and (c) signature
  narrowing (churns consumers; (a)'s guarded sorry on the true `2≤L` statement is the honest building block). **NEW unifying general-L
  gap:** the recursive multi-factor Schur-core-of-product identity subsumes the 3 L≥3 guarded sorries (2680-L≥3 / 3169 / 3174) — it is
  THE general-L producer obstruction. This sharpens Item 24's general-L arm: the general-L=2 producer (option a) is MODERATE/in-progress;
  the FULL general-L producer is research-grade here too.
- **9th catch (2026-06-25, numeric, pinned before a false build) — the bridge's exact hCore is FALSE under endpoint frames.** af8305f1's
  numeric check (L=2, rect, nontrivial frames): h1 is SOUND (framed-block LDU cores reproduce the global Schur EXACTLY), but the banked
  bridge's `hCore : coreΦ = frobSq(S0·S1)` (EXACT) is FALSE — `frobSq(framed S0S1)=1.065` vs frame-free `coreΦ=0.938`; the surviving
  endpoint frames Pf_0=P0/Qf_1=QL decorate the cores. The bridge stays SOUND as a conditional (the implication holds), but its hCore is
  unmeetable under the framed producer. **CORRECTED (pp adjudication, same day): the discrepancy is O(1), NOT O(Sreg)** — pp owned its
  h1-cert error ("work frame-free post-hconj" was wrong: hconj strips frames from the PRODUCT, but Rcore is the Schur of the FRAMED Mw,
  and the Schur is NOT frame-invariant — global ratio ~5e7, per-layer ~9e4, unbounded) AND refuted the controller's premature O(Sreg)
  framing (the gauge frames are w-independent O(1) constants, not →I at w0). So the germ-relax route is DEAD. **Real resolution =
  FRAME-CONSISTENCY:** make the producer's `coreΦ` framed-consistent with the LDU's framed cores. Decisive fork (pp taking the focused
  adjudication): is `deepestCoreAbsorb` (the core) frame-consistent with `deepestEFull` (the framed reg term)? If the true loss core is
  framed ⇒ clean framed=framed identification (~1-2 tides); if mismatched ⇒ re-point coreΦ (check it preserves `deepest_loss_squeeze`'s
  public conclusion) OR a frame-covariance lemma (heavier — a stronger scope-fork trigger). NOT a wall, but real and MEDIUM. Both the
  cert AND the controller made the same unverified-assumption error (frames vanish at w0); the numeric check corrected both — the lesson
  is to NUMERICALLY VERIFY the order of a claimed-small term before designing around it.
- **10th catch (2026-06-25, the BIG one — the independent confirm earned it).** The fully-decorrelated confirm seat (a8a8b2ff,
  commissioned BECAUSE pp self-flagged its error rate) REFUTED the additive bound `|frobSq(Rcore) − coreΦ| ≤ Ccore·Sreg` by
  EXPLICIT COUNTEREXAMPLE on the CLEAN S5a interior (cond P00=1): a reachable family with Sreg=Θ(t⁶), cores Θ(t), gap/Sreg→∞ (~1/a²);
  the bridge premise hRem is also false there; generic order Θ(Sreg³). pp's earlier O(Sreg)/O(Sreg²) readings were corner-dirty
  (hcorner-violating) artifacts. **The additive route — assumed since the 8th catch — is DEAD.** BUT `deepest_loss_squeeze`'s actual
  CONCLUSION (the folded sandwich `c₁(Sreg+coreΦ) ≤ loss ≤ c₂(Sreg+coreΦ)`) is TRUE and survives (coreΦ=Θ(t⁴) dominates Sreg; the gap
  charges to coreΦ). Only the 2681 additive INTERMEDIATE is the false piece — a bounded re-architecture of the producer's FOLD PROOF
  (re-state 2681 to the coreΦ-charge `|frobSq(Rcore)−coreΦ| ≤ 2√(coreΦ·frobSq(D)) + frobSq(D)` → multiplicative comparability → the
  sandwich; verified 0/20000). **Headline NOT threatened; deepest_loss_squeeze's STATEMENT unchanged.** This is the decorrelation
  discipline working: a load-bearing claim from an error-prone seat, gated on an independent adversarial confirm, was refuted before the
  build chased a false bound. **Process signal for the operator:** the producer fold has now re-scoped FIVE times — but the destination
  (the folded comparability) keeps surviving every probe; it's the intermediate lemma shapes that are slippery. Sound destination,
  intricate route. A strong input to Item-24's scope fork, though I continue under charge-ahead (the repair is verified + bounded).
- **11th catch (2026-06-25, the DEEPEST — operator-decision-grade).** Commissioned to PROVE the folded (♦), the decorrelated seat (a8a8b2ff)
  instead REFUTED it — triple-confirmed (its exact algebra + Codex + a decorrelated pp cross-check ad67c6b4). Exact ON-FIBRE counterexample
  ((2,3,2), r=1, a tilted kernel K=Z1Y0 nilpotent ⟹ Rcore=0 ⟹ Score=0, but coreΦ=t⁸≠0; loss=Sreg=0). **This refutes `deepest_loss_squeeze`'s
  published coreΦ conclusion itself** (`c₁(Sreg+coreΦ) ≤ loss` fails). ROOT CAUSE: **coreΦ (per-layer-product core) is the WRONG quantity** — it
  overcounts where per-layer cores cancel in the product (the tilted-kernel locus, OPEN in the fibre, NOT measure-zero). The right quantity is
  **Score = frobSq(Rcore)** (global Schur, the genuine deepest-layer residual); `loss ≍ Sreg+Score` is the BANKED leaf. **Fix:** restate the
  squeeze + producer with Score (the (♦) sorry vanishes — it becomes the banked leaf). **Headline NOT disproved** (Score gives the true loss
  RLCT by the banked comparability) **but RE-GATED** on the uncertified `rlctAtOn(Sreg+Score)=C/2` re-derivation (Newton-polytope; commissioned
  to pp + I'll independently confirm) + whether the R1 recursion also assumed coreΦ. **Lesson:** when a load-bearing identity has survived only
  narrow adversary families, commission a seat to REFUTE it (not confirm). The decorrelation discipline caught what 5 prior catches' confirm-
  framings missed. **Process note for the operator:** the producer's last
  piece has now surfaced four corrections (general-L recursion, rectangularity, the cast grind [beaten], this frame finding) — each caught
  by a tide/numeric check before a green-but-wrong build, each bounded. The L=2 close is progressing solidly but the germ-charge geometry
  is genuinely intricate; the L2-close ETA has extended across these. A candidate point to weigh Item-24's scope fork, though I continue
  under charge-ahead. Recurring API lesson worth hardening: state in-sum/core comparabilities as germ charges (`|·−·| ≤ C·Sreg`) by
  default, not exact equalities.

## 24. SCOPE-DECISION POINT for the operator: full general-L=2 producer (h1/h2/h3) vs the RRR (L=2) milestone (2026-06-25).
The L2 gauge-chart producer (the general-L=2 front-pivot body) has now re-scoped twice on its germ charge (Item 22). The remaining
h1/h2/h3 is genuine multi-tide geometry (h1 ~300+ LoC alone). **This is the natural point for the operator's pending scope call.** The
options, stated plainly:
- **(A) Push the general-L=2 producer to completion** (h1 design→build, then h2/h3, then the final wire). This is the charge-ahead
  default; I am driving it. It completes the L2 gate's gauge-chart arm for arbitrary widths at L=2 (front pivot, WLOG-reduced).
- **(B) Declare the RRR (L=2 reduced-rank-regression, Aoyagi Thm 1) milestone as the L=2 deliverable.** RRR is ALREADY DONE (#17,
  committed) — it is the L=2 headline for the reduced-rank-regression case. Under (B) the general-L=2 gauge-chart producer is
  roadmapped (the h1/h2/h3 geometry deferred), and the near-term deliverable is RRR + the R1 (3,3,4) anchor + the engine.
Note: descoping to L=2 does NOT avoid the producer — the producer IS the general-L=2 body. The real fork is (A) general-L=2 gauge
chart vs (B) the RRR special case. Either way the FULL general-L headline additionally needs R1-general + general-hdiv (the
(3,3,3,3) Frame-det wall, HELD) + D1, which are far. **No action needed from the operator to keep progress** — I default to (A) and
record this for the eventual review. The decision matters for how the close is *named* (general-L=2 vs RRR-L=2), not for whether
work continues.
- **STRENGTHENED (2026-06-25, after the 11th catch — this is now the live decision).** The L2 gauge-chart producer turned out to rest on a
  fundamentally wrong core quantity (coreΦ), refuted only after 5+ catches by adversarial decorrelation; the fix (Score) is sound but RE-OPENS
  the L2 RLCT derivation (the headline value is re-gated on the uncertified `rlctAtOn(Sreg+Score)=C/2`). Option (A) (push the general-L=2 gauge-
  chart producer) now carries: the squeeze restatement (in progress) + the RLCT re-derivation from Score (pp, gating) + possibly an R1-recursion
  coreΦ-vs-Score check + the final wire + the general-L L≥3 gaps. Option (B) (declare RRR-L=2, #17, DONE+clean, as the L=2 deliverable + roadmap
  the gauge-chart producer) is now materially more attractive — RRR is Aoyagi Thm 1 proven cleanly without ANY of this coreΦ/Score machinery.
  **My charge-ahead default remains (A)** — the fix is sound, the headline likely survives, and abandoning a nearly-converged (if hard-won)
  producer mid-repair would waste the banked PIN1/PIN2/h1/regroup/rectangular-LDU work. But this is the genuine fork: if pp's re-derivation
  shows `rlctAtOn(Sreg+Score)=C/2` cleanly, (A) is close; if it's hard or the R1 recursion is also coreΦ-infected, (B) (ship RRR-L=2, roadmap
  the general producer) is the disciplined call. **Recommend the operator weigh this on return** — it's the clearest scope decision of the
  expedition. (No block: I drive (A)'s fix + the gating re-derivation now.)

## 23. A stray off-path θ-components expedition appeared in the worktree — a real LR-θ vs Aoyagi-θ finding (2026-06-25).
`expeditions/2026-06-25-theta-components/` appeared untracked in the worktree (created by another context — not commissioned by
this controller, like the earlier `2026-06-23-fibre-codim/` stray). **Left untracked** — it is a *different* expedition (θ is the
LR component-count / SLT multiplicity, not the aoyagi-full λ headline), so committing it onto `expedition/aoyagi-full` would muddy
the branch. It carries a clean decorrelated-Codex adjudication worth preserving: **LR-θ and Aoyagi-θ are GENUINELY DIFFERENT
invariants.** LR θ_geom = number of top-dimensional irreducible components of Σ⁰ = QIP-minimiser count = `binom(m, |δ|)`; Aoyagi
θ_order = the RLCT pole order (SLT multiplicity `max Card{j : (h_j+1)/(2k_j)=λ}`) = `|δ|(m−|δ|)+1`. They **agree iff |δ|≤1**
(equivalently `S mod m ∈ {0,1,m−1}`); smallest disagreement is the all-width-2 depth-4 net (2,2,2,2,2): θ_geom=binom(4,2)=6 vs
θ_order=2·2+1=5. The mechanism: binom(m,|δ|) counts *which* |δ| active coordinates take the Voronoi rounding correction, whereas
Aoyagi's a(ℓ−a)+1 counts minimal-ratio resolution directions (an a×(ℓ−a) crossing + 1 base) — these coincide only via the small
binomial identities. **Aoyagi-full impact: NONE on the headline** — `aoyagi_learning_coefficient` is a *λ* statement, and λ AGREES
between the papers (LR codim/2 = Aoyagi λ = 3/2 for (2,2,2,2,2), F2). **Forward-looking caveat:** if aoyagi-full ever states the
multiplicity/θ (e.g. the `log log n` order term), it must use Aoyagi's order-form `a(ℓ−a)+1`, NOT LR's binom — they are not
interchangeable beyond |δ|≤1. Operator decision: whether to adopt / re-home / discard the stray θ-components expedition.

## 25. Item-24 SHARPENED by the #print-axioms reckoning (2026-06-26) — the clearest scope framing.
a8ecfbab's load-bearing point: `#print axioms` is a static term scan, so `deepest_gauge_construction` carries sorryAx from ANY sorry
in its body regardless of branch — `aoyagi_rrr` ALREADY carries sorryAx (from the 3041/3046 L≥3-interior); only the concrete
`aoyagi_rrr_222` is clean, via a SEPARATE Case222 path bypassing the general construction. **Implication:** the gauge-chart producer
route does NOT yield a clean GENERAL-width headline without closing the general-L interior (3041/3046, research-grade) — closing the
3195 L=2 diffeo only banks a separate clean lemma (`deepest_diffeo_bridge_L2`), not a clean producer/headline. So the operator's fork
is now crisp: **(A)** push the FULL general-L producer (3041/3046 + 3195-general + R1-general + general-hdiv + D1 — far, partly
research-grade) toward a clean GENERAL `aoyagi_learning_coefficient`; vs **(B)** name the CONCRETE-ANCHOR milestone as the deliverable
— RRR(2,2,2) clean (via Case222) + R1 (3,3,4) clean + the network-free engine + the banked clean L2 bricks (PIN1, PIN2, the Score
squeeze, the rectangular LDU, the diffeo bridge, `deepest_diffeo_bridge_L2`). (B) is honest + banked-now; (A) is the paper's full
general claim. I'd been imprecisely narrating toward "L=2 producer complete → L2 gate" — corrected: the gauge-chart producer is general
machinery, sorryAx from the general-L interior; clean L=2 results are concrete-path. Under charge-ahead I bank the clean L2 bricks and
hold the general-L interior as the frontier; **recommend the operator pick (A) vs (B) on return** — it determines what "done" means.

## 26. 12th catch (2026-06-26): the joint-Ψ E2 (reg-preservation) is unsound at general frames; the L=2 diffeo needs a triangular-frame bundle re-thread (1a).
The joint-Ψ cert's E2 (`deepestEFull∘Ψ = deepestEFull`) was verified by pp at IDENTITY endpoint frames only (its recurring
special-case-verification gap); a8ecfbab + pp's decorrelated re-run found it FAILS 7/8 at general invertible frames (the endpoint
conjugation leaks Ψ's moved P11 into the read blocks unless the frames are block-triangular). **Route 1 is confirmed mathematically
sound** (the front-pivot rank-r corner admits an explicit block-lower normalizer `P=[[A11⁻¹,0],[−A21A11⁻¹,I]]`, A11 invertible) — so
the fix is **(1a): strengthen `rank_normal_form_left_only/_right_only` to RETURN triangular frames + re-thread the frame bundle**. That's
a Core+producer change. Per Item-25, the L=2 diffeo this unblocks is a building block toward the FAR general headline, NOT the
concrete-anchor milestone — so a large bundle re-thread for it is lower-VOI; if the ripple is big I'll bank the L2 bridge stub as a
precise sorry naming the (1a) dependency + roadmap it (joining the general-L gaps), rather than do a bundle-wide change off the milestone
path. The triangular-normalizer Core lemma itself is clean + bedrock-valuable (banking it regardless). Another data point for the (A)/(B)
fork: the gauge-chart producer's L=2 close keeps surfacing real, bounded-but-costly soundness work (12 catches), reinforcing that the
**concrete-anchor milestone (B) is the clean banked deliverable** while the full general-L producer (A) is a long, soundness-intensive grind.

## 27. R1-general lower-leg classification refined (2026-06-26) — corrects Item-24's "(3,3,3,3) Frame-det det wall"; a third concrete R1 anchor in flight.
The general-hdiv atom `routeMCore_box_diverges_achiever` (`RouteMLayerCoverGE:120`, the lower leg of the R1 gate) was classified by a
pen-and-paper design probe (`threads/32-r1-general-hdiv-design`, exact symbolic Jacobian + decorrelated Codex xhigh) as
**NEEDS-DESIGN-then-build, NOT the research wall** Item-24 assumed. Two facts moved the estimate: (i) the atom is reduced
**M-agnostically, sorry-free**, to "construct one `NodeAchieverChart M`" (`routeMCore_box_diverges_of_nodeChart`), so each concrete `M`
is a self-contained chart build; (ii) the two anchors (4,4,2,2)/(3,3,4) are opposite ends of ONE family. The general atom still needs
**one design pass** (a descent-path-indexed `φ_M` + one general composed-determinant lemma over a variable-length factor list + a
finite-family null-slice cov) — that is the genuinely new piece, and the honest risk is that the variable-length `det_comp` is a
dependent-`Fin`-cast fight (fallback: finite-per-node). **In flight:** the **(3,3,3,3)** instance (build-now) — the tide confirmed the
ACTUAL Lean chart det MATCHES the design read exactly (`x0⁵·x1⁴·x4²·x9³`, soundness) and banked the hard det bricks
(`Kparam3333Deriv_det`, `Frame3333Deriv_blockTri`, `K7sub_det`) sorry-free + axiom-clean; the ~350-450 LoC mechanical assembly
(`Frame3333Deriv_det` + `phi3333_abs_det`/`injOn`/`cov` + `nodeChart3333` + atom) is resuming → a THIRD concrete R1 achiever-divergence
anchor. **(A)/(B) impact:** lowers the (A) cost estimate for R1-general's *lower* leg (reachable, not a wall) — but the *upper* leg
(the corank-sensitive N2b/N4 hfin lift, `RouteMSchur:164/284`) is separate and still the harder R1 pole; and the *general* atom remains
a design pass + bounded build away. The concrete-anchor reading of R1 (3,3,4) [Item-24's (B)] is unaffected; this adds (3,3,3,3) to the
banked-clean concrete inventory either way.

> **Item-27 UPDATE (2026-06-26): the (3,3,3,3) instance LANDED.** Banked sorry-free + integrated
> (`RouteM3333Atom.lean`, green-gate 8353 jobs). `#print axioms routeMCore_box_diverges_achiever_3333`
> = the (4,4,2,2)/(3,3,4)-sibling profile `[propext, Classical.choice, Quot.sound, monomial_rlct]` (the
> pure-analysis det/cov/injOn bricks are S2-free). So R1-general's LOWER leg now has three concrete
> sorry-free anchors (4422/334/3333) — demonstrably reachable, not a wall. The general atom (the design
> pass) + the R1 UPPER leg (corank-sensitive hfin) remain the frontier for the (A) path.

## 28. R1-general reachability map COMPLETE (2026-06-26) — both legs NEEDS-DESIGN-then-build, NOT walls; sharpens the (A)/(B) cost read.
Two bounded pen-and-paper probes (threads/32 lower, threads/33 upper; each with a decorrelated Codex consult) now fully map the
R1 gate `resolution_charts` for the (A) decision:
- **LOWER leg (`≤`, achiever box-divergence): REACHABLE, anchored.** Reduced M-agnostically sorry-free to one `NodeAchieverChart M`;
  THREE concrete sorry-free anchors banked ((4,4,2,2), (3,3,4), (3,3,3,3) — the last landed this session). The GENERAL atom is a
  single design pass: a descent-path-indexed `φ_M` + one general composed-determinant lemma (over a variable-length factor list — the
  one genuinely new piece) + a finite-family null-slice cov. Risk: the variable-length `det_comp` could be a dependent-`Fin`-cast fight.
- **UPPER leg (`≥`, hfin / `cover_le`): NEEDS-DESIGN, corank worry RESOLVED.** The corank-≥2 obstruction that broke the threshold-only
  VALUE recursion does NOT break hfin: hfin needs only the LOWER direction of the Schur comparison (N2b), which holds with a UNIFORM
  constant at every corank (the classical complete-pivoting shear bound `‖M21·M11⁻¹‖ ≤ 1`; the done (3,3,4) anchor already proves it,
  `frobSq_angularR_ge`). The heaviest single piece is N4 (`routeMCore_threshold_lt_top`, `RouteMSchur:284`): the depth-`r`
  WellFounded-on-corank measure recursion — a Lean-engineering long pole (dependent `Fin (r−j)` arity casts + nested cover fold), NOT
  open math (threshold arithmetic matches `½·minAdm` 30/30; two analytic atoms banked). A build-now de-risker exists (a depth-3 Route-S
  hfin instance, the upper-leg twin of (3,3,3,3)) but is FROM-SCRATCH (no pre-banked infra) → a large lift, roadmapped not charged.
- **Net for (A)/(B):** R1-general has **no research walls** — it is a sequence of bounded design passes + large from-scratch builds on
  both legs (plus the L2 (1a) + L≥3 interior + D1). This LOWERS the (A) risk profile (nothing is impossible) but confirms (A) is a
  LONG, build-heavy grind. (B) — name the concrete-anchor milestone (RRR + R1 (3,3,4)/(4,4,2,2)/(3,3,3,3) + the engine + the banked
  clean L2 bricks) — remains the honest banked-now deliverable. **The controller has consolidated here**: the reachable pieces are
  banked + the frontier is fully mapped; the (A)-vs-(B) scope choice (do we invest in the long general push, or ship the milestone?)
  is the operator's, and is now the single gate for all remaining work. No further large from-scratch (A) build will be started without it.

> **Item-28 UPDATE (2026-06-26): R1 lower-atom #1 risk RESOLVED — the (A) lower leg is build-ready.** A
> bounded Lean feasibility spike (`DLNFibre/Spike/GeneralComposedDet.lean`, axiom-clean, green) confirmed
> the variable-length composed-det is NOT a dependent-`Fin`-cast wall: in the full-ambient `List.prod` form
> the det telescopes via the determinant `MonoidHom` (`LinearMap.det.map_list_prod`) — a one-liner. So the
> general lower atom is BUILD-READY modulo bounded mechanical per-level work (full-ambient factor embeddings
> + per-factor dets + the finite-family cov), no research risk. Net for (A): BOTH R1 legs are now de-risked
> to "bounded build, no walls" — lower leg build-ready-modulo-mechanical; upper leg = one hard depth-`r`
> WellFounded recursion build. The (A) de-risking is COMPLETE; what remains under (A) is the large
> from-scratch BUILDS themselves (R1 both legs + L2 (1a) + L≥3 interior + D1). The (A)-vs-(B) scope choice
> — invest in those large builds, or ship the concrete-anchor milestone (B) — is the operator's, and is the
> single gate for all remaining substantial work. The controller has maximally de-risked + spec'd; it will
> not start a large from-scratch (A) build without the scope decision.

## 29. (A)/(B) SCOPE FORK — RESOLVED → (A) (operator, 2026-06-26). Items 24/25/26/27/28 closed.
The operator decided: **(A) GO THE DISTANCE.** This is a hero expedition; the deliverable is the FULLY GENERAL
`aoyagi_learning_coefficient` (arbitrary `L`, `M`), not the concrete-anchor milestone (B). Concrete anchors are
templates + validation, not the endpoint. Plus an **ambition recalibration**: the controller's risk-estimates have
skewed too pessimistic — mapped-as-"too large/risky" pieces frequently are not; a build that largely follows
well-established mathematics is within the "break it into pieces, dissolve one by one, let the sea rise, adapt with
state" reach and should be CHARGED, not deferred. "Roadmap + operator" is reserved for genuine research walls / bare
unargued extensions only. Both directives are now baked into `loop-prompt.md` (the mission + the ambition calibration
+ the de-risked critical path) so every tick re-grounds on them. The controller holds the strategic vision as a
feedback controller (measure, adapt) and charges the general builds. Items 24/25/26/27/28 (the (A)/(B) framing and the
R1-general reachability inputs to it) are RESOLVED by this decision; they remain on record as the de-risking trail.
The only items still genuinely needing the operator: the strays (Item 23: the off-path θ-components / fibre-codim
expeditions + `docs/expositions/theta-invariants-distinction.md`), and the PR/dev→master promotions (still gated).

## 30. Infra/CLAUDE.md drift (2026-06-26, minor) — for operator reconciliation.
`lean/scripts/lb` (the shared-mathlib-store build wrapper + global concurrency cap) exists in the main checkout
(dated Jun 24) and is used by worktree formalisers, but the main checkout's `lean/CLAUDE.md` does NOT document
it (still says "lake build"); the worktree's `lean/CLAUDE.md` DOES document it (+ a refined Aoyagi-citation note:
`RlctInterface.cited_aoyagi_dln` = the equality, vs the bare `monomial_rlct`). This is harmless branch drift — the
controller green-gates via bare `lake build` in the main checkout (works), worktrees use `scripts/lb`. Worth a
one-time reconciliation: promote the refreshed `lean/CLAUDE.md` (scripts/lb docs + the citation refinement) to the
expedition branch so main + worktrees agree. Likely originated from a parallel infra update / stray expedition.

## 31. Teammate pushed the shared branch directly (2026-06-26) — a benign dev-catch-up; process note.
The bridge/decouple tide (aac4c025) branched fresh-from-dev (the worktree default `baseRef`), merged my expedition tip,
and PUSHED its result to `origin/expedition/aoyagi-full` DIRECTLY — bringing `origin/dev`'s accumulated content
(the rlct-payoff sibling expedition, the perm-invariance + fibre-codim Core, the scripts/lb infra, CLAUDE.md updates)
onto the expedition branch as a catch-up merge. Teammates should push their OWN worktree branch (`worktree-agent-*`) and
let the controller integrate at file level; pushing the shared expedition branch bypasses controller review. **I verified
+ accepted it** because it was benign: `origin/dev` is a strict ANCESTOR of the pushed tip (a clean catch-up, no
divergence/rewrite), ALL my aoyagi work survived the merge intact, `scripts/sorries` stayed 13 (dev content is
sorry-free), and the eventual aoyagi-full→dev PR diff excludes dev's own content (dev is an ancestor). It also resolved
the Item-30 CLAUDE.md/scripts.lb drift (the branch is now consistent with dev). Force-pushing to "clean" the branch would
have been riskier (irreversible history rewrite) for no real benefit. **Going forward:** controller commissions now tell
worktree formalisers to push their worktree branch only. Operator: no action needed unless you want the expedition
branch's history kept free of dev catch-ups (then the aoyagi work would be cherry-picked onto a fresh expedition fork).

## 32. R1-lower atom ∀M gated on the general Jacobian determinant (2026-06-26) — settled math, multi-pass Lean; charging via design-then-build.
The R1-lower box-divergence atom `routeMCore_box_diverges_achiever` ∀M (an in-gate `Skeleton`/`RouteMLayerCoverGE` sorry)
is now reduced — via the LANDED ∀M chart identity `routeMCore_phiGen = u²·V` + the banked det-free `NodeAchieverChart`
fields (`RouteMGenLeafIntegrand`) — to ONE residual: the **general achiever-`t` Jacobian determinant**
`|det Dφ_{M,t}| = ∏_j |u_j|^{leafH j}` (with `leafH p = minAdm−1`), which drives the `cov` field + the a.e.-positivity.
The math is SETTLED (the parametric Schur-frame/LDU det = `|det K|^{r+c}`, sympy-verified; the descent-product Jacobian
pulls back to the source-monomial exponents). The LEAN is the work: the (3,3,3,3) `RouteM3333Atom` det is hand-instance
(literal grading + hand-built 7×7 block det + 27-coord injOn, not reusable), and the rate-engine chart `phiGen` is abstract
(chainA/chainQ reindexes, not a flat frame product) so its det isn't `phi3333`'s. Routes: (a) flat-coordinatize `phiGen`
+ a parametric Schur-frame det theorem, or (c) re-architect the general chart as a flat frame product (generalizing
`phi3333`) + re-derive the identity from the rate engine. This is a multi-pass build (the agent + Codex estimate ~multi-week),
but NOT a research wall — per the operator's ambition mandate I'm CHARGING it (a design pass to adjudicate the route + spec
the Schur-frame det keystone, then bounded sub-builds), not deferring. Flagged for operator awareness: this general det is
the single largest remaining R1-LOWER-leg piece; the R1-UPPER leg (the depth-`r` hfin recursion) + L2-general + D1 remain
beyond it. The concrete anchors (334/4422/3333) are banked for all of R1-lower if the ∀M det proves longer than hoped.

## 33. Global-memory pollution from the theta-components stray (2026-06-26, housekeeping flag).
A design scout flagged global-memory files under `~/.claude/projects/.../memory/` written by OTHER contexts —
`bundle-per-pivot-conjugation-route.md` (theta-components thread 22), `MEMORY.md`,
`c2a-fibre-component-dimension-mismatch.md`, `theta-components-count-chain-is-ncard-only.md`. These violate the
no-global-memory rule but are NOT aoyagi-full's content (they're the theta-components / fibre-codim strays', Items 23/29).
The controller did NOT delete them (deleting another expedition's notes is not aoyagi-full's call; re-homing them into
aoyagi-full would be wrong). Operator: as part of the strays' disposition, these global-memory notes should be re-homed
in-repo (in theta-components' / fibre-codim's docs) and the global files cleared. Aoyagi-full writes in-repo only.

## 34. Shared branch advanced externally again + an unsaved Codex consult (2026-06-26, minor process).
(a) `origin/expedition/aoyagi-full` (and my local branch) advanced `e0f43b23 → fa6d185c` without a controller commit:
two doc commits (a3901f84's thread.md UPDATE-7/8 blueprint) PLUS a ~30k-line dev-catch-up of OLD fibre-codim threads
(13/25/26 scripts/codex). Authored as the git user. The controller verified it's benign — NOT a merge, no `lean/`
touched, my banked Lean (`a692c021`) byte-identical, build still green 8470, my commits all ancestors — and built the
fresh OPTION-1 tide off it. Recurrence of Item 31. Process: such direct catch-ups onto the shared branch are fine for
docs but the controller can't distinguish them from a Lean change without a per-push diff; a heads-up (or routing
catch-ups via a separate branch) would tighten integration discipline. (b) thread.md UPDATE-8 cites a decorrelated
bridge-design Codex consult at `codex/bridge-design-{prompt,answer}.md`, but those files were never written to disk
(the blueprint content IS captured in thread.md). The fresh `option1-bridge` tide is instructed to re-save it. No
soundness impact.

(c) THIRD instance (2026-06-27): the `option-c-chart` formaliser's bash used absolute-path `cd`, so a `git commit`
ran against the MAIN checkout (not its worktree) — landing a stray DOCS commit (`3cf2e5fc`, the (2,2,1) statement
card) on `expedition/aoyagi-full` + pushing it to origin, and advancing the controller's local HEAD. Again benign
(docs-only, no Lean), and the agent self-flagged + cherry-picked it onto its feature branch. This is now a clear
RECURRING pattern with a clear cause: **teammates' bash defaults to the worktree, but an absolute-path `cd <repo>`
in a command silently retargets git to the main checkout.** Mitigation options for the operator: (i) instruct
teammates to use worktree-relative paths / `git -C <worktree>` for all git ops; (ii) a pre-commit hook rejecting
commits to `expedition/aoyagi-full` from a non-controller identity; (iii) accept it (controller verifies each such
advance is benign before building on it, as done here — Lean-diff check + no-merge check). The controller has been
doing (iii) successfully each time.

## 35. `codex exec` drifts into repo-dump on broad architecture questions (2026-06-27, minor process).
A formaliser's `local-codex-consult` for an "architecture/ordering" verdict drifted into a repo-context dump +
code generation rather than a sharp strategic verdict (not usable; the agent made the scoping call from the
pen-and-paper certificates directly). Observation for the codex-consultation policy: `codex exec` returns a
usable VERDICT when the prompt is a sharp decidable question with named options ("adjudicate route (i) vs (ii),
pick one, give the construction") — and drifts when asked to "analyze the architecture / figure out the ordering."
Mitigation (already applied to the next decoder-fix consult): frame strategic consults as "give a verdict on
THESE options, do NOT analyze the repo." Worth a one-line addendum to `docs/policies/codex-consultation.md`.

## 36. ∀M nodeChartGeneral scope recalibration + a worktree-base infra bug (2026-06-27).
(a) SCOPE (operator awareness, NOT a blocker): decorrelated convergence (genm-lift + xhigh Codex + 15 thread
updates) puts the full ∀M `nodeChartGeneral` at ~4 more tides — (1) the parametric `B_det M` design cert
[decoder-fix, in flight], (2) `B_det M`+rate+`Ubound` (~1 build tide), (3) the bridge funext `chartParamsGen =
pack_M∘T_M` over opaque widths (multi-tide), (4) `cov`+assemble (multi-tide). The (2,2,1)/(2,2,2)/(3,3,4)/(3,3,3,3)
anchors are all DISCHARGED + the route-(i) template validated at 2+3 boundaries + the rate ∀M banked, so this is
the width-parametric generalization, not new math. Beyond the R1-lower atom: the R1-UPPER leg, the L2 general-L
interior, D1, the headline remain. The controller is charging this autonomously per the operator's standing (A)
mandate (multi-tide-is-fine, charge the general, anchors are templates) — surfaced here for awareness, not a
decision request. If the operator wants to bank the 4 concrete anchors as an interim deliverable / re-prioritize,
that's the lever.
(b) INFRA BUG: spawning a formaliser with `isolation: worktree` bases the worktree off the DEFAULT branch's
merge-base (`413566b3`, dev) — NOT `expedition/aoyagi-full` — so the worktree LACKS the aoyagi work
(RouteM3333Det/RouteMAchieverPath absent). genm-lift hit this (worked against the shared checkout instead;
`git reset --hard` to rebase was correctly denied by the safety classifier). The prior two worktree agents
(option-c-chart/nodechart222-finish) succeeded only because they `git merge origin/expedition/aoyagi-full` into
their worktree. FIX for future build tides: instruct the agent to `git merge origin/expedition/aoyagi-full` as
step 0 (now baked into spawn prompts), OR set `worktree.baseRef = head` in settings so worktrees branch from the
current HEAD (which is on expedition/aoyagi-full). Operator may prefer the settings fix.
(c) RECURRENCE + INTEGRATION-SIDE CONSEQUENCE (2026-06-27, confirmed 2nd instance): genm-boundary's worktree
branch carries a `Merge pull request #11 theta-components` in its history (the worktree-base picked up dev's
PR-#11 content — `Core/TopDimMinPrimes*`, `ThetaOrderDistinction` — which is NOT on `expedition/aoyagi-full`).
Consequence for the CONTROLLER: a raw `git diff <my-HEAD> <worktree-HEAD>` is misleading (it mixes PR-#11 base
noise + shows integrated CLEAN modules as spuriously "deleted"), so branch-level merge of a worktree branch is
UNSAFE. The mitigation is **file-level copy of the specific deliverable files onto the clean HEAD** (identify the
agent's own commits via `git log <merge-base>..HEAD`, copy only its touched files, green-gate on my tree). This
adds per-integration overhead and is now standard practice. **This strengthens the case for the settings fix
(`worktree.baseRef = head`)** — it would eliminate both the agent-side build gap (36b) and this integration-side
base-divergence in one stroke. Recommend the operator apply it.
(d) ESCALATION — the bug now causes a SHARED-CHECKOUT TANGLE, not just a stale base (2026-06-27). `genm-upper`
(R1-UPPER N2b), spawned with `isolation: worktree`, did NOT get an isolated worktree — it operated with cwd =
the CONTROLLER's main checkout and wrote its work there (`RouteMSchur.lean` modified + `RouteMSchurAlg`/
`RouteMSchurShear`/`DetScratch` created, all uncommitted). This is worse than 36b (genm-lift merely lacked the
aoyagi work): two agents (controller + genm-upper) now share one working tree, risking (i) concurrent `lake build`
races and (ii) a stray `git add -A` tangling both parties' uncommitted files into one commit. Mitigation this
time: I asked genm-upper to REST, am holding my (1,2,1) integration until the tree is quiescent, will preserve
genm-upper's work + re-home it into a proper worktree. **This makes `worktree.baseRef = head` (or whatever makes
`isolation: worktree` reliably isolate) a HIGH-PRIORITY infra fix — the failure mode has gone from "inconvenient"
to "actively hazardous to the shared checkout."** Until it's fixed, the controller must check `git status` after
spawning worktree agents and treat any unexpected main-checkout changes as an isolation failure.
(e) RESOLUTION (2026-06-27): no actual corruption occurred. genm-upper, despite running in the shared
checkout, committed with TARGETED `git add <explicit paths>` (never `-A`), so its commits (9d1d8b34 N2b proof,
58f77fde card) contained only its own files; the controller's (1,2,1) integration (e85e0eb7) and UPDATE docs
interleaved cleanly on a linear history with zero tangle. N2b verified independently (sorry-free, axiom-clean).
Resolution adopted: (i) serialize-in-place when an agent is already mid-work in the shared checkout (let it
finish + commit targeted, controller holds builds), and (ii) a STEP-0 **self-healing isolation guard** baked into
new spawn prompts — the agent runs `git rev-parse --show-toplevel`; if it's the bare main checkout it
self-creates a worktree (`git worktree add -b <name> .claude/worktrees/<name> origin/expedition/aoyagi-full`)
and cd's in before any build/edit. genm-recstep launched with this guard. The `worktree.baseRef = head` settings
fix remains the cleaner permanent fix (operator's call); the guard is the in-band mitigation until then. NOT a
blocker; surfaced for the operator's settings decision.

## 37. ∀M achiever-chart STRUCTURAL gap + a process learning (2026-06-27) — operator awareness, NOT a blocker.
EXHAUSTIVE exact-arithmetic (genm-witness, 351 M over {1,2,3}^{L+1}, L∈{2,3,4}) found the structured-decoder
achiever chart `phiFlatStructV` is DEGENERATE (`achieverUfun ≡ 0`, the chart maps into the zero-loss locus) for
66/351 ≈ 19% of M — exactly those whose achiever rank-drops sit only at boundary layers. Root cause: the chain is
"one boundary too short" (`tStar`'s final drop falls off the chain leaf). The rate-side fields I reported "DONE
∀M" (UPDATE-147/148) hold only for the 285 interior-drop M. **Nothing false was banked** — the witness was an
explicit OPEN hypothesis (precision discipline ⟹ the gap is visible/conditional, not a hidden falsehood).
PATH (adopted autonomously, least-disruptive, genm-witness's pick): OPTION A — a 3-case ∀M chart: interior-drop
(the colPath structured-decoder chart) / boundary-drop (a separate chart, likely the pure-radial (4,4,2,2)-anchor
pattern) / L=1 (banked DeepestBaseL1). This expands the ∀M-chart scope to a 3-case construction (more tides).
PROCESS LEARNING (the important one): the witness/positivity design was certified WRONG by decoder-fix + Codex
THREE times (§5 simple witness; the "validated" carriers; the live-leaf model) — and EXHAUSTIVE ENUMERATION
(genm-witness) is what caught it each time, not Codex consults. The 5 validated anchors were ALL interior-drop,
so they never exercised the degenerate class. **New standing gate (now in lessons.md): ∀M witness/positivity/
non-vacuity claims must be exhaustively enumerated over the small-M grid BEFORE a certificate asserts them; a
Codex "validated, no wall" on hand-picked anchors is insufficient.** Operator levers: (i) sanction option A
(default, in progress); (ii) prefer option B (re-derive the decoder so the last drop is represented — bigger
blast radius, makes one uniform chart); (iii) re-scope/re-prioritize. I'm charging (i) autonomously per the (A)
mandate; flagged for a knowing-decision check since it's architecture-level + the 4th design iteration here.

## 38. L2 leg re-scoped (l2-scope, 2026-06-28) — the L2 path is MUCH cleaner than the synthesis implied + one research-risk surfaced.
A read-only scout (source-verified + Codex-xhigh) corrected the L2 picture: (a) the headline's actual L2 `sorryAx`
is a SINGLE bare sorry `deepest_regular_core_normal_form` (Skeleton:1131), not the elaborate
`deepest_gauge_construction` (whose 4 sorries are DISCONNECTED — the producer `deepest_gauge_squeeze_exists`:403 is
itself a bare sorry and the 3 modules aren't even imported into DLNFibre.lean); (b) the prior "~20 sorries / 3099/3104"
framing was stale (grep artifact; 4 active sorries); (c) **a clean BOUNDED L=2 headline needs only wiring
(Skeleton:1131 := the unwired bridge + 3 imports) + the (1a)/2915 `IsDeepLayers` strengthening** — at L=2 the L≥3
sorries (3118/3123/3289) are vacuous. (A)-PREMISE VERDICT (partly true): the L=2 leg is bounded (no research wall;
(1a) is invasive-but-localized); 3118/3123 bounded; **3289 (L≥3 grouped recursive diffeo) is a GENUINE RESEARCH-RISK
— the one place the (A) "no walls" premise is least secure.** Operator awareness: the FULLY-GENERAL (∀L) headline's
L2 leg has a research-risk at 3289; a clean L=2 instance is bounded + in progress (genm-l2). If 3289 walls, the
∀L-L2 may need operator-level design (or a scoped L=2 deliverable as an interim). NOT a blocker now — charging the
bounded L=2 path autonomously; surfaced because 3289 is the genuine general-L wall-candidate. Also a process note: I
had carried the stale "20 sorries / entangled" L2 read for ~2 ticks (used it to justify holding L2) — the scout's
source-trace corrected it; lesson = re-derive sorry-counts from `grep -c '^\s*sorry'` + the actual term, not synthesis prose.

## 39. R1-UPPER ∀M N4 general-corank lift hit a research-adjacent obstruction (2026-06-28) — the (A) "no wall" premise under test at the long pole.
genm-recstep STOP+reported (correctly, BEFORE any Lean build) that the general-corank N4 finiteness recursion has a
genuine research-adjacent gap, not laborious plumbing. The closed (3,3,4) depth-2 weld (`core_schur2_lt_top`, banked
sorry-free) is a TERMINAL base case — Sc is a scalar at corank-2, so the recursion is never exercised; corank-3 is
where the corank-(r−1) Schur core is first a non-leaf and the real recursion appears. Two gates: O1 = a j×j-minor-
dominant chart cover (the minors are degree-j polynomials, not coordinates, so the banked `pivotBlowupOn` doesn't
apply — NEW covering machinery, sizeable); O2 (the kill-condition) = the Sc-core pushforward density inequality
(`Sc = M22−M21·M11⁻¹·M12` is rational in R, so recursing on `‖Sc·S_bot‖²` via the corank-(r−1) IH needs `Sc-law ≼
free-(r−j)-box` with constants independent of the spectator entries — if it fails, the recursion plan breaks). I
commissioned a `pen-and-paper` (n4-o2-adjudicate) to settle O2 at corank-3 BEFORE declaring a wall or sinking a build.
OPERATOR AWARENESS: this is exactly where the (A) "no research wall" premise was always least secure (the N4 long
pole, flagged HIGH-risk from the start). Decorrelating first per the mandate (operator reserved for *confirmed*
research walls). If O2's verdict is OBSTRUCTION (the pushforward fails / needs spectator-dependent constants), the
∀M R1-UPPER finiteness needs an operator-level re-scope or a different N4 route — I'll surface it as a decision then.
NOT a blocker now: the corank-2 weld + N1/N2a/N2b/N3a/N3b stand; R1-LOWER, L2, D1 continue. The fallback if O2 walls:
R1-UPPER's finiteness already has a CITED route (Watanabe's universal `rlct ≤ ½codim`) — the from-scratch N4 is the
"go the distance" upgrade, and a scoped retreat to the cited upper bound keeps the headline intact if N4 proves a wall.

**Item 39 RESOLVED (2026-06-28, same day):** `n4-o2-adjudicate` (pen-and-paper, exact algebra r=3,j=1 + r=4,j=2 +
decorrelated Codex-xhigh) returned **O2 HOLDS (witness)**. The controller's "pushforward density `dR ≽ ρ·dSc`"
framing was the wrong lens — the recursion never changes variables R→Sc; at fixed spectators `M22↦Sc` is a pure
translation (Jac≡1) into a fixed spectator-independent box, so the Sc-core R-integral is spectator-uniformly
dominated by the free-box corank-(r−j) JOINT core (the IH). The additive threshold survives (Morse block integrated
jointly). O1 (the minor-dominant cover) is a build cost, not a math wall (minorpivot-cert BUILD-READY). **The ∀M
R1-UPPER N4 is bounded-after-machinery; the (A) "no research wall" premise SURVIVES the N4 long pole.** No operator
re-scope needed; genm-recstep re-engaged on the build (corank-3 first; the one fragile Lean point is the JOINT-core
IH statement shape). The cited-rlct fallback stays unused. Net: the decorrelation both confirmed the gate AND
corrected the controller's framing — the bedrock-checkpoint discipline working a fourth time this expedition.

### Item 40 — D1 is L2-COUPLED via a shared gauge-slice; build it REUSABLE (heartbeat 2026-06-28)
Goal-distance map (this tick, verified against Skeleton): the headline `aoyagi_learning_coefficient` (1725) rests on
exactly four named sorries — **1234 `resolution_charts` (R1)** [staffed: genm-boundary LOWER + genm-c3wire/genm-recstep
UPPER], **1131 `deepest_regular_core_normal_form` (L2)** [staffed: genm-l2 KC1 + the producer #102], **1177
`rlctAt_deepest_le_of_optimal` (D1)** [UNSTAFFED], and **1707 `aoyagiTheta_eq` (A2/θ)** [secondary, off the λ path,
standing decision 6]. A1 (`lambdaCore_eq_clean`, the closed-form↔core-value Karamata bridge, 4246) is **PROVED** — so
the "headline arithmetic" is NOT an open decoupled piece (it was a candidate 5th front; recon retired it).

**D1 finding (re-read cert #112 / thread 04-d1-scope):** D1≥ is value-free and closes parallel to R1, but its hard
obligation **(a)** — the homogeneous-residual constant-rank chart at an arbitrary optimal `v` — is *the same
gauge-slice / Morse-with-parameters machinery* as L2's `deepest_regular_core_normal_form` (#44/1131). So D1(a) is
**L2-coupled, not a clean decoupled front** — spawning a D1 Lean build now would front-run L2's unvalidated gauge-slice
machinery (the same "don't stand on an unvalidated instance" bar applied to genm-recstep's recStep this morning).
Obligation **(b)** (the fibre-cone closure `prod(t•A)=t^L·prod A`, pure algebra) IS decoupled + small.

**ARCHITECTURE ITEM (action when the L2 producer phase #102 starts):** the producer's gauge-slice lemma should be built
as a REUSABLE `local_constant_rank_chart` interface that BOTH L2 (1131) and D1(a) (1177) consume, rather than a
producer-internal specialization. If built reusable, D1 collapses to (a)=reuse + (b)=pure algebra. Surface to genm-l2
when it transitions KC1 → producer; don't block. Net for this tick: the critical path is at **maximal sound
parallelism** (4 fronts on named sorries); no further front is warranted without front-running a dependency.

### Item 41 — FRAMING CORRECTION: the ∀M-smeared lift is materially larger than "template parametrization" (2026-06-28)
genm-boundary (R1-LOWER smeared, bg `a223…`) rested at a genuine wall with a finding that **corrects the controller's
de-risking**. I had de-risked the ∀M-smeared lift (UPDATE-191) to "3 bounded families, all r·c≤2 — just parametrize
the (1,2,1)/(2,3,1)/(1,3,2) validate-small templates, charge through." genm-boundary + a decorrelated Codex
(`genM11-arch`) found this **under-estimates the (1,1) family** (34/46, the largest): it spans **L∈{2,3,4}** with
varying bottleneck layer + flatDim, and for L≥3 the front `P = A⁰·A¹·…` is a **degree-(L−1) matrix product**. The
validate-smalls' per-M explicit reshape (`packNNN`/`finNEquivFlatIdxNNN`/`splitN`) is **scaffolding, not the ∀M
substrate** — it can't generalize over varying L/flatDim. The lift must adopt the **boundary-CLEAN "Option-A"
flat-coordinate architecture** (generic `deepestCoords`/`paramsEquivFlat_symm_decode`/`LossHomogeneity`, front product
carried abstractly), not a template reshape.

**Still a BOUNDED build, NOT a research wall** (per the ambition calibration): the missing piece — the front-bottleneck
→ rank-one bridge — is standard linear algebra (product through a `Text=r=1` width-1 layer ⟹ likely a literal outer
product `u·vᵀ` ⟹ rank-one columns). genm-boundary banked the load-bearing generic cancellation
(`scalarGram_cancel_of_rankOneColumns`, sorry-free/S2-free/validated-5/5, on branch `aoyagi-full-genM-smeared-lift`,
NOT yet on canonical) and rested soundly at the fresh-infrastructure sub-target rather than sinking it silently under a
"charge through" framing. **Controller decision:** took genm-boundary's recommendation (b)-then-(a) — spawned a
decorrelated pen-and-paper (`genm-frontrank`) to adjudicate the front-bottleneck → rank-one structural fact (mechanism
+ exact statement + minimal Lean bridge + whether the (2,1)/(1,2) families also need Option-A) BEFORE the large
formalise, given the framing was just corrected (bedrock-checkpoint: decorrelate before a large fresh build). genm-boundary
stood down; its lemma stays banked on the feature branch (integrate the (1,1) atom as a complete unit, not the lone lemma).
**Operator note:** the R1-LOWER smeared branch is a larger build than synthesis UPDATE-191 implied; no research wall,
but the "3 quick template parametrizations" estimate was wrong. Watching whether the recalibration extends to all 3 families.

### Item 42 — Cross-lineage name-clash deconfliction REQUIRED before final-headline aggregation (2026-06-28)
Integrating `core_schur3_lt_top` (R1-UPPER corank-3) into the FULL `DLNFibre` aggregator surfaced latent top-level
name-clashes between two separately-developed concrete-anchor lineages that had never been co-aggregated:
the **(3,3,4)-anchor lineage** (`Case334RouteStep`, `RouteM334Ratiofin`, `RouteMSchurDepth2`, `RouteMSchurCorank3`)
vs the **(4,4,2,2)/(3,3,3,3) lineage** (`RouteM4422`, `RouteM3333Atom`). Confirmed clashes: `e2`
(RouteMSchurDepth2 `Fin2×Fin2≃Fin4` vs RouteM3333Atom `Fin3≃{frameB=2}`), `minAdm_M4422` (Case334RouteStep vs
RouteM4422); likely more. Each is a generic file-local helper that both lineages happened to name the same.

**Controller decision:** `core_schur3_lt_top` is sound — sorry-free, **axiom-clean** `[propext, Classical.choice,
Quot.sound]` (verified via the AxCheck import closure, which excludes RouteM4422 → no clash), **standalone-green**
(8290 jobs). Banked as a **verified file** on canonical (`09a16420`, the bdca2da3 pattern), NOT aggregated. The
co-aggregation is a **mechanical packaging cleanup**, NOT on the immediate critical path — each leg (R1-UPPER recStep,
R1-LOWER, L2) builds in its own import closure where the lineages don't collide. It IS required eventually: the final
`aoyagi_learning_coefficient` proof will import both lineages (R1's resolution_charts needs the Schur recursion AND the
achiever atoms), so the clashes must be resolved before the monolithic headline builds. Deferred to a dedicated
formaliser tide (task #113): enumerate ALL clashes across the two lineages, rename/namespace the colliding helpers in
ONE systematic pass + single rebuild — NOT whack-a-mole (the iteration cost is ~5-10min/rebuild). **Operator note:** this
is the first concrete sign that the separately-grown concrete-anchor modules will need a namespacing/deconfliction pass
to co-exist in the final headline — a known, bounded, mechanical cost, surfaced early.

### Item 43 — The L2 producer's heavy core scoped; 3289 (L≥3) is THE research-risk to flag (2026-06-28)
genm-l2 completed the L2 KC1 leg (probe + KC2 + row-WLOG + leading-block invertibility + the row-selector — all banked
axiom-clean) and recon'd the L2 producer. **Finding:** the headline's L2 obligation (1131 `deepest_regular_core_normal_form`)
routes `1131 ← deepest_normal_form_of_value ← deepest_gauge_squeeze_exists ← deepest_gauge_construction`, and the `sorry`
at 2915 is the ENTIRE BARE BODY of `deepest_diffeo_bridge_L2` — a multi-hundred-line gauge-slice diffeo-bridge build (the
g146/#44 non-measure-preserving CoV via `rlctAtOn_unit_invariant_aux`), NOT a wiring. It assembles banked bricks (E1, the
IFT local-diffeo, the `rlctAtOn_diffeo_bridge_of` interface, the Core normalizers, KC1's [Invertible A11]) + the unbuilt
Ψ-construction + E2 reg-preservation.

**Controller decision (within the autonomous mandate — charge large-but-established, roadmap genuine walls):**
- **The L=2 bridge (`deepest_diffeo_bridge_L2`) is large-but-BOUNDED → CHARGED** (genm-l2, #118; SPECIFY-first, diff-gated
  through the E1/E2 soundness region, g146-design-check first). It's the heavy L2 core on the headline critical path AND the
  D1 1177(a) lynchpin.
- **3289 (the L≥3 grouped recursive diffeo) is THE genuine research-risk** (#120) — the one place the (A) "no walls" premise
  is least secure. Even a perfect L=2 bridge leaves `deepest_gauge_construction` L≥3-sorryAx. **Roadmapped: scope LAST** (after
  the L=2 bridge + the other legs land, design in hand). **Operator-relevant: the fallback if 3289 is a true wall is the CITED
  Watanabe `rlct ≤ ½·codim`** (the upper-bound half; the geometric codim is the new content either way) — but that's a
  citation the brief otherwise avoids, so flag it as the decision point if 3289 doesn't yield. This + N4's 3289-analogue are
  the two research-risk frontiers; everything else is bounded/landed.

**Item 42 RESOLVED (2026-06-28):** genm-c3wire did the systematic deconfliction — 5 (3,3,4)-lineage renames + 1
false-positive call — and AGGREGATED general-T corank-3 into the full `DLNFibre` build: green 8511 jobs, the
two lineages co-exist, `core_schur3_lt_top`/`lintegral_matBox_smul` clean-three in the aggregated context.
Integrated to canonical (`b515a412`). The cross-lineage co-aggregation WORKS — this de-risks the eventual
final-headline aggregation (the concrete-anchor lineages can co-exist; the remaining aggregation cost is
mechanical, demonstrated bounded). The mechanical-cost prediction held exactly.

### Item 44 — L2 bridge sig was UNSOUND (the (1a) triangularity gap); controller-miss owned + route (A) (2026-06-28)
genm-l2 + a decorrelated Codex (xhigh, consult 8a0e82ad) caught that `deepest_diffeo_bridge_L2` (2853, the L2 bridge
the 2915 sorry must fill) is UNSOUND as stated: E2 (`deepestEFull∘Ψ=deepestEFull`) reads the reg blocks through the
GENERIC endpoint frames (`endpointP0=Pf 0`, `endpointQL=Qf last`), and the (2,2) block leaks into P01 via
`(Pf 0)₀₁·M11·(Qf 1)₁₀` — FALSE at general frames. The sig is missing `(Pf 0)₀₁=0` + `(Qf last)₁₀=0` (block-triangular
boundary frames). This is the synthesis **Item-26 (1a)** gap, now precisely located in-Lean.

**Controller-miss owned:** my skeleton-approval (UPDATE-211) verified the `_impl` sig typechecks + matches the 2915
obligation, but did NOT verify the OBLIGATION (the 2853 sig) is itself PROVABLE — and it isn't. genm-l2 correctly
refused to fill the unsound verbatim sig despite the approval (precision + don't-build-green-but-wrong). **Lesson for the
controller's skeleton-gate: a sig that typechecks + matches an existing sorry can still be a WRONG-STATEMENT sorry
upstream — verify the obligation's soundness, not just the sig-match.** (The 2853 sig was authored unsound originally;
the diff-gate's spirit + the decorrelated Codex caught it before any green-but-wrong shipped.)

**Route decided (A):** amend the bridge `_impl` + the 2853 sig to add the two triangularity hyps; CONSTRUCT triangular
frames in genm-l2's `_L2` wrapper (deepestPoint_leadingBlock_isUnit + the banked blockLower/Upper normalizers); the
frame producer + Core stay UNTOUCHED (generic path stays sorryAx). The one soundness check: the SAME triangular frames
through both the bridge AND the `_L2` squeeze. **Fallback → O1** (controller strengthens `deepestPoint_frame_pivot_exists`
to return triangular frames — the Item-26 (1a) Core+producer re-thread) if the frames turn out producer-internal.
**Operator-relevant:** the L2 bridge is a bit larger than the "~2-tide" estimate (the (1a) triangular-frame construction
rides on top), but still bounded + sound via route A; no new research-risk (3289 remains the only one).

### Item 45 — R1-UPPER firing PASS modulo carving; the "fixed-R inner is false, the JOINT is needed" soundness point (2026-06-28)
genm-firing built the full R1-UPPER recStep firing (`schurRecStep_four : SchurRecStep 4 schurLambda`, ~770 LoC,
RouteMSchurFiring.lean) — fidelity-reviewed PASS, ALL pieces sorry-free + axiom-clean except the one scoped carving
`schurRatioResidGen_mid`. The abstract-IH decoupling HELD end-to-end (no concrete general-T core_schur3 needed — the
firing invokes the abstract `SchurLowerIH`). Dispatched the carving (~200 generic-r lines, Codex×3+reviewer ROUTE-A/no-wall)
to a dedicated `genm-carving` tide on genm-firing's branch; genm-firing stood down. When the carving lands →
`schurRecStep_four` sorry-free → `schurGen_lt_top_modulo_recStep` capstone CLOSES R1-UPPER.

**Soundness point (recurring — record for the Schur recursion):** genm-firing caught (reviewer-confirmed) that a
*fixed-R* inner-S finiteness `∫_S frobSq(R·S)^{−c'} < ⊤` is FALSE (it DIVERGES at singular R) — the heart must be the
**JOINT ratio-residual** (integrate z carrying the free M22 that the IH consumes), mirroring corank-3's
`schurInner3_ratiofin`. This is the same shape as the earlier corank-3 "R-integrated inner" finding (n4-o2): the fixed-R
slice undershoots/diverges; the joint free-(M22,S_bot) core is the correct, IH-consuming abstraction. Any future
Schur-recursion work (the general ∀p lift beyond p=4, etc.) must use the JOINT residual, never a fixed-R inner. Caught
before sinking, both times — the decorrelated-Codex + reviewer discipline working.

### Item 46 — Controller-miss: recorded "bridge near-done" from trivial-about-placeholder fills (2026-06-28)
genm-l2 honestly corrected the L2-bridge progress reading: I'd recorded (UPDATE-214/216/217) the bridge as
"S2-heaviest filled, S6 last / dual near-completion" — propagating genm-l2's task-completions (#125-131) at face value.
But `psiSplitRawL2` was still the placeholder `id`, so S2/S3/S4 were proven TRIVIALLY-about-id (δ=0, `*_const`) and
re-open when the real joint action lands. The genuine bridge content (real Ψ + re-proven S2/S3/S4 + S6) is ~2 tides
UNBUILT; only S5 (the genuine E2 identity) + the scaffold + the wiring are real.

**Lesson (controller skeleton/progress-gate):** "filled"/task-completed ≠ substantively-proven — a sub-lemma can be
proven trivially about a placeholder def. Before recording a leg as near-done, verify the load-bearing defs are REAL
(not placeholder `id`) and the heavy sub-lemmas were proven for the REAL map. This is the same family as Item-44
("typechecks ≠ provable") — both are recording progress without verifying substance. genm-l2's honest re-check + the
diff-gate caught it before it travelled. The R1-UPPER firing, by contrast, IS genuinely ~1-piece (carving) — its pieces
are really sorry-free (reviewer-PASS, force-#print-axioms), not trivial-about-placeholder. So the dual-near-completion
claim was half-right; the L2 bridge is the longer pole (~2 tides). No overstated "done" shipped; corrected in UPDATE-218.

### Item 47 — Carving coordination tangle: consolidate on the de-facto builder + commit-forward-only (2026-06-28)
The R1-UPPER carving handoff tangled: after genm-firing delivered the firing (reviewed-PASS, modulo the carving) and
recommended a fresh `genm-carving` tide, I dispatched genm-carving + told genm-firing to stand down. But genm-firing
(message-crossing) kept productively working — banked +2 carving prereqs, reused the canonical cover, then FORCE-PUSHED
(a4c053e9, rebased onto 92485be7) — so the base genm-carving was told to rebase onto (e5396a3d) was rewritten, leaving
genm-carving chasing a moving target. Three agents (genm-firing, genm-carving, genm-recstep-on-call) entangled on one heart.

**Resolution + lesson:** consolidated on genm-firing (the de-facto builder — best state, all prereqs banked, actively
executing the carving sub-tasks), stood down genm-carving, and mandated **commit-forward-only** (force-push rewrites
history + breaks others' rebases — it's what tangled this). General controller pattern when a teammate doesn't heed a
stand-down due to crossing AND has out-executed the handoff: don't fight to enforce the original plan — adapt to reality
(consolidate on whoever holds the best state + is executing), stand down the now-redundant tide, and enforce no-force-push
on the shared branch. The underlying friction is message-crossing (teammates iterate faster than the relay); mitigations
already in use: anchor on each teammate's LATEST substantive state, flag crossings explicitly, resolve collisions decisively.
No work was lost (all prereqs banked on genm-firing's branch). Operator note: this is process friction, not a math wall —
the carving itself is bounded (ROUTE-A, prereqs done); only the bespoke generic zEG reshape remains.

### Item 48 — "Approve-continue" acks cross with teammate self-dispatch → duplicate agents on the same work (2026-06-28)
Third coordination crossing this session, same root cause as Item-47 (message-crossing), new shape. Sequence: I acked
genm-l2 "path-2-continue approved" (UPDATE-221 tick); that prompted genm-l2 to RESUME its background sub-agent
`a9db8d3fdc94a478e` on the CLE→S4→S2→S6 work. One tick later genm-l2 depth-checkpointed; I spawned a FRESH tide
`genm-l2cle` on the *same* work. Result: two agents (a9db8d3 in genm-l2's worktree; genm-l2cle in its own) on identical
work. genm-l2 flagged it fast + couldn't TaskStop a9db8d3 (didn't own it). I owned a9db8d3 → TaskStop succeeded;
consolidated on genm-l2cle (fresh context, honors the checkpoint; a9db8d3 was the 1.3M-token-deep one). **Separate
worktrees ⟹ no file-clobber** — the cost was only duplicate effort. **Silver lining:** a9db8d3 had just cracked the
single gating brick `regGaugeSlotEquivCLE` (Variant B, coe-by-rfl) before the stop; I harvested it from its result
snapshot → genm-l2cle, so nothing was lost.

**Lesson + mitigations** (controller-side, since the crossing is intrinsic to fast async teammates):
1. **An "approve-continue" ack must name the OWNER explicitly** ("genm-l2cle continues X", not a bare "continue
   approved") — a bare approval invites the teammate to self-dispatch a (possibly background) agent onto the same work.
2. **A depth-checkpoint acceptance must say "dispatch nothing further; do NOT resume any sub-agent"** — otherwise an
   earlier "continue" ack + a later "checkpoint" ack both fire, spawning duplicates.
3. **Track who OWNS each background sub-agent** — the controller could TaskStop a9db8d3 where the spawning teammate
   couldn't; know your stop-authority before a collision.
4. **Separate worktrees are the safety net** — even under a full duplicate-dispatch, separate worktrees prevent
   corruption (only wasted tokens), and a killed agent's result-snapshot can still be harvested. Keep one-tide =
   one-worktree.

### Item 49 — A depth-checkpoint that didn't stick: when a teammate builds through a stand-down AND lands clean work (2026-06-28)
genm-firing depth-checkpointed the carving (UPDATE-220) → I spawned genm-carve2 + stood genm-firing down. But genm-firing
kept building through the stand-down (message-crossing, as in Items 47/48) and landed REAL clean work: #133 + #134
(`frobSqGenJoint_ne_zero_ae`, the substantial a.e.-positivity) axiom-clean + green, plus a Codex zEG consult that resolved
the carving's only design risk (pure-volume, no gap). So two agents (genm-firing + genm-carve2) were on the carving, and
genm-firing — the one I'd stood down — held the best state.

**Call:** reversed the handoff, consolidated FINALLY on genm-firing, stood down genm-carve2 (harvest-first). Rationale:
(1) Item-47 — consolidate on the de-facto builder holding the best state; (2) the depth-checkpoint's PURPOSE (avoid bad
late commits) was being served regardless — genm-firing landed axiom-clean, not green-but-wrong; (3) the Codex consult
*removed* the design risk that made depth-thrash scary, so the remaining work is mechanical volume (low thrash-risk even
for a deep agent); (4) keeping the fresh-but-behind genm-carve2 would waste the landed #134 + re-run the consult + require
fighting genm-firing to stop (failed 3× via crossing).

**The discipline isn't "obey the checkpoint ritually" — it's "don't charge work your depth makes risky."** When the depth
isn't biting (clean commits) and the design risk is gone, the fresh-tide swap loses more than it saves. **But the flip-flop
itself (approve→checkpoint→re-approve across 3 ticks) is the real cost** — each flip seeded a duplicate-dispatch tangle.
Mitigation going forward: (a) a depth-checkpoint acceptance must come with "ACTUALLY STOP — tell me + rest, don't build
through it" so the next checkpoint is real; (b) don't pre-emptively spawn the fresh tide until the deep agent CONFIRMS it
stopped (the spawn-then-it-keeps-going is what creates the duplicate); (c) one firm consolidation, then hold it — resist
re-flipping on the next crossed message. Net: no work lost (harvest), carving materially de-risked, but ~2 ticks of churn
that tighter sequencing (confirm-stop-before-spawn) would have avoided.

### Item 50 — Carving split-brain: a branch audit should have caught the parallel duplicate earlier (2026-06-28)
The carving (R1-UPPER's `schurRatioResidGen_mid`) ended up split across two diverged branches: genm-firing (+29 from
base 162fc569: readback + a.e.-pos + cover + design consult) and genm-carving (+18: #135 carve cellOfG/bgShiftG + #136
resolvedShiftRG_le + a 2nd a.e.-pos + inner machinery). Both still `sorry` at the final lemma. They built COMPLEMENTARY
halves (plus an overlapping a.e.-positivity, done two different ways) — so neither branch alone closes the lemma, and
genm-firing was about to RE-DERIVE #135/#136 (~250-300 lines) that genm-carving had already built.

**My error:** across Items 47-49 I repeatedly framed genm-carving as a "redundant duplicate to harvest + stop," and acted
on confirm-stops, without ever AUDITING what it had actually built. The git log (lemma names per branch) showed it was
producing the load-bearing half — I only ran that audit this tick, after it had diverged 18 commits. The harvest-relays
I did send (stepShearG, cellOfG) were piecemeal; I never stepped back to see the whole parallel build.

**Resolution:** redirected genm-firing to RECONCILE genm-carving's bricks (read via `git show origin/<branch>:<file>`,
re-place additive defs, resolve the a.e.-pos name overlap) + assemble — NOT re-derive. genm-firing stays integrator
(canonical, active, holds design+cover+readback); genm-carving stopped with full credit.

**Lesson / standing mitigation:** when two tides touch the SAME target (even if one is nominally "stood down"), run a
periodic **branch audit** — `git log --all` + per-branch lemma-name diff (`git show <branch>:<file> | grep '^theorem'`)
— BEFORE the branches diverge far, not after. A confirm-stop that doesn't stick (Items 47-49) is a signal to AUDIT what
the non-stopping tide is producing, not just to re-send the stop. Cheaper still: never let two tides own overlapping
sub-bricks of one lemma — assign disjoint sub-bricks explicitly, or accept ONE builder and truly enforce it. The
reconcile cost here (~one focused tide) is the price of the split; it's recoverable (no work lost, all bricks banked),
but a 5-line branch audit two ticks earlier would have prevented the divergence.

### Item 51 — Branch audit must include SORRY-DISTANCE, not just lemma-name presence (2026-06-28)
Refines Item-50. Last tick I ran a lemma-name branch audit (good). But THIS tick I spawned genm-assemble to re-derive the
carving coupled-core on genm-firing's base WITHOUT checking which lineage was closest to its FINAL sorry — genm-carving was
~1 sorry from R1-UPPER done (full machinery + assembly skeleton; only schurRatioResidGen_mid open). genm-firing's read-only
diligence caught it and halted #137 rather than add a 4th lineage. Had I checked `git show <branch>:<file> | grep -c sorry`
per carving branch (a 3-line audit), I'd have seen genm-carving at 1 sorry and assigned the finish THERE, not spawned a
from-scratch coupled-core build on a less-complete base.

**Lesson:** when consolidating duplicate lineages, the audit is two-dimensional — (a) which lemmas each branch has
(Item-50), AND (b) **sorry-DISTANCE: how many/which sorries remain on each branch.** Assign the finish to the branch CLOSEST
to its terminal sorry (fewest remaining), not the branch with the "canonical" base or the one I last designated. Closing a
near-complete branch's last sorry then reconciling its lineage into canonical (cover/names) as a SEPARATE step beats
re-deriving the whole thing on the canonical base. Concretely, before assigning any "finish the proof" task across
divergent branches: `for b in <branches>; do echo $b; git show $b:<file> | grep -nc sorry; done` and read the sorry
identities. Cheap; would have saved this tick's mis-spawn. Credit: genm-firing's unprompted read-only diligence (sorry-count
+ lemma inventory per branch) is exactly the audit discipline — bake it into the controller's consolidation routine.

### Item 52 — Redirecting a tide's BASE is not free: an existing worktree stays on its original base (2026-06-28)
genm-assemble was redirected across bases multiple times (genm-firing → genm-carving → "re-base on e2941aa1"). It had
created its worktree on the genm-carving base during an early redirect; the later "re-base on e2941aa1" did NOT take —
it kept building (sub-step-A: re-deriving cellRG/zσG/zEG) on the genm-carving lineage (merge-base 162fc569), re-deriving
machinery e2941aa1 already had probe-confirmed. Caught by a branch audit (`git merge-base --is-ancestor`), not by a
teammate report.

**Lesson / mitigation:** a worktree is pinned to the base it was `git worktree add`-ed from; telling an agent to
"re-base onto X" mid-flight is friction (it must tear down + recreate the worktree, which it may not do). So:
1. **When the canonical BASE changes, prefer STOP + fresh tide (clean worktree on the new base) over redirecting an
   in-flight worktree.** A fresh agent with one clear base instruction beats a redirected one with worktree inertia.
2. **Give base-sensitive spawns a HARD base-verification gate as STEP 0** — `git merge-base --is-ancestor <required-base>
   HEAD` + a grep that the expected machinery is present, ABORT if either fails. This makes a wrong-base build
   impossible to start silently (genm-capstone got this gate).
3. Root cause was upstream: the redirect churn itself (Items 47-51 carving oscillation). Fewer base-redirects = fewer
   such stranded worktrees. Net cost here: genm-assemble's sub-step-A wasted (redundant), caught before it diverged far.

### Item 53 — Default to "in-context owner finishes, gated"; reserve fresh-tide for a TRUE valve-trip (2026-06-28)
Consolidated meta-lesson across Items 47-52 (the carving + L2 coordination churn). Pattern observed repeatedly: a deep
teammate depth-FLAGS (or checkpoints), I spawn a fresh tide, then the owner RESUMES and delivers — so the fresh tide is
superseded (duplicate) or, worse, ends up stranded on a now-stale base re-deriving the owner's latest work (genm-assemble
on the carving; genm-l2leaves on L2). The owner consistently held the decisive advantage: the full in-context knowledge
of the just-built bricks + the LATEST branch state.

**Revised default:** when a teammate depth-FLAGS but the remaining is (a) intricate wiring of bricks IT built, or (b)
mechanical-but-large on a toolkit IT holds — **let the owner finish, gated by MANDATORY forced `#print axioms`
(olean-deleted) per increment + green-only commits + a strict valve.** Those gates make the depth-risk (a masked slip)
DETECTABLE and recoverable, which is the actual content of the depth concern — so gated-continue is safe, and it avoids
the duplicate/stale-base churn. **Reserve spawning a fresh tide for a TRUE valve-trip** (the owner attempts and the build
genuinely won't go green after a real try) — a clean, well-specified handoff at that point — NOT for a depth-flag alone.
A depth-flag from a productive owner is a signal to TIGHTEN THE GATES, not to immediately hand off.

Caveat (keep): a depth-flag is still real — when the remaining is a genuinely-NEW hard CONSTRUCTION (not wiring of
already-built bricks), fresh context is the right call (e.g. the zEG carve depth-stop → cleaner Fin-r re-attempt did
work). The discriminator is construction-vs-wiring + does-the-owner-hold-the-latest. Net: fewer spawns, tighter gates,
spawn-fresh only on a real wall.

### Item 54 — "Carve = R1-UPPER's last piece" was an overclaim; a teammate's pre-stage audit found the 2nd long pole (2026-06-28)
I'd been tracking (and writing in synthesis) that closing the carve `schurRatioResidGen_mid` = R1-UPPER done. genm-carving's
read-only post-capstone-wiring pre-stage — which I'd commissioned precisely to check the chain ready-to-flip — found that
`routeMCore_threshold_lt_top` (the ∀M R1-UPPER **hfin** headline, RouteMSchur:426, a SKELETON sorry) needs TWO independent
halves: (i) the matBox inner-finiteness (= `SchurCore`, which the carve provides), AND (ii) a generic `routeMCore_le_matBox`
(the M-dependent routeMCore→frobSq-box reduction) that exists ONLY for r=3. I VERIFIED before acting: `routeMCore_le_matBox`
appears in zero files on origin/genm-firing; `routeMCore_threshold_lt_top` is a sorry @429. The gap is real — the carve is
the hard INNER piece, but R1-UPPER hfin has a 2nd long pole (the N4 M-shape reduction). Commissioned `genm-n4` for it (in
parallel with the carve).

**Lesson:** the bedrock/precision discipline caught a confident-headline overclaim — and the catch came from a STRUCTURED
read-only audit ("verify the dependency chain above the target is actually ready-to-flip, name every remaining sorry"), not
from the build (the carve's branch is green; green ≠ the headline is one step away). Bank the move: **before declaring a
sorry "the last piece" of a headline, audit the FULL dependency chain from that sorry UP to the headline + grep that every
consumer lemma exists (not just the ones below it).** A teammate (or the controller) running that audit proactively — as a
"ready-to-flip" pre-stage — turns a future surprise into a parallel work-item. The cost of NOT catching it: a "R1-UPPER
done!" headline that travels far while routeMCore_le_matBox is still unbuilt. (Also: scope-name precisely — "R1-UPPER hfin"
≠ `resolution_charts` Skeleton:1234, the separate higher RLCT layer; conflating them is the same overclaim trap.)

### Item 55 — The carve is the binding p=4 subcase, not the ∀M R1-UPPER engine: the fully-general ∀M headline hinges on RouteMBoxThresholdFinite ∀p (operator scope call) (2026-06-28)
genm-n4's pre-build substance check (+ decorrelated Codex xhigh; I verified by grep) found that a literal ∀M
`routeMCore_le_matBox → SchurCore 4 r` is a CATEGORY ERROR — and this reshapes the headline's scope. The carve (the entire
genm-firing/genm-carving multi-tide effort: zEG, cellR, schurRatioResidGen_mid, schurGen_lt_top_modulo_recStep) closes the
**binding p=4 Schur residual** (the M334-style core), NOT arbitrary M. Three structural reasons (all verified):
1. `prod M A` is an **L-fold** product (`prod = prodAux … L`); the r=3 template `routeMCore_M334_le_matBox` works only because
   M334 has L=2. No single MP reshape collapses L factors to a 2-matrix box for general L.
2. `SchurCore` is **hardcoded at p=4** (right factor `r×4`; `matBox 2 4`, `morseBox 4`). General output width `M(last)` is arbitrary.
3. `schurLambda r = 2r−2` (the p=4 thresholds) ≠ `½·minAdm M` in general — the SchurCore radial blow-up only matches the
   p=4 binding family.

**Honest restatement of the deliverable.** R1-UPPER hfin ∀M = `routeMCore_le_matBox` (the honest ∀M MP open-box⊆cube reduction,
genm-n4 (a), axiom-clean) + `RouteMBoxThresholdFinite M` (the box-finiteness for c'<½·minAdm, genm-n4 (b)). The carve discharges
`RouteMBoxThresholdFinite` for the **binding p=4 family** (the (2,2,2)/(3,3,4)/(4,4,2,2) anchors + p=4-binding M). So what the
expedition has built — once the in-flight legs land — is the binding-p=4-family ∀M (a real, substantial, honest result), with
the fully-general ∀M gated on TWO precisely-named open analytic pieces:
- **`RouteMBoxThresholdFinite` ∀p** (general output-width box-finiteness) — the R1 general-p gap.
- **`3289`** (general-L grouped recursive diffeo) — the L2/D1 general-L gap (already roadmapped).

**OPERATOR STRATEGIC CALL.** Is `RouteMBoxThresholdFinite` ∀p a bounded build or a research wall?
- Bounded-build route: generalize the carve machinery (cellR/zEG/schurLambda) from fixed p=4 to ∀p — the p=4 case is a worked
  template, so per the ambition calibration this is "large-but-established → break it down." But it is plausibly comparable in
  size to the entire carve effort (i.e. very large).
- Alternative: the **iterated-fibre** route (the paper's other method) — a different substantial machinery.
My lean: it is large-but-established (the paper proves it), so within reach in principle — but it is the single largest remaining
piece and a real decision point. Recommend the operator weigh: (i) charge RouteMBoxThresholdFinite ∀p this expedition (commit to
the general-p lift), (ii) bank the binding-p=4-family ∀M result + named gaps as the expedition deliverable and roadmap the
general-p + general-L lifts, or (iii) a scoped middle (e.g. ∀p for a stated width-class). No action is being deferred silently:
genm-n4 is building the honest reduction + named gap NOW; this item is about the general-p discharge, not the structure.

**Lesson (caps Items 51/54):** the bedrock/precision discipline — pre-build substance checks + dependency-chain audits — caught
three successive overclaims in the R1 chain (the missing routeMCore_le_matBox; the carve≠∀M-engine). A green branch + a worked
family is NOT the ∀M headline. Always: name the family the result covers, grep that the "generic" consumer actually exists at the
claimed generality, and check the worked anchor's special structure (here L=2, p=4) isn't load-bearing before calling it ∀M.
