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
