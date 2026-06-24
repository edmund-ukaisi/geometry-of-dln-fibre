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
