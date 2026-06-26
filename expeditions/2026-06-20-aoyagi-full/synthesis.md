# synthesis.md — Aoyagi-Full controller's integrative read

(Internal ledger; assumes repo context. Flushed every tick; read on re-ground. Not a deliverable.)

## Current read (2026-06-23): re-grounding after compaction — the per-layer-Morse→CITE drift located + CORRECTED; R1 is the S2-only explicit-charts grind, NOT a cite

**Trigger.** Operator flagged (twice) that my post-compaction context did not reference the expedition
policies / files — first the deeper regroup ("the 'cite Aoyagi budget' framing is incoherent for an
INDEPENDENT Aoyagi formalisation"), then "compactification doesn't reference the expedition files —
re-read them." Owned: the controller tick MANDATES a full re-ground (expedition.md §State) after any
compaction; skipping it is what let a cite-drift sit uncorrected. Re-grounded fully now
(expedition.md / brief / priorities / synthesis / threads / lessons).

**The drift, located precisely (the untracked `threads/14-r1-design/Lge3-morse-count-crosscheck.md`).**
It correctly REFUTES the **per-layer Morse recursion** `rlctAtOn(core)=M_last/2 + child` as L=2-only
(structural root: blow up layer 0 → `Erow` is a degree-`(L−1)` form for L≥3, not a free Morse
coordinate; `schurStateRed` preserves depth so the recursion never reaches the L=2 free-`B` base) — that
refutation STANDS. But it then DRIFTED to "the realistic general-L route is **(ii) cite Aoyagi
`rlct=½·codim`**" — a forbidden 2nd citation that contradicts the brief (S2-only) and `lessons.md`
(citing `rlct=codim/2` was explicitly rejected — cites away the new content, breaches
Aoyagi-independence). **Root of the drift:** the crosscheck lost sight that the expedition ALREADY built
the determinantal resolution as explicit charts — the SETTLED g152/g153 mechanism (per-node blow-up +
det-1 **measure-preserving** Schur peel + recurse, monomial-min-fold, codims = Mval) + pp2's landed #68
RouteStep cert IS the rank-profile determinantal resolution, **proven from scratch, S2-only**. The
per-layer Morse recursion was a refuted shortcut (deriv-finish's retracted "Route A"), never the settled
design. Crosscheck §4's cite recommendation is now banner-RETRACTED in-file; §1–§3 kept.

**My #18 partial-rank validation (post-regroup) = the CORRECTION, landing back on the settled design.**
Decorrelated from the paper images, #18 re-confirmed: the clean-disjoint depth-recursion is rank-1-only;
partial rank (t₁≥2) is exactly the coupled `diag(b)` Schur structure (witness (3,3,2,2) t=(2,1,0)); the
VALUE `½·min Mval` is robust general-L, all branches (ideal-preservation + cover lower bound; confirmed
`(3,3,2,2)→2`). That coupled Schur recursion = the settled g152/g153 det-1 peel. So #18 walked the
crosscheck's drift back to the settled, S2-only, from-scratch resolution. Three shortcuts now recorded
dead, NONE of which was ever the settled design: §8 one-shot (L≥3), per-node Morse recursion (L≥3,
the crosscheck), clean-disjoint depth-recursion (t₁=1-only).

**Actual state (verified against the branch, not guessed).** On `expedition/aoyagi-full`: latest commits
are all `lessons:`/`synthesis:` docs; `30b57535` = "rs-grind's trap-iii routeStep body" (5th vacuity
surfacing) — R1's routeStep is MID-LEAN-GRIND on `fm3/routem` (unmerged; that's why
`routeStep`/`RouteMTree` aren't in the main checkout). So R1's OPEN work is the **Lean build** (the
explicit-charts dispatcher, fighting vacuity traps), NOT a math-design question — the math is settled +
re-confirmed. Integration #6 is OVERDUE (merge `fm3/routem` + `fm2/deepest-gauge-chart*` + `crux2/*`
into the expedition branch). Headline `aoyagi_learning_coefficient` proven-conditional (4 gates: #59
gauge chart / #39 R1 dispatcher / #70 degenerate boundary / #42 D1 ≥-leg). Reproduction (#14) + RRR
(#17) are the operator-requested deliverables: reproduction §0–§3.4 + typo ledger DONE (was untracked,
now banked this commit; §4 Lemmas 3–5 / §5 RRR remain); RRR Lean not started.

**Net + next.** The operator's regroup pulled the controller toward reproduction + understanding + R1
hard-validation (vision-maintenance). That arc is largely complete and its verdict is REASSURING: R1 is
sound, S2-only, explicit-charts-from-scratch — no conceptual wall, no 2nd citation. Next: finish the
reproduction (§4/§5) + RRR write-up as the operator asked; then re-engage the Lean frontier (routeStep
vacuity on fm3/routem, integration #6, D1 #7). Standing process fix: re-ground (synthesis + brief) after
EVERY compaction before acting — banked as a lesson.

**★ R1 LIGHT-vs-COUPLED FORK — DECISIVELY RESOLVED (r1-design-light, verify-r1-light-recursion.md;
Newton-LP + decorrelated Codex, exact).** The threshold-only (per-row weight multiplicity, no symbolic
support) recursion is **provably insufficient**: it BREAKS at corank≥2 (genuine ≥2×2 residual Δ-block),
because a per-row multiplicity cannot encode WHICH divisor variables are shared, and sharing changes the
Newton polytope/RLCT. Obstruction: ⟨δx,δy⟩ rlct=½ vs ⟨δ₁x,δ₂y⟩ rlct=1 (identical light data). **CORRECTION
(r1-diagb-4422, exact ×3 methods + Codex):** the original DLN witness (4,4,2,2) t=(2,1,0)→7/2 was
NON-BINDING — rlct(4,4,2,2)=2 (the CLEAN branch t=(4,2,0) Mval=4 binds via one radial blow-up; t=(2,1,0)
Mval=7 is non-binding; threshold-only there gives the CORRECT 2). The genuine coupled-binding witness is
(3,3,4) [an L=2 RRR core]: Mval(t₁)=(3−t₁)²+4t₁=9,8,9,12 → minimiser t=(1,0), Mval=8, rlct=4, corank-(2,2);
clean t₁∈{0,3} give 9,12>8, so NOT clean-reachable. The BREAK still holds (the abstract obstruction +
(3,3,4)'s corank-2 minimiser). NOW CERTIFIED (verify-r1-diagb-334.md, #26/#27 DONE): (3,3,4) binds at 4
while threshold-only gives 3 → the obstruction BINDS at a genuinely-binding DLN branch; coupled diag(b)
support is NECESSARY (literature-anchored to Aoyagi-Watanabe 2005 RRR + decorrelated Codex).
**R1 Lean shape DECIDED = option (ii), the coupled diag(b) recursion**
(minimal sufficient invariant = per-generator symbolic divisor support + sharing relations, up to unit
equivalence). The "hybrid" option (i) is NOT one-citation-viable — it would import the forbidden
rlct=½·codim cite for the corank≥2 branches. So the coupled recursion is the ONLY sound general-L route
under the S2-only constraint, which **VINDICATES the routeStep/GeneralR1Recursion dispatcher as necessary,
not over-engineering** (its SOUNDNESS NOTE already had the clean-recursion-is-false lesson: ambient/2=4≠3/2
for (2,2,2)). Guards against any future "lighten R1" drift. R1-BUILD SPEC CERTIFIED (verify-r1-diagb-334.md §3):
the (3,3,4)→4 binding resolution + threshold-only-gives-3 proof exhibit the routeStep datum's
support : Gen → Finset DivVar field (sharing identity load-bearing, raises Δ-block 1→2). Optional
refinement (not blocking): an L≥3 binding deep-factor-sharing witness (the support field already covers
it — the non-binding (4,4,2,2) t=(2,1,0) demo exhibited shared-C³-via-u). Folded into reproduction §3.4
(with the (4,4,2,2) correction).

**★ PHASE TRANSITION (2026-06-24): design/validation COMPLETE → implementation (routeStep mountain) STARTED.**
The entire design/validation arc is certified + banked: reproduction airtight+red-teamed (§0–§5+ledger,
(4,4,2,2) corrected); R1 = coupled diag(b) CERTIFIED ((3,3,4) binds 4 vs threshold-only 3); integration
phase-1 (R1-side) green @0bd03ad2/e1735700/8026c80d. Now driving the IMPLEMENTATION: `routestep-build`
(fresh lean-formaliser, background) on resolution_charts / the general routeStep dispatcher (RouteMRecursion
:198 honest sorry) as the coupled diag(b) recursion, briefed with the CERTIFIED data-structure spec
(support : Gen → Finset DivVar) + the (3,3,4)/(4,4,2,2) worked examples + STRICT anti-vacuity discipline
(do NOT fabricate the body — the trap-iii lesson; honest sorry if unreachable; inhabitant-test signatures).
THE MOUNTAIN — honest partial progress + a precise blocker report is success; a fabricated green is failure;
controller reviews its output rigorously on report (vacuity risk). BIG REMAINING COMMITMENTS after/alongside:
the L2-PIN soundness reconciliation (DEFERRED — split-reindex's #120 EPivot correction vs the base's
fold3-close version; per-file cherry-pick at L2-wiring), D1 ≥-leg, RRR-Lean (#17), the θ analytic seam (A2).

**ROUTESTEP FIRST-TIDE INTEGRATED @b37f5116 (routestep-build, reviewer-passed, green 3708 jobs).**
(A) RECONCILIATION (verified in-code, RouteMBranchRead:32): the RouteStep per-cell codim:ℕ is the GEOMETRIC
(Mval M₀ T).toNat (root-anchored PivotWitness), NOT a per-row multiplicity — so the per-row obstruction
does NOT bind the datum; no support:Gen→Finset DivVar field is needed ON the datum. The coupled diag(b)
geometry lives in the OPEN dispatcher PROOF (per-chart codim=Mval), not a datum field. Consistent with the
r1-design cert (which ruled out the per-row RECURSION the build correctly avoids).
(B) 3 decidable anchors (Case334RouteStep.lean, 0 sorry/axiom, S2-only, genuine RouteStep.branch):
(3,3,4)→4 binding, (4,4,2,2)→2 non-binding, (3,3,5,4)→4 L=3 deep-sharing (closes the deferred leg).
THE R1 CRUX NOW = the GENERAL-M dispatcher (#135): the rank-pattern READ producer (RouteMBranchRead M₀ M for
arbitrary non-leaf M) + the routeAtlas-folds-to-codims (cover/reachability) proof — where the per-chart
coupled-diag(b) resolution must be proven for general M. resolution_charts (Skeleton:1017) stays honest-sorry
until this lands; NO degenerate single-cell fill (trap-iii forbidden). LIKELY needs a general-M COVER DESIGN
pass (pen-and-paper) BEFORE the Lean tide (design-before-lines) — the per-branch value is certified, the
general-M COMPLETENESS/cover is the open geometry (the "R1.6 mountain" of lessons.md). PROCESS NOTE: spawn the
next R1 formaliser with isolation:worktree (routestep-build worked in the main checkout + switched its branch
uncommitted; recovered cleanly @b37f5116, but worktree isolation avoids the recurrence).

**★ INTEGRATION #6 IN PROGRESS (controller, sole merger; branch-recon → integration-recon.md).** Goal:
one coherent base (clear the scattered-branch debt). NOTE: all 4 Skeleton gates remain sorry after merging
everything — the merge is CONSOLIDATION of supporting modules, NOT headline-closing. Progress:
- **Merge 1 DONE @9cf2035c** — `crux2/r1-222-wrap` (R1 RouteM* + Schur* + ResolutionAtlas/RouteMBridge/
  LossHomogeneity/NodeHomogeneity modules). Clean, reproduction files verified intact, green-gating.
- **Merges 2–4 DONE** (R1-side consolidation; green-gating @bjt25cs1p): merge 2 `fm3/routem` @be15fd9c
  (RouteMNReg/Scaffold/Value + geometric-codim bridge), merge 3 `fm3/routem-ga-transport` @c93e1243
  (MvalMultSum add/add conflict → took fm3/routem's 376-line FULL proof; theirs was a 60-line specify-stub),
  merge 4 `crux2/fold3-close` @0bd03ad2 (DeepestTelescoping PROVEN 362L + DeepestRegAbsorbIFT/SchurShift/
  SplitReindex). Reproduction verified intact at every step. Base now = coherent R1-side + PARTIAL L2-PIN set.
- **Merge 5 (L2-PIN reconciliation) DEFERRED — soundness-sensitive, do NOT blind-merge.** After 1–4 the base
  ALREADY carries fold3-close's versions of DeepestSplitReindex (343L)/RegAbsorbIFT/SchurShift. But:
  (a) HEAD's DeepestSplitReindex (343L) appears to LACK the #120 EPivot shear-CLE correction (0 shear/CLE
  matches) that `fm2/split-reindex` (382L) carries; sub34's is 478L — three divergent versions. (b)
  `fm2/deepest-gauge-chart-sub34` and `fm/deriv-frame-resume-cont` now CONFLICT vs HEAD (divergent Deepest*
  versions); `fm2/split-reindex` previews clean. So the L2-PIN modules on the base may be an UNCORRECTED
  version — INERT now (gates sorry) but MUST be reconciled to the CORRECTED specs (the #120 _deriv
  =fst→shear-CLE fix; the dE(0)=id overclaim fix) BEFORE wiring the L2 gate. RESOLUTION: careful per-file
  reconciliation at L2-wiring (cherry-pick split-reindex's corrections onto the chosen base version, verify
  name=content), NOT a blind merge. Flagged for operator input. **Integration phase-1 (R1-side) is the
  scoped 'clear the mess' deliverable; phase-2 (L2-PIN) is wiring-time work.**
- VACUITY DISCIPLINE: merged supporting modules are inert (gates stay sorry) until WIRED; the routeStep
  body's soundness (the trap-iii vacuity risk, latest lesson) gets verified when R1's resolution_charts is
  wired, not at merge time.

**★ RRR (#17) COMPLETE @0eef1154** — Aoyagi Thm 1 as the L=2 instance of the headline (general-L-first),
sorry-free anchors (3/2, 1), combinatorial rrrTheta; AUDIT-passed (5/5+Codex), aggregator-wired, green 3703.
The weak-existential θ theorem was caught + dropped (controller); analytic θ-binding = flagged seam.

**★ R1 ESCALATION (honest) — the gate is TWO MOUNTAINS, not the bounded construction the #135 cert hoped.**
routestep-read (formaliser, triple+Codex) found r1-135-design's "bounded READ" over-optimistic: the existing
`ChainDimSplit` carrier is FIXED-ARITY (width-only) and CANNOT express the LAYER-COLLAPSING minAdm recursion
`minAdm(M₀,…,M_L)=min_t[(M₀−t)(M₁−t)+minAdm(t,M₂,…,M_L)]` (reduced chain Fin L, one fewer layer = Aoyagi's
layer-peeling, matches #18 depth-recursion). The cert's `codim=(M₀−t)(M₁−t)` is the per-EDGE term, not the
per-path Mval (conflated). Blocker doc merged in-file @9c9fcb89 (RouteMRecursion:219-246). honest sorry kept,
NO fabrication. **Two R1 mountains:** (1) the **LayerSplit re-architecture** (layer-collapsing carrier +
routeAtlas recurse on (L',red) + the descent cert generalised to dlnLoss-of-collapsed-chain — the #18
geometry) — BUILDING (layersplit-rearch, validate-first, worktree); (2) the **general-M IsRouteMCover**
(only (2,2,2) atoms exist; routeM_rlctAtOn_eq_iInf takes it as a hypothesis) — separate second lane, not yet
started. R1 is the genuine LONG POLE; the headline stays honest-conditional on it. The MATH (layer-collapsing
recursion, value ½·minAdm) is validated; the Lean carrier needed re-architecting. NOT a wall — a precise
re-arch path. (Recorded discuss-at-close item 6.)

**★ R1 UPDATE (2026-06-24) — carrier blocker RESOLVED; keystone BANKED; migration commissioned.** Lane 1
landed its hardest piece: `RouteMLayerSplit.lean` (657 LoC, 0 sorry, merged+aggregator-wired @8afeedc0,
green 3707, axiom-clean S2-only, fidelity-reviewer SURVIVED 7/7) proves the LayerSplit layer-collapsing
carrier + the KEYSTONE `minAdmRec_eq_minAdm` (layer-peeling recursion = brute-force minAdm) + value-fold =
½·minAdm + the descent-cert to the collapsed chain (the #18 peel); found+defused a 5th wall (additive-fold
vs min-fold → accumulate to one leaf divisor = Mval). So the hardest R1 MATH is DONE+banked. REMAINING: (a)
the MIGRATION — wire `routeLayerAtlas` into `resolution_charts`, migrate ~17 consumers off ChainDimSplit
(staged surgery) — COMMISSIONED (layersplit-migrate, worktree, assess parallel-vs-in-place then migrate
incrementally, preserve green); (b) the general-M `IsRouteMCover` (2nd lane, only (2,2,2) atoms) — separate,
after the migration. Each R1 dead-end (per-node Morse / §8 / threshold-only-corank≥2 / ChainDimSplit carrier)
was caught honestly before building on it; the keystone is the first R1 piece to LAND. RRR (#17) also COMPLETE
+ integrated @0eef1154 (green, AUDIT-passed).

**★ R1 UPDATE-2 (2026-06-24) — VALUE LANE DONE; gate reduced to ONE obligation (the analytic cover).** The
migration (layersplit-migrate, PARALLEL approach, reviewer-SURVIVED) made a key Codex-confirmed finding: in
`resolution_charts = (rlctAtOn(core) = ⨅ monomialThreshold)`, the VALUE (=½·minAdm) and the ANALYTIC COVER
(rlctAtOn=⨅, the measure-theoretic IsRouteMCover) are ORTHOGONAL. RouteMLayerValue.lean (merged+wired
@ff9702e6, green 3711, reviewer-SURVIVED): `routeLayerAtlas_value_eq_lambdaCore` (⨅ = ½·minAdm, S2-only, NO
sorryAx) + `resolution_charts_of_layerCover` (resolution_charts REDUCED to EXACTLY the layer-family
IsRouteMCover, clean-three). So R1 = VALUE LANE DONE + the ANALYTIC COVER (#104) as the ONE remaining crisp
obligation. The analytic cover (general-M IsRouteMCover: cover_le finiteness + cover_ge_div divergence, the
explicit blow-up/Jacobian generalizing the (2,2,2) Case222RouteMCover atoms via the proven layer-peel descent)
is COMMISSIONED — `r1-analytic-cover` (formaliser, worktree, validate-first). resolution_charts_of_layerCover
closes the R1 gate the moment it lands. This is the genuine resolution-of-singularities geometry — the LOWER
bound, the last R1 mountain. After R1: L2 (gauge chart + PIN reconciliation), D1. The old ChainDimSplit routeStep
arm is superseded by the layer atlas (off the headline path; documented sorry).

**★ R1 UPDATE-3 (2026-06-24) — cover lane HONEST PARTIAL; R1 terrain-mapped; squeeze (Route B) is the sanctioned route.**
`r1-analytic-cover` (the cover lane, Route A) reported HONEST PARTIAL, reviewer-FAITHFUL: it banked the
cover-ASSEMBLY sorry-free (`routeMLayerCover_of_atoms` — the full layer-family `IsRouteMCover` GIVEN two atoms;
merged + wired @5db401fa, green 3713) and pinned the residual to EXACTLY two honest analytic atoms (`hfin` =
global completeness "charts cover the box up to null"; `hdiv` = box-integral divergence) as HYPOTHESES, not
sorries, no smuggle. `resolution_charts` still carries sorryAx — the gate is NOT closed via Route A.
**Controller terrain-map (`theory/aoyagi-2023-reproduction/verify-r1-route-adjudication.md`):** there are TWO
routes. Route A (cover) is WALLED on `hfin`/`hdiv` (the (2,2,2) single-chart `monomial·unit` is a depth-2
miracle; for L>1 the Jacobian tower is non-triangular; the proven squeeze is additive — wrong shape for the
box-integral `=⊤`). **Route B (the per-node squeeze, `GeneralR1Recursion` 699 LoC 0 sorry) is SANCTIONED** —
the clean measure-preserving-chart route was RETRACTED as unsound (telescopes to `ambient/2=4 ≠ 3/2`; pp2 #129:
transvection is det-1 but loss not invariant). Proven machinery: `rlctAtOn_squeeze` (same-point sandwich, NO
chart), `schur_straighten_squeeze_exists` (per-node datum exists GIVEN `hnode`), `rlctAtOn_reduced_transport`
(recursion-closing link), `dlnLoss_one_layer_deepest` (L=1 base). Residual = **`hnode`** (the loss in Schur form
after the measure-preserving det-1 GL-straightening — LOCAL, explicit, near deepest pt) + the recursion assembly
(via keystone `minAdmRec_eq_minAdm`) + re-routing `resolution_charts` through the squeeze (off the cover).
LAUNCHED (both background): (1) `r1-route-adjudicator` (pen-and-paper, decorrelated Codex) — adjudicate Route A
vs B, work a small general-M case past depth-2, scope whether `hnode` is provable, recommend ONE route + the
single load-bearing atom. SOUNDNESS GATE: no re-intro of the retracted MP-chart route; no value-correct
degenerate `hnode`. (2) `l2-branch-mapper` (scout) — map the L2 integration.
**L2 CLARIFIED (not "7 sorries"):** base `DeepestGaugeConstruction` has 2 sorry bodies — line ~435
`deepestEPivot_regSlice_fderiv_id` (PIN1), line ~530 `deepest_loss_squeeze` (PIN2). Fills completed on
un-integrated branches; the L2-drive is the deferred **integration #6** (controller, soundness-sensitive: the
#120 EPivot shear-CLE correction + dE(0)=id fix across ~5 consumers). `l2-branch-mapper` producing the
integration map (which branch fills each sorry, what #120 changes, the cleanest merge path + the manual
reconciliation). Next: R1 adjudication → build the squeeze route's load-bearing atom; L2 map → controller merge;
then D1 → headline.

**★ R1 UPDATE-4 + L2 (2026-06-24) — route ADJUDICATED (Route A is the spine); #120 L2 merge LANDED; hdiv_achiever BUILDING.**
Both efforts reported.
- **L2 #120 merge LANDED (@ab4fc740, soundness-POSITIVE).** `l2-branch-mapper`'s decorrelated map found the base
  PIN1 (`deepestEPivot_regSlice_fderiv_id = id`) is FALSE-as-stated (id only up to an opaque relabel; repo's own
  2c9c492f/12846aae + Codex confirm). Merged `fm/deriv-frame-resume` (the #120 shear-CLE family): replaces it with
  the CORRECT frame-sandwich `deepestEPivot_regSlice_fderiv : ∃ F : ≃L[ℝ], HasStrictFDerivAt … F 0` (invertible
  frame factor, not id). One conflict (DeepestTelescoping.lean → took incoming sorry-free FOLD3). Builds green
  (3752). HONEST post-merge L2 landscape (the map UNDERCOUNTED "2"; verified true count): DeepestGaugeConstruction
  has 4 sorries — PIN1 (443, frame-sandwich, analytic), PIN2 (624, framedParams_split_eq_frame_raw, 4 sub-steps),
  + 2 frame-endpoint wiring facts (831/832, dischargeable via the refined deepestFrameFamily) — plus pre-existing
  DeepestGaugeChart:365 + DeepestNormalFormWiring. NOT yet in the aggregator (deferred to product_reduction wiring).
- **R1 route ADJUDICATED — Route A (cover) is the general-M spine.** `r1-route-adjudicator` (pen-and-paper +
  decorrelated Codex gpt-5.5 xhigh) CORRECTED the controller's Route-B lean: Route B's `hnode` is unprovable at
  corank-≥2 binding branches (the RRR-core family `(n,n,p)`, n≥3, 14/64 ≈22% — the (3,3,4) obstruction). At (3,3,4)
  the reduced core is a (2,2,4) PRODUCT singularity, not the (1,4) smooth leaf — rlct values coincide (2=2) but the
  germs are NOT MP-homeomorphic, so `redEmbed` would be the forbidden value-only degenerate fill. The value lane
  stays corank-robust (reads the closed Mval form at the root); the obstruction bites ONLY the analytic `rlctAtOn=⨅`
  content = the cover's 2 atoms.
- **hdiv_achiever BUILDING (the load-bearing R1 atom).** `r1-hdiv-achiever` (formaliser, worktree, validate-first)
  is building the achiever-path box-integral divergence: for the achiever leaf i⋆ (monomialThreshold = ½·minAdm),
  ∀ c'≥½·minAdm ∀ ε>0, `∫ cubeBox |routeMCore|^{−c'} = ⊤`. The lower bound `rlctAtOn ≤ ½·minAdm`. ONE leaf suffices
  (the min-threshold achiever's divergence forces the whole), so it is IMMUNE to the corank obstruction (coupling
  only helps divergence). The proven GeneralR1Recursion squeeze is the right instrument here (single-path), even
  though it was the wrong shape for the full per-node cover. Discharges `cover_ge_div` via banked
  `routeM_coverGeDiv_of_boxDiverges`. **Next R1 probe after hdiv: is `hfin` (completeness/upper bound) ALSO
  corank-sensitive?** (the adjudicator's flagged risk — if yes, commit to Aoyagi's coupled diag(b) charts for both
  bounds). Critical path: hdiv_achiever → hfin probe → resolution_charts (via routeMLayerCover_of_atoms); L2 close
  (PIN1/PIN2 + frame-endpoint + wire) → D1 → headline.

**★ UPDATE-5 (2026-06-24) — hdiv leg INTEGRATED (reduced to the achiever-wedge atom); L2-close DECISION (gauge=2≤L, L=1 smooth base).**
- **R1 hdiv leg INTEGRATED (@a642f945, green 3714).** `RouteMLayerCoverGE`: the cover_ge_div leg, wiring
  SORRY-FREE (S2-only) — `layerCover_hdiv` discharges `routeMLayerCover_of_atoms`'s hdiv field; achiever-only-
  suffices VERIFIED in Lean. Reduced to ONE honest atom `routeMCore_box_diverges_achiever` (full-fidelity).
  The tide AVOIDED the trap: the squeeze gives only the point-RLCT bound `rlctAtOn ≤ ½·minAdm` (sSup bound on
  c'>t), strictly weaker than the sharp BOUNDARY box-divergence at c'=½·minAdm; faking `=⊤` from it would be
  the forbidden fill (Codex named it; not done). Open content: a general-M **achiever geometric chart/wedge**
  (`|routeMCore ∘ φ| ≤ C·monomial` on a positive-measure box) — the (2,2,2) phiUnit is a depth-2 miracle that
  doesn't generalise. NEXT R1 lower-bound step: the achiever wedge/tube (curve γ(t)→0, F(γ(t))≲t^minAdm,
  tubular Fubini divergence — Codex's lighter route than a full chart).
- **L2 close BLOCKED → DECISION banked (`theory/aoyagi-2023-reproduction/verify-l2-gauge-architecture.md`).**
  `l2-gauge-close` closed none (faked nothing) + surfaced a real blocker: the 4 GaugeConstruction sorries
  (831/832/443/624) share the boundary-frame-triviality keystone (Qf(first)=1, Pf(last)=1), FALSE at L=1
  (first=last). DECISION: the gauge chart is a `2 ≤ L` construction (straightens a product of ≥2 matrices;
  matches IsDeepLayers' existing 2≤L guard); L=1 is the smooth-quadratic base (`prod=A`, `‖A−B‖²` → rank-r
  normal form + sum-of-squares RLCT, a genuine direct proof, NOT vacuous). `product_reduction` is ALREADY PROVEN
  modulo `deepest_regular_core_normal_form` (the gate sorry, Skeleton:1124 = regular/2 + lambdaCore(H−r)).
  Unblock sequence: (1) Core one-sided normal-form lemma — LANDED @1cdfd2aa (rank_normal_form_left_only/right_only,
  sorry-free, axioms [propext,Classical.choice,Quot.sound], wired+green 3715; `l2-rearch` tide now driving 2–3) → (2) refine
  deepestPoint_frame_exists (2≤L boundary identities) → (3) restrict gauge chain to 2≤L, fill 831/832→624→443
  → (4) L=1 smooth base → (5) wire GaugeChart:365 + aggregator. Then the L2 gate falls.

**★ UPDATE-6 (2026-06-24) — R1 shape PINNED: hdiv build-ready at L=2 (building); hfin = the full coupled resolution (THE long pole).**
The wedge-design cert (@2ea5e25d, pen-and-paper + decorrelated Codex) settled both R1 cover legs:
- **hdiv (cover_ge_div, lower bound) BUILD-READY at L=2.** A single weighted radial blow-up: `F∘φ = u²·U`
  (sympy-exact), Jacobian `u^{minAdm−1}`, binding axis `(1,minAdm−1)` → `monomialIntegrand_lintegral_box_eq_top`
  (same chain as routeM222_box_diverges). Covers the binding corank-2 (3,3,4); corank-IMMUNE (the clean block
  bounds U below on a positive-measure slice; coupling only adds). `r1-hdiv-l2-wedge` BUILDING the L=2 case
  (#44). L≥3 = a recursive gauge chain (heavier; ship L=2 first).
- **hfin (cover_le, upper bound, rlctAtOn ≥ ½·minAdm) CORANK-SENSITIVE — CONFIRMED. THE R1 LONG POLE (#45).**
  Must control EVERY stratum incl corank-≥2; threshold-only mis-resolves (3,3,4) (codim 3 not 8). The only
  honest from-scratch route is the **full coupled-diag(b) resolution atlas covering U up to null** — "as hard
  as the route that refuted hnode". REQUIRED from scratch: citing rlct ≥ ½·codim is a forbidden 2nd citation
  (held binding). The dominant remaining difficulty of the expedition. Prior design exists (verify-r1-diagb-334.md,
  #26-#30). Operator-discussion item (discuss-at-close Item 6 VERDICT): default = pursue the full resolution;
  bank an L=2/RRR milestone as the guaranteed floor.
- **R1 shape now precise:** hdiv = the wedge (L=2 building, L≥3 gauge chain); hfin = the full coupled resolution
  (the long pole). L2 = `l2-rearch` building the 2≤L gauge close; D1 = L2-gated. Active tides: l2-rearch (L2),
  r1-hdiv-l2-wedge (R1 hdiv L=2). hfin (the long pole) is the next major design-first effort.

**★ UPDATE-7 (2026-06-24) — L2 INTEGRATED to 2 PINs (831/832 closed, refined frame); wedge re-spawned; isolation incident handled.**
- **L2 gauge chart INTEGRATED @dfb8997b (green 3752): 4 sorries → 2.** The `l2-rearch` tide refined
  `deepestPoint_frame_exists` with 2≤L boundary conjuncts (via my new Core lemmas, case-split: layer-0
  left-only / layer-(L−1) right-only / interior-L1 generic), CLOSED 831/832 (hQf0/hPfL), threaded hL2:2≤L,
  banked readY_regSlice_last + devXZ_corner_devY. Remaining: PIN1 (458, deepestEPivot_regSlice_fderiv — the
  ∃F:≃L invertibility does NOT follow from IsUnit(Qf last) alone: a unit Qf can have singular ₂₂ block;
  needs a Qf-₂₂ invertibility fact, NOT smuggled) + PIN2 (651, framedParams_split_eq_frame_raw — needs
  deepestSplit_exists to expose its concrete decode). Both sharp, tractable ("strengthen an existence lemma").
- **ISOLATION INCIDENT (handled, lesson @68dd764f):** the resumed wedge tide (a12ac…) lost its worktree on
  resume + was operating in the MAIN checkout (writing Scratch_L2.lean). Stopped it, preserved its L=2
  validation (threads/22/scratch-L2-wip.lean), re-spawned ISOLATED. Protocol banked: verify worktree presence
  after spawn/resume; contain if in main.
- **2 isolated tides driving (sharp sub-blockers):** `r1-wedge-l2-build` (a11ac, hdiv L=2 single weighted
  blow-up, covers (3,3,4)) + `l2-pins-unblock` (a680, PIN1 frame-₂₂-invertibility + PIN2 deepestSplit-decode).
- **R1/L2 remaining map:** L2 = PIN1+PIN2 (unblocking) → L=1 smooth base + wiring (steps 4-5) → gate falls.
  R1 = hdiv (L=2 building; L≥3 gauge chain) + hfin (the full coupled resolution — THE long pole, dominant).

**★ UPDATE-8 (2026-06-24) — L2 PIN2 structurally unblocked + integrated; PIN1 fix REFUTED→pivot-compatible frame; l2-pins-close driving both.**
- **PIN2 unblock INTEGRATED @4e6a9b2b (green 3752).** `l2-pins-unblock` found a hidden enumeration mismatch
  (deepestRoleIndexEquiv used opaque Fintype.equivFin vs the explicit regGaugeIdxSplit) blocking the round-trip
  cancellation; REBUILT it through the shared enumeration → the round-trip is now definitionally reachable.
  Remaining for PIN2: concrete deepestSplit def + the readX/Y/Z index-chase + the banked endpoint/reindex/comparability.
- **PIN1 fix REFUTED → the honest fix is a pivot-compatible frame.** The proposed ₂₂-invertibility strengthening
  is IMPOSSIBLE under rank_normal_form_right_only's hypotheses (counterexample r=1,A=[0 1]); ∃F:≃L is false from
  IsUnit(Qf last) alone. F block-structure recorded: invertible iff IsUnit A (hPf) ∧ IsUnit B₂₂. Honest fix:
  make the deepest last layer pivot-compatible (first r cols independent ⟹ B₂₂=I via Q=[[A11⁻¹,−A11⁻¹A12],[0,I]]).
  SOUND (RLCT is coordinate-invariant — a column-choice is a smooth coord change — so the headline value is
  preserved), provided the deepestPoint construction can satisfy the clause (it has frame freedom). The
  overclaiming PIN1 docstring was corrected.
- **`l2-pins-close` tide (aadbe…) driving BOTH** (PIN2 close + PIN1 pivot-compatible implementation), with a
  base-check (the worktree-base hazard — a680 was branched off an infra commit, self-corrected by merging
  aoyagi-full; lesson banked) + a hard soundness gate (no IsDeepLayers change without re-verifying the headline
  axioms; surface if the construction can't satisfy the clause). Concurrent with `r1-wedge-l2-build` (R1 hdiv L=2).
- **L2 remaining after PINs:** L=1 smooth base + wiring → gate falls. R1 unchanged (hdiv L=2 building; hfin long pole).

**★ UPDATE-9 (2026-06-24) — PIN2 index round-trip BANKED (sorry-free); PIN1 2nd refutation → B-determined permutation under validation.**
- **PIN2 highest-risk piece BANKED + integrated @10274c59 (green 3753):** `DeepestSplitConcrete.lean` (sorry-free,
  axiom-clean) — concrete `deepestSplit` + the `piCongrLeft` index round-trip Codex flagged as hardest. PIN2's
  remainder (~200-300 LoC matrix-block assembly) is UNBLOCKED → `l2-pin2-close` tide building it.
- **PIN1 fix REFUTED a 2nd time (decorrelated):** the pivot-compatible "first r cols independent" clause is
  B-determined → would restrict the rank-r target B → breaks headline generality (correctly NOT forced; my
  coordinate-invariance reasoning missed the B-determination). Honest fix proposed: a B-determined pivot-aligned
  PERMUTATION of the residual pack (per-B, so no restriction; measure/RLCT-preserving). `l2-pin1-designer`
  (pen-and-paper, decorrelated) STRESS-TESTING it before any build (2 refutations ⟹ validate-on-paper-first).
- **L2 PIN1 is harder than it first looked** — a coordinated residual-pack re-architecture (if the permutation
  survives) or a different gauge-chart architecture (if refuted). Potential 2nd hard residual alongside R1 hfin;
  will frame for the operator once `l2-pin1-designer` reports SURVIVES/REFUTED.
- **3 tides running:** `r1-wedge-l2-build` (R1 hdiv L=2), `l2-pin2-close` (PIN2 matrix-block), `l2-pin1-designer`
  (PIN1 design-validation). Non-overlapping. hfin long pole + L2 L=1 base + wiring still queued.

**★ UPDATE-10 (2026-06-24) — R1 hdiv (3,3,4) anchor BANKED (reviewed); L2 PIN J-independent atoms banked + PIN1 fully specced; coordinated L2-close + anchor-finish building.**
- **R1 hdiv (3,3,4) achiever box-divergence INTEGRATED @c1bf8ba4 (REVIEWED, green 3716).** `routeM334_box_diverges`:
  the binding corank-2 headline obstruction, L=2. Soundness-critical math SORRY-FREE (exact F∘φ=u₀²·U via Schur
  shear + weighted blow-up, sympy-verified; threshold 4=½·minAdm; the assembly). 3 sorries = geometric
  measure-plumbing (c-o-v Jacobian u⁷, image containment, a.e.-positivity). Sub-reviewer confirmed fidelity +
  soundness. `r1-334-residuals` (ad05d8a5) closing the 3 → fully-sorry-free anchor.
- **L2 PIN1 build plan COMPLETE (thread-23, @4f90bfb1) + PIN2 J-independent atoms banked @99c18329** (DeepestFrameRaw:
  the read→raw chain; DeepestSplitConcrete: the index round-trip — both sorry-free). So both PINs are now
  fully-specced + de-risked. `l2-pins-coordinated` (a4406e39) building BOTH on a SINGLE shared LastPivot J
  (exists_pivot_cols_of_rank Core brick → pivotThresholdSplit → frame B22-invertible → PIN1 via
  regStraightenTotalCLM_equiv_of_regBlock_isUnit → PIN2 J-dependent tail → assembly tripwire).
- **WORKTREE-BASE HAZARD is SYSTEMATIC** (a680, a11ac both off 2ca5e07a not aoyagi-full; both self-corrected via
  the STEP-0 base-check now in every brief). The base-check mitigation works.
- **2 tides driving:** l2-pins-coordinated (L2 close: PIN1+PIN2 on shared J), r1-334-residuals (anchor finish).
  After L2 PINs: L=1 smooth base + wiring → L2 gate. R1: (3,3,4) anchor → general-(M₀,M₁,M₂) lift + hfin (long pole).
  **hfin DESIGN now in flight** (`r1-hfin-designer`, decorrelated): scoping the general coupled-diag(b) resolution
  atlas + the completeness proof structure + an honest MAGNITUDE assessment (bounded-formalizable vs deep-AG-mountain)
  to inform the operator's R1 scope decision (discuss-at-close Item 6: full resolution vs L=2/RRR milestone).

**★ UPDATE-11 (2026-06-24) — SOUNDNESS CORRECTION: the (3,3,4) hdiv chart is DEGENERATE; both R1 legs need the resolution.**
- **CORRECTING UPDATE-10's "(3,3,4) anchor REVIEWED, soundness-critical sorry-free" — OVERSTATED.** r1-334-residuals
  + Codex xhigh found `achieverChart334.cov` is FALSE-as-stated: `chartParams334` pins A(0,1)=A(0,2)=0 + never reads
  u2,u3 ⟹ phi334:ℝ²¹→ℝ²¹ has Jacobian det≡0 (rank 19) + Lebesgue-null image ⟹ cov asserts 0=⊤. So
  routeM334_box_diverges has NO honest proof via this chart. The factorization (routeMCore_phi334) + assembly are
  sorry-free + sound; only the CHART is broken. The STATEMENT is plausibly true; the PROOF route is broken. Honest
  correction committed @d7bcf936 (file documents det≡0 / null image / 0=⊤ + the fix sketch). cov is now a documented
  WRONG-STATEMENT sorry.
- **The prior sub-reviewer MISSED it** (verified the algebraic factorization F∘φ=u₀²·U but NOT the chart's
  non-degeneracy / the c-o-v Jacobian ≠ 0); I integrated @c1bf8ba4 on that review. Lesson banked (a factorization-only
  review ≠ soundness; verify the measure-c-o-v / chart is a genuine diffeo).
- **R1 RE-ASSESSMENT (corrects the wedge designer's "hdiv = light wedge, corank-immune"):** right about the VALUE
  (achiever is the min) but UNDERESTIMATED the chart's measure-change-of-variables. The honest hdiv chart fix
  (b free + Schur shear back to flat) hits the a=0 obstruction (achiever through the blow-up center, shear singular)
  — genuine resolution geometry. So **BOTH R1 legs (hdiv chart + hfin cover) need the resolution**; the hdiv/hfin
  asymmetry (one wedge vs full cover) was WRONG.
- **UNIFICATION question fed to r1-hfin-designer:** does ONE coupled-diag(b) resolution serve BOTH bounds (shared
  a=0 / pivot-vanishing crux)? If so, one hard construction (not two) — the key R1 scope question; its magnitude
  verdict now addresses the unified hdiv+hfin resolution. R1 is harder than the (3,3,4) "milestone" suggested.

**★ UPDATE-12 (2026-06-24) — hfin MAGNITUDE VERDICT: BOUNDED-and-formalizable (NOT a multi-month AG mountain). R1 is REACHABLE.**
`r1-hfin-designer` + decorrelated Codex (independent same decomposition/crux/magnitude): hfin (the dominant residual)
is **person-weeks of toric/monomial-principalization combinatorics**, NOT general determinantal resolution of
singularities. Cert: `threads/24-r1-hfin-design/hfin-design-certificate.md`. Decomposition:
- **COMPLETENESS — BANKED** (argmaxCellOn_cover + coordZero_null + recStep, sorry-free network-free): recStep is an
  EQUALITY ⟹ completeness step-by-step, NO monolithic surjectivity (the half a naive read fears doesn't bind).
- **TERMINATION** — lexicographic μ=(μ_mat,μ_vec,μ_mon), coupled-block area drops a+b−1 per Schur step; branch tree
  bounded by Adm(M) (DLN product structure, NOT Hironaka). (2,2,2) is fixed-depth; general-M needs the (L,M) induction.
- **PER-LEAF THRESHOLD (the CRUX)** — the monomial-sum refinement: a disjoint sum's additive rlct (2+2=4) vs a single
  chart's naive min{2,2}=2 UNDERSHOOT; fix = blow up the corank plane once more → single dominant monomial (h+1=8=Mval,
  threshold 4). This IS the corank-≥2 diag(b) content. Newton-LP + Codex exact. Soundness: every leaf = Mval/2 ≥ ½·minAdm
  (Mval ≥ minAdm definitional); S2 at the leaf only, no rlct≥½·codim smuggled.
- **UNIFICATION CONFIRMED:** the (3,3,4) chart redesign (task #44) IS the reusable per-node c-o-v atom hfin iterates.
  So the dominant cost is the per-node measure-c-o-v, front-loaded on that one chart.
- **Cleanest path:** (1) the genuine-diffeo (3,3,4) chart [the per-node atom — `r1-hfin-designer` now spec'ing it
  precisely, validate-det≠0-on-paper, then a build tide], (2) the monomial-sum-refinement lemma (standalone toric),
  (3) termination + chart-tree assembly induction. (4) completeness banked.
- **SCOPE (operator, discuss-at-close Item 6/8):** general-L hfin is REACHABLE + bounded (person-weeks); OR bank the
  L=2/RRR milestone (clean, sound, S2-only, sidesteps the recursion — at L=2 the single Schur+blow-up node IS the leaf,
  no monomial-sum refinement / termination induction needed). My default: pursue the full resolution, milestone as floor.

**★ UPDATE-13 (2026-06-24) — L2 bricks + keystone BANKED; both gates' remaining = LARGE Lean geometry bodies (math settled).**
- **L2 foundation complete + banked:** the bricks `exists_pivot_cols_of_rank` + `pivotThresholdSplit` (@88855a96) and
  the keystone `toBlocks22_isUnit_of_pivot_corner` (@969fbedf, numerically-verified, generic-frame B22 invertibility
  — the explicit Q' is NOT needed). PIN1's frame-fact MATH gap is CLOSED.
- **SCOPE FINDING (two tides + decorrelated Codex):** the L2 PINs are NOT "thread one J onto the bricks" — both PIN
  bodies are LARGE UNWRITTEN GEOMETRIC PROOFS: PIN1 = the per-layer Leibniz product-fderiv collapse across all L
  layers (the prior tide DEFERRED it; prodAux_regSlice_through_first only does the Y=0/first-layer slice — the
  last-layer readY + framedLayer rewrite is unwritten); PIN2 = the readX/Y/Z→raw chain + telescoping. Several hundred
  lines each, J-threading + the (mechanical) frame-fact reindex bridging folded in at the end.
- **Net: both gates' remaining work is LARGE Lean geometry bodies, the MATH fully settled** (consistent with hfin's
  "cost is formalisation surface, not conceptual"). R1: the per-node genuine-diffeo chart (Layer 1 verified + Layer 2
  a=0 orbitStraighten). L2: PIN1 fderiv collapse + PIN2 raw chain (+ the frame fact, mechanical). Then L=1 base +
  wiring → L2 gate; D1 (L2-gated); R1 hfin tree (general-L). Person-weeks of formalisation, no conceptual walls.
- **2 large-geometry tides running:** `l2-geometry` (a6c94a1: frame fact → PIN1 collapse → PIN2 chain, geometry-budgeted),
  `r1-pernode-chart` (af399d4: the (3,3,4) chart Layer 1+2). Non-overlapping.

**★ UPDATE-14 (2026-06-24) — DEGENERATE-CHART ISSUE RESOLVED: honest genuine-diffeo (3,3,4) chart banked (reviewer-PASSED).**
The degenerate phi334 (false cov=⊤) is REPLACED by an honest genuine-diffeo chart @172f16a8 (REVIEWER-PASSED
soundness gate). Codex's b=a·β trick clears the Schur a⁻¹ pole POLYNOMIALLY → ONE chart does both Layer 1
(genuine diffeo) AND Layer 2 (reaches the origin). Genuine-diffeo VALIDATION done FIRST, all sorry-free:
det Dφ = −u₀⁷·u₁² ≠ 0 (reviewer independently recomputed it AND confirmed it MATCHES the bundle weight
|u₀|⁷·|u₁|² — the new cov is a TRUE statement), reads-all-21-coords, phi334_zero, InjOn, image-in-every-cube,
F∘φ=u₀²·U, threshold=4. routeM334_box_diverges: 3 sorries (one FALSE) → 1 HONEST sorry (the Jacobian c-o-v,
blocked precisely on building paramsEquivFlat-as-linear-iso through the opaque Fintype.equivFin = the heavy
per-node measure-plumbing / hfin cost driver 2, + the {u₁=0} null slice). The honest chart + the generalized
two-axis L2AchieverChart bundle + the sorry-free assembly = the REUSABLE shared hfin per-node c-o-v atom.
`r1-cov-cov` (a531fc6) closing the cov. So R1's geometry crux is DONE+validated; the remaining is measure-plumbing.
The validate-det≠0-first discipline (the slip lesson) worked. 2 tides: l2-geometry (PIN bodies), r1-cov-cov (the c-o-v).

**★ UPDATE-15 (2026-06-24) — L2 frame fact (a) BANKED (sorry-free); 2nd keystone-route soundness correction; latent-dup L2-close blocker flagged.**
- **Frame fact (a) banked @c73f6ec5** (DeepestPivotFrame.lean, sorry-free): `exists_pivotFrame_lastBlock_isUnit` +
  `exists_deepest_lastLayer_pivotFrame` (the shared J/Q for PIN1+PIN2). l2-geometry CLOSED (a); punted (b)(c) honestly.
- **SOUNDNESS CORRECTION #2 (Codex xhigh ×2):** my brief's "feed rank_normal_form_right_only A·Pπ" route is UNSOUND
  (corM threshold-indexed, but B22-invertibility needs pivot-indexed → singular ₂₂ for non-pivot-front B). ac6eed46's
  keystone is VALID but its pivots-front hypothesis was NOT met by threshold-front corM (an over-claim). The sound
  route: explicit pivot-aligned Q = fromBlocks VJ⁻¹ (−VJ⁻¹VK) 0 1 (B22=1 directly, no B-restriction; keystone sidestepped).
- **DeepestPivotFrame UN-WIRED** (deliberate): wiring it pulls the un-wired L2 family (DeepestGaugeChart) → surfaces a
  LATENT DUPLICATE — `continuous_dlnLoss` in BOTH DeepestGaugeChart AND Foundations.LossContinuity (fatal once both in
  build). *** L2-CLOSE BLOCKER: dedupe continuous_dlnLoss before wiring the L2 family. *** Built explicitly (2712); DLNFibre green (3716).
- **(b) PIN1 body + (c) PIN2 cert = the non-incremental rThresholdSplit→pivotThresholdSplit migration** (all-or-nothing,
  several hundred lines, on the banked frame algebra) — the next focused tide, HELD until `pivot-frame-reviewer` passes
  the frame fact (a) (gating the large migration on a verified foundation; the area is soundness-subtle — 2 corrections).
- 2 tides + 1 reviewer: r1-cov-cov (R1 c-o-v), pivot-frame-reviewer (frame fact fidelity); l2-geometry stood down.
- **UPDATE: pivot-frame-reviewer returned SURVIVES** — frame fact (a) cleared as bedrock (statement=intent vs the
  consumer; NO hidden B-restriction — verified against a genuinely non-front-pivot witness r=2 J={1,2} Q≠I, B22=1
  real; axioms clean; decorrelated Codex agrees). So the L2 (b)(c) **migration is UNBLOCKED + commissioned**
  (`l2-migration` a0a2ace0): the non-incremental rThresholdSplit→pivotThresholdSplit J migration → PIN1 (Leibniz
  fderiv collapse) + PIN2 (read→raw + telescoping + reindex) on the verified frame fact, shared-J tripwire. Closes
  the L2 gauge chart (then L=1 base + wire, incl. the continuous_dlnLoss dedupe). 2 tides: r1-cov-cov, l2-migration.

**★ UPDATE-16 (2026-06-24) — both gates: foundations fully banked+verified; remaining = LARGE formalisation-surface writes.**
- **R1 linear-iso atom banked @349bffa3** (paramsEquivFlat-as-linear-iso, FULLY GENERAL, reviewer-SOUND, rfl-compatible
  normed-Params). cov narrowed to the c-o-v measure-plumbing (~400-600 LoC) — `r1-cov-final` (a4e79a2) building it.
- **L2 PIN1 consumer bricks banked @9acee389** (mulRightUnitCLE + shearCLE → the F ≃L) + architecture VALIDATED
  (Codex ×2 + green Lean check): the pivot twist is LAST-LAYER-ONLY (first/interior + regResidualPack SURVIVE);
  toBlocks₁₂ identity green; finCongr caveat. **L2 MAGNITUDE: ~1500-2500 LoC** (value-fold ~350-700 unwritten
  strict-derivative geometry + PIN2 ~500-900 + the API thread). `l2-pin1-valuefold` (a0d8733a) building the value-fold
  → PIN1 green (PIN2 follow-on, per Codex PIN1-green-PIN2-sorry).
- **Net (the honest state):** the MATH is fully settled + the FOUNDATIONS banked+reviewer-verified for BOTH gates
  (R1: chart+linear-iso; L2: frame fact+bricks+keystone+consumer bricks+validated architecture). What remains is LARGE
  formalisation surface — person-weeks, NO conceptual walls: L2 value-fold (~1500-2500) + R1 cov (~400-600) + L=1 base
  + wiring (+ continuous_dlnLoss dedupe) + D1 (L2-gated) + the R1 hfin tree (general-L, reusing the banked per-node atom).
- 2 tides: r1-cov-final (R1 cov), l2-pin1-valuefold (L2 PIN1 value-fold). Non-overlapping.

**★ UPDATE-17 (2026-06-24) — L2 PIN1 REAL UNIT identified (frame-fact-connection gap): the deepest-point-frame PIVOT RE-ARCHITECTURE. Honest correction of the "frame fact cleared the migration" framing.**
- **The finding (l2-pin1-converge @aff1bfff, Codex-xhigh-verified, ZERO false-progress edits):** the J-migration is
  **NOT green-bankable** — and the blocker is deeper than framed. The frame fact `exists_deepest_lastLayer_pivotFrame`
  (DeepestPivotFrame:233, which I'd celebrated as "reviewer-SURVIVED bedrock cleared for the migration") certifies an
  **ABSTRACT** pivot frame Q with IsUnit B22 — but the call site uses `Qf last := (deepestPoint_frame …).2`, whose
  `deepestPoint_frame_normal` (DeepestFrame:162) carries to the **rThreshold** corner `corM`, NOT the pivot Q. So
  `hQf22` is NOT dischargeable at the call site, and changing `deepestEPivot`'s codomain split breaks
  `deepestEPivot_base` (the origin product = the rThreshold corner, frame-INDEPENDENTLY, via
  `prodAux_framedParamsReg_zero`). **HONEST CORRECTION:** the frame fact is *sound* but *not connected* to the actual
  deepest-point frame; the connection is the unbuilt core. (Names results for what they are — the abstract fact was
  over-credited as "cleared the migration".)
- **The real unit = the deepest-point-frame pivot RE-ARCHITECTURE** (slots into `verify-l2-gauge-architecture.md`
  unblock step 2, refined): re-target `deepestPoint_frame_exists`'s last-layer arm to the pivot-aligned Q so
  `deepestPoint_frame_normal` lands the PIVOT corner; THEN the migration + value-fold + PIN2 are mechanical.
- **RE-DECOMPOSITION (breaks the 7-tide all-or-nothing revert pattern):** **Stage A** = a NEW *additive* lemma
  `deepestPoint_frame_pivot_exists` (the deepest point admits a pivot-aligned last-layer frame, B22=1; first/interior
  arms unchanged — last-layer-only) — GREEN-BANKABLE on its own (doesn't touch the existing rThreshold lemma), and it
  IS the connection the finding demands (abstract fact → actual deepest point). **Stage B** = the coupled consumer
  migration (deepestEPivot split + _base + _sq_sum + PIN1 + PIN2), red-spanning, attempt-PIN1, honest red-state report
  if it can't land (no revert, no no-op). Soundness: same deepest point, different (pivot) frame — RLCT-invariant;
  verify #print axioms unchanged.
- **`l2-frame-pivot-rearch` (a9c7dfa) commissioned** with this Stage-A/Stage-B brief. The L2 magnitude (Item 11,
  ~1500-2500 LoC) is unchanged — the re-architecture is *within* it, now correctly targeted (not the J-migration).
- **L=1 BASE parallelized (`l2-base-L1`, ac2db524):** the OTHER arm of deepest_regular_core_normal_form (the L=1
  smooth-Morse case) is INDEPENDENT of the gauge chart + has all prereqs banked (Core one-sided normal form +
  smoothBlockND_rlct + the lambdaCore-at-L=1 arithmetic), proven as a standalone lemma in a new file (Skeleton:1130
  can't import the downstream 2≤L helper — import order; wiring happens later). ZERO citations, import-clean (no
  continuous_dlnLoss dup). Fills the L2 gate's L=1 arm while the 2≤L gauge chart grinds.
- 3 tides, non-overlapping files: r1-cov-final (a4e79a2, R1 cov), l2-frame-pivot-rearch (a9c7dfa, L2 2≤L Stage A+B),
  l2-base-L1 (ac2db524, L2 L=1 base).

**★ UPDATE-18 (2026-06-24) — L2 Stage A "connected bedrock" BANKED+INTEGRATED (axiom-clean); R1 cov reduced to the trivial reshape; the additive decomposition WORKS.**
- **R1 cov (a4e79a2):** the GENUINE c-o-v `phi334_cov` is PROVEN + reviewer-SURVIVED + Codex-corroborated — det `|u₀|⁷·|u₁|²`
  (matching leafH334), the chain rule, the two-sided null-slice drop. The soundness-critical content is DONE. The whole-c-o-v
  sorry collapsed to ONE narrow residual: `Q334CLM_abs_det` (|det Q|=1 for the outer coord-reshape, trivially true). Tide
  RESUMED to close it via the reusable reshape-MP (banks once for ALL hfin nodes). → fully-sorry-free (3,3,4) anchor next.
- **L2 Stage A INTEGRATED @c1ca836e (axiom-clean [propext,Classical.choice,Quot.sound], headline green 2723 jobs):**
  `deepestPoint_frame_pivot_exists` — the CONNECTION the frame-fact-gap demanded: the whole per-layer frame family with
  first/interior = `deepestPoint_frame` (threshold corner, existing lemmas verbatim), last-layer = the pivot Q (PIVOT corner
  `fromBlocks 1 0 0 0` + unit B22). Plus item-1 `pivot_devY_read_toBlocks₁₂` (the Y·B22 L1-soundness gate). **The Stage-A/B
  additive decomposition WORKED** — Stage A green-banked as designed (breaks the prior 7-tide all-or-nothing).
- **The next L2 layer (Stage B finding, Codex-verified, no false progress):** `framedLayer` hardcodes `rThresholdSplit` on the
  column side, so the origin product lands the THRESHOLD corner frame-independently → a naive migration makes
  `deepestEPivot_base` FALSE. The migration needs a **pivot-aware origin-product lemma** (re-derive
  `prodAux_framedParamsReg_zero` → pivot corner) FIRST (Stage C, additive/green-bankable), THEN the coupled consumer migration
  + value-fold → PIN1 (Stage D, the cast-wall-budget red-span).
- **SEQUENCING (disciplined):** `rv-stageA` reviewing Stage A's bundle-soundness now; the Stage C+D migration tide is HELD
  pending the verdict (do NOT build the big coupled write on an unverified foundation — the exact mistake the frame-fact-gap was).
- 3 background agents: a4e79a2 (R1 cov residual), ac2db524 (L=1 base), rv-stageA (Stage A review). Migration tide held.

**★ UPDATE-19 (2026-06-24) — R1 (3,3,4) hdiv anchor FULLY SORRY-FREE + axiom-target-clean; the reusable reshape-MP banked.**
- **`routeM334_box_diverges` INTEGRATED sorry-free @b72c7364** — `#print axioms` = exactly
  `[propext, Classical.choice, Quot.sound, monomial_rlct]` (the single S2 leaf, no sorryAx). The genuine c-o-v
  `phi334_cov` (det `|u₀|⁷·|u₁|²` = leafH334, reviewer-SURVIVED + Codex-corroborated) + the last trivial residual
  `Q334CLM_abs_det` (|det Q|=1 for the outer coord reshape) both closed. Full library green (3718 jobs); sorry total 10→9.
- **Reusable reshape-MP banked (`Foundations/ParamsReshapeMP.lean`, axiom-clean, 143 LoC):**
  `measurePreserving_paramsPack_of_flatIdxEquiv` (reshape by an explicit computable `Fin N ≃ FlatIdx H` is MP — the
  computable replacement for the opaque `Fintype.equivFin`) + `continuousLinearMap_abs_det_eq_one_of_measurePreserving`
  (MP linear self-map has |det|=1). This is the "bank once, share across all hfin per-node charts" fact — cost driver 2
  of the hfin tree is now retired. The (3,3,4) anchor also banks the reusable c-o-v TEMPLATE (Schur-shear det-1 +
  chain-rule composite det + reshape pull-out + the null-slice assembly).
- **What this means for R1:** the hdiv leg's concrete (3,3,4) binding-node anchor is DONE end-to-end — the full c-o-v
  machinery demonstrated with only `monomial_rlct` cited. Remaining R1: the general-M hdiv atom
  (`routeMCore_box_diverges_achiever`, RouteMLayerCoverGE's 1 sorry) + the hfin tree (general-L), both reusing this
  banked reshape-MP + template. Task #44 COMPLETE.
- 2 background agents now: ac2db524 (L=1 base), rv-stageA (Stage A review). Migration tide still held pending rv-stageA.

**★ UPDATE-20 (2026-06-24) — L2 L=1 base BANKED (citation-free); a genuine SOUNDNESS over-claim caught + the headline re-scoped all-widths-positive.**
- **L=1 base @173557a6:** `deepest_regular_core_normal_form_L1` PROVEN sorry-free + axiom-clean
  `[propext,Classical.choice,Quot.sound]` — NOT even `monomial_rlct` (the L=1 base needs no resolution; the single
  layer is a full nondegenerate sum of H0·H1 squares, RLCT H0·H1/2, + lambdaCore=H0·H1/2 at one reduced layer).
  Reusable: `sumSq_rlctAtOn_finN` (full quadratic on Fin n has RLCT n/2). The non-gauge-chart arm of
  deepest_regular_core_normal_form is DONE; the Skeleton:1124 case-split (L=1→this / 2≤L→gauge) is the later wire.
- **SOUNDNESS over-claim CAUGHT (the L=1 tide's flag, Codex-corroborated) + FIXED @9c96786a:** the parent
  `deepest_regular_core_normal_form` — hence `product_reduction`, `aoyagi_learning_coefficient`, `aoyagi_rrr` —
  was FALSE at a degenerate zero-width layer (`H s = 0`, reachable at r=0 under hr): the loss is identically 0 so
  rlctAt = ⊤ (`rlctAtOn_zero_eq_top`) while the closed form is finite. Added `(hpos : ∀ s, 0 < H s)` to all four +
  threaded the call sites + caveat in the docstrings. At r≥1 hpos is automatic from hr, so this restricts ONLY the
  degenerate r=0 zero-width corner — the honest DLN-positive-widths scoping. Full build green (3719); headline axiom
  footprint unchanged. (Precision discipline working: a tide caught the over-claim, the controller re-scoped before
  the proofs lock in.) Flagged for the operator (discuss-at-close Item 12 — a statement change to the deliverable).
- 1 background agent now: rv-stageA (Stage A review). Migration tide held pending its verdict. L2 status: Stage A
  bedrock banked + the L=1 arm DONE; remaining = the Stage C+D migration (held) + PIN2 + the case-split wire.

**★ UPDATE-21 (2026-06-24) — R1 #135 (general-M achiever chart) DESIGN commissioned; the "does not generalise" docstring is STALE.**
- With L2 gated on rv-stageA, drove the next named critical-path item: **R1 #135** (general-M dispatcher, the atom
  `routeMCore_box_diverges_achiever`, RouteMLayerCoverGE's single honest sorry). Its docstring's
  "the (2,2,2) chart phiUnit does not generalise / does not exist on the layer atlas" is **STALE** — it predates the
  (3,3,4) anchor, which IS a fully-proven achiever chart (a DIFFERENT, coupled-`diag(b)` chart) + banks the reusable
  reshape-MP + c-o-v template. #135 = generalize the (3,3,4) chart to arbitrary M.
- **`pp-r1-genM` commissioned** (pen-and-paper, witness seat, decorrelated Codex): adjudicate whether the (3,3,4)
  coupled-`diag(b)` chart generalizes — the general-M chart construction + Jacobian (verify det≠0, the degenerate-chart
  cautionary tale) + the box-divergence argument tied to ½·minAdm M, VALIDATED on witnesses beyond (3,3,4) ((2,2,2),
  (3,3,3), (4,4,2,2), asymmetric). Output: a build-ready general-M chart spec OR the characterized M-class + obstruction
  boundary. Design-first (soundness-sensitive); a formaliser builds it after (reusing the banked machinery).
- R1 #135 is option-(i)-flavoured (the L=2/RRR milestone needs only the concrete anchor + resolution_charts wiring),
  but per the autonomous mandate + loop-prompt naming it critical path, charging ahead on the default (option i).
  Open question for the next R1 read: does resolution_charts admit a single-node route for the milestone, or need the
  general atlas? (code-read, not yet done.)
- 2 background agents: rv-stageA (L2 Stage A review), pp-r1-genM (R1 #135 general-M chart design). Migration held.

**★ UPDATE-22 (2026-06-24) — Stage A SURVIVED (bundle SUFFICIENT, gate GREEN); the L2 PIN1 migration COMMISSIONED on the verified foundation.**
- **rv-stageA verdict: SURVIVED, bundle SUFFICIENT** (decorrelated-Codex-corroborated). `deepestPoint_frame_pivot_exists`
  supplies exactly `regBlockCLE`'s two invertibility inputs (`IsUnit A` first-arm + new `IsUnit B22`, square
  `Fin (H last.succ − r)`); the rThreshold-row/pivot-column asymmetry matches framedLayer; corner `fromBlocks 1 0 0 0`
  + B22 mutually consistent; B21/B12 read off Q directly (no bundling needed); "RLCT-invariant" is justification prose,
  not a statement over-claim. NOTHING must be added to the lemma. Two carry-forwards the MIGRATION owns (not bundle
  fixes): (i) the `finCongr (H_lastLayer_succ)` cast bridge (J/Q on `Fin (H lastLayer.succ)` vs the split on
  `Fin (H (Fin.last L))`); (ii) the RLCT/nReg-invariance argument for the last-layer-only frame swap.
- **`l2-pivot-migrate` (ab63e543) COMMISSIONED** on the verified foundation: **Stage C** (additive pivot-aware framed-product
  origin lemma — re-derive `prodAux_framedParamsReg_zero` → pivot corner; green-bankable, solves the framedLayer
  threshold-corner trap) + **Stage D** (coupled consumer migration: deepestEPivot split→pivot + _base via the pivot origin
  product + _sq_sum + PIN2 shape + the value-fold → PIN1, with the two carry-forwards; cast-wall budget, honest red-state
  if it can't land). PIN2-proof may stay a migrated sorry (target PIN1 green, per the prior Codex call).
- 2 background agents: pp-r1-genM (R1 #135 general-M chart design), l2-pivot-migrate (L2 Stage C+D → PIN1). Non-overlapping.

**★ UPDATE-23 (2026-06-24) — R1 #135 verdict: the (3,3,4) achiever mechanism GENERALIZES (3 witnesses); build + uniform-φ_M design commissioned.**
- **pp-r1-genM verdict (cert @ec2acefc):** the (3,3,4) achiever-chart mechanism GENERALIZES to all positive M — verified
  exactly (rate + V-bound + det≠0) on (3,3,4) [banked], (4,4,2,2) [L=3 pure-radial], (3,3,3,3) [L=3, the decisive
  nonzero-intermediate-codim "shared deep factor" regime]. The mechanism: after the Aoyagi Schur gauge the achiever loss
  is a SUM-of-squares F~Σg_i² (CORRECTS thread 22's "product axis"), radialized by one pivot → F∘φ=u_p²·V,
  |det Dφ|=|u_p|^{minAdm−1}·spectator, binding axis at threshold EXACTLY ½·minAdm. The atom's "(2,2,2) phiUnit does not
  generalise" docstring is now REFUTED at the mechanism level. **Atom REACHABLE**; residual = a uniform closed φ_M
  (construction effort, NOT a math obstruction; the codim-0-stay case is the boundary).
- **Levels kept HONESTLY separate (pp-r1-genM):** this is the LOWER/box-divergence leg only (cover_ge_div, rlctAtOn ≤
  ½·minAdm). The upper `cover_le` (corank-sensitive) is NOT addressed — still needs the full coupled cover or the cited
  Aoyagi/Watanabe bound. The VALUE ⨅monomialThreshold=½·minAdm is already PROVEN; rlct=½·codim rides the cited S2 bound.
- **Commissioned (pp-r1-genM's recommended order):** `r1-node-bundle` (aef6a73b, formaliser) — the reusable
  `NodeAchieverChart M` bundle (the (3,3,4) L2AchieverChart fields generalized) + the M-agnostic atom assembly + the
  (4,4,2,2) instance (verify det≠0; bank the det=u_p^{minAdm−1} radial-blowup lemma); reuses ParamsReshapeMP. AND
  pp-r1-genM CONTINUES on the uniform closed φ_M (strictly-decreasing class) + a clean codim-0-stay frame — the design
  that, with the banked bundle, instantiates the GENERAL atom.
- 3 background agents: l2-pivot-migrate (L2 PIN1, Stage C+D), r1-node-bundle (R1 NodeAchieverChart + (4,4,2,2)),
  pp-r1-genM (R1 uniform φ_M design). Non-overlapping (L2 / R1-build / R1-design).

**★ UPDATE-24 (2026-06-24) — soundness: hpos STRENGTHENED to `r < H s` (strict); resolution_charts read resolves the milestone-route question.**
- **hpos strengthened `0 < H s` → `∀ s, r < H s` (strict) @15fc3913.** Reading `resolution_charts` (Skeleton:1228)
  showed it requires `hMid : 0 < M s` (all layers), docstring: "the headline supplies it in H-form (∀ s, r < H s)".
  The L2 core reduction routes through resolution_charts, so the earlier `0 < H s` was INSUFFICIENT — it fixed the L=1
  loss-empty case but missed the L≥2 CORE degeneracy (at r=H_s, M_s=0 ⟹ reduced prod≡0 ⟹ rlctAtOn=⊤ ≠ finite
  aoyagiLambda). Strengthened across the L2 chain + headline + aoyagi_rrr; D1 (deepest_point_reduction) deliberately
  UNCHANGED (deepest point stays the minimizer at r=H_s; only the L2 split-value breaks). Full build green (3719).
  Refines the paper's r≤min to the realisable non-degenerate domain. (Two re-scopings now: the over-claim is closed.)
- **The flagged milestone-route question is RESOLVED:** `resolution_charts` (the R1 gate) = `rlctAtOn(core) = ⨅ monomialThreshold`
  needs BOTH legs — `layerCover_hdiv` (≤ ½·minAdm, the general-M achiever atom, what #135/pp-r1-genM/r1-node-bundle are
  building) AND `cover_le` (≥ ½·minAdm, corank-SENSITIVE). The headline (even the L=2/RRR milestone, via the 2≤L L2 core
  → resolution_charts) needs the FULL resolution_charts = BOTH legs. So the general-M hdiv is only HALF of R1.
- **OPEN/RECONCILE (next R1 tick):** `cover_le` status — task #45 ("the R1 hfin atlas, cover_le, THE R1 LONG POLE") is
  marked completed, but pp-r1-genM reports cover_le is "NOT addressed; needs the full coupled cover or the cited
  Aoyagi/Watanabe bound". Resolve the discrepancy (is cover_le proven, sorry'd, or open?) before claiming R1 reachable
  as a whole — the hdiv leg (being built) is necessary but not sufficient. The VALUE ⨅monomialThreshold=½·minAdm IS proven.

**★ UPDATE-25 (2026-06-24) — L2 PIN1: Stage C+D bedrock INTEGRATED (reviewer-PASSED); the 2 final blockers scoped+de-risked; closer commissioned.**
- **l2-pivot-migrate banked + INTEGRATED @147fef09** (reviewer + Codex PASS, axiom-clean, no hidden B restriction):
  Stage C `DeepestFramedProductPivot.lean` (`prodAux_framedParamsRegPivot_zero` — the pivot origin product SOLVING the
  framedLayer threshold-corner trap; additive, framedLayer unmutated) + Stage D bedrock (`reindex_prodAux_framedParamsRegPivot_zero`
  — the `deepestEPivot_base` consumer + the finCongr cast bridge SOLVED via `pivotJSucc J = J`) + `DeepestRegSliceFderivPivot.lean`
  (`prod_framedParamsRegPivot_regSlice_collapse` — the value the PIN1 strict-derivative fold differentiates). The naive
  coupled migration was done then REVERTED (can't land green in-session; no fragment) — honest, no false progress.
- **PIN1's 2 remaining blockers (scoped + de-risked — mechanically reachable from the banked bricks, bulk not unknown):**
  (1) frame-family rewiring (~150 LoC, single-writer): `deepest_loss_squeeze`/PIN2 HARDCODE `deepestPoint_frame`, but PIN1's
  hQf22 comes from `deepestPoint_frame_pivot_exists` (different last-layer Q) → parametrize them on `(Pf,Qf)` + thread the
  bundle's pivot frame at the call site (this is where the RLCT-invariance carry-forward surfaced — under-scoped in the
  prior brief). (2) the value-fold (~300 LoC): strict-deriv on the banked collapse → regBlockCLE → PIN1.
- **`l2-pin1-final` (a8759c33) commissioned:** Stage E (frame-family rewiring, GREEN-BANKABLE refactor + threading, PIN
  sorries intact) + Stage F (value-fold → PIN1, coupled, honest red-state if it can't land). The additive-prefix pattern again.
- 3 background agents: l2-pin1-final (L2 PIN1), r1-node-bundle (R1 bundle + (4,4,2,2)), pp-r1-genM (R1 uniform φ_M).

**★ UPDATE-26 (2026-06-24) — R1 general-M LOWER atom (hdiv) DESIGN-CLOSED; cover_le reconciled → the hfin UPPER atom is the remaining R1 long pole; pp-r1-genM dispatched to adjudicate it.**
- **hdiv DESIGN-CLOSED (pp-r1-genM @22c21bb1):** the UNIFORM closed-form φ_M (closed in M + the descent path; LDU-core
  compressed-transition + unit-tri B/C chaining; one radial residual slot → genuine diffeo ninputs=flatDim;
  F∘φ=u²·V; |det Dφ|=|u|^{minAdm−1}·∏|q|^… with q's k=0 spectators → threshold exactly ½·minAdm). Verified from
  scratch on 5 witnesses incl the (2,3,4,2) codim-0-stay boundary (which broke every naive frame — now a genuine
  diffeo under ONE recipe, no separate roadmap). Instantiates NodeAchieverChart `phi`; r1-node-bundle formalising.
- **cover_le RECONCILED (#50, my read):** `routeMLayerCover_of_atoms` (RouteMLayerCover:155) takes BOTH `hdiv`
  (→cover_ge_div, the lower bound, design-closed) AND `hfin` (→cover_le via `routeM_coverLe_of_finiteness`, the UPPER
  bound). #45's "completed" = the cover_le WIRING; the **hfin ATOM (the resolution-atlas COMPLETENESS, rlctAtOn ≥
  ½·minAdm) is OPEN + corank-sensitive** — the remaining R1 long pole, needed for resolution_charts (BOTH options),
  proven-from-scratch S2-only (the Aoyagi/Watanabe cite is NOT allowed by the hero task). So closing hdiv is necessary
  but NOT sufficient — hfin is the other half.
- **pp-r1-genM dispatched to adjudicate hfin (#51):** does routeLayerAtlas COVER the base nbhd (incl corank directions)
  + a per-chart upper c-o-v? Witness (the completeness design) / obstruction (the uncovered corank stratum). THE
  decisive R1 reachability question — determines whether R1 is fully reachable from scratch or hfin is the genuine
  headline obstruction.
- 3 background agents: l2-pin1-final (L2 PIN1), r1-node-bundle (R1 hdiv bundle + (4,4,2,2)), pp-r1-genM (R1 hfin adjudication).

**★ UPDATE-27 (2026-06-24) — R1 hfin ADJUDICATED: reachable from scratch ONLY via the recursive coupled cover (the largest R1 build); ONE feasibility risk under validation.**
- **hfin verdict (pp-r1-genM @e62c9e5e, exact + Codex):** OBSTRUCTION from the combinatorial atlas alone. The
  combinatorial `routeLayerAtlas` (single-divisor leaves) does NOT supply hfin; it needs the unit bounded BELOW on the
  whole chart (normal-crossing), but the #135 φ_M's unit VANISHES on a deeper in-chart corank sublocus {V=0} (hdiv was
  immune — its slice avoided {V=0}; hfin must resolve {V=0} RECURSIVELY). hfin = a recursive coupled cover generalising
  the (2,2,2) Lean `Case222CoverGETail` (already a recStep cover for (2,2,2)) — per-cell = #135 φ_M + coupled diag(b)
  sub-charts for corank-≥2 cells. The LARGEST remaining R1 build; needed for resolution_charts at ANY L (both options).
- **THE feasibility risk (hero-task level):** does the {V=0} recursion TERMINATE with S2-only normal-crossing leaves?
  YES → R1 fully from-scratch (hero-task feasible, hfin "just" the long pole). NO → R1-upper needs a non-S2 cite
  (Aoyagi/Watanabe) → S2-only infeasible for the full headline (operator decision). pp-r1-genM dispatched to validate
  (option b) on (3,3,4) + a corank-≥2 case — THE decisive question. Flagged: discuss-at-close Item 13.
- **R1 net:** hdiv DESIGN-CLOSED (#135, formalising via r1-node-bundle); hfin REACHABLE but the long pole + the one
  feasibility risk under validation. The headline is honest-conditional on hfin until the recursive cover is built.
- 3 background agents: l2-pin1-final (L2 PIN1), r1-node-bundle (R1 hdiv bundle + (4,4,2,2)), pp-r1-genM (R1 hfin {V=0}-recursion validation).

**★ UPDATE-28 (2026-06-24) — R1 hdiv bundle + (4,4,2,2) INTEGRATED (reviewer-SURVIVED); hdiv-general HELD pending the hfin verdict.**
- **R1 hdiv infrastructure INTEGRATED @fd08d958** (r1-node-bundle, reviewer-SURVIVED, full build green 8347 jobs):
  `NodeAchieverChart M` (the (3,3,4) L2AchieverChart fields generalized) + `routeMCore_box_diverges_of_nodeChart` (the
  REUSABLE M-agnostic assembly — discharges the box-divergence atom for ANY M from a bundle) + `pivotBlowupOn_abs_det`
  (the reusable radial-blowup det lemma) + the (4,4,2,2) instance (`routeMCore_box_diverges_achiever_4422`, det=|u₀|³,
  degenerate-chart guard passed). Wired (RouteM family, no dup). Axioms = [propext, Classical.choice, Quot.sound,
  monomial_rlct]. Honestly named (the (4,4,2,2) instance, NOT the general atom).
- **hdiv-general HELD:** the (3,3,3,3) instance + the general closed-φ_M chaining lemma → the general-M atom
  (RouteMLayerCoverGE:120, still sorry) is the remaining hdiv build. Holding it pending the hfin S2-only feasibility
  verdict (pp-r1-genM #51) — that gates the whole R1 strategy (if hfin needs a cite, the "full from-scratch R1"
  investment changes). The hdiv leg is design-closed + bundle-banked + (4,4,2,2)-validated — no urgency to build more
  instances while the gating questions (hfin feasibility, L2 PIN1) resolve.
- 2 background agents: l2-pin1-final (L2 PIN1, the dominant bottleneck), pp-r1-genM (R1 hfin {V=0}-recursion feasibility — THE decisive R1 question).

**★ UPDATE-29 (2026-06-24) — DECISIVE: R1 hfin S2-only FEASIBLE. The WHOLE programme is provable from scratch; remaining = bounded Lean builds.**
- **hfin feasibility DECIDED @a194f1e4 (pp-r1-genM (b), decorrelated-Codex-red-teamed): S2-only YES.** The corank-r
  determinantal core's {V=0} recursion (radial Δ=a·R → rank-stratified Morse-block ⊕ strictly-lower corank core)
  TERMINATES at bounded depth (≤ corank) — leaves = monomial divisors (S2) + Euclidean Morse blocks (S2-FREE, Mathlib
  `radial_ball_iff`, the SAME terminal the (2,2,2) Lean hfin already uses). The recursion threshold λ_{r,p} = ½·minAdm
  EXACTLY (10/10, incl corank-3 (3,3,3)→7/2, (3,3,4)→4). **R1's upper bound is provable from scratch, S2-only — NO
  Aoyagi/Watanabe cite. HERO TASK FEASIBLE.** The red-team caught + repaired an over-clean first pass (intermediate
  strata bind); the conclusion survives. discuss-at-close Item 13 RESOLVED (no operator infeasibility flag).
- **THE PROGRAMME IS NOW CONFIRMED FROM-SCRATCH-FEASIBLE (S2-only) end-to-end.** No conceptual walls remain; the
  remaining is LARGE BOUNDED Lean builds: L2 (PIN1 closing via l2-pin1-final; then PIN2 + the case-split wire +
  product_reduction; L=1 base DONE), R1 hdiv (design-closed + bundle + (4,4,2,2); remaining = (3,3,3,3) + the general
  closed-φ_M chaining → the general atom), R1 hfin (the recursive coupled cover — the biggest single piece, recipe in
  hand, pp-r1-genM spec'ing build-ready lemmas #54), D1 (≥-leg, L2-gated), the headline assembly.
- **hdiv-general UN-HELD (feasibility resolved):** commissioned `r1-node-3333` (af879315) — the (3,3,3,3) NodeAchieverChart
  instance (the decisive MULTI-PIVOT case, LDU-core + B/C chaining per the closed-φ_M cert), validating the bundle beyond
  (4,4,2,2)'s pure radial + banking the LDU/chaining det machinery (the input to the eventual general chaining lemma).
  Reuses NodeAchieverChart + pivotBlowupOn_abs_det + ParamsReshapeMP; det≠0 guard + independent review required.
  Productive use of capacity while L2 PIN1 (can't parallelize the one coupled write) + the hfin spec run.
- 3 background agents: l2-pin1-final (L2 PIN1, dominant), pp-r1-genM (hfin recStep spec #54), r1-node-3333 (R1 hdiv (3,3,3,3)).

**★ UPDATE-30 (2026-06-24) — R1 DESIGN ARC COMPLETE (hfin cover spec banked); pp-r1-genM released; hfin BUILD held for bandwidth.**
- **hfin recStep cover SPEC banked @fabdc203 (pp-r1-genM (a), #54):** 3 build-ready lemma families / 6 steps, grounded in
  verified-real signatures, axiom-hygiene CONFIRMED zero-new, the (2,2,2) `myF222_threshold_lt_top'` as the depth-2 worked
  example, risks ranked (HIGH = the r²-chart Δ-blow-up cover; mitigation = ship (4,4,2,2) corank-2 first). **R1 is now
  DESIGN-CLOSED end-to-end** (hdiv chart → closer → hfin adjudication → S2-only feasibility → cover spec), math validated
  S2-only. pp-r1-genM RELEASED (its R1 design arc is comprehensively complete; the remaining R1 is formalisation).
- **hfin BUILD (#55) HELD for bandwidth** — the spec is build-ready; commission when r1-node-3333 / l2-pin1-final reports
  (avoid 3 concurrent build tides as sole integrator). Build plan: L1.1 terminal → (4,4,2,2) corank-2 instance → general L3.1.
- 2 background BUILD agents: l2-pin1-final (L2 PIN1, dominant), r1-node-3333 (R1 hdiv (3,3,3,3)). pp-r1-genM released.
  Queued: the hfin BUILD (#55), the R1 hdiv-general chaining (after (3,3,3,3) banks the LDU machinery), L2 PIN2 + wiring, D1.

**★ UPDATE-31 (2026-06-25) — L2 Stage E (frame migration) INTEGRATED (reviewer-SURVIVED); PIN1 value-fold (~250 LoC) commissioned as the finish.**
- **Stage E INTEGRATED @c9cfe648** (l2-pin1-final, reviewer-SURVIVED 5/5 + Codex): the frame-family rewiring —
  deepestEPivot + 4 helpers + both PINs + deepest_loss_squeeze + the call site migrated from the THRESHOLD split to the
  PIVOT split (framedParamsRegPivot J), threading the B-determined J; `deepestEPivot_base` re-proved sorry-free + axiom-clean;
  PIN1 gains J + hQf22 (the genuine B22-unit); the call site discharges hQf22 from the banked deepestPoint_frame_pivot_exists
  via the pivotJSucc cast bridge. Faithful migration (not a weakening, no hidden generality loss). Full build green (8347
  jobs); 2 sorries (the 2 PINs), no new axioms. Plus PIN1 value-fold bedrock banked: pivot_devY_read_toBlocks₁₁ + matrixPiCLE.
- **CONFIRMED CORRECTION (banked):** PIN1's residual blocks are LINEAR + a genuine QUADRATIC cross — the clean "P12 =
  Y·B₂₂ exactly" is FALSE; the quad folds into quadResidual. (Caught by the value-fold attempt; handled.)
- **PIN1 value-fold COMMISSIONED (l2-pin1-valuefold aeb04fc2):** the remaining ~250 LoC — the encode/decode reshape ≃Ls +
  the normal form hnormal + the combine → the invertible frame factor regBlockCLE → PIN1. Precisely scoped (2× Codex-validated
  skeleton), bricks banked, but 4/5-difficulty with documented cast walls (the prior tide made the honest call to bank +
  hand off rather than red-spiral). The focused finish of PIN1 (the dominant L2 bottleneck's core).
- 2 background BUILD agents: l2-pin1-valuefold (L2 PIN1 value-fold), r1-node-3333 (R1 hdiv (3,3,3,3)). Queued: hfin BUILD (#55),
  R1 hdiv-general chaining, L2 PIN2 + the case-split wire + product_reduction, D1.
- **hfin BUILD STARTED (hfin-4422 a2dcef0e, 2026-06-25):** the LOW-risk terminal `radial_morse_dominates_lt_top` (S2-free,
  build first) + the (4,4,2,2) corank-2 depth-2 hfin instance (generalising the (2,2,2) Case222CoverGETail depth-2 worked
  example) — the concrete anchor before the general L3.1 (the HIGH-risk r²-chart cover, pp-r1-genM on-call). Used the idle
  heartbeat's free integration bandwidth. **3 BUILD agents now:** l2-pin1-valuefold (L2 PIN1), r1-node-3333 (R1 hdiv (3,3,3,3)),
  hfin-4422 (R1 hfin (4,4,2,2)) — all three open fronts (L2 PIN1 / R1 hdiv / R1 hfin), non-overlapping files.

**★ UPDATE-32 (2026-06-25) — L2 PIN1 value-fold infrastructure BANKED (reviewer-SURVIVED, ~450 LoC); PIN1 one finCongr-cast from green.**
- **l2-pin1-valuefold @7a847924 (origin/worktree-branch, reviewer-SURVIVED 5/5, full build green 8367):** decomposed PIN1's
  monolithic value-fold sorry into ~450 LoC of PROVEN infrastructure + 2 small MECHANICAL sorries. Banked sorry-free:
  `decodeRegSliceCLE` (the reg-slice reshape ≃L, cast-free) + the block-read helpers (`corner_mul_devY`, `mulBlock_devXZ_*`,
  `pivot_devY_read_toBlocks₂₁`, …) + `hPexp` (the product expansion `firstShapeF·last = corner + Y-frame + A·devXZ + quad`
  THROUGH the firstShapeF-codomain cast wall — the 4-5/5 crux, resolved via a `show`-retype) + the block identities + the
  derivative-combine structure. Reviewer: F/regBlockCLE are GENUINE invertible CLEs (real invFuns, gated by IsUnit(Pf first)
  + hQf22); the quadratic cross is genuinely present (the "P12 = Y·B₂₂ exactly" overclaim correctly REJECTED).
- **The 2 remaining PIN1 sorries (mechanical, reviewer-confirmed CORRECT statements, NO math gap):** (1) `hNF` the final
  per-coordinate gluing — blocked on a `H 0` vs `(firstLayer hL).castSucc` defeq-not-syntactic clash; fix = a finCongr cast
  bridge at the decode/Fblk seam. (2) `hquadderiv` the quad deriv-0 (self-contained hasStrictFDerivAt). PIN1 is "one
  finCongr-cast away from green." **aeb04fc2 RESUMED** to close both → PIN1 green (then I integrate PIN1-green in one pass).
- 3 background BUILD agents: aeb04fc2 (L2 PIN1 finish, the 2 mechanical sorries), r1-node-3333 (R1 hdiv (3,3,3,3)),
  hfin-4422 (R1 hfin (4,4,2,2)). The value-fold infra is safe on origin/worktree-agent-aeb04fc2.

**★ UPDATE-33 (2026-06-25) — hfin (4,4,2,2) BUILT via a CLEANER iterated-fibre route (S2-free); the general-route question re-opened.**
- **hfin (4,4,2,2) INTEGRATED @a09033ac** (hfin-4422, reviewer-SURVIVED, full build green 8350): a CLEANER route than the
  spec's rank-stratified recursion — Codex steered to the ITERATED-FIBRE route (avoiding the HIGH-risk r²-chart cover;
  single-global-shear confirmed DEAD). 3 new files, all S2-FREE [propext, Classical.choice, Quot.sound]: S1RadialMorse
  (radial_morse_dominates_lt_top, the Morse leaf terminal), MatMulFibre (`fibre_lintegral_mul_le` — the REUSABLE per-layer
  fibre peel ∫frobSq(X·Y)^{−c'} ≤ const·frobSq(Y)^{−c'}, Y-independent; + triple_fibre_lt_top the 3-fold iterate),
  RouteM4422Hfin (the (4,4,2,2) hfin atom, 1 residual reshape sorry — the paramsEquivFlat entry-reshape, bridge identities
  banked, not math). Threshold 2 = ½·minAdm confirmed exact.
- **THE GENERAL-ROUTE QUESTION (re-opened):** the iterated-fibre route is much cleaner + S2-free + avoids the HIGH-risk
  r²-chart cover — IF it generalizes. Crux: does iterating the fibre peel give ½·minAdm for GENERAL M, incl the corank-≥2
  BINDING that pp-r1-genM's rank-stratified route was designed for? (4,4,2,2) worked, but whether its binding is corank-1
  (so only the easy case validated) or corank-≥2 (so the iterated-fibre genuinely supersedes rank-stratified) is unknown.
  **pp-r1-genM RE-ENGAGED** (on-call) to adjudicate — decisive for the general hfin build route.
- 2 background BUILD agents: aeb04fc2 (L2 PIN1 finish), r1-node-3333 (R1 hdiv (3,3,3,3)). + pp-r1-genM (iterated-fibre
  generality adjudication). Queued: close the (4,4,2,2) reshape sorry, the general hfin (route TBD by pp-r1-genM), the
  general hdiv chaining, L2 PIN2 + wiring, D1.

**★ UPDATE-34 (2026-06-25) — iterfibre route does NOT generalize: HYBRID verdict. CORRECTS UPDATE-33 — the corank-≥2 rank-stratified cover REMAINS the hfin long pole.**
- **pp-r1-genM verdict (@3976d339):** the iterated-fibre route is STRICTLY WEAKER at the corank-≥2 binding cores. The
  per-peel threshold p/2 sees only ONE column of Y (no rank/coupling), so `best_iterfibre(M) = max_s min(...)` = O(max
  single width), which undershoots ½·minAdm (a SUM of block codims) whenever the singularity ACCUMULATES across layers.
  CLASSIFICATION (exact): MATCH (iterfibre suffices, single-factor-concentrated) = (2,1,2),(2,2,4),(4,4,2,2),…; WEAKER
  (needs rank-stratified) = (3,3,4),(3,3,3),(4,4,4),(3,3,3,3),… [ALL corank-≥2 binding]. VERDICT: **HYBRID** — dispatch by
  the decidable `best_iterfibre(M) =?= ½·minAdm`; iterfibre for its class (cheap, S2-free), rank-stratified {V=0} for the rest.
- **CORRECTION of UPDATE-33:** the iterated-fibre did NOT cheapen the long pole — it is a MATCH-class SHORTCUT, not a
  replacement. The corank-≥2 rank-stratified {V=0} cover (the #54 spec, the HIGH-risk r²-chart) **REMAINS the hfin long
  pole**. The (4,4,2,2) build is sound (it IS in the MATCH class). Hero-task feasibility UNCHANGED (rank-stratified covers
  all M; iterfibre reduces, not eliminates, its build scope).
- **pp-r1-genM RELEASED** — its hfin design arc is comprehensively complete (adjudication → feasibility → #54 cover spec
  → iterfibre-generality verdict → hybrid). On-call for the one trigger: the rank-stratified build's HIGH-risk r²-chart step.
- **The next hfin BUILD = the rank-stratified cover (#55, the corank-≥2 long pole), HELD for bandwidth** — commission when
  aeb04fc2 (PIN1) or r1-node-3333 (hdiv (3,3,3,3)) reports; anchor on (3,3,4) hfin via the {V=0} recursion (#53-validated),
  reusing the banked L1.1 (radial_morse) terminal. The r²-chart cover is HIGH-risk → wants full controller attention, not a
  3rd concurrent grind. The (4,4,2,2) reshape sorry (MATCH class) is a low-priority concrete finish.
- 2 background BUILD agents: aeb04fc2 (L2 PIN1 finish), r1-node-3333 (R1 hdiv (3,3,3,3)). pp-r1-genM released/on-call.

**★ UPDATE-35 (2026-06-25) — L2 PIN1 CLOSED (axiom-clean). The dominant L2 bottleneck's core is DONE; PIN2 is the only remaining gauge-chart sorry.**
- **PIN1 `deepestEPivot_regSlice_fderiv` CLOSED @96ad9b2a** — axiom-clean `[propext, Classical.choice, Quot.sound]`, full
  build green (8350). The value-fold: decodeRegSliceCLE + hPexp (the product expansion through the firstShapeF cast wall)
  + hNF (per-coord gluing via `erw` across the genuine rfl-defeq `H 0`/`(firstLayer).castSucc` seam) + hquadderiv (quad
  deriv-0 via the scalar route — the non-square matrix-mul bilinear CLM is absent at v4.29) → regBlockCLE →
  regStraightenTotalCLM_equiv → PIN1. Reviewer-SURVIVED (F a non-vacuous invertible CLE ≠ id; no overclaim).
- **CONTROLLER SOUNDNESS CATCH (the #print-axioms gate worked):** the first integration `#print axioms` showed a spurious
  `sorryAx` — traced (NOT dismissed) to a STALE OLEAN (`scripts/lb` served the pre-copy monolithic-sorry version; PIN1 was
  literally `sorry` there). A forced clean rebuild (rm the module olean + rebuild) confirmed PIN1 genuinely clean. Banked the
  lesson (lessons.md): after copying a file into the main tree, force-rebuild the module before trusting `#print axioms`.
- **L2 status:** Stage A/C/D/E banked + PIN1 CLOSED. **PIN2 (`framedParams_split_eq_frame_raw`, DGC:1452) is the ONLY
  remaining L2 gauge-chart sorry.** Then: the L=1/2≤L case-split wire (Skeleton:1131 deepest_regular_core_normal_form,
  using the L=1 base + the gauge chart) + product_reduction → the L2 gate. + the continuous_dlnLoss dedupe at wiring time.
- 1 background BUILD agent: r1-node-3333 (R1 hdiv (3,3,3,3)). pp-r1-genM released/on-call. Queued: PIN2, the L2 case-split
  wire, the rank-stratified hfin cover (corank-≥2 long pole), the general hdiv chaining, D1.

**★ UPDATE-36 (2026-06-25) — L2 PIN2 statement-CORRECTED (was unprovable as stated); the geometry body (~200-300 LoC) commissioned.**
- **PIN2 precision catch + fix @5ad8074d** (l2-pin2-close, Codex-corroborated + reviewer-PASS): `framedParams_split_eq_frame_raw`
  was UNPROVABLE as stated — it took a GENERIC `split` with no tie to the concrete `deepestSplit`, but the banked round-trip
  decode (readX/Y/Z_deepestSplit, DeepestSplitConcrete) holds ONLY for `deepestSplit`. Fixed the "wrong statement misleads"
  sorry-gate trap: added `hsplit : ∀ w, split w = deepestSplit … w` to PIN2 + deepest_loss_squeeze; rewired
  deepest_gauge_construction to supply the CONCRETE deepestSplit (`hsplit := rfl`). The sorry now sits under a PROVABLE
  statement. PIN1 STAYS clean (verified via forced rebuild); no new axiom; headline byte-identical; full build green (8350).
  (The tide also correctly applied the stale-olean lesson — forced-rebuild before #print.)
- **PIN2 geometry body COMMISSIONED (l2-pin2-geom a378f6db):** the ~200-300 LoC — `rw [hsplit]` then the 3-arm readX/Y/Z→raw
  decode (banked DeepestSplitConcrete) + entry-wise reindex(fromBlocks)=deviation + endpoint_telescoping + J-dependent
  B-normalisation + core_comparability_squeeze. Closing it closes the L2 gauge chart (deepest_regular_core_normal_form_of,
  2≤L) → one wire from the L2 gate.
- **L2 status:** PIN1 CLOSED; PIN2 statement-provable + the body building (l2-pin2-geom); then the case-split wire +
  product_reduction → the L2 gate. The L=1 base is banked.
- 2 background BUILD agents: l2-pin2-geom (L2 PIN2 body), r1-node-3333 (R1 hdiv (3,3,3,3) — bounded composition-det cycle).
  pp-r1-genM released/on-call. Queued: the L2 case-split wire, the rank-stratified hfin cover (corank-≥2), the general hdiv chaining, D1.

**★ UPDATE-37 (2026-06-25) — R1 (3,3,3,3) hdiv INFRA banked (994 LoC, green, reviewer-SURVIVED); det deferred (Lean-cost, optional); det-tactic lesson banked.**
- **r1-node-3333 finalized (commit 99f2b377, worktree):** RouteM3333.lean — 994 LoC, GREEN, ZERO sorry/axiom (verified
  twice). The multi-pivot core (reviewer-SURVIVED, 27×27 det independently re-derived): chartA/B/C3333 (LDU + B/C
  chaining), `dlnLoss_chartParams3333` = **F=u²·V** (the soundness-critical telescoping A·B·C=u·H), Vval3333_ae_pos +
  bounded, leafH3333 (exact exponents, u-exp 5 = minAdm−1), continuity/zero/image. + the REUSABLE Jacobian/composition
  infra (pack3333 + reshape MP + T3333 + T3333Deriv + T3333_hasFDerivAt + the composition T3333=Frame3333∘Kparam3333 +
  both HasFDerivAt) — the bricks the general closed-φ_M chaining reuses. Det-guard CERTIFIED (det≠0 off {u0=0}, sympy+reviewer).
- **The det/atom DEFERRED** (Frame3333Deriv_det → phi3333_abs_det → nodeChart3333 → the (3,3,3,3) atom): a Lean
  ELABORATION-COST wall (NOT math — certified). The per-file cost (two 27-row HasFDerivAt + the 4M-heartbeat composition
  identity = ~7-10min; +det → non-green) → a dedicated RouteM3333Det.lean follow-up (imports RouteM3333 as oleans). Since
  (3,3,3,3) is OPTIONAL validation, the det module is a LOW-priority deferred follow-up.
- **INTEGRATION decision: bank RouteM3333.lean UN-WIRED** (committed but NOT in the aggregator — avoids the +7-10min
  recurring aggregator-build cost; build on-demand, like the Deepest* family). The infra banks safely on origin + is
  reusable; the optional det doesn't slow every build.
- **Det-tactic LESSON banked (lessons.md + thread 30):** det = ∏ factor-dets via LinearMap.det_comp (never a single n×n
  product identity — the 729-entry A·B·C blew 2M heartbeats); BlockTriangular by ROW (27 not 729); explicit literal-match
  CLMs; SPLIT HasFDerivAt-heavy infra from the det into separate files. Directly informs the general chaining det strategy.
- (3,3,3,3) green-gate building on my base now (verify before commit). 1 other BUILD agent: l2-pin2-geom (L2 PIN2 body —
  the decode bedrock is green; assembling telescoping + B-normalisation + comparability). pp-r1-genM released/on-call.

**★ UPDATE-38 (2026-06-25) — PIN2 route steps 1+2 INTEGRATED; PIN2 found unprovable-as-written AGAIN (generic frames); the close (statement-correction + body) commissioned.**
- **PIN2 route steps 1+2 INTEGRATED @9af25ece** (DeepestFrameRaw, +180 LoC, 9 lemmas, axiom-clean, full build green 8350):
  the 4-arm index decode (readX/Y/Z + readT_deepestSplit_raw) + `reindex_fromBlocks_reads_eq_deviation` (the consolidating
  entry-wise identity). The "probed convergent only" hardest PIN2 piece is DONE — banked as bedrock.
- **2nd PIN2 statement-correction needed (l2-pin2-geom, reviewer + Codex + EXACT counterexample):** PIN2
  `framedParams_split_eq_frame_raw` + `deepest_loss_squeeze` are UNPROVABLE as written — they take ARBITRARY frames Pf,Qf
  with no tie to the deepest point, but the germ identity is CONTRADICTORY for generic frames (counterexample: L=2,
  widths=r=1, B=[1], Pf=Qf=2 → no conjugating scalar). [The 1st correction was `hsplit` tying split to deepestSplit;
  this 2nd is the FRAMES.] Fix: thread the frame facts `deepestPoint_frame_pivot_exists` already produces (hNF, hPunit/
  hQunit, hQf0/hPfL, hQf22, hcorner) into PIN2 + deepest_loss_squeeze; the caller deepest_gauge_construction has them.
- **`l2-pin2-final` (a3e80946) commissioned:** the statement-correction (thread the frame facts) + the body (the banked
  route steps + deepestPoint_frame_normal + corner=reindex(fromBlocks 1 0 0 0) + endpoint_telescoping + J-normalization +
  core_comparability_squeeze) → close PIN2. Reviewer to verify the correction is sound (provable + headline-constructs +
  no over-restriction), per the recurring precision pattern.
- **L2 status:** PIN1 CLOSED; PIN2 = bedrock done + the close building (l2-pin2-final); then the case-split wire +
  product_reduction → the L2 gate. The L=1 base is banked. (Two PIN2 statement-corrections this run — the precision
  discipline catching over-general statements before they lock in.)
- 1 background BUILD agent: l2-pin2-final (L2 PIN2 close). pp-r1-genM released/on-call. (3,3,3,3) infra banked un-wired
  (det deferred). Queued: the L2 case-split wire, the rank-stratified hfin cover, the general hdiv chaining, D1.

**★ UPDATE-39 (2026-06-25) — L2 PIN2 statement is FALSE (T-core leak, 3rd + decisive issue); needs a COMPARABILITY re-architecture. "L2-close" was PREMATURE.**
- **The decisive finding (l2-pin2-final, 2 decorrelated confirmations + counterexample):** PIN2
  `framedParams_split_eq_frame_raw` + `deepest_loss_squeeze`'s `hSreg_eq` assert EXACT equalities for the regular blocks
  read off `framedParamsRegPivot` (T-core ZEROED) — but the telescoped loss is FULL-T, and the ₂₂ T-core LEAKS into the
  off-diagonal regular blocks: `(C0·C1)₁₂ = (1+X0)Y1 + Y0·T1`. Counterexample (L=2, H=[2,2,2], r=1): prod(full)₁₂ = y·t
  ≠ 0 = prod(T=0)₁₂, y (readY) ⊥ t (T-core) independent coords → exact h01 FALSE in every neighborhood. The frame facts
  (2nd correction) do NOT fix this. This is the 3rd + DEEPEST PIN2 issue (after hsplit-genericity, frame-genericity).
- **HONEST CORRECTION: the "L2 gate is close / one wire from done" framing was PREMATURE.** PIN2 is the open geometric
  heart, and its EXACT-equality statement is false. The MATH is fine (the RLCT formula holds); the cert's PHRASING was
  over-claimed (exact, where only comparability is true). NOT a math obstruction — a formalisation re-architecture.
- **The repair (option 2, being designed): COMPARABILITY.** Weaken h00/h01/h10 + hSreg_eq from EXACT to two-sided
  comparability `Sreg ≍ ∑deepestEPivot²`, folding the higher-order Y·T leak into γ₁/γ₂ — exactly as the cert ALREADY
  does for the CORE blocks (docstring 1302-1305); the bug is asserting EXACT for the REGULAR blocks. rlctAt is
  comparability-invariant (the squeeze is built for it), so `deepest_regular_core_normal_form_of`'s VALUE is unaffected.
  Secondary issues flagged: (i) last-layer pivot-vs-threshold COLUMN mismatch (framedParams threshold-col vs hcorner
  pivot-col); (ii) endpoint_telescoping needs strict-interior interface hyps for L≥3.
- **`pp-pin2-rearch` commissioned** (decorrelated design): validate option 2 sound + RLCT-sufficient (the leak is
  higher-order → comparability holds) + the build-ready restatement + the secondary fixes. Then a build. The banked PIN2
  route steps (the 4-arm decode + the consolidating identity) + PIN1 (closed) are unaffected.
- L2 status REVISED: PIN1 CLOSED · L=1 base banked · PIN2 route-step bedrock banked · **but PIN2's statement needs the
  comparability re-architecture (the open heart) — not a body-fill.** Then the case-split wire + product_reduction.
- 1 design agent: pp-pin2-rearch (PIN2 comparability re-architecture). pp-r1-genM on-call (R1 r²-chart). No builds running.

**★ UPDATE-40 (2026-06-25) — PIN2 option-2 (comparability) REFUTED; the SAFE repair = full-reg regStraighten; the PIN1/fderiv consumer is the open gate.**
- **pp-pin2-rearch (decorrelated Codex + exact algebra) REFUTED my option-2 (comparability) lean** [UPDATE-39 was wrong]:
  the Y0·T1 leak is DEGREE-2 (same order as the signal, exact cancellation), NOT higher-order. `Sreg ≍ ∑deepestEPivot²`
  fails BOTH directions (counterexamples on 2 lines). And `loss_squeeze` ITSELF is false as typed (the harness g161 note
  confirmed — the T=0 reg slot can't fix an INTER-layer leak; deepestEPivot didn't fix it). Comparability can't be the
  instrument.
- **The SAFE repair (option-1-flavoured, spec'd thread 31): repoint `regStraighten` to the FULL-product reg blocks.**
  Then `∑(regStraighten·).1² = Sreg` becomes an IDENTITY (both = the full reg blocks from hconj), and the squeeze becomes
  the BANKED leaf lemma `dlnLoss_two_sided_of_frame`'s TRUE comparability `dlnLoss ≍ Sreg+Score`. Delete the T=0
  `h00/h01/h10` (cert) + `hSreg_eq` (squeeze) + `deepestEPivot_sq_sum_eq_blocks` from the path. The full reg blocks have
  unit transversal Jacobian (the 3=nReg dirs; leaks pure-quadratic), so `dE(0)=id` plausibly survives. core_comparability_squeeze,
  endpoint_telescoping, exists_deepest_lastLayer_pivotFrame all stay sound.
- **THE OPEN GATE (being adjudicated, pp-pin2-rearch re-engaged): the PIN1 consumer.** PIN1 `deepestEPivot_regSlice_fderiv`
  is CLOSED but reads the T=0 `deepestEPivot` fderiv; the repair repoints to the full product. Hypothesis (pp-pin2-rearch):
  PIN1's fderiv at 0 is UNCHANGED (leak is quadratic → 1st-order at 0 unaffected → `dE(0)=id` survives), so PIN1 is re-used
  or trivially re-pointed. Adjudicating exactly (witness/obstruction) + finalizing the build-ready full-reg spec incl PIN1.
  This is the GATE before I commission the repair build.
- **Path:** PIN1-risk adjudication (pp-pin2-rearch) → the full-reg repair build (regStraighten full-product + loss_squeeze
  = leaf lemma + PIN2 simplified + PIN1 resolved) → the L=1/2≤L case-split wire + product_reduction → the L2 gate.
- Secondary (pp-pin2-rearch): (i) pivot/threshold column = NOT a real inconsistency (evaporates once framedParamsRegPivot
  leaves the squeeze path); (ii) endpoint_telescoping hinterface needed only L≥3 (L=2 target fine).
- 1 design agent: pp-pin2-rearch (PIN1-risk + full-reg spec). pp-r1-genM on-call (R1 r²-chart). No builds running.

**★★ UPDATE-96 (2026-06-26) — HONEST CORRECTION (a8ecfbab's #print-axioms reckoning): closing 3195-L=2 banks a SEPARATE clean lemma, NOT a clean producer/headline. The general headline = the full general-L frontier. Item-24 sharpened. HEAD 1e28ceb5. ★★**
- **The reckoning (a8ecfbab, correct — corrects my framing):** `#print axioms` is a STATIC term scan — a sorry ANYWHERE in `deepest_gauge_construction`'s body makes the WHOLE def sorryAx, inherited by every consumer regardless of branch/instance. **`aoyagi_rrr` ALREADY carries sorryAx today** (from the 3041/3046 L≥3-interior); only the concrete `aoyagi_rrr_222` is clean, via a SEPARATE concrete path (Case222) that BYPASSES the general construction. So my repeated "the L=2 instance is axiom-clean / the L≥3 sorry must not leak" was IMPRECISE — a per-instance axiom-cleanliness of a sorry-bearing general def is not a thing.
- **Consequence (own it):** closing 3195's L=2 branch does NOT make `deepest_gauge_construction` or the general headline clean — 3041/3046 (general-L interior) remain, so the def stays sorryAx (as it already was). What it DOES: banks a SEPARATE axiom-clean lemma `deepest_diffeo_bridge_L2` (the L=2 diffeo content, a reusable building block) + replaces 3195 with a guarded L≥3 sorry. **The clean L=2 deliverables are the CONCRETE anchors** (RRR (2,2,2) via Case222; the R1 (3,3,4) anchor; the engine) — NOT a "clean general-width L=2 gauge-chart producer" (which needs either the general-L interior closed or a separate L=2 construction path).
- **DECISION:** a8ecfbab factors `deepest_diffeo_bridge_L2` (separate, independently axiom-clean) + guards L≥3; NO bigger restructure now (a fully-clean L=2 producer path is Item-24-tied). The deliverable is the clean lemma.
- **Item-24 STRENGTHENED — the clearest framing yet.** The GENERAL headline `aoyagi_learning_coefficient` (clean) = the FULL general-L frontier: `deepest_gauge_construction`'s 3041/3046 (general-L interior, research-grade) + 3195-general (grouped-block diffeo) + R1-general + general-hdiv + D1. That's far + partly research-grade. The CONCRETE-ANCHOR milestone (RRR (2,2,2) clean + R1 (3,3,4) clean + the engine + the now-banked clean L2 bricks: PIN1/PIN2/squeeze/LDU/bridge/`deepest_diffeo_bridge_L2`) is the banked, honest deliverable. **Operator fork: (A) push the full general-L producer toward the clean GENERAL headline [far, research-grade interior] vs (B) consolidate + name the concrete-anchor milestone as the deliverable.** Recommend the operator weigh this; under charge-ahead I bank the clean L2 bricks (incl. `deepest_diffeo_bridge_L2`) and hold the general-L interior as the roadmapped frontier.

**UPDATE-95 (2026-06-26) — L-scope decision: 3195 is L=2-scoped (collapsed Ψ, case-split, guard L≥3); the general-L grouped-block diffeo joins the L≥3 gap. a8ecfbab proceeding with the L=2-collapsed close. HEAD 1e28ceb5.**
- **a8ecfbab surfaced a real L-scope question** (de-risking before committing Ψ_split): the producer is general-`L` (hL2:2≤L), so the cert's two-factor blocks `(A0,Y0,Z0,T0)` are the GROUPED `G0=prodAux(L−1)` product blocks (not a single layer) — the W:=I+Z1A1⁻¹A0⁻¹Y0 + ⅟P00 + A0⁻¹ then involve grouped-G0 blocks + a grouped-pivot inverse (materially heavier). Only at L=2 do they collapse to single-layer blocks (the cert's closed form verbatim, much lighter).
- **DECISION (controller): L=2-scope 3195.** Close via the L=2-collapsed Ψ; case-split on L; close the L=2 branch; guard the L≥3 branch with a precise sorry (the general-L grouped-G0 diffeo), JOINING 3041/3046 as the general-L gap. Reasoning: (1) the producer ALREADY has the L=2-validated/L≥3-guarded pattern (Item 19); (2) the near-term deliverable is the L=2 milestone; (3) closing 3195 at general L would NOT unblock general-L (still gated by 3041/3046) — so the grouped-block W⁻¹ is wasted effort until the WHOLE general-L producer is done (the deferred frontier). Non-negotiable: the L=2 instance axiom-clean (L≥3 sorry must not leak, like 3041/3046).
- **a8ecfbab banked this turn:** `DeepestPsiLens` (the joint-Ψ read-after-write lenses — Codex's index-cast keystone risk CLEARED) + located ALL (a) inverse-smoothness primitives (`contDiffAt_matrix_inv_entry_of_det_ne_zero`, `contDiff_contDiffBump_smul`, `unitSet`/`cutoffBump`, all banked in DeepestSchurSmooth). The Ψ build is fully de-risked; proceeding with the L=2-collapsed close (proceed-nudge sent — it defaults to L=2-collapsed, decision confirms).
- **NEW companion general-L gap (Item 19/24):** the general-L grouped-block hstep2 (the recursive multi-factor diffeo on prodAux(L−1)-grouped blocks) — deferred alongside the L≥3-interior; the whole general-L producer is Item-24's roadmapped frontier. Headline C/2-safe (L=2 milestone); the L=2 producer close is the imminent L=2-collapsed Ψ-wiring.

**★ UPDATE-94 (2026-06-26) — #2 keystone certs landed (pp): (b) EASY exact + (a) MODERATE no-new-math; split-promotion already banked ⟹ #2 is ~1-2 tides. Ψ-wiring close commissioned. HEAD bd0f8d63. ★**
- **E1 BANKED** (`DeepestCompositionE1`, prior tick): the `coreΦ∘Ψ=Score` core-half (`frobSq_prod_absorbed_eq_rcore` via the LDU), axiom-clean.
- **pp's both joint-Ψ keystones (`h2-joint-psi-cert.md`, verified exact + deps confirmed):**
  - **(b) E2 reg-preservation — EXACT + EASY (~tens LoC):** `deepestEFull∘Ψ=deepestEFull` on the whole {A0 invertible} chart. P00/P10 contain no T1/Y1 (fixed); P01=A0Y1+Y0T1 — the Ψ formula `Y1'=Y1+A0⁻¹Y0(T1−T1')` makes `P01'−P01 = A0·A0⁻¹Y0(T1−T1')+Y0(T1'−T1) = 0` (the **A0·A0⁻¹=I cancel**, the one-line keystone). NOT the bottleneck.
  - **(a) W⁻¹/⅟P00 cutoff inverse-smoothness — MODERATE ~1 tide, NO new math:** U_inv open ∋ wstar (W(wstar)=P00(wstar)=I); cutoff `I+χ(W⁻¹−I)` globally ContDiff⊤ via the banked `contDiff_schurCutoffShift` + Mathlib `ContDiffAt.inv` + the banked per-layer (1+readX)⁻¹. Heaviest = the composite W⁻¹ + r×r ⅟P00 (extends the banked per-layer; may reuse S5a's `eventually_P00_invertible`).
- **KEY:** pp called the split smooth-affine promotion "the bottleneck" — but it's ALREADY BANKED (`DeepestSplitSmooth`, prior tick). So with E1 + split-promotion + the abstract bridge all banked, and (b) easy + (a) moderate, **#2 is now ~1-2 tides**: (a) + (b) + the Ψ-wiring. Commissioned a8ecfbab for the close: build (a)+(b) + construct the joint Ψ → `rlctAtOn_diffeo_bridge_of` (E1 core half + (b) reg half) → close 3195.
- **State:** the 11-catch producer fold is near-done — every #2 piece designed/banked, the close a ~1-2 tide Ψ-wiring, the headline C/2-safe. After it: producer axiom-clean for L=2 (modulo L≥3) → the inhabitant gate + the final wire → the L2 gate.

**UPDATE-93 (2026-06-26) — #2 (the 3195 diffeo bridge) decomposed: E1 (LDU core-algebra, building) + (a) inverse-smoothness + (b) reg-preservation keystone (pp design); no-shortcut CONFIRMED. HEAD ecc9cc77.**
- **a8ecfbab mapped the #2 terrain (didn't force a partial Ψ — correct).** It CONFIRMED no shortcut (the banked S5c `DeepestSchurComparability` docstrings refute both the box-ratio `∑‖R‖²≍∑‖∏S‖²` [false M>1 off-germ] AND the additive O(Sreg) charge; the (1−K) MUST be absorbed by Ψ — matches my tilted-kernel analysis). The LDU is banked + L-general (`schur_product_ldu` + `reindex_mul_schur_factor` + `prod_eq_prodAux_mul_last` + `deepestCoreF_coreAbsorb_eq_prodSchur`).
- **#2 decomposes into 3 pieces (parallel):** **E1** core-algebra `frobSq(prod absorbed cores)=frobSq(Rcore)` (LDU-based, sorry-free, no Ψ — a8ecfbab building, unblocks the wiring); **(a)** W⁻¹/⅟P00 cutoff inverse-smoothness (NEW ContDiff⊤ family — the per-layer (1+X)⁻¹ cutoff is banked, extend to the joint W⁻¹/product-pivot; pp design); **(b)** E2 reg-preservation — the KEYSTONE: the joint (T1,Y1) Ψ must leave `deepestEFull(split x)` invariant, and deepestEFull reads ALL THREE slots incl. core, so it's load-bearing (a8a8b2ff verified ~1e-17; pp pins the exact `deepestEFull∘Ψ=deepestEFull` algebra). Then a formaliser wires Ψ (E1 + (a) + (b)) → `rlctAtOn_diffeo_bridge_of` → close 3195.
- **State:** the producer fold's last math is this 3-piece #2 (E1 building, (a)/(b) in pp design); genuinely multi-tide but each piece scoped + the soundness pinned (verified joint Ψ + confirmed no-shortcut). Headline C/2-safe. After #2: producer axiom-clean for L=2 (modulo L≥3) → the inhabitant gate + the final wire → the L2 gate.

**UPDATE-92 (2026-06-26) — #1 measurability CLOSED + #2 prerequisites banked (split smooth-affine + abstract bridge); #2 reduces to the joint-Ψ construction, commissioned. HEAD a881b26c.**
- **Integrated a8ecfbab's partial** (reviewer PASS + Codex): **#1 Score measurability CLOSED** (entrywise, the 3129 sorryAx gone); NEW `DeepestSplitSmooth.lean` (the split smooth-affine promotion — `deepestSplitCLE` + `contDiff_deepestSplit(_symm)` + `hasStrictFDerivAt_deepestSplit(_symm)`, the cert's heaviest prerequisite) + `DeepestDiffeoBridge.lean` (`rlctAtOn_diffeo_bridge_of` — the abstract reduction: local-diffeo Ψ + eventual `Φcore∘Ψ=ᶠΦscore` ⟹ the RLCT equality). All axiom-clean; deepest_loss_squeeze still axiom-clean; PIN1 clean; new modules standalone-green (unwired — Deepest* out until gate-close). Producer now: 3041/3046 L≥3 + the lone **3195 diffeo**.
- **#2 reduces to the joint-Ψ construction** (the prerequisites + the abstract bridge are banked): build the verified JOINT (T1,Y1) Ψ → the `rlctAtOn_diffeo_bridge_of` antecedents (ContDiff⊤ via W⁻¹-cutoff, strict-deriv=CLE, fix wstar) + the composition identity (E1 via LDU, E2 reg-preservation) → close 3195. Commissioned to a8ecfbab (it built the bridge + knows its antecedents). pp on-call (E2/W⁻¹).
- **Controller analysis banked:** the Codex "shorter route" (a 2nd squeeze via `‖prod−Schur‖²≤B·reg`) is refuted-or-equivalent (on the tilted kernel `‖S0S1−Rcore‖²=coreΦ=t⁸ ≤ B·0` fails unless the correction IS the (1−K) diffeo) — so no shortcut; the verified joint-Ψ route is THE route. Saved a wasted tide.
- **State:** the producer fold's last math is the 3195 joint-Ψ (in build); then `deepest_gauge_construction` axiom-clean for L=2 (modulo L≥3); then the inhabitant gate + the final wire → the L2 gate. Headline C/2-safe (confirmed); Item-24 (A) viable, a bounded grind.

**UPDATE-91 (2026-06-25) — #2 diffeo-bridge design landed (corrected JOINT Ψ, verified exact; ~3-4 tides confirmed); #2 build commissioned. Soundness saga OVER — bounded formalization grind. HEAD 98977bde.**
- **a8a8b2ff's design cert (`h2-diffeo-bridge-cert.md`) — design-before-build paid off again:** the naive Ψ (act on the last-layer core T1 only) gives `coreΦ∘Ψ=Score` BUT fails Sreg-invariance (Sreg_E's `P01 = A0·Y1+Y0·T1` contains the core leak T1). The CORRECTED **joint (T1,Y1) Ψ** (W:=I+Z1A1⁻¹A0⁻¹Y0; T1':=W⁻¹·[(1−K)S1+...]; Y1':=Y1+A0⁻¹Y0(T1−T1'); else fixed) holds P01 fixed (Sreg_E invariant) AND gives absorbed S1'=(1−K)S1 ⟹ `(Sreg_E+coreΦ)∘Ψ=Sreg_E+Score` — verified ~1e-17 all shapes + Codex. A formaliser would have hit the Sreg-leak only after a wasted tide; caught in design.
- **The 4 deliverables (build-ready):** (1) Ψ on flat coords = split⁻¹∘Ψ_split∘split — `split` is an AFFINE iso (C⊤ diffeo; the ≃ₜ typing understates it), so the prerequisite is promoting `split` to a smooth affine chart (NEW, load-bearing, heaviest); (2) the composition identity `coreΦ∘Ψ=Score` via banked `deepestCoreF_coreAbsorb_eq_prodSchur` + LDU `rcore_schur_factor_of_corner_split`; (3) Ψ'(wstar)=id + Ψ(wstar)=wstar (verified, correction O(read³)) + global ContDiff⊤ via the banked cutoff-bump + germ-eventual equality (rlctAtOn germ-local); (4) **~3-4 tides (multi-tide CONFIRMED, a9711b920's call right).**
- **#2 build commissioned** (fresh formaliser, base 98977bde, a8a8b2ff's cert): split-promotion FIRST (bank), then the joint Ψ + cutoff + inverse-smoothness (W⁻¹/⅟P00) + the composition + #1 measurability (bundled) → close 3143+3129. Bank checkpoints. pp on-call (frame/LDU).
- **Disposition note:** the 11-catch SOUNDNESS saga is OVER — the math is pinned, the headline confirmed C/2-safe, coreΦ↔Score diffeo-equivalence verified. #2 is now a BOUNDED formalization grind (split promotion + cutoff + plumbing), no more soundness risk. The honest remaining L2 cost: #2 (~3-4) + the inhabitant gate + the final wire (several tides). **Item-24 fork stands** (the operator may prefer (B) the done RRR-L=2 milestone over (A)'s remaining grind); under charge-ahead I drive (A), the more-general general-width L=2 deliverable.

**★ UPDATE-90 (2026-06-25) — Route-B structure migration INTEGRATED (downstream GREEN incl. Skeleton); producer reduces to #1 measurability (mechanical) + #2 the diffeo bridge (multi-tide, design commissioned). HEAD a3f4908e. ★**
- **Integrated a9711b920's structure migration** (reviewer APPROVE + Codex): `DeepestGaugeChart.loss_squeeze` migrated pointwise-coreΦ-sandwich → the RLCT-EQUALITY `rlctAt(dlnLoss)=rlctAtOn(Sreg_E+coreΦ)` (RHS coreΦ-shaped — RLCT diffeo-invariant, so `_rlct`/`deepest_regular_smooth_split` UNCHANGED); `deepest_squeeze_transport` re-wired. **Verified GREEN in MAIN incl. Skeleton (2671 jobs, the headline aggregator + deepest consumer)** — the structure-field ripple is contained. deepest_loss_squeeze AXIOM-CLEAN; PIN1 clean; deepest_gauge_construction sorryAx, no monomial_rlct.
- **The producer's 3095 monolith split into 2 better-scoped residuals:** **#1** Score measurability (~3129, mechanical Mathlib plumbing, no math risk, bundles into the #2 build) + **#2** the diffeo bridge `rlctAtOn(Sreg_E+Score)=rlctAtOn(Sreg_E+coreΦ)` (~3143). The BUILD revealed #2 is **multi-tide** (the abstract `rlctAtOn_comp_localDiffeo` is banked, but constructing the EXPLICIT Ψ on flat coords + the composition identity `coreΦ∘Ψ=Score` via the LDU is the genuine work) — the "~1 tide" hope was optimistic; honest. **#2 design commissioned to a8a8b2ff** (the explicit Ψ + composition identity + fderiv/domain hyps → build-ready cert; design-before-build per a9711b920's recommendation).
- **L2 close remaining (post-#2):** the producer (#1+#2) → deepest_gauge_construction axiom-clean for L=2 (modulo the 2 L≥3-interior, the general-L gap); THEN the final wire — the pre-existing `deepest_gauge_squeeze_exists` inhabitant gate (DeepestGaugeChart:365) + the squeeze-exists relocation + L=1/2≤L case-split + product_reduction + the WLOG colPerm → the L2 gate. So the L2 close is the producer-residuals + the inhabitant gate + the wire (multi-tide remaining, but each piece scoped + the headline confirmed safe).
- **State:** headline + R1 SAFE (decorrelated, triple-confirmed); the 11-catch producer-fold saga converged through the Route-B migration to #1 (mechanical) + #2 (the last genuine math, in design). Item-24 option (A) viable; the L2 close has a clear (if multi-tide) remaining ladder.

**★★ UPDATE-89 (2026-06-25) — MILESTONE: `deepest_loss_squeeze` is AXIOM-CLEAN (the false (♦) GONE); the producer fold reduces to ONE L2-local ripple-boundary sorry. HEAD 9dd13e91. ★★**
- **Integrated a9711b920's Route-B coreΦ→Score fix.** `deepest_loss_squeeze` is now the TRUE pointwise **Score-sandwich** (loss ≍ Sreg+Score, the banked leaf), **AXIOM-CLEAN `[propext, Classical.choice, Quot.sound]`** (controller #print axioms) — the false (♦) sorry is GONE. The producer `framedParams_split_eq_frame_raw` dropped the γ/(d')/(e') folded-core conjuncts (the (♦) carriers); also axiom-clean. PIN1 clean. Forced green-gate (2733 jobs) INCLUDING the downstream `DeepestNormalFormWiring` (the ripple is contained). After the 11-catch saga, the L2 PIN2 squeeze is **proven clean**.
- **The producer fold now reduces to ONE L2-LOCAL ripple-boundary sorry** (DeepestGaugeConstruction:3095) + the 2 L≥3-interior (3044/3049, the known general-L gap). `deepest_gauge_construction` sorryAx (3095 + L≥3), no monomial_rlct.
- **Route-B close commissioned (a9711b920, controller-authorized DeepestGaugeChart scope):** migrate `DeepestGaugeChart.loss_squeeze` from the pointwise sandwich to the RLCT-equality `rlctAt(loss)=rlctAtOn(Sreg+coreΦ)`, proven via the Score-sandwich → `rlctAtOn_squeeze` → the diffeo bridge (`rlctAtOn_comp_localDiffeo` + Ψ:S1↦(I−K)S1; coreΦ↔Score diffeo-equivalent ⟹ same RLCT, headline C/2 SAFE) → closes 3095 + re-wire the loss_squeeze consumers (`deepest_squeeze_transport` etc.). After this: `deepest_gauge_construction` axiom-clean for the L=2 path (modulo the 2 L≥3) ⟹ the producer fold COMPLETE for front pivot, then the final wire.
- **State:** headline + R1 confirmed SAFE (decorrelated, triple-confirmed); Item-24 option (A) close; the producer fold's 11-catch saga converged to ONE clean migration + the L≥3 general-L gap. A strong positive turn.

**★★ UPDATE-88 (2026-06-25) — ripple-confirm CONFIRMED (decorrelated, 3 ways): R1 SAFE, headline SAFE (C/2); coreΦ↔Score are DIFFEO-EQUIVALENT (same RLCT). The 11th catch resolves to a CLEAN ~1-tide diffeo fix. HEAD a86d389f. ★★**
- **a8a8b2ff confirmed pp's verdict, decorrelated + triple-confirmed** (`h2-ripple-confirm.md`): R1 semantically UNAFFECTED (seam trace: R1's `redCore_eq` resolves `rlctAtOn(dlnLoss(reduced chain))`, never the per-layer coreΦ; coreΦ enters ONLY as the squeeze's transfer summand) + paired numerics (rlctAtOn(Sreg+Score)=rlctAtOn(Sreg+coreΦ)=rlctAtOn(loss) across (2,2,2)/(2,3,2)/(2,4,2)/(3,3,3)) + the decisive STRUCTURAL argument.
- **The mechanism (clean + checkable):** coreΦ=‖∏S'‖² and Score=‖Rcore‖² are related by the ANALYTIC-UNIT DIFFEOMORPHISM Ψ: S1↦(I−K)·S1 (K(0)=0 ⟹ I−K a unit) — `(Sreg+coreΦ)∘Ψ = Sreg+Score` — so they have the SAME RLCT (RLCT is diffeo-INVARIANT). This CORRECTS ad67c6b4's "different zero-set ⟹ different RLCT" (Codex flagged thin-set as the wrong justification; diffeo-invariance is right). So the coreΦ RLCT was the SAME VALUE as Score all along — the slip was a wrong-zero-set identification with no RLCT consequence.
- **The fix is CLEANER than feared** (a8a8b2ff): replace the 2667 sorry NOT with a germ charge/Taylor (which (♦) made impossible) but with the analytic-unit change-of-variables `rlctAtOn(Sreg+Score)=rlctAtOn(Sreg+coreΦ)` via Ψ + the banked `rlctAtOn_comp_localDiffeo` — no (♦), no Taylor, ~1 tide. Relayed to a9711b920 to pick the route ((ii) RLCT-diffeo if the downstream consumes the RLCT, vs (i) pointwise-Score restatement) against the actual Lean consumption. Spot-checks: `dlnLoss_two_sided_of_frame` genuinely two-sided; `case222`=3/2, full local RLCT=3. ✓
- **NET — a strong POSITIVE turn:** the 11th catch (which looked like the deepest problem) resolves to: headline SAFE (C/2, diffeo-invariant), R1 SAFE, slip L2-LOCAL, fix ~1 tide. **Item-24's option (A) is now clearly viable and close** — the producer fold closes for front pivot (modulo the L≥3 general-L gap) + the final wire. The RRR-fallback urgency softens (A is near). Residual: a9711b920's route choice + close, then the final wire; the L≥3 general-L gap + the R1-general/D1 remain (separate). Holding the verdict as confirmed (it's structural + triple-confirmed, not a narrow measurement — higher confidence than the flipped intermediates).

**★ UPDATE-87 (2026-06-25) — pp's headline-gate verdict (PROVISIONAL, confirm in flight): C/2 SAFE (anchor-independent) + ripple L2-LOCAL / R1 SAFE. If confirmed, the producer fold is near-done. HEAD 9568d400. ★**
- **pp's verdict (`h2-score-rederive.md`), reassuring:** (a) `rlctAtOn(Sreg+Score) = C/2` is **anchor-independent + nearly tautological** — the banked TWO-SIDED leaf `loss ≍ Sreg+Score` (Score = the loss's OWN framed global-Schur residual) ⟹ `rlctAtOn(Sreg+Score)=rlctAtOn(loss)=aoyagiLambda`; (2,2,2) gives 3/2 = `case222_rlctAtOn_eq`. The C/2 VALUE is UNCHANGED — coreΦ was a downstream identification slip (wrong zero-set on the OPEN tilted-kernel locus), not a value change. (b) **Ripple L2-LOCAL, R1 SAFE:** the headline core `deepestCoreF := dlnLoss(deepestM)` (the REDUCED-chain loss) and R1's `redCore_eq : G²=dlnLoss(S.red)` both operate on the reduced-chain loss — **R1 NEVER touches the per-layer-product coreΦ**; coreΦ was a squeeze-INTERNAL core-bridge (PIN2 relating the full loss to `∑reg² + deepestCoreF`). So the coreΦ→Score fix is confined to the L2 squeeze.
- **Held PROVISIONAL — confirm in flight (don't collapse to the reassuring mode).** pp flags the load-bearing (b) rests on a read-from-code it distrusts (its error history): that deepestCoreF/R1 use the reduced loss, NOT the per-layer product. The subtlety: the 11th-catch curve had `deepestCoreF(coreAbsorb) = coreΦ = t⁸` AT THE POINT while loss=0 — so whether that's a squeeze-internal artifact (R1's reduced-loss RLCT unaffected) or silently feeds R1 needs COMPUTE-confirm. Commissioned a8a8b2ff (decorrelated, compute on the curve + R1 semantic-unaffected check) + (a) spot-check (leaf two-sided? case222 = 3/2?); a9711b920's downstream-breakage report triangulates empirically.
- **If (b) confirms (positive turn after the 11th catch):** the headline value + R1 are safe, the coreΦ→Score fix is L2-local, and a9711b920's squeeze restatement closes the producer fold for front pivot (modulo the L≥3 general-L gap) — the squeeze becomes the banked leaf, no germ charge. If (b) refutes (the slip propagates into R1): deeper, and Item-24's option (B) (ship RRR-L=2, roadmap the producer) becomes the call. Either way the headline VALUE is C/2 (a is exact); the open question is the ripple SCOPE.

**★★ UPDATE-86 (2026-06-25) — 11th catch (DEEPEST): (♦) is FALSE — coreΦ is the WRONG core quantity; it refutes `deepest_loss_squeeze`'s published coreΦ conclusion. Fix = Score (global Schur); the L2 RLCT is RE-OPENED (re-derive from Sreg+Score). Headline NOT disproved but re-gated. HEAD 914f7a7f. ★★**
- **a8a8b2ff (commissioned to PROVE (♦)) instead REFUTED it — triple-confirmed** (its exact algebra + Codex xhigh + ad67c6b4 = a decorrelated pp cross-check with its own sympy+Codex). Exact, reachable, ON-FIBRE counterexample: L=2, r=1, H=(2,3,2), a **tilted kernel** (K=Z1·Y0 nilpotent rank-1 ⟹ Rcore=S0(I−K)S1=0, so Score=frobSq(Rcore)=0; but per-layer cores don't cancel ⟹ coreΦ=frobSq(S0·S1)=t⁸≠0; W0·W1=B exactly ⟹ loss=0, Sreg=0). So `deepest_loss_squeeze`'s conclusion `c₁(Sreg+coreΦ) ≤ loss` is FALSE (c₁·t⁸ ≤ 0). The (♦) sorry at 2667 has a FALSE statement.
- **Root cause: coreΦ (per-layer-product core) is the WRONG quantity — it OVERCOUNTS where per-layer cores cancel in the product (the tilted-kernel locus, which ad67c6b4 confirms is OPEN in the fibre, NOT measure-zero).** The right quantity is **Score = frobSq(Rcore)** (the global Schur = the genuine deepest-layer residual); `loss ≍ Sreg+Score` is the BANKED leaf `dlnLoss_two_sided_of_frame` (=1.0000 on the curve).
- **Fix (commissioned):** (a9711b920) restate the producer conjuncts + (d')/(e') + `deepest_loss_squeeze` with Score in place of coreΦ → the folded charge IS the banked leaf, the (♦) sorry DISAPPEARS (no germ charge); + a downstream-breakage report (the empirical coreΦ→Score ripple scope). (pp) the HEADLINE-VALUE GATE: certify `rlctAtOn(Sreg+Score)=C/2` (should hold — Score is the true residual, loss≍Sreg+Score banked, so its RLCT = the loss RLCT) on the (2,3,2) r=1 anchor + scope whether R1 (RouteM*) also assumed coreΦ vs the genuine Score residual. I'll independently confirm pp's C/2 before the headline relies on it.
- **The decorrelation discipline is now decisively vindicated:** the coreΦ identification was assumed through PIN2 / the whole h2 fold; the cert, pp's measurements, and my framings ALL missed it across catches 6–10; only the adversarial decorrelated confirm (a fresh seat told to PROVE (♦), which instead refuted it) caught the tilted-kernel germ path. **Lesson (load-bearing): when a load-bearing identity has survived only narrow adversary families, commission a seat to REFUTE it, not confirm it.**
- **Honest read for the operator (STRONGEST Item-24 trigger):** the L2 gauge-chart producer used a fundamentally wrong core quantity (coreΦ) on an OPEN locus — a deep, real defect, now correctly diagnosed + the fix (Score) resting on a banked leaf. The headline is very likely SAFE (Score gives the true loss RLCT by the banked comparability) but is genuinely RE-GATED on the uncertified `rlctAtOn(Sreg+Score)=C/2` re-derivation. **The RRR-L=2 milestone (#17, DONE + clean) is the standing fallback deliverable.** This is the moment Item-24 (general-L=2 gauge-chart producer vs RRR-L=2 milestone) most wants the operator's call — see discuss-at-close Item 24 (strengthened) + the 11th catch. Driving the fix + re-derivation under charge-ahead; if the C/2 re-derivation fails, that's a harder escalation.

**★ UPDATE-85 (2026-06-25) — h2 fold re-architecture INTEGRATED (false additive → folded (♦); the residual is now TRUE — [SUPERSEDED by UPDATE-86: the (♦)/coreΦ itself is FALSE; fix = Score]); only (♦) remains. HEAD 914f7a7f. ★**
- **Integrated a9711b920's re-architecture** (reviewer APPROVE + Codex SOUND, a sound precision repair). Producer's FALSE additive obtain → the FOLDED `|Score−coreΦ| ≤ ½(Sreg+coreΦ)` (the (♦), TRUE/robust); `refine ⟨1,1+C,…⟩` → `⟨1,2,2,…⟩` (γ=2); (d')/(e') re-proved by nlinarith. Banked (★) `schur_gap_le_coreRelative` (gap charged to core energy, corollary of banked S5c) + `fold_comparability_of_core_relative`. DELETED both dead additive bridges. Forced green-gate (2732 jobs) + controller #print axioms: (★)+fold-bridge+PIN1 clean; deepest_loss_squeeze/_gauge_construction sorryAx (the (♦) at 2667 + L≥3), NO monomial_rlct. **deepest_loss_squeeze body UNCHANGED.** Same sorry count (3) — but the (♦) is now a TRUE statement (was FALSE).
- **The producer's SOLE remaining residual (L=2 path) is (♦):** `∀ᶠ w on S5a, |Score−coreΦ| ≤ ½(Sreg+coreΦ)` (reduces to `frobSq(D) ≤ ⅛(Sreg+coreΦ)`). a8a8b2ff is designing its leading-order germ-analysis proof (no banked shortcut; sub-tasks #62 reachability ✓ / #63 coreΦ-fidelity ✓ / #64 RLCT-impact + thinness-of-failure-locus pending). On its design, a follow-up tide discharges (♦) → 2667 closed → **the L2 body complete for front pivot** (the 2 L≥3-interior remain the known general-L gap, vacuous at L=2).
- **State:** the L2 producer has converged from the 10-catch saga to a SINGLE correctly-stated obligation, with the headline verified-safe throughout. Once (♦) lands, the L2 close is the final wire (squeeze-exists relocation + L=1/2≤L case-split + product_reduction + the WLOG colPerm). a9711b920 at rest (ready for the (♦) discharge tide); a8a8b2ff on (♦) design; pp on-call.

**★ UPDATE-84 (2026-06-25) — repair spec landed: reachability SETTLED (it's spectator reg coords, NOT frames); re-architecture (★ + folded sandwich) commissioned; the genuine remaining piece is (♦), a leading-order germ analysis with NO banked shortcut. HEAD 0c5b7764. ★**
- **Reachability SETTLED (a8a8b2ff, `h2-repair-spec.md`):** the additive-bound counterexample is reachable in the RAW producer chart with IDENTITY frames — `cond(P00)=1`, gap/Sreg→∞, while `loss/(Sreg+coreΦ)→1.0000`. The mechanism is **spectator reg coordinates** (X₁,Y₀,Z₁) that shrink the product blocks (hence Sreg) UNCHARGED. So the "frame" framing across UPDATE-78→83 was partly a red herring — the additive bound fails even frame-free; re-architecture IS needed (not avoidable). Codex confirmed + a pointwise failure (P01=0 ⟹ Sreg=0, gap>0).
- **The re-architecture is READY + commissioned (a9711b920):** (★) `|frobSq(Rcore)−coreΦ| ≤ 2√(coreΦ·frobSq D)+frobSq D` (a ~3-line corollary of banked `schur_core_germ_comparability`, verified 0/20000) + the FOLDED sandwich via (♦) with γ₁=γ₂=2 (the `(Sreg+coreΦ)` denominator load-bearing — coreΦ-alone fails under product cancellation) + a new ~30-LoC bridge (NOT the two dead bridges). This REPLACES the FALSE additive 2681 with a CORRECT (♦) sorry (precision: fix the wrong statement). Built against (♦) as a NAMED HYPOTHESIS (its statement is pinned 0/20000).
- **The genuine remaining obligation — (♦), commissioned to a8a8b2ff:** `|Score−coreΦ| ≤ η·(Sreg+coreΦ)`, η→0. a8a8b2ff established it does NOT discharge from any banked sub-mult/operator-norm bound (every norm-factoring route blows up under product cancellation, 1e6–1e17); it's TRUE/robust (Θ(t²)→0) but its proof is **genuine leading-order germ analysis**. Its difficulty (1 tide vs multi-tide) is the open question — a8a8b2ff doing the leading-order pass + an honest difficulty read (a key Item-24 input). pp on-call.
- **Net:** headline SAFE (the folded squeeze survives, verified). The producer's open piece reduces to ONE correctly-stated obligation (♦), being proof-designed in parallel with the re-architecture build. The producer fold's TRUE depth is (♦)'s leading-order analysis — the last load-bearing piece.

**★ UPDATE-83 (2026-06-25) — 10th catch (the BIG one): the independent confirm REFUTED the additive bound by explicit counterexample. The 2681 additive intermediate (assumed since the 8th catch) is FALSE. deepest_loss_squeeze's FOLDED conclusion is TRUE — bounded re-architecture, headline SAFE. HEAD 2624a20f. ★**
- **The decorrelated confirm (a8a8b2ff) REFUTED `|frobSq(Rcore) − coreΦ| ≤ Ccore·Sreg`** by EXPLICIT construction (independent setup + exact sympy + Codex, all agree): on the CLEAN S5a interior (cond P00 = 1 exactly), a reachable family (A1=I−Y0Z1 ⟹ P00=I, P01=Θ(t³) ⟹ Sreg=Θ(t⁶), cores Θ(t)) gives gap/Sreg → ∞ (~1/a²). The bridge premise `hRem` (frobSq(D) ≤ Crem·Sreg²) is ALSO false there. Generic order is **Θ(Sreg³)**. pp's "O(Sreg)/O(Sreg²)" were the **corner-dirty regime** (hcorner-violating frames) — artifacts, not the clean bound.
- **BUT `deepest_loss_squeeze`'s CONCLUSION survives (verified by me against the Lean + the confirm):** the conclusion is the FOLDED sandwich `c₁·(Sreg+coreΦ) ≤ loss ≤ c₂·(Sreg+coreΦ)` (TRUE — folded distortion ≈ 0 on the refuting curves; coreΦ=Θ(t⁴) DOMINATES Sreg=Θ(t⁶), so the gap is correctly charged to coreΦ, not Sreg). Only the 2681 additive INTERMEDIATE (the route to the sandwich) is the false piece. Its statement is WRONG ⇒ fix-the-statement-first: re-state to the coreΦ-charge.
- **Repair (verified 0/20000, uses banked S5c):** `|frobSq(Rcore) − coreΦ| ≤ 2√(coreΦ·frobSq(D)) + frobSq(D)` (D = Rcore−S0S1 → 0) → the multiplicative comparability → the sandwich constants (replacing the false `refine ⟨1,1+C,…⟩`). a9711b920's banked `germ_charge_of_core_charge` (charges frobSq(R) directly, NOT Sreg) is likely the tool. **Commissioned a8a8b2ff for the build-ready repair spec** (re-stated 2681 + the c₁/c₂ derivation + the lemma + a CRITICAL reachability check: is the counterexample in the producer's actual parameterized chart?). a9711b920 HOLDS the close pending it; pp on-call (its design superseded by the confirm).
- **This VINDICATES the decorrelation discipline, strongly.** The additive route had been the assumed shape since the 8th catch; pp's measurements (corner-dirty) and my own premature framings (O(Sreg)/O(1)) all missed it. Only the FULLY decorrelated confirm — which I commissioned precisely BECAUSE pp self-flagged its error rate — caught it, by explicit counterexample. The lesson is now load-bearing: gate a load-bearing claim from an error-prone seat on an independent adversarial confirm before the build commits. (Had I let the build proceed on pp's measurement, the formaliser would have chased a FALSE bound.)
- **5th producer-fold finding / 10th catch.** Honest read for the operator: the DESTINATION is sound (gauge chart → the folded comparability, which keeps surviving every probe) — it's the intermediate LEMMA SHAPES that have been slippery (additive vs folded vs multiplicative; Sreg- vs coreΦ-charge). Not a wrong approach; a genuinely intricate fold whose correct form took a decorrelated refutation to pin. The L2-close ETA extends again — a STRONG input to the operator's Item-24 scope fork. Continuing under charge-ahead.

**★ UPDATE-82 (2026-06-25) — h2 conditional scaffolding INTEGRATED (both bridges + h1 hR + h3 regroup, axiom-clean); the close is gated on the independent confirm a8a8b2ff. [UPDATE-83: the confirm REFUTED the additive route the scaffolding's additive bridge serves; the folded `germ_charge_of_core_charge` variant + the coreΦ-charge repair are the live path.] HEAD 2624a20f. ★**
- **a9711b920 checkpoint integrated** (reviewer APPROVE + Codex SOUND): the complete frame-agnostic CONDITIONAL machinery, with the contested `coreΦ_germ_charge` correctly HELD + NO re-pointing (per directive). 7 lemmas, all `[propext, Classical.choice, Quot.sound]`; PIN1 clean; producer sorryAx (2681 + L≥3), no monomial_rlct. Forced green-gate (2732 jobs) + controller #print axioms verified.
  - `germ_charge_of_schur_factorization` RELAXED (exact hCore → germ charge) + `germ_charge_of_core_charge` (NEW, charges the global Schur frobSq(R) directly). **Both bridge variants banked** — covers whichever charge-point the confirm picks.
  - h1 hR producer-spelling (`rcore_{eq,}schur_factor_of_corner_split`); h3 regroup (`schur_product_regroup` + the remainder identity + frobeniusSq bound, the NON-naive route).
- **Only the close remains, gated:** (1) `coreΦ_germ_charge` on the S5a domain — the contested O(Sreg) bound, HELD on **a8a8b2ff** (the fresh decorrelated obstruction seat adversarially testing it); (2) the producer wiring at 2681 (L=2 case-split via `prod_eq_prodAux_mul_last` m=1, instantiate the corner-split hR on Mw/hRegBlocks, the reg-block estimates + ⅟P bound) + the L≥3 guarded sorry. Both deferred to the post-confirm iteration to avoid thrash. a9711b920 ready to build on relay.
- **Net:** the L2 producer is now ONE bound (coreΦ_germ_charge) + the mechanical wiring from closing — and that bound is under independent stress-test. If a8a8b2ff confirms, the close is a single focused tide; if it refutes, pp re-adjudicates (both bridge variants are pre-banked to absorb either charge-point).

**UPDATE-81 (2026-06-25) — h2 fork: MISMATCH branch (loss-core framed, coreΦ frame-free); gap folds O(Sreg) on S5a but pp owns a 3rd error → INDEPENDENT decorrelated confirm commissioned before commit. HEAD e4b2f86a.**
- **pp's fork verdict (`h2-fork-verdict.md`):** the true loss core IS the framed `frobSq(Rcore)` (banked leaf `dlnLoss_two_sided_of_frame`), `coreΦ` is frame-free ⇒ MISMATCH branch. Gap `|frobSq(Rcore) − coreΦ|/Sreg` BOUNDED on the S5a domain (cond P00 ≤ M, the **correct +1 pivot** P00=N11+1→1 at w0, bounded ⅟P00) — O(Sreg), median ~0.011. **NO re-pointing** (keep coreΦ frame-free, preserves `deepest_loss_squeeze`'s public conclusion; charge the gap to Sreg). Bridge relax: hCore → `|coreΦ − frobSq(Rcore)| ≤ Ccore·Sreg` (the framed **Rcore**, NOT the per-layer product — pp's earlier O(Sreg²) measured the wrong object).
- **pp owns a THIRD error + asks for an independent confirm.** Its first fork-hunt found a ~1e9 blow-up = wrong pivot (bare N11→0, not N11+1). Sub-thread error tally (pp's own): h1-cert "frame-free" wrong; h2-germfold tested the per-layer-product not frobSq(Rcore); fork's first hunt wrong pivot. Each was caught (the formaliser's caution / my "O(1) not O(Sreg)" / pp's self-check). **Given the error rate, I commissioned a FULLY decorrelated confirm** (a8a8b2ff, fresh obstruction seat, independent numeric setup — NOT pp's Codex): adversarially test `|frobSq(Rcore) − coreΦ| ≤ Ccore·Sreg` uniformly on S5a, red-teaming the kill-conditions (blow-up on S5a? uniform? right domain? order?). This GATES the build.
- **Build state:** a9711b920 HOLDS `hCore_germ` (don't prove a possibly-mis-scoped bound) but builds the SAFE conditional pieces — the bridge germ-relax (sound regardless), h1's hR (banked), h3's regroup. pp on-call to re-adjudicate if the confirm refutes. The bounded-⅟P00 / `eventually_P00_invertible` (S5a) hypothesis is LOAD-BEARING (the bound only holds there; excludes the blow-up).
- **Honest meta (operator-relevant):** the h2 sub-thread has had FOUR corrections; the underlying math keeps SURVIVING (the gap folds — just on a refined object/domain each time), so it reads "intricate but sound," not "wrong approach." But the error rate + the extending L2-close ETA are real, and I'm now gating on an independent confirm. This is the disposition working (no green-but-wrong; stress-test the load-bearing claim) — and a strong input to the operator's Item-24 scope call. Recorded; continuing under charge-ahead.

**★ UPDATE-80 (2026-06-25) — 9th catch RESOLVED: the frame discrepancy is O(Sreg²) (reg-read-gated); germ fold works, NO escalation. h2 build RESUMING. [REFINED by UPDATE-81: the O(Sreg²) was the per-layer-product gap; the RIGHT object is frobSq(Rcore), gap O(Sreg) on S5a; independent confirm pending.] HEAD d7b87943. ★**
- **pp's decisive sweep (w→w0):** `|frobSq(framed Ŝ0Ŝ1) − coreΦ| / Sreg → 0`; `/Sreg²` scale-invariant ⇒ disc = **O(Sreg²)**. Mechanism (the insight all of us missed): the gauge frames are O(1) constants, but their Schur distortion enters ONLY through off-diag frame blocks × the vanishing reg reads (Y_s,Z_s=O(√Sreg)) — **reg-read-gated**, so it vanishes at w0. So UPDATE-78's O(Sreg) CONCLUSION was right (UPDATE-79's intermediate "O(1)" was a single-point-away-from-w0 artifact); only the SWEEP settled the order. Lesson vindicated: verify a claimed-small term's ORDER (sweep to w0) before designing around it.
- **Resolution (clean, no wall):** the germ fold works. Two pieces, build resuming (a9711b920): (1) RELAX the bridge `germ_charge_of_schur_factorization`'s `hCore` from exact to `|coreΦ − frobSq(S0S1)| ≤ Ccore·Sreg` + a one-line triangle fold (S5c machinery unchanged, C = C_old+Ccore, ~5-10 LoC; authorized to edit DeepestGermCharge); (2) the producer's `coreΦ_germ_charge : |coreΦ − frobSq(Ŝ0·Ŝ1)| ≤ Ccore·Sreg` — the MEDIUM frame-decoration bound (h3-style Cauchy–Schwarz on frame-off-diag × vanishing-reg-reads). Then h3 (regroup, framed Ŝ) + h1 hR (banked) → close 2680 at L=2 + L≥3 guarded sorry.
- **Residual risk (flagged):** `coreΦ_germ_charge`'s exact proof MAY need the symbolic `Ŝ_s − S'_s` expansion (rect blocks + 3 inverses, heavy) pp didn't derive — pp on-call to pin it. The numeric sweep + reg-read-gating are strong evidence the bound is TRUE, so it's finding the proof, not whether it holds. The producer's last piece is now: h1 DONE + bridge-relax (small) + coreΦ_germ_charge (MEDIUM) + h3 + L=2 close. 4 producer findings, all caught before a false build, all resolved bounded — no wall.

**UPDATE-79 (2026-06-25) — CORRECTION: the frame discrepancy is O(1), NOT O(Sreg) (my UPDATE-78 framing was premature); resolution = FRAME-CONSISTENCY (pp adjudicating). [SUPERSEDED by UPDATE-80: the sweep shows O(Sreg²) — the "O(1)" was an away-from-w0 artifact; germ fold works.] HEAD 4ad2527b.**
- **pp owned its h1-cert error + corrected ME.** pp's honest adjudication (`h2-frame-cert.md`, Codex + exact/numeric): the formaliser is RIGHT — there IS a real frame obligation; pp's cert "work frame-free post-hconj" was an ERROR (hconj strips frames from the PRODUCT, but `Rcore` is the Schur of the FRAMED Mw — the Schur is NOT frame-invariant). AND pp refuted MY UPDATE-78 "O(Sreg) relax": the gauge frames are **w-independent O(1) constants** (NOT →I near w0), so the discrepancy is **O(1)**, not O(Sreg). Verified: global Schur ratio under frames unbounded (~5e7); per-layer Schur ratio unbounded (~9e4). The germ-relax route is DEAD. **I was premature in UPDATE-78** (assumed frames vanish at w0) — the same unverified-assumption trap the cert hit; the numeric check corrected both of us.
- **The real resolution — FRAME-CONSISTENCY (pp's dichotomy).** Not frame-cancellation, not O(Sreg)-relax: make the producer's core framed-CONSISTENT with the LDU's framed cores. The decisive load-bearing question (pp taking the focused adjudication): is the producer's `coreΦ` (`deepestCoreAbsorb`, frame-free reads) consistent with `deepestEFull` (the framed reg term)? IF the true loss core IS framed (deepestCoreAbsorb should read framed) ⇒ h2 is a clean framed=framed identification (`coreΦ = frobSq(Ŝ0·Ŝ1)` EXACT, hCore holds as-is, ~1-2 tides). IF deepestCoreAbsorb is genuinely frame-free while the reg term is framed ⇒ real mismatch (re-point coreΦ to framed reads [check it preserves `deepest_loss_squeeze`'s public conclusion] OR a frame-covariance lemma [heavier — a stronger Item-24 trigger]).
- **What STANDS (pp confirms):** h1's `hR` (the LDU is frame-AGNOSTIC, gives `Rcore = Ŝ0·(1−K̂)·Ŝ1` with framed cores — sound as banked); h3's regroup (re-derives with framed Ŝ); the S5c atom, the bridge, the LDU — all banked, all sound. So the banked foundation is intact; the open point is purely the h2 core frame-consistency.
- **Agents:** pp on the frame-consistency adjudication; a9711b920 (sole builder) de-risking h1+h3 with the FRAMED cores (h2 paused). 9th catch (4th producer finding) — caught before a false build; bounded pending pp's branch.

**UPDATE-78 (2026-06-25, SUPERSEDED by UPDATE-79 on the O(Sreg) point) — h1 breakthrough banked (cast cleared, general-L); h2 frame finding: exact hCore is FALSE under frames → [WRONG: I proposed an O(Sreg)-relaxed sibling; pp refuted — the discrepancy is O(1), resolution is frame-consistency, see UPDATE-79]. HEAD 440bbbf8.**
- **h1 DONE + integrated (440bbbf8):** `prod_eq_prodAux_mul_last` — af8305f1 cleared the `prodAux_succ` cast grind (a single fold `prod = prodAux m · recast last`, avoiding the `prodAux 0 = 1` One-friction; general-L). With `reindex_mul_schur_factor` this gives h1's `hR` end-to-end. Axiom-clean. The cast (the documented hardest blocker) is BEATEN.
- **Agent hygiene:** af8305f1 (rect foundation + h1, ~407k tokens) stood down after delivering h1 + the h2 finding; a2795a88 (a duplicate I'd spawned for the same wiring) killed; **a9711b920 is now the sole h2/h3 builder** (fresh context, base 440bbbf8), paused on h2 / de-risking h1+h3.
- **h2 FRAME FINDING (numeric, load-bearing — pinned before a false build).** af8305f1's numeric check (L=2, rect, nontrivial frames): h1 SOUND (FRAMED-block LDU cores reproduce the global Schur EXACTLY), but the bridge's EXACT `hCore : coreΦ = frobSq(S0·S1)` is FALSE under frames (`frobSq(framed S0S1)=1.065` vs frame-free `coreΦ=0.938`) — the surviving endpoint frames Pf_0=P0/Qf_1=QL decorate readY/readZ/coreRead. The banked bridge `germ_charge_of_schur_factorization` is SOUND as a conditional (the implication holds), but its `hCore` hypothesis is unmeetable under the framed producer.
- **Resolution (pp adjudicating, decisive question pinned):** is the discrepancy `frobSq(framed S0S1) − coreΦ` itself **O(Sreg)** (vanishing at w0, since the frame factors are I+O(√Sreg) there)? If YES (expected) → re-state the bridge with `hCore` RELAXED to the germ charge `|coreΦ − frobSq(S0S1)| ≤ C·Sreg` (the S5c-split proof absorbs the extra term) — EXACTLY the 8th-catch pattern (exact equality false, germ charge true), one level deeper. If NO → escalate (producer germ charge false as posed). pp verifying numerically (sweep to w0) + producing the re-stated bridge.
- **Net:** the producer's last piece is now: h1 DONE; the bridge needs a bounded O(Sreg) re-statement (pp); then h2 (the discrepancy charge) + h3 (regroup) + L=2 close. A modest extension, NOT a wall — the numeric check pinned the issue before the formaliser built the false exact hCore. The recurring `exact-→-germ` lesson (8th catch) re-applies; consider hardening the bridge's API to germ-charge form by default.

**★ UPDATE-77 (2026-06-25) — rectangular foundation INTEGRATED (green, axiom-clean); producer wiring (close 2680) commissioned. HEAD 7e987a8e. ★**
- **af8305f1 checkpoint integrated.** The full S5c/LDU/germ-charge stack generalized in-place to RECTANGULAR (3 widths) + the new `DeepestBlockDecomp.lean` (h1 helpers `reindex_mul_split`/`_fromBlocks`/`_schur_factor`). Copied at file level (supersedes the square dfcfeb82 copies); producer UNMODIFIED. Forced green-gate (2732 jobs); controller `#print axioms`: the 4 foundation lemmas (`schur_product_ldu`, `schur_core_germ_comparability`, `germ_charge_of_schur_factorization`, `reindex_mul_schur_factor`) + PIN1 all `[propext, Classical.choice, Quot.sound]`; `deepest_loss_squeeze`/`_gauge_construction` `sorryAx` (the 3 producer sorries), no `monomial_rlct`. Reviewer SOUND. Committed 7e987a8e.
- **Producer wiring commissioned (a2795a88, FRESH formaliser, clean context for the ~300-LoC cast-grind, base 7e987a8e).** The precise 4-step residual: (i) h1 connect `prod(F w)=F_0·F_1` at L=2 (`prodAux_succ` cast reduction) → `reindex_mul_schur_factor` via `hRegBlocks` ⇒ `hR`; (ii) h2 coreΦ-match (`deepestCoreF_coreAbsorb_eq_prodSchur`, clean@L=2); (iii) h3 the REGROUP (dead-end pinned SOUNDNESS-CRITICAL); (iv) L=2 case-split + precise L≥3 guarded sorry → `exact germ_charge_of_schur_factorization`. Non-negotiable: L=2 path axiom-clean (the L≥3 sorry must not leak); PIN1 clean. Spawned FRESH (not re-engaged af8305f1's 322k-token context) — heavy cast work wants a clean context; the design transfers via the precise spec + the documented lemmas.
- **Honest tally:** the producer's last piece is now 2 tides (rectangular foundation DONE + the wiring IN FLIGHT) — the cert's MODERATE 2-3 was wrong on general-L recursion + rectangularity (both caught + handled). The rectangular foundation is solid banked progress the wiring stands on. If a2795a88 closes 2680, the L2 body is complete for front pivot (L=2) and the L2 close reduces to the final wire.

**UPDATE-76 (2026-06-25) — 2nd finding: the banked S5c/LDU/bridge stack is SQUARE but the producer is RECTANGULAR (bites at L=2); APPROVED in-place generalization to 3 widths.**
- The formaliser (af8305f1) found the banked `schur_product_ldu` / `germ_charge_of_schur_factorization` / `schur_core_germ_comparability` (all from l2-framestrip THIS session) are stated for SQUARE blocks (one type M), but the producer's Schur complement `Rcore` is RECTANGULAR `(H0−r)×(Hlast−r)` (general/RRR B has H0≠Hlast). So `exact germ_charge_of_schur_factorization` can't typecheck — independent of L. Its h1 block-decomp helpers (new `DeepestBlockDecomp.lean`) already BUILD sorry-free and are rectangular-correct; only the final factor needs the rectangular bridge.
- **DECISION — option (Y): generalize the three lemmas IN-PLACE to three widths** (the square form was an over-narrow ACCIDENT of l2-framestrip — the math is width-generic; the lemmas have no load-bearing external consumers yet, so this is the precision/weakest-hypotheses fix, not a duplicate). Lifted "consume unmodified" for exactly these three. Conditions pinned: grep-verify no external consumers first; genuine 3-width statements with ported witnesses; re-verify axiom-clean + PIN1 clean. Supersedes my square copies (dfcfeb82) — I integrate the formaliser's rectangular versions at file level. Net: +1 tide (rectangular re-statement), still MODERATE; the h1 helpers building sorry-free is real progress.

**UPDATE-75 (2026-06-25) — architecture finding: the germ charge is general-L-research-grade at L≥3 (h2 recursion); APPROVED option (a) — close L=2, guard L≥3 (the 3169/3174 pattern).**
- **The h1/h2/h3 formaliser (af8305f1) caught a real snag BEFORE the budget (Codex xhigh-confirmed).** The banked bridge `germ_charge_of_schur_factorization` + `schur_product_ldu` is a **TWO-FACTOR** Schur-LDU; the germ charge is stated for the full `2≤L`. h1(hR) lifts to general L by grouping C0=(first L−1)·C1=(last); but **h2 is NOT clean for L≥3** — h1's S0 (the Schur core of the grouped first-(L−1) product) must equal the (L−1)-product of per-layer absorbed cores, a RECURSIVE multi-factor Schur-core-of-product identity (off-diagonal-leak absorption), research-grade. At L=2 it's trivially two-factor (h2 clean, no recursion) ⇒ the germ charge CLOSES at L=2. The cert's "h2 CLEAN" was correct AT L=2; the general-L recursion is a refinement.
- **DECISION — option (a) (close L=2 fully, guard L≥3 as a precise sorry).** Reasoning: (i) the producer ALREADY has this split — 3169/3174 (Item 19) are the same pattern; (ii) the deployment target is the L=2 milestone, and the general-L recursive induction (option b) is research-grade AND insufficient alone (general R1 + general hdiv + D1 are also held general-L); (iii) (a) keeps the true `2≤L` statement with a correct guarded sorry (honest building block, precedent, zero churn) over (c)'s signature narrowing. The disposition: (a) fills the L=2 layer; the recursive Schur-core induction is a research-grade boundary move → roadmap. NON-NEGOTIABLE I pinned: the L=2 instance must be genuinely axiom-clean (the L≥3 sorry must not leak) + the L≥3 sorry stated precisely.
- **NEW unifying general-L gap (recorded Item 22 + Item 24 input):** the general-L producer needs the **recursive multi-factor Schur-core-of-product identity** (subsumes the 3 L≥3 guarded sorries 2680-L≥3/3169/3174). This SHARPENS Item 24: the general-L=2 producer (option a) is the MODERATE deliverable in progress; the FULL general-L producer is research-grade here too — so the operator's scope fork (general-L vs L=2/RRR milestone) now has a clearer cost on the general-L arm.

**★ UPDATE-74 (2026-06-25) — h1 design LANDED (probed: MODERATE, NOT a grind; h3 dead-end pinned); h1/h2/h3 formaliser build commissioned. HEAD ee3eb198. ★**
- **pp-pin2-rearch delivered the h1 design (`h1-blockdecomp-cert.md`, banked).** PROBED third estimate (ruthless, decorrelated Codex xhigh + sympy/numeric): **h1 MODERATE 2 tides, h2 CLEAN, h3 MODERATE (one non-obvious regroup) — NOT research-grade.** Crucially more credible than UPDATE-70's unprobed downgrade: each obligation individually analyzed, the LDU banked (the l2-framestrip build confirms), h2's feared framed-vs-raw `⅟A_s` mismatch resolved from code (lemma-1's `schurCorrection` uses the SAME raw `⅟(1+readX_s)` ⇒ `S'_s = S_s` exactly), and h3's DEAD-END found + ruled out.
- **The h3 soundness pin (high-value).** The naive submult `frobSq S0·frobSq K·frobSq S1` is a VERIFIED dead end (the core T_s escapes Sreg ⇒ blows up). The clean route REGROUPS: `R−S0S1 = −S0·K·S1 = −(S0·Z1)·⅟P·(Y0·S1)` (K=Z1⅟PY0); the off-diag blocks pair a BOUNDED core-S with a REGULAR read (Z1,Y0=O(√Sreg)) ⇒ `frobSq(S0Z1),frobSq(Y0S1) ≤ C·Sreg` ⇒ `hRem ≤ Crem·Sreg²`. I verified the regroup algebra independently. NO bridge restatement — `germ_charge_of_schur_factorization`'s `hRem` form is achievable as-is.
- **Commissioned the contained h1/h2/h3 build** (af8305f1, lean-formaliser worktree, base ee3eb198): supply `Mw_eq_blockProduct` (h1⇒hR), `coreΦ_eq_frobSq_prodSchur` (h2), `frobSq_S0Z1_le_Sreg`+`frobSq_Y0S1_le_Sreg` (h3⇒hRem via regroup) → `exact germ_charge_of_schur_factorization` → close 2680. h3 dead-end flagged SOUNDNESS-CRITICAL. Also: check the L=2 path is axiom-clean (discharge/isolate the 2 L≥3-interior sorries 3169/3174). pp on-call for the reindex_mul cast-noise (h1) / off-diag bounds (h3). Reviewer + #print axioms before report.
- **Design-before-build gate satisfied.** This is the FOURTH estimate of the producer's last piece — but the first fully PROBED one (math verified end-to-end, the one trap pinned). If the formaliser closes it, the L2 body is complete for front pivot, and the L2 close reduces to the final wire (squeeze-exists relocation + L=1/2≤L case-split + product_reduction + the WLOG `rlct_infimum_colPerm_eq`).

**★ UPDATE-73 (2026-06-25) — R1 (3,3,4) hfin COMPLETE (S2-free, axiom-clean); the (3,3,4) ANCHOR is done both legs. HEAD d95a074b. ★**
- **r1-ginnerz LANDED + integrated.** `ginnerZ_lt_top` (STEP-3b, the outer z-change-of-variables) CLOSED via the per-p slot bijection `Fin 8 ≃ (Fin 2×Fin 2)⊕Fin 4` + the MP reshape + the banked `resolved334_box_lt_top` reduction (+446/−55, `RouteM334Ratiofin.lean`). **`routeMCore_M334_threshold_lt_top` now fully `[propext, Classical.choice, Quot.sound]`** — NO sorryAx, NO monomial_rlct (re-verified by controller `#print axioms`). Reviewer PASS (decorrelated, byte-identical statement, axiom hygiene re-run, banked atoms untouched).
- **Milestone: the R1 (3,3,4) anchor is COMPLETE S2-free on BOTH legs** — hdiv (`routeMCore_box_diverges_achiever`, banked) + hfin (this). The Route-M cover route is now fully validated at the anchor witness. This is the concrete R1-gate evidence for (3,3,4); it banks the upper-leg long pole (#55) for the anchor.
- **General R1 remains HELD** (standing decision / operator bandwidth): the general-r lift (N2b r≥3 + general N4 + the rank-stratified ladder) + general hdiv (`routeMCore_box_diverges_achiever` general — the (3,3,3,3) Frame-det Lean-cost wall, a det-tactic grind). The anchor-complete milestone makes the general lift the natural next R1 target when focused bandwidth frees; not un-holding autonomously (large det-tactic build the operator flagged).
- **Live tracks now:** L2 producer h1 design (pp-pin2-rearch, in flight) is the sole active critical-path track. D1 ≥-leg is L2-gated (can't proceed until L2 closes). Aggregator wiring + the `continuous_dlnLoss`/`minAdm_M4422` dedupes stay deferred to gate-close (the Deepest* subtree can't enter the aggregator until h1/h2/h3 close anyway).

**★ UPDATE-72 (2026-06-25) — INTEGRATED l2-wlog (complete) + l2-framestrip (partial); HONEST RE-ESCALATION: the producer is NOT one piece away — gap = h1/h2/h3. HEAD dfcfeb82. ★**
- **l2-wlog LANDED + integrated (complete, axiom-clean).** `FrontPivotWLOG.lean` (NEW, 2648-job green): the front-pivot WLOG transfer — `front_pivot_perm_exists`, `dlnLoss_colPerm_eq`, `paramColPermLast_measurePreserving`, `rlct_infimum_colPerm_eq`, all `[propext, Classical.choice, Quot.sound]`. Discharges `hJfront` via the headline ⨅-over-optimalSet form. Fidelity-reviewed PASS (the review agent a57309af confirms). **This piece is DONE.**
- **l2-framestrip LANDED + integrated (PARTIAL — banks the genuinely-new lemma, does NOT close the producer).** `schur_product_ldu` (the frame-free two-layer LDU, the ONE genuinely-new lemma, all r,M, any CommRing) + `germ_charge_of_schur_factorization` (the conditional bridge, explicit C) — both axiom-clean, sorry-free. PIN1 `deepestEPivot_regSlice_fderiv` re-verified STILL clean (no regression). `deepest_loss_squeeze`/`_gauge_construction` trace `sorryAx` (the 3 open obligations + 2 L≥3-interior), **NO `monomial_rlct`**.
- **HONEST RE-ESCALATION (corrects UPDATE-70's MODERATE downgrade).** l2-framestrip + decorrelated Codex(xhigh) + reviewer: the brief's "the ONLY new piece is the frame-free LDU" was WRONG. The producer germ charge additionally needs THREE precisely-named unbuilt obligations — **h1** (the per-layer block decomposition `Mw.toBlocks ↔ (fromBlocks A0 Y0 Z0 T0)·(fromBlocks A1 Y1 Z1 T1)` — the interior-frame telescope at the BLOCK level, NOT the banked single-matrix `hS2_front`; the HEAVIEST, ~300+ LoC), **h2** (match lemma-1's absorbed cores to `schur_product_ldu`'s `S_s = T_s−Z_s⅟A_sY_s`), **h3** (the reg-block size estimate `‖Y0‖,‖Z1‖ ≤ √Sreg` ⟹ `K=O(Sreg)` quadratic remainder). Multi-tide (~300-1500 LoC). **The L2 body is NOT complete for front pivot.** Net progress: the gap went from "vague structural bridge" → three attackable, individually-named obligations (the bridge + LDU are the banked half). The pattern (6th/7th/8th catch + this) is real layer-filling — each banked piece is solid — but the producer keeps revealing the next layer; this is now a genuine **operator scope-decision point** (recorded Item 22 correction + the scope flag).
- **Next directed target:** h1 (the per-layer block telescope at L=2) — the heaviest, the producer's load-bearing geometry, the natural next attack. Commissioning a design-first pass (the established design→build discipline; h2/h3 are lighter and follow). r1-ginnerz (ad5cc07d) still running (the (3,3,4) hfin's last sorry); a57309af review came to rest (PASS).

**UPDATE-71 (2026-06-25) — idle heartbeat: 4 builds in flight (none reported); drift-glance found a stray θ-components expedition (off-path, captured + left untracked).**
- **Tick state:** the 4 final-piece builds (l2-framestrip a3a53074, l2-wlog af2c20b4, r1-ginnerz ad5cc07d, + a fidelity review of FrontPivotWLOG a57309af) all still running; r1-ginnerz actively grinding measurability errors. Nothing LANDED ⟹ idle heartbeat, no integration this tick. HEAD = e78ed0ff.
- **Drift-glance found a stray, off-critical-path expedition** `expeditions/2026-06-25-theta-components/` (untracked, created by another context — not mine, like the fibre-codim stray). It carries a clean decorrelated-Codex θ adjudication: **LR-θ and Aoyagi-θ are GENUINELY DIFFERENT invariants** — LR θ_geom = #top-dimensional components = `binom(m,|δ|)`; Aoyagi θ_order = pole order/SLT multiplicity = `|δ|(m−|δ|)+1`; they agree **iff |δ|≤1** (smallest disagreement (2,2,2,2,2): 6 vs 5). **Aoyagi-full impact: NONE on the headline** — `aoyagi_learning_coefficient` is a **λ statement**, and λ AGREES between the papers (codim/2 = 3/2 for (2,2,2,2,2)). The caveat is forward-looking: any θ/multiplicity claim in aoyagi-full must use Aoyagi's order-form, never LR's binom. Recorded as discuss-at-close Item 23; left untracked (not committed onto the aoyagi-full branch — wrong expedition).

**★ UPDATE-70 (2026-06-25) — frame-stripping DOWNGRADED to MODERATE (not a wall); all 3 final-piece builds in flight. ★**
- **frame-stripping bridge: NOT research-grade — MODERATE 2-3 tides (~200-350 LoC)** (pp-pin2-rearch + Codex honest re-read,
  frame-stripping-cert @d111fee7). The "frames" worry resolves: frame-stripping is ALREADY DONE (the banked (b)-exact hconj → the
  frame-free ∏C_s); only the frame-free 2-layer LDU `Rcore=S0·(1−K)·S1` is new (= the hR the S5c atom defers). Mathlib SchurComplement
  API is the toolkit; a bounded 4-lemma directed sequence (schur_P11_decomp style), one watch-item (⅟P bookkeeping). Item 22 downgraded.
- **l2-framestrip LAUNCHED** (a3a53074) — builds the frame-free LDU (the 4-step route) → hR → the banked S5c charge → closes (d')/(e')
  → the L2 body COMPLETE for front pivot. pp-pin2-rearch on-call (step-2 unipotent-strip / ⅟P).
- **3 builds in flight (independent files):** l2-framestrip (the producer's last piece) + l2-wlog (the WLOG transfer, hJfront discharge)
  + r1-ginnerz (the (3,3,4) hfin's last sorry). pp seats on-call. The L2 close = these + the final wire (squeeze-exists relocation +
  case-split). General hdiv + general lifts + D1 ahead. No operator wall — the producer's last piece is a contained build.

**UPDATE-69 (2026-06-25) — L2 producer down to the frame-stripping bridge (research-grade, verified algebra); 8th catch fixed; WLOG launched.**
- **l2-core-de @4a3bdd60:** (d')/(e') reduced 2→1 sorry. Banked: lemma-1 decode `deepestCoreF_coreAbsorb_eq_prodSchur` (coreΦ=‖∏S‖²)
  + the γ=1+C composition. **8th catch:** the prior γ=1 demanded the FALSE standalone Score=coreΦ (M>1); rebound to γ=1+C (in-sum
  fold) + the charge made a genuine germ. PIN1 clean.
- **The producer's LAST piece = the FRAME-STRIPPING BRIDGE** (1 germ charge): `Rcore = S0·(1−K)·S1` with the SAME S_s as lemma-1,
  despite Pf,Qf frames. Algebra sympy+Codex VERIFIED (ALL ZERO, K=Z1⅟P Y0) — TRUE, not a math wall — but flagged RESEARCH-GRADE in
  Lean (3 inverses, no clean ring, non-telescoping middle). pp-pin2-rearch pinning the Lean route (frame-stripping-cert; asked to
  flag honestly if multi-tide). Item 22 — operator-relevant: the hardest-to-formalise L2 piece; a candidate scope-call point.
- **In parallel (independent):** l2-wlog (af2c20b4) building the WLOG transfer (b-wlog 1-4: front-pivot-perm + loss identity + MP +
  the ⨅-transfer — the headline-level hJfront discharge machinery) + r1-ginnerz (ad5cc07d) the (3,3,4) ginnerZ final sorry.
- L2 close now gated on: the frame-stripping bridge + the final wire (WLOG [building] + squeeze-exists relocation + case-split).
  R1 (3,3,4) hfin gated on ginnerZ [building]. Active: l2-wlog + r1-ginnerz (builds) + pp-pin2-rearch (frame-stripping design).
  General hdiv + general lifts + D1 ahead. 8 soundness findings, all resolved/fixed; PIN1 verbatim throughout.

**UPDATE-68 (2026-06-25) — (3,3,4) hfin spine ALL banked @e0f6681a; gap → one index-relabel (ginnerZ_lt_top); both poles' final pieces building.**
- **r1-ratiofin banked:** the entire hratiofin spine is sorry-free — STEP-1 (the permutation, Codex's flagged highest-risk), STEP-2
  (outer), STEP-3a (inner T-peel), the per-z Schur comparability — and `RouteM334Hfin` is now ZERO-sorry; the (3,3,4) headline
  relocated to the new RouteM334Ratiofin.lean (breaks the import cycle). Gap narrowed to `ginnerZ_lt_top` (STEP-3b).
- **r1-ginnerz LAUNCHED** (ad5cc07d) — closes `ginnerZ_lt_top`: the per-p z-slot identification (raw/g/b, via Fin.exists_succAbove_eq)
  + the raw↦Δ translation (banked `lintegral_translate_le`) + the feed to the banked `resolved334_box_lt_top 3`. Index bookkeeping,
  everything feeding it banked. pp-r1-genM-2 on-call. On close → routeMCore_M334_threshold_lt_top FULLY clean → (3,3,4) hfin complete S2-free.
- **L2:** l2-core-de (a78499af) building the producer (d')/(e') (the Rcore↔coreAbsorb identification + decode + the banked S5c germ charge).
- Active: l2-core-de (L2 producer final) + r1-ginnerz (R1 (3,3,4) final). pp seats on-call. General hdiv + general lifts + D1 ahead.
- Both long poles converged to their last index-relabel / identification; all geometric bedrock built; PIN1 verbatim; 7 findings resolved.

**★ UPDATE-67 (2026-06-25) — the L2 gauge-chart geometric heart is DESIGNED END-TO-END; producer's final (d')/(e') building. ★**
- **Rcore↔coreAbsorb pinned @2770ccb2** (pp-pin2-rearch + Codex): (d')/(e') is NOT new geometry — `Rcore = S0·W·S1` (the banked
  S5c block-LDU, NOT =∏S), so it closes via the banked S5c GERM CHARGE `|frobSq(Rcore)−coreΦ| ≤ C·Sreg` in the IN-SUM folded form
  `Sreg+frobSq(Rcore) ≍ Sreg+coreΦ` (γ=1+C; never a standalone ratio — the germ lesson). `coreΦ=‖∏S‖²` EXACT (coreShearHomeo
  add-form + χ=1 decode). The only new work: one IDENTIFICATION lemma (producer Rcore blocks ↔ S5c input) + a routine decode + the linarith.
- **l2-core-de LAUNCHED** (a78499af) — builds the (d')/(e') (deepestCoreF_coreAbsorb_eq_prodSchur + rcore_coreAbsorb_germ_charge +
  the γ=1+C composition). On close → **the L2 body (the chart) is COMPLETE for front pivot** (only the 2 vacuous-at-L2 interior remain).
  pp-pin2-rearch on-call for the step-3 block-extraction glue.
- **The entire L2 gauge-chart heart is now DESIGNED END-TO-END:** PIN1 → PIN2(full-reg) → S5c germ atom → hTilde →
  (b)-route-B (front-pivot, (b) EXACT) → leak(c) → Rcore↔coreAbsorb. The deepest part of the programme. Remaining L2: this build +
  the final wire (WLOG discharge hJfront + squeeze-exists relocation + case-split + product_reduction).
- **R1 (3,3,4):** r1-ratiofin (a22cef05) building the last sorry (hratiofin) → complete S2-free hfin.
- Active: l2-core-de (L2 producer final) + r1-ratiofin (R1 (3,3,4) final). pp seats on-call. General hdiv + general lifts + D1 ahead.

**UPDATE-66 (2026-06-25) — L2 hproducer leak (c) CLOSED @8dd67a56; producer down to the core (d')/(e') (the Rcore↔coreAbsorb block-LDU).**
- **l2-leak-core:** the leak conjunct (c) `∑(P10·⅟P00·P01)² ≤ Sreg` closed sorry-free (`eventually_leak` + the coupled-U {S5a}∩{S5b},
  t=1; reviewer PASS incl. goal-not-weakened). hproducer = (a)+(b)-EXACT+S5a+leak(c) all PROVEN; PIN1 clean; no monomial_rlct.
- **The producer's LAST piece = the folded core (d')/(e') (2 sorries):** needs the UNBUILT structural bridge `Rcore = P11−P10⅟P00P01
  ↔ deepestCoreF(deepestCoreAbsorb)` (the block-LDU; the decomp-cert under-specified (iv) as "pure wiring"; confirmed by Codex). The
  banked `schur_core_germ_comparability` charges it at γ=1+C once the identity exists. **pp-pin2-rearch pinning it** (rcore-coreabsorb-cert,
  design-before-build to avoid another thrashing cycle). Then a formaliser build → the L2 body complete for front pivot.
- **R1 (3,3,4):** r1-ratiofin (a22cef05) building the last sorry (hratiofin) → on close the (3,3,4) hfin is complete S2-free.
- Active: r1-ratiofin (R1 build) + pp-pin2-rearch (L2 Rcore↔coreAbsorb design). pp-r1-genM-2 on-call. The L2 producer (d')/(e') build is
  HELD pending pp's pin. General hdiv + general lifts + D1 ahead.

**UPDATE-65 (2026-06-25) — (3,3,4) hfin down to ONE sorry (hratiofin); radial separation built @acd5c4e2; both poles' last pieces building.**
- **r1-chart banked:** the per-chart radial separation is PROVEN (piFinSuccAbove MP + Fubini + radialAxis discharge; `angularA1_integral_le`
  the integral-level schur comparability + the zero-guard). `matBox334_chart_lt_top`'s gap narrowed to the lone `hratiofin` (the ratio
  residual: per-pivot permutation + Step-C translation-CoV → the banked `angularA1_integral_le` + `resolved334_box_lt_top 3`).
- **r1-ratiofin LAUNCHED** (a22cef05) — closes `hratiofin` (clean interface). On close → routeMCore_M334_threshold_lt_top fully
  `[propext, Classical.choice, Quot.sound]` → **the (3,3,4) hfin is a COMPLETE S2-free proof.** pp-r1-genM-2 on-call.
- **L2:** l2-leak-core (ab31f89e) building the producer leak+core (eventually_leak + the core charge via the banked S5c atom) → on close
  the L2 body (chart) complete for front pivot → then the WLOG/final-wire (discharge hJfront + squeeze-exists relocation + case-split).
- Active: l2-leak-core (L2 producer) + r1-ratiofin (R1 (3,3,4) last sorry). pp seats on-call. General hdiv + general lifts + D1 ahead.

**★ UPDATE-64 (2026-06-25) — L2 (b)-route B LANDED @2077d929: (b) EXACT under front pivot; hproducer down to leak+core; both gates near. ★**
- **l2-broute landed:** the B insight realized — under `hJfront` (J=frontEmbed) the producer's (b)-conjunct is the EXACT equality
  `∑deepestEFull²=Sreg` (δ₁=δ₂=1), no Pπ-telescope/FACT2/germ-Taylor. PROVEN inside hproducer: (a) block-decomp + (b)-EXACT + S5a.
  NEW `FrontPivotProducer.lean` (front-pivot alignment + S5a moved upstream, circular import fixed); `deepestEFull_sq_sum_eq_blocks`
  + the clean per-w telescope `hS1'_front/hS2_front`. The chart now carries `hJfront` (discharged by the WLOG at squeeze-exists).
  PIN1 clean; headline sorryAx unchanged from baseline; no monomial_rlct. The giant hproducer sorry SHRANK to 3 narrow
  pivot-agnostic ones (leak (c) + folded core (d')/(e')).
- **l2-leak-core LAUNCHED** (ab31f89e) — closes the producer: (c) `eventually_leak` (sub-mult, P01/P10→0, ⅟P00 bounded from S5a) +
  (d')/(e') `eventually_core_comparable` (the per-layer↔global Schur charge via the BANKED `schur_core_germ_comparability`) + the
  coupled-U. pp-pin2-rearch on-call. On close → the L2 body (the chart) is COMPLETE for front pivot (only the 2 vacuous-at-L2 interior).
- **L2-gate remaining after the producer:** the WLOG transfer (b-wlog 1-5: front_pivot_perm + dlnLoss_colPerm_eq + the coordinate-perm
  MP + the ⨅-transfer via banked rlctAtOn_comp_homeomorph + headline rw) discharging `hJfront` + the squeeze-exists downstream
  relocation + the case-split (L=1 base/2≤L) + product_reduction → the L2 gate. (Controller-coordinated final wire.)
- **R1 (3,3,4):** r1-chart (ae1cc7f4) building the final lemma `matBox334_chart_lt_top` → on close the (3,3,4) hfin is complete S2-free.
- Active: l2-leak-core (L2 producer completion) + r1-chart (R1 (3,3,4) final lemma). pp seats on-call. General hdiv + general lifts + D1 ahead.

**UPDATE-63 (2026-06-25) — R1 (3,3,4) hfin is ONE lemma from complete; matBox cover banked @99e7bb04; r1-chart on the final lemma.**
- **r1-matbox banked** (+349 LoC, aggregator green 8370): the 9-chart A0 cover assembly is built; `matBox334_blowup_lt_top` is PROVED
  modulo the lone `matBox334_chart_lt_top`. Sorry-free, S2-free: the exponent-bump (0<c'<4 → 2<c'<4), the box-radius-K resolved
  generalisation (`resolved334_box_lt_top`, K=3), the A0↔Fin 9 flatten + MP reindex, the indicator decoupling (Codex-vetted), the
  radial pull-out, and `matBox334_blowup_lt_top_gt2` (flatten + recStep 9-chart cover + ENNReal.sum_lt_top).
- **r1-chart LAUNCHED** (ae1cc7f4) — the (3,3,4) hfin's FINAL lemma `matBox334_chart_lt_top` (the per-chart radial transport):
  the piFinSuccAbove radial Tonelli + the per-pivot permutation invariance (A1↦Q⁻¹A1 MP) + `frobSq_angularR_ge` + the feed to
  `resolved334_box_lt_top 3`. Codex-vetted interface (2 xhigh consults). pp-r1-genM-2 on-call. **On close → routeMCore_M334_threshold_lt_top
  fully [propext, Classical.choice, Quot.sound] (no monomial_rlct) → the (3,3,4) hfin is a COMPLETE S2-free proof.**
- The (3,3,4) hfin convergence: bedrock → residual-power → resolved-form → algebraic heart → 9-chart cover → now ONE per-chart lemma.
- **L2:** l2-broute (a51044d4) building the (b)-route-B (front-pivot chart (b)-exact + producer + WLOG transfer + headline rw).
- Active: l2-broute (L2 (b)-route-B) + r1-chart (R1 (3,3,4) final lemma). pp seats on-call. General hdiv + general lifts + D1 ahead.

**★ UPDATE-62 (2026-06-25) — L2 (b)-route DECIDED: B (front-pivot WLOG), sound + decisively less-Lean; (b) EXACT; build commissioned. ★**
- **B is the (b)-route** (pp-pin2-rearch + decorrelated Codex, b-wlog-spec.md @2095bd64): 3 exact checks (loss identity
  `dlnLoss B A = dlnLoss (B·Π)(τ_Π A)`, τ_Π MP |det Π|=1, rank+front ⟹ (b) EXACT). **Soundness subtlety resolved:** the headline
  is `⨅ w∈optimalSet, rlctAt` (Skeleton:1725) — τ_Π is a global MP homeomorphism mapping optimalSet(B)↔optimalSet(B·Π) preserving
  each rlctAt (banked `rlctAtOn_comp_homeomorph`) ⟹ the ⨅ transfers choice-independently through the headline's EXISTING ⨅-form.
  B avoids A's unbuilt Pπ-telescope+FACT2 ENTIRELY; the Π-frame caveat fully avoided (fresh chart). (b) becomes an EXACT equality
  (front pivot) — the producer's S5a/b/c/(d,e) decomp UNCHANGED, S5a + the S5c atom banked.
- **l2-broute LAUNCHED** (a51044d4) — the full B route: the front-pivot chart ((b)-exact via the clean telescope) + complete the
  hproducer + the 5 WLOG lemmas (front_pivot_perm_exists → dlnLoss_colPerm_eq → paramColPermLast_MP → rlct_infimum_colPerm_eq →
  headline rw). pp-pin2-rearch on-call (front-pivot-perm LA / the ⨅-transfer). On close → the L2 body done + the headline WLOG'd to
  front pivot → the L2 gate (+ the case-split/product_reduction final wire).
- **The L2 (b) saga is RESOLVED in design** (6th catch → comparability → germ/Taylor overturned → A'/B re-adjudicated → B-decisive,
  (b) EXACT). The geometric heart's route is settled + contained; remaining is the B build (l2-broute) + the final wire.
- **R1 (3,3,4):** r1-matbox (ac9892b0) building the 9-chart A0 cover (the last (3,3,4) hfin piece; algebraic heart banked).
- Active: l2-broute (L2 (b)-route-B) + r1-matbox (R1 (3,3,4) cover). pp-pin2-rearch + pp-r1-genM-2 on-call. General hdiv + general lifts + D1 ahead.

**UPDATE-61 (2026-06-25) — L2 hproducer: S5a banked; A's (b) revealed unbuilt Pπ-telescope+FACT2 → A'/B re-adjudication to B (likely wins).**
- **S5a banked @68a51768** (route-independent): `eventually_P00_invertible` (P00 invertible on a 𝓝 w0) + the abstract IsUnit-on-𝓝
  lemma, in the new `DeepestEFullSregComparability.lean` (0 sorries, axiom-clean). NOT wired (Deepest* convention).
- **The (b)-atom (deepestEFull_Sreg_comparable) did NOT close — and it revealed more depth:** A's pointwise comparability rests on
  TWO unbuilt several-hundred-LoC pieces, (1) the corrected Pπ-telescope + (2) the FACT2 reindex identity (the decomp-cert's
  "banked machinery" was the assembly GIVEN them). Structural finding (banked decode lemmas): all 4 reads decode to the SAME raw
  deviation — the telescope is structurally sound. **This FLIPS the A'/B balance** (the prior A'-#1 ranking assumed A's (b) was
  cheap). B (front-pivot WLOG) makes (b) an EXACT equality (front J ⟹ no Pπ ⟹ no FACT2), cost = the MP-invariance
  `rlctAt(loss B)=rlctAt(loss B·Π)` + a fresh chart for B·Π. pp-pin2-rearch re-adjudicating DEFINITIVELY (b-wlog-spec; verify B
  sound + resolve the Π-frame caveat + the build-ready spec for the winner). L2 hproducer build HELD pending the verdict.
- **R1 (3,3,4):** r1-matbox (ac9892b0) building the 9-chart A0 cover (matBox334_blowup_lt_top) — the last (3,3,4) hfin piece.
- **Honest read on hproducer:** it's the genuinely-hard geometric core of the L2 gauge chart (the per-w framed-product telescope +
  reindex + the (b)-comparability for a non-front pivot), peeling layers across tides (6th catch → comparability → germ/Taylor
  overturned → now the Pπ-telescope+FACT2 cost → likely B). Tractable (the comparability HOLDS), but the route choice (A' vs B) is
  the deciding call, now in pp's hands. S5a + the squeeze machinery + the S5c atom are banked for the assembly.
- Active: r1-matbox (R1 build) + pp-pin2-rearch (the A'/B verdict). pp-r1-genM-2 on-call. General hdiv + general lifts + D1 ahead.

**UPDATE-60 (2026-06-25) — R1 (3,3,4) frame-transport algebraic heart BUILT @a393ea89; gap → the 9-chart A0 cover alone; matbox tide launched.**
- **r1-frametransport banked** (+400 LoC, S2-free axiom-clean): `routeMCore_M334_threshold_lt_top` is NO LONGER a sorry — reduces
  to the lone `matBox334_blowup_lt_top`. Built: the MP plumbing (routeMCore→matBox), the exact Schur-shear `R·A1=L_γ·[T;Δ·S]`,
  the SOS comparability `frobSq(R·A1) ≥ (1/5)·(∑T²+frobSq(Δ·S))` (σ_min(L_γ)²=2−√3>1/5, sympy-verified), the radial divisor.
  Decorrelated Codex: pivot on A0, the Jacobian-weighted blow-up is genuinely forced (no MP global reparam).
- **r1-matbox LAUNCHED** (ac9892b0) — the (3,3,4) hfin's LAST piece: `matBox334_blowup_lt_top` = the 9-chart A0 argmax radial
  cover-up-to-null + per-chart radial c-o-v (Jac |a|^8) + the banked `frobSq_angularR_ge` + box-rescale to the banked
  `resolved334_lt_top` + ENNReal.sum_lt_top (~17-37 lemmas remaining of ~35-55; the algebraic heart banked). Per L32a-cover-cert +
  the phi334 single-pivot precedent. pp-r1-genM-2 on-call. On close → (3,3,4) hfin fully S2-free.
- **Both long poles' last pieces BUILDING:** l2-hprod-build (L2 hproducer 5-sub-lemma ∩-of-𝓝) + r1-matbox (R1 (3,3,4) 9-chart cover).
  Convergence: each R1 tide banks more + shrinks the gap (bedrock → residual-power → resolved-form → algebraic heart → now just the
  cover assembly). pp seats on-call; general hdiv + general lifts + D1 ahead.

**★ UPDATE-59 (2026-06-25) — L2 hproducer: germ/Taylor was a FALSE ALARM (A' pointwise); 5-sub-lemma decomp build-ready + commissioned. ★**
- **The 7th finding (germ/Taylor) is OVERTURNED** (pp-pin2-rearch + decorrelated Codex, `hproducer-decomp-cert.md` @03004ccb): the
  formaliser feared Π_J on a varying internal interface ⟹ unbanked germ/Taylor. FALSE — hS1' shows Π_J (Pπ) is a FIXED orthogonal
  OUTPUT-side permutation, so `∑deepestEFull²` and `Sreg` are the SAME residual N=∏A−B under two FIXED invertible reindexings
  (FACT2) ⟹ POINTWISE comparable (the BANKED fixed-map Frobenius machinery applies, no Taylor). The earlier 'failures' had
  colPerm'd the corner (the bug). A' pointwise ranked #1 (no restructure, no WLOG).
- **The "coupled 𝓝" is a clean finite-∩-of-nbhds: 5 build-ready sub-lemmas** — (i) deepestEFull_Sreg_comparable (A' pointwise) →
  (ii) eventually_P00_invertible → (iii) eventually_leak + (iv) eventually_core_comparable (wiring to the BUILT
  schur_core_germ_comparability) → (v) hproducer = hconj + U:=⋂(4 nbhds). Import circularity resolved (the (b)-atom → a NEW module
  GaugeChart.DeepestEFullSregComparability; the generic Frobenius lemma stays low-level).
- **l2-hprod-build LAUNCHED** (a2c823f3) — executes the 5-sub-lemma decomposition (soundness-critical: FACT2 on the deviation only,
  corner in the pivot convention). pp-pin2-rearch on-call (general-H pointwise / B WLOG fallback). On close → L=2 body COMPLETE
  (only the 2 vacuous-at-L2 interior remain) → the final wire → L2 gate.
- **R1 (3,3,4):** r1-frametransport (acb008b3) building the frame transport (the last (3,3,4) hfin piece; resolved-form banked).
- Both long poles' last pieces BUILDING on de-risked decompositions: l2-hprod-build (L2 body) + r1-frametransport (R1 (3,3,4) hfin).
  pp-r1-genM-2 on-call. General hdiv + general lifts + D1 ahead. (The germ/Taylor scare resolved: the design-before-build loop turned
  a feared multi-step development into a contained 5-lemma build.)

**★ UPDATE-58 (2026-06-25) — both long poles down to their HARD-CORE last piece; (3,3,4) hfin resolved-form BUILT; frame-transport tide launched. ★**
- **L2:** (b) restated equality→comparability @049e6efe (squeeze rewired sorry-free, public conclusion + PIN1 clean). 7th finding
  (build-effort refinement, not an obstruction): the comparability's PROOF is the unbanked germ/Taylor route (fderiv quad-form at
  w0 + isLittleO), and hproducer is a COUPLED 𝓝 construction (S5a∩S5b∩S5c+(b)) — beyond a contained tide. pp-pin2-rearch
  re-engaged to DECOMPOSE the coupled producer into build-ready sub-lemmas (`hproducer-decomp-cert`) + re-adjudicate A' (germ/Taylor)
  vs B (front-pivot WLOG, (b) exact). L2 hproducer build HELD pending the decomposition.
- **R1: (3,3,4) hfin resolved-form BUILT @5e7759b7** (r1-334cover, +393 LoC, S2-FREE): the KEYSTONE `resolved334_lt_top`
  (`∫(∑Tᵢ²+frobSq(Δ·S))^{−c'}<⊤` for 2<c'<4 — the additive threshold 4=2+2 COMPOSES) + the core finiteness (S-first transpose-fibre,
  avoiding the r≥3 Schur split) + `measurePreserving_matTranspose` + the {core=0} null set — all axiom-clean. **Open content shrank
  to the FRAME TRANSPORT alone** (the MP Schur-frame cover-up-to-null reducing flat `frobSq(A0·A1)` → the resolved form = the L3.2a
  cover for (3,3,4); ~8-15 lemmas, Codex-confirmed irreducible).
- **r1-frametransport LAUNCHED** (acb008b3) — closes the (3,3,4) frame transport per L32a-cover-cert, target `resolved334_lt_top`.
  pp-r1-genM-2 on-call. On close, routeMCore_M334_threshold_lt_top is fully S2-free.
- **Honest state:** both long poles' LAST pieces are now hard multi-lemma cores (L2 coupled germ-producer being decomposed; R1
  (3,3,4) frame transport building); everything around them (keystones, atoms, resolved-form, squeeze) is built. 7 soundness catches
  this session, all resolved soundly, all from review/decorrelated design, PIN1 verbatim throughout.
- Active: r1-frametransport (R1 build) + pp-pin2-rearch (L2 hproducer decomp). pp-r1-genM-2 on-call. General hdiv + general lifts + D1 ahead.

**★ UPDATE-57 (2026-06-25) — 6th catch RESOLVED: hproducer (b) → comparability (option A, contained); hproducer build resumed. ★**
- **hproducer (b) adjudicated @788c7fab — option A (comparability) is SOUND, the contained repair** (pp-pin2-rearch + decorrelated
  Codex; `r2-frontpivot-cert.md` + an exact PD certificate): the equality `∑deepestEFull²=Sreg` is false, but the COMPARABILITY
  `∑deepestEFull²≍Sreg` HOLDS — both energies vanish at w0 (`deepestEFull_base`) ⟹ PD Gram forms in the deviation, differing only
  by the invertible kernel-preserving reindex `π_J·QL` (generalized eigenvalues [0.52,1.93] ∋ the 0.76 witness — which refuted
  EQUALITY, not comparability). `deepest_loss_squeeze` ALREADY folds the two-sided shape (never needed the equality). **No headline
  restructure, no PIN1 touch, no WLOG.** Same kernel-preserving mechanism as S5c. (B front-pivot WLOG validated as fallback.)
- **l2-hprod-comp LAUNCHED** (ac67c116): restate (b) as `≍`, build `deepestEFull_sq_comparable_Sreg` (via `dlnLoss_two_sided_of_frame`,
  the structural invertible-reindex argument; SOUNDNESS-CRITICAL = read the corner off the shared `pivotThr.symm`), assemble
  hproducer (consume the built S5c atom; π_J cancellation no longer needed). pp-pin2-rearch on-call for general-H / B fallback.
- **L2 close back on track:** hproducer (this tide) → L=2 body done (only the 2 vacuous-at-L2 interior remain) → final wire
  (squeeze-exists + case-split, wiring hL2/hpos/hinterface) → L2 gate. The body's hard pieces (S5c atom, hS1', telescope) all banked.
- 2 builds in flight (independent files): l2-hprod-comp (L2 hproducer) + r1-334cover (R1 (3,3,4) cover). pp seats on-call. General hdiv held.

**★ UPDATE-56 (2026-06-25) — 6th L2 catch (the deepest): hproducer (b) FALSE for non-front pivot; the front-pivot-WLOG repair adjudicating. ★**
- **l2-hproducer landed — hproducer is NOT fillable as stated** (banked `hproducer-verdict.md` @06989e60). Conjunct (b)
  `∑deepestEFull²=Sreg` is FALSE for a non-front pivot J (the GENERIC headline case): deepestEFull threshold-effective (pivotThr J)
  vs Sreg pivot-aligned; π_J moves the −1 corner between blocks. Triply confirmed (index algebra + witness 17.98≠23.65 + 2 Codex).
  The formaliser refused to fabricate; PIN1 stays clean; the sorry honest. **This is the deepest L2 architecture catch — the
  gauge chart as built only closes for a front pivot.**
- **Controller decision (autonomous): the most-contained sound repair, being spec'd by pp-pin2-rearch (re-engaged):** (A) IF the
  COMPARABILITY `∑deepestEFull²≍Sreg` holds uniformly on a 𝓝 (the squeeze needs only `≍`, not `=`) → restate (b) as `≍`, no
  restructure; (B) ELSE R2 the front-pivot WLOG (`rlctAt(loss B)=rlctAt(loss B·π)` via `A_{L-1}→A_{L-1}·π` MP; front J'⟹(b) holds).
  Neither touches PIN1. **No math at risk** (RLCT invariant under the column perm / the comparability) — a gauge-chart-architecture
  correction. Item 21.
- **hproducer build HELD** pending pp-pin2-rearch's (A)/(B) verdict. The L2 gate is NOT "one piece away" until the (b) repair lands;
  then hproducer → L=2 body done → final wire → L2 gate. (The S5c atom + hS1' + the other body gaps remain closed/banked.)
- **R1 continues independently:** r1-334cover (the (3,3,4) frame-transport + cover-assembly) still building. R1 (3,3,4) hfin is
  on track; the keystones (residual-power, N1-N3b) banked.
- Active: r1-334cover (R1 build) + pp-pin2-rearch (L2 (b)-repair design). pp-r1-genM-2 on-call. General hdiv (det wall) held.
- 6 soundness catches this session — every one from review/decorrelated design, none from a green build; PIN1 verbatim throughout.

**★ UPDATE-55 (2026-06-25) — both long poles down to ONE "last piece" each; S5c atom + residual-power keystone BUILT; 4th+5th catches. ★**
- **L2: the S5c germ atom is BUILT** @bd37613c (`schur_core_germ_comparability`, axiom-clean, 0 sorries — the hardest standalone
  L2 piece) + hS1' closed. **4th L2 catch:** hproducer's (d)/(e) uniform-MULTIPLICATIVE comparability `∑Rcore²≍coreΦ` refuted
  for M>1 (Codex + a tilted-kernel germ counterexample) → RESTATED to the regular-energy-FOLDED form, `deepest_loss_squeeze`
  public conclusion preserved. L2 body now down to **hproducer** (1 binding gap; (d')/(e') reduce to the built atom + ∑E² charge)
  + 2 L≥3-interior (vacuous at L=2).
- **R1: the residual-power keystone is BUILT** @9909ab21 (`radial_morse_residual_power_le`, S2-free, 0 sorries) + the (3,3,4) N4
  (`routeMCore_M334_threshold_lt_top`, 1 cover sorry). **5th catch (a CONTROLLER-recipe error):** my N4 commission's `radial_morse`
  peel UNDERSHOT the additive `c'<4` by 2 — the tide+pp-r1-genM-2+Codex caught it + built the residual-power convolution. R1
  (3,3,4) hfin now down to **the frame-transport + cover-assembly** (1 gap; the atom+threshold+core algebra banked).
- **Both "last piece" tides launched:** l2-hproducer (a064b129, the final L2 body gap) + r1-334cover (af795d4e, the (3,3,4)
  frame-transport + recStep cover). Different files, parallel; pp-pin2-rearch + pp-r1-genM-2 on-call.
- **Cleanup item (20):** `minAdm_M4422` name duplicate (Case334RouteStep vs RouteM4422) — de-dup before the final aggregator wiring.
- L2 close path: hproducer → L=2 body done → final wire (squeeze-exists + case-split) → L2 gate. R1 (3,3,4): cover-assembly →
  (3,3,4) hfin done → general lift → R1 hfin; + general hdiv (the held det wall) → R1 gate. Then D1 → headline.
- 5 soundness catches this session (PIN2 false-eq · framedParams under-hyp · g156 false prose · germ-vs-box S5c · hproducer
  mult-comparability · radial_morse undershoot), PIN1 verbatim throughout — every catch from review, none from a green build.

**★ UPDATE-54 (2026-06-25) — R1 hfin ladder BEDROCK banked @bc877c6d (N1/N2a/N3a/N3b proved); N4 wall tide launched. ★**
- **RouteMSchur bedrock banked** (r1-ladder; standalone green-gate + #print axioms; SELF-reviewed — its own reviewer caught +
  it repaired an N2b vacuity, re-audit survived): N1 `radialDelta_loss_factor` (ring), N2a `rankOne_outerProduct_split` (the
  r=2 rank-1 leaf = the (3,3,4) terminal rank-drop), N3a `radial_aAxis_divisor_lt_top`, N3b `radial_loss_chart_lt_top` — all
  PROVED axiom-clean `[propext, Classical.choice, Quot.sound]`, no monomial_rlct. NEW file RouteMSchur.lean, NOT wired into the
  aggregator (2 sorries; wire when hfin closes). N2b statement REPAIRED non-vacuous (uniform c₀,c₁, complete-pivoting cell hyps).
- **2 R1 hfin gaps remain:** N2b (r≥3 block-Gauss proof — de-risked in minorpivot-cert, NOT needed at (3,3,4) where r=2) + N4
  `routeMCore_threshold_lt_top` (the assembly = the wall): the depth-r WellFounded cover + the (3,3,4) hfin CHART BUNDLE (the
  ParamsReshapeMP frame transport on the hfin side, not yet instantiated).
- **r1-n4 LAUNCHED** (a0435aec) — the (3,3,4) hfin: the chart bundle (routeMCore M334 → ‖T‖²⊕‖Δ·S‖²) + N4 depth-2 assembly,
  reusing the banked bedrock + recStep/radial_morse. pp-r1-genM-2 on-call. The (3,3,4) is r=2 (N2a leaf, no N2b-r≥3 needed).
- 2 builds in flight (independent files): l2-s5c-body (L2 body: S5c atom + hS1' + hproducer) + r1-n4 (R1 (3,3,4) hfin N4 wall).
  pp-pin2-rearch + pp-r1-genM-2 on-call. The other open R1 piece is general hdiv (RouteMLayerCoverGE:120, the det wall, HELD).

**★ UPDATE-53 (2026-06-25) — L2 framedParams body 5/8 gaps closed @b7916f4d; down to hS1'+hproducer at L=2; S5c-atom tide launched. ★**
- **l2-body-fill landed + integrated** (forced-rebuild + #print axioms; PIN1 stays clean; reviewer PASS 5/5): CLOSED sorry-free —
  hKP_pos/hKi_pos (from the strict `hpos:∀s,r<H s`), hinterface (explicit hyp, L=2-discharged), hS1 (non-last round-trip), hS2/
  hS3b (the axiom-clean witnessed `endpoint_telescoping_eq`; hS3b sound via the `w0` deepest-gauge instance). **Third L2
  soundness catch:** hS1' option-α REFUTED (the last layer carries a column-perm π_J for non-front J) — corrected to the permuted
  statement; hS2/hS3b re-architected onto the sound w0 form. Body sorryAx from the 4 remaining gaps only, no extra axiom.
- **L2 body remaining (4 correct-statement gaps):** hS1' (permuted last-layer) + hproducer (π_J cancellation + S4/S5a/b + **the
  unbuilt S5c germ atom**) — the two L=2-BINDING gaps. + 2 L≥3-interior-frame sorries VACUOUS at L=2 (Item 19; general-L only,
  need the DeepestPivotFrame identity-interior-frame choice). Signature: hL2/hpos/hinterface added (wire from headline).
- **l2-s5c-body LAUNCHED** (a2edef67) — S5c germ atom PRIMARY (new file DeepestSchurComparability.lean, per s5c-r2-cert: the
  matrix middle-factor `R=S0·W·S1`, germ bound `|∑‖R‖²−∑‖∏S‖²|≤C∑E²` — germ-scoped, NOT box), then hS1' + hproducer. The S5c
  atom was deferred by the prior body tide (the hard standalone piece) — now the explicit primary. pp-pin2-rearch on-call.
- **L2 close path:** S5c atom + hS1' + hproducer (this tide) → framedParams body done at L=2 → the final wire (squeeze-exists +
  case-split + import-arch relocation; wires hL2/hpos/hinterface from the headline) → the L2 gate.
- 2 builds in flight (independent files): l2-s5c-body (L2 body finish) + r1-ladder (R1 (3,3,4) hfin). pp-pin2-rearch + pp-r1-genM-2 on-call.

**★ UPDATE-52 (2026-06-25) — R1 hfin ladder DESIGN-COMPLETE end-to-end (general-r N2 de-risked); pp-r1-genM-2 released. ★**
- **General-lift N2 de-risked + banked @d57e9247** (pp-r1-genM-2 + decorrelated Codex; `minorpivot-cert.md`): the nested
  minor-pivot cover = `argmaxCellOn`/`Finset.exists_max_image` at the MINOR level (active = j×j minor-index pairs, coord =
  det∘submatrix; no "rank=max-minor" theorem needed). **The sharpest risk — det M11→0 — is CLOSED EXACTLY:** the shear
  M21·M11⁻¹ entries are Cramer minor-ratios ≤ 1 by complete-pivoting (the argmax pivot), symbolic to (4,3) — no blow-up, no
  cell subdivision. 4 refinements amending spec L2.2: **R1 comparison-not-equality** (`c0·D ≤ ‖R·S‖² ≤ c1·D`, the row-op is
  non-orthogonal — RELAYED to r1-ladder; its (3,3,4)/r=2 equality instance unaffected) · R2 the Cramer edge · R3 deterministic
  tie-break (disjointness without the null-set proof) · R4 per-level re-pinning (termination, depth ≤ r). Mathlib bridge
  verified (cramer_apply/mul_adjugate/inv_def, v4.29). Build-risk = N2a/N2b index-permutation bookkeeping (Lean-cost, not math).
- **pp-r1-genM-2 RELEASED** — R1 design arc comprehensively complete (route distinction → L3.2a cover = existing infra →
  minor-pivot general de-risk). On-call only for an r≥3 N2 build math-snag.
- **R1 hfin is now design-complete end-to-end** — the whole ladder (cover + Jacobian + integrand + minor-pivot + Schur +
  termination + threshold λ=½·minAdm) is build-ready; remaining is FORMALISATION (r1-ladder building (3,3,4); then the general
  lift, fully spec'd ahead). The other open R1 piece is general **hdiv** (RouteMLayerCoverGE:120, the (3,3,3,3) Frame-det
  Lean-cost wall — needs a det-tactic formaliser tide, HELD for focused bandwidth).
- Active: l2-body-fill (L2 framedParams body) + r1-ladder (R1 (3,3,4) hfin). pp-pin2-rearch + pp-r1-genM-2 on-call.

**★ UPDATE-51 (2026-06-25) — the R1 hfin wall (L3.2a) DE-RISKED + the (3,3,4) ladder build commissioned. ★**
- **L3.2a cover DE-RISKED, banked @8161f79e** (pp-r1-genM-2 + decorrelated Codex): the r²-chart Δ-blow-up cover CLOSES up to
  null at general r and **IS the existing `argmaxCellOn`/`pivotBlowupOn` machinery** at the r² Δ-entry level — no new cover
  geometry (Jacobian |a|^{r²−1}; integrand G∘φ=a²·‖R·S‖² by ring; threshold MIN(r²/2, inner); λ_{r,p}=½·minAdm, 10/10). The HIGH
  build-risk #1 is downgraded to "reuse existing infra + 4 targets." **Codex soundness refinement:** the rank recursion is a
  nested minor-pivot OPEN-neighbourhood cover (NOT measure-zero exact strata, illegal as integration domains); the Schur
  complement carries corank-(r−j) via `det R = det M11·Sc`. 4 new targets: N1 (ring) / N2 minor-pivot (MED, r=2 ring-clean,
  r≥3 block-Gauss) / N3 (MED) / N4 assembly (HIGH).
- **r1-ladder LAUNCHED** (a56bbdeb) — the (3,3,4) depth-2 hfin ladder (N1–N4, ring-clean, the direct lift of
  myF222_threshold_lt_top'), reusing the existing cover infra verbatim. Validates the general machinery at minimal corank;
  general-r is the follow-on. pp-r1-genM-2 on the general minor-pivot follow-up (de-risk N2 at r≥3) for the lift.
- **R1 status:** hfin upper — (4,4,2,2) banked S2-free; general via the now-de-risked ladder ((3,3,4) building). hdiv lower —
  general still open (RouteMLayerCoverGE:120, the (3,3,3,3) Frame-det wall). S2-free conclusion throughout.
- 2 builds + 1 design in flight (independent files): l2-body-fill (L2 framedParams body) + r1-ladder (R1 (3,3,4) hfin) +
  pp-r1-genM-2 (R1 general minor-pivot). pp-pin2-rearch on-call.

**★ UPDATE-50 (2026-06-25) — (4,4,2,2) hfin closed S2-FREE @902ce5a7; R1 route distinction settled; the L3.2a wall is the R1 binding constraint. ★**
- **(4,4,2,2) hfin CLOSED, S2-FREE** (r1-hfin; reviewer PASS; `#print axioms = [propext, Classical.choice, Quot.sound]`, no
  monomial_rlct, no sorryAx): `routeMCore_M4422_threshold_lt_top` — the depth-2 template + a reusable reshape API
  (paramsEquivFlat_decode, measurePreserving_eParams4422). L1.1 (radial-morse) confirmed already-banked. NOTE: discharges the
  (4,4,2,2) INSTANCE only, not `routeMLayerCover_of_atoms`'s general-M hfin field.
- **DECISIVE R1 route distinction (settled):** the iterated-fibre route is SPECIAL-CLASS only — `best_iterfibre(M) < ½·minAdm M`
  for ALL corank-≥2 binding M (incl. (3,3,4),(3,3,3),(4,4,4),(3,3,3,3), even (2,2,2)). So general-M hfin REQUIRES the
  rank-stratified {V=0} ladder (spec L2.1/L2.2/L3.x). The (4,4,2,2) win does NOT generalize — it's the MATCH-class template.
- **pp-r1-genM-2 ENGAGED on the wall (L3.2a):** the r²-chart Δ-blow-up cover up to null at general r (spec build-risk #1, HIGH).
  De-risk the binding constraint BEFORE the big ladder build → then commission the full ladder (L2.1→L2.2→L3.2→L3.1) with the
  cover design in hand. Output: thread 28 `L32a-cover-cert.md`, anchored on (3,3,4). Ladder formaliser build HELD pending it.
- **R1 remaining (honest, the largest chunk left):** TWO open general pieces — (a) general **hfin** (the rank-stratified ladder,
  wall = L3.2a, in design) + (b) general **hdiv** (`routeMCore_box_diverges_achiever`, RouteMLayerCoverGE:120 — the (3,3,3,3)
  Frame-det elaboration-cost wall, still open). Bears on the operator scope decision (full general-L vs the L=2/RRR milestone).
- Active: l2-body-fill (L2 framedParams body) + pp-r1-genM-2 (R1 L3.2a design). pp-pin2-rearch on-call.

**UPDATE-49 (2026-06-25) — framedParams body: statement CORRECTED (soundness catch) + skeleton banked @06385657; body-completion + R1 in flight.**
- **l2-body landed + integrated** — another soundness catch (same discipline as PIN2): `framedParams_split_eq_frame_raw` was
  UNDER-HYPOTHESIZED (false as stated — bare Pf,Qf,J don't make P0 a unit / P00 invertible / the corner normalize). FIXED by
  adding the 7 frame hypotheses (= the `deepestPoint_frame_pivot_exists` bundle), threaded through the caller (which discharges
  them). The inverse-frame assembly + the producer-determined t,γ are FILLED + banked. PIN1 stays clean; no monomial_rlct.
- **HONEST REASSESSMENT (the L2 gate is further than "one body sorry"):** the body decomposes into **8 named correct-statement
  internal gaps** (hS1/hS1' round-trip · hinterface · hS2 telescope · hS3b B-normalize · hKP_pos/hKi_pos positivity · hproducer
  = S4 reg-energy + S5a/b + the S5c germ atom). All design-complete (framedbody-cert + s5c certs) + most have banked anchors
  (reindex_fromBlocks_reads_eq_deviation, endpoint_telescoping, deepestPoint_interior_frame_id, prod(deepest)=B). The hardest
  (hproducer) needs BUILDING the S5c germ atom `schur_core_germ_comparability` (the matrix middle-factor `R=S0·W·S1`, W→I + the
  germ bound) — genuinely-new geometry, not yet in Lean. Latent: hKP_pos needs H s≥1 (derivable from the strict r<H s).
- **l2-body-fill LAUNCHED** (aef4bc35) — fills the 8 gaps + builds the S5c atom, off the certs; pp-pin2-rearch on-call for the
  S5c germ geometry. Edits DeepestGaugeConstruction (+ maybe a helper) — different file from r1-hfin.
- **2 builds in flight (independent files):** l2-body-fill (framedParams body) + r1-hfin (the R1 hfin long pole). pp-pin2-rearch
  + pp-r1-genM on-call. After the body closes: the final L2 wire (squeeze-exists + case-split + the import-arch relocation).

**★ UPDATE-48 (2026-06-25) — assembler gap CLOSED @2a0e6bd9; the L2 gauge chart is down to ONE geometric sorry; R1 hfin in flight. ★**
- **l2-pi-assembler landed + integrated** (forced-rebuild + `#print axioms` re-verified): `hasStrictFDerivAt_schurShiftRaw_zero`
  sorry-free + axiom-clean via Route (b) (the paramsEquivFlat flat-decode — Route (a)'s Params-Pi `pi'` confirmed walled by a
  Mathlib-v4.29 whnf timeout). **`deepest_gauge_construction`'s sorryAx now traces to ONLY the framedParams body (1491)** — the
  single piece l2-body is building. No new axiom, no monomial_rlct.
- **R1 hfin tide LAUNCHED** (r1-hfin, ad9b74f1) — off the build-ready thread-28 `spec.md` (3 lemma families L1.1/L2.1/L2.2 +
  recursion carrier L3.1/L3.2, dependency order, S2-FREE conclusion). Validate-small-first: inventory the banked L1.1
  (radial-morse, S1RadialMorse) + the (4,4,2,2) instance, then L2.1/L2.2 + the (3,3,4) corank-2 anchor. pp-r1-genM on-call for
  the HIGH-risk r²-chart Δ-blow-up cover (L3.2a). The hfin conclusion is S2-FREE — `#print axioms` stays within
  `[propext, Classical.choice, Quot.sound, monomial_rlct]`, no new axiom.
- **L2 remaining = the body (l2-body building) + the final wire** (squeeze-exists + L=1/2≤L case-split + product_reduction;
  needs the import-arch relocation of `deepest_gauge_squeeze_exists` downstream — same file as l2-body, serialized after it).
- 3 builds in flight (independent files): l2-body (framedParams body) + r1-hfin (the R1 long pole). pp-pin2-rearch released;
  pp-r1-genM on-call.

**★ UPDATE-47 (2026-06-25) — hTilde INTEGRATED @4a02398a; the parallel L2 build push is launched. ★**
- **hTilde landed + integrated** (l2-htilde; forced-rebuild green-gate + `#print axioms` re-verified): sorry-free chain-rule
  wire in `deepest_gauge_construction` (PIN1's D_E + `D(coreAbsorb.symm)(0)=id` + `regStraightenOf2_gen`) + a NEW 437-LoC
  axiom-clean `DeepestSchurSmooth.lean` (the global ContDiff⊤ ladder for the cutoff Schur shift — the brief's "coreAbsorb.symm
  is a CLE" premise was wrong; it's a homeo with `(1+X)⁻¹` poles + a ContDiffBump cutoff, and the consumer demands GLOBAL
  smoothness). PIN1 stays `[propext, Classical.choice, Quot.sound]`. ONE new narrow correct-statement gap
  (`hasStrictFDerivAt_schurShiftRaw_zero`, DeepestSchurSmooth:365 — the Params-Pi assembler; value 0 proved per-entry).
- **Parallel L2 push launched (independent files):** **l2-body** (a4bf381d) — the framedParams body (DeepestGaugeConstruction
  ~1491), design-complete via framedbody-cert + s5c-cert + s5c-r2-cert (germ form, feed global R not ∏S, readX/Y/Z banked).
  **l2-pi-assembler** (a0a89c1a) — the DeepestSchurSmooth:365 Params-Pi gap (assembler or paramsEquivFlat decode). Different
  files → no clobber at integration.
- **R1 hfin DEFERRED (not rushed):** it's the single HARDEST remaining build (the corank-≥2 binding `‖Δ·S‖²` coupled `diag(b)`
  resolution + {V=0} recursion — "the largest remaining R1 build", thread-27 statement-card). I do NOT have the #54 build-ready
  lemma spec crisply located, so launching now would be a low-quality rush. NEXT focused action: locate + digest the #54
  build-ready lemmas → crisp commission ((3,3,4) anchor via {V=0} recursion + the done (2,2,2) `myF222_threshold_lt_top'`
  recStep template; pp-r1-genM on-call for the corank-≥2 coupled-chart step). The forbidden Aoyagi cite is the only shortcut;
  the recursive coupled cover is the from-scratch path.
- **Final L2 assembly (after l2-body lands):** the squeeze-exists + case-split (L=1 base / 2≤L gauge arm) + product_reduction —
  needs an import-arch decision (DeepestGaugeChart imports the construction circularly → relocate `deepest_gauge_squeeze_exists`
  downstream). Same file as l2-body, so serialized after it.
- Active: l2-body + l2-pi-assembler (builds). pp-pin2-rearch released/on-call. pp-r1-genM on-call (R1 hfin, spec-locate next).

**★ UPDATE-46 (2026-06-25) — S5c FULLY CLOSED; the framedParams-body design is complete; L2 is now BUILD-bound. ★**
- **S5c fully closed** (r≥2 matrix-PIVOT LDU confirmed): `R = S0·W·S1·…`, `W = I − Z₁A⁻¹Y₀ → I`, germ orders survive with a
  matrix pivot (X-linear term absorbed by the pivot block, not the off-diagonal). Both orthogonal generalizations done
  (matrix core M=2 + matrix pivot r=2); the LDU is uniform in r,M,L. Germ atom `schur_core_germ_comparability` unchanged.
- **The entire framedParams-body decomposition (S0–S5) is now adjudicated + build-ready** — framedbody-cert (S0–S5 + S1'
  pre-derivation + the S3b `hcorner`-about-`deepestPoint` resolution) + s5c-cert + s5c-r2-cert, with the readX/Y/Z decode
  ALREADY BANKED and the germ-not-box scoping pinned. No open design gaps.
- **pp-pin2-rearch RELEASED** — its PIN2/framedbody design arc is comprehensively complete (transfer → framedbody → s5c →
  s5c-r2 → matrix-pivot confirm; the germ-vs-box catch + readX/Y/Z-banked de-risk along the way). On-call for a body-build
  design snag or the later r≥2 R1 work.
- **L2 is now BUILD-bound, not design-bound.** Two remaining builds:
  1. **l2-htilde** (in flight): hTilde → `deepest_gauge_squeeze_exists`.
  2. **framedParams-body formaliser tide** (UNBLOCKED, HELD): edits `DeepestGaugeConstruction.lean` — the SAME file as
     l2-htilde's hTilde. SERIALIZED to avoid a copy-integration clobber: commission off l2-htilde's integrated HEAD.
  then the L=1/2≤L case-split wire + `product_reduction` → the L2 gate.
- **R1 parallelization plan (deliberate sequencing decision):** R1 hfin build (the other long pole, design-closed, #54 spec in
  thread 27 — Vzero-termination + iterfibre + statement-card) is HELD this tick to keep focus on the L2 close. PLAN: launch it
  in parallel WHEN the body tide launches (independent files — RouteM*/ResolutionAtlas vs Deepest* — so no conflict; the body
  tide is a long build during which R1 fills parallel capacity), pp-r1-genM on-call for the HIGH-risk r²-chart step. Not now:
  the hardest build deserves focused integration attention, and the critical path to the headline runs through L2→D1 first.
- Active: l2-htilde (build). pp-pin2-rearch released. pp-r1-genM on-call (R1, held → next to launch).

**UPDATE-45 (2026-06-25) — S5c matrix-core: TRUE but GERM-scoped (box bound would be unsound); last residual dispatched.**
- pp-pin2-rearch + Codex closed the r≥2 matrix-core S5c (`s5c-r2-cert.md`): exact middle-factor `R = S0·W·S1·…`,
  `W_s = I − Z_{s+1}A⁻¹Y_s → I` at the deepest point. **Codex caught a real confound the first MC missed:** the two-sided BOX
  ratio `∑‖R‖² ≍ ∑‖∏S‖²` is FALSE for M>1 off-germ (rank-deficient `S0=εE12,S1=εE21` ⇒ R=0≠∏S — the rank-≤1 W gives no rank
  protection). But on a true germ `R−∏S=O(ε⁴)` vs `∏S=O(ε²)`, so the in-sum germ bound `|∑‖R‖²−∑‖∏S‖²| ≤ C·∑E²` HOLDS — and
  `rlctAt` is a germ invariant, so the germ form is the right + only safe scope. **The build atom MUST be the germ form, not a
  box bound.** g156 docstring refined to the matrix middle-factor + germ scope; Item 18 updated.
- **Last S5c residual dispatched:** the r≥2 matrix-PIVOT (a_s an r×r block) LDU symbolic confirm (pp-pin2-rearch). On confirm →
  S5c fully closed → commission the framedParams-body formaliser tide (using framedbody-cert + s5c-cert + s5c-r2-cert, germ form).
- Drives: l2-htilde (hTilde→squeeze-exists build) + pp-pin2-rearch (r≥2 matrix-pivot confirm). pp-r1-genM on-call (R1, held).

**UPDATE-44 (2026-06-25) — S5c adjudicated (unit-rescaling, NOT ideal); g156 false prose corrected; r≥2 gap flagged+dispatched.**
- **framedbody-cert (pp-pin2-rearch) staged + banked** — the `framedParams_split_eq_frame_raw` body S0–S5 decomposition. KEY
  de-risk: the docstring's "genuine bulk" (readX/Y/Z→raw decode) is ALREADY BANKED (`reindex_fromBlocks_reads_eq_deviation`).
  Decorrelated Codex reordered the residual risk onto S5c + S5b (not S1').
- **S5c adjudicated — WITNESS (clean), banked (`s5c-cert.md`):** the core identification is an EXACT unit-rescaling
  `R = u·∏S_s`, `u = ∏(1+X_s)/P00` a bounded unit (→1 at the deepest point) ⟹ standalone comparability `∑R² ≍ ∑(∏S)² =
  deepestCoreF(coreAbsorb)`, NO ∑E² charge. **A FALSE prose claim was found + corrected:** g156's `fullProduct_core_split`
  docstring asserted `R−∏S ∈ ideal(E)` — Gröbner-FALSE (`−Y1·Z0 ≠ 0`); the theorem+proof were always sound (used only
  `frobenius_fromBlocks`+`schur_P11_decomp`), the false claim lived only in prose. Corrected (Item 17). **Load-bearing
  build-ordering:** feed `core_comparability_squeeze` the GLOBAL `R`, not `∏S` (else the leak `R−∏S` is not E-controllable).
- **r≥2 / matrix-core S5c is the last named open L2 dependency:** exact for r=1 all L, but only MC-supported for M>1 (the
  scalar `u` becomes a bounded invertible similarity) — and the headline NEEDS the matrix case (Item 18). DISPATCHED to
  pp-pin2-rearch (witness/obstruction, `s5c-r2-cert.md`; likely a singular-value sandwich via the matrix Schur-of-product
  identity). NOT deferred.
- **L2 status:** PIN2 integrated+green+axiom-clean @bcfb8b60. framedbody design complete for r=1 (S5c done); r≥2 in flight.
  Near-term build: l2-htilde (hTilde→squeeze-exists). Then the body formaliser tide (using framedbody-cert + s5c-cert[+r2])
  + the case-split wire + product_reduction → the L2 gate.
- Drives: l2-htilde (build) + pp-pin2-rearch (r≥2 S5c design). pp-r1-genM on-call (R1, held).

**★ UPDATE-43 (2026-06-25) — L2 PIN2 full-reg repair INTEGRATED + green-gated + axiom-verified @bcfb8b60. ★**
- **l2-pin2-fullreg landed; I integrated it into main** (forced-rebuild green-gate + `#print axioms` re-verified MYSELF, not just
  trusting the report): the false `h00/h01/h10` (T=0 block-equalities) are DELETED, replaced by the TRUE reg-energy identity
  `∑(deepestEFull (split w))² = Sreg` (what `dlnLoss_two_sided_of_frame` consumes — no over-count). `deepest_loss_squeeze` +
  `deepest_regAbsorb_exists` bodies sorry-free. New infra all axiom-clean `[propext, Classical.choice, Quot.sound]`:
  `regStraightenOf2`/`regStraightenTotalCLM2_equiv_of_regBlock_isUnit` (the transfer = simplification of the banked `_isUnit`,
  `W:=C×S` unsplit) + `rlctAtOn_regAbsorb_reduce2` + `deepestEFull`/`_coreZero`/`_deriv`. **PIN1 re-used VERBATIM, axiom-clean.**
  `deepest_loss_squeeze`'s only `sorryAx` is inherited from the cert body — **NO `monomial_rlct`** (the squeeze does not smuggle
  the S2 cite). Independent reviewer SURVIVED all 4 contract points. Deepest* subtree still OUT of the aggregator (controller-gated).
- **The open rlct-risk gamble is CLOSED:** the squeeze now rests on the BANKED leaf lemma's TRUE comparability, not an unverified
  `rlct(Φ_struct)=rlct(dlnLoss)`. The PIN2 false-statement → sound-repair arc is complete.
- **L2 gate's remaining transitive sorries (all CORRECT-statement) + who's driving:**
  1. `hTilde` (DeepestGaugeConstruction ~1883): the `∂deepestEFull/∂core(0)=0` local-diffeo atom — LARGELY DERIVABLE from the
     proved `deepestEFull_deriv` (`D(deepestEFull)(0)=[F|0|G]`, core-column 0) + chain rule + `regStraightenTotalCLM2_equiv`. →
     **l2-htilde** (formaliser, worktree, ad7f46ec) + then `deepest_gauge_squeeze_exists` (DeepestGaugeChart:361, "one assembly").
  2. `framedParams_split_eq_frame_raw` body (~1490, ~200-300 LoC geometric cert: round-trip + telescoping + pivot-frame + core
     comparability) → **pp-pin2-rearch** re-engaged to structure the build-ready cert (thread 31 `framedbody-cert.md`).
  3. then the L=1/2≤L case-split wire + `product_reduction` (Skeleton) → the L2 gate.
- 2 background drives: l2-htilde (build) + pp-pin2-rearch (design). pp-r1-genM on-call (R1, held).

**UPDATE-42 (2026-06-25) — tick: housekeeping banked + goal-distance glance (on-path, healthy).**
- **Banked @5ecff7ca:** pp-pin2-rearch's PIN2 `transfer-cert.md` (thread 31 — the regStraightenTotalCLM transfer is a
  SIMPLIFICATION of the banked `_isUnit`, `W:=C×S` unsplit; relayed to l2-pin2-fullreg) + thread 27's iterfibre ceiling
  refinement + discuss-at-close Items 15 (PIN2 resolved: full-reg supersedes Item-14 comparability) & 16 (the stray
  cross-expedition `2026-06-23-fibre-codim/` dir — left untracked, flagged for operator homing, NOT banked here) +
  gitignored `**/.codex-consult/` scratch.
- **Goal-distance glance (`scripts/sorries`):** 6 RLCT files carry real sorries — Skeleton (the named gates L2:1131 /
  R1:1234 / D1 / headline), DeepestGaugeChart + DeepestGaugeConstruction (L2 PIN2, actively building), RouteM4422Hfin +
  RouteMLayerCoverGE + RouteMRecursion (R1 hdiv/hfin, build-held). EVERY live sorry-bearing file is on the critical path to
  a named gate — no orphan off-path file. Trajectory downward: the PIN2 repair closes the DeepestGauge* sorries + the
  Skeleton L2 sorry. (DeepestBaseL1 + RRR.lean are sorry-FREE; earlier raw-grep hits were "sorry-free"/"-conditional" prose.)
- 1 background BUILD agent: l2-pin2-fullreg (PIN2 full-reg repair). pp-pin2-rearch idle-on-standby (cert staged+relayed;
  not re-messaged — idle pings are auto-emitted substrate events). pp-r1-genM on-call (R1, held).

**★ UPDATE-41 (2026-06-25) — PIN1 gate GREEN (survives verbatim); the PIN2 full-reg repair is build-ready + COMMISSIONED.**
- **PIN1-survival adjudication GREEN (pp-pin2-rearch, exact + decorrelated Codex):** PIN1 `deepestEPivot_regSlice_fderiv`
  survives the T=0→full-product `regStraighten` swap VERBATIM. The leak `E_full − E_zero = (0, Y0·T1, T0·Z1)` is purely
  degree-2 ⟹ `D(E_full)(0) = [F | 0 | G]` (reg-in F = the SAME invertible regBlockCLE; core-in 0; spec-in G). PIN1 RE-USED
  as-is via the 1-line bridge `E_full(·,0,0) = deepestEPivot(·,0)`. The contained fix: `regStraighten`'s reg OUTPUT reads
  the core (`E_pivot:R×S→R` → `E_full:R×(C×S)→R`); the corrected chart deriv at 0 is block-triangular `[[F,0,G],[0,I,0],
  [0,0,I]]`, det = det F ≠ 0 — still invertible (the IFT peel input intact); `∑(regStraighten).1² = Sreg` exactly. **This
  ALSO closes the open rlct-risk gamble** — the squeeze is now the BANKED leaf lemma `dlnLoss_two_sided_of_frame`'s TRUE
  comparability `dlnLoss ≍ Sreg+Score`, so the headline rlct no longer rests on an unverified `rlct(Φ_struct)=rlct(dlnLoss)`.
- **`l2-pin2-fullreg` (a93075b4) COMMISSIONED** — the 4-file repair (per thread 31 restatement-spec.md): generalize
  regStraightenOf/regStraightenTotalCLM to (reg,core,spec)→reg + delete the T=0 h00/h01/h10/hSreg_eq/deepestEPivot_sq_sum +
  define E_full + re-aim deepestEPivot_deriv via PIN1 (verbatim) + the bridge + the ∂E_full/∂core(0)=0 atom + re-prove
  loss_squeeze via the leaf lemma. RE-USES PIN1's F + the leaf lemma. Flagged risk: the regStraightenTotalCLM generalization
  transfer (the shear invertibility) — pp-pin2-rearch on-call for it.
- **pp-pin2-rearch RELEASED** — its PIN2 design arc is comprehensively complete (refuted my option-2 lean → the full-reg
  repair → PIN1-survival → the build-ready 4-file spec). On-call for the regStraightenTotalCLM transfer.
- **L2 status:** PIN1 closed + survives the repair · L=1 base banked · PIN2 route-step bedrock banked · the full-reg repair
  building → closes PIN2 → then the case-split wire + product_reduction → the L2 gate. The MATH is sound (the leaf-lemma
  comparability); the false T=0 squeeze is being replaced by the true full-reg one.
- 1 background BUILD agent: l2-pin2-fullreg (the PIN2 full-reg repair). pp-pin2-rearch + pp-r1-genM on-call.

## Prior read (2026-06-22): ★ DESIGN CLOSED (g132→g153) — general-M λ on three concurrent Lean grinds ★

**★ LATEST (2026-06-22, cont'd) — #64 fix-route RESOLVED (e); R1 skeleton GREEN, routeStep delegated; #66 closed.**
- **#64 (e), confirmed-composing (cobuild-sub34 + Codex).** The MP split (`deepestSplit_exists`) delivers RAW
  slots; its reg slot `(split w).1` is a coordinate PROJECTION, NOT the nonlinear gauge residual E ⟹
  `loss_squeeze` over it is FALSE (the "green ≠ right" trap — a lemma that proves the wrong thing for its
  use-site). FIX (e): KEEP the MP split (raw slots) + add `regAbsorb` (non-MP self-map of the split codomain,
  raw-reg → E = ∏C−D residuals, the regular analog of `coreAbsorb`) + `coreAbsorb` (Schur, raw-core →
  dlnLoss M 0). Then Φ = ∑(regAbsorb(split w).reg)² + coreF(coreAbsorb(split w).core) = G' ∘ split FACTORS
  through the MP split ⟹ sub-6 (`rlctAtOn_comp_homeomorph split split_mp`) is UNCHANGED, and the two
  unit-Jacobians peel separately via `weightedThreshold_weight_unit_invariant`. DIVISION: crux2 = MP split +
  `regAbsorb` field/`regAbsorb_rlct` (paralleling coreAbsorb) + the SLOT-GROUPING contract (a NAMED obligation:
  reg slot = raw gauge pivots, core slot = raw T — NOT an arbitrary relabel; the absorptions' clean-shear /
  unit-Jacobian structure depends on it). cobuild-sub34 = regAbsorb + the two peels + loss_squeeze
  (`core_comparability_squeeze`) + assembly. **This SUPERSEDES item 3's "split = the heavy long-pole crux2
  owns": the split is MP-fine; the open work is the regAbsorb addition + the two peels.** (Ledger correction:
  my earlier "split (i) DONE" bank was PREMATURE — MP-correct but didn't compose; the reg-slot→E reconciliation
  was the genuine hard core, now closed by (e).)
- **R1 #39 skeleton GREEN (fm3) + #66 closed (crux2).** crux2 resolved the seam: fm3 CONSTRUCTS the per-node
  dispatcher; ChainDimSplit = consumed carrier (crux2's straighten did NOT generalize to all C-cases; consumer
  recipe given). fm3 built the WHOLE recursion shape green (single sorry): `RouteStep M := leaf | branch (cells)
  (split : cells → ChainDimSplit M) (codim)` + `routeAtlas = WellFounded.fix chainRel_wf` +
  routeMIota/Fintype/routeD/K/H — the rebase onto ChainDimSplit validated END-TO-END, parallel RouteState
  DELETED, ΣM-termination = crux2's `sum_red_lt`. hMid all-s re-threaded into `resolution_charts` (@0cedc7e,
  endpoint M_0/M_L=0 fidelity, NOT vacuous at L=1).
- **The ONE R1 open core = routeStep, DELEGATED (#68, pp2).** The rank-pattern → leaf/branch + pivot-cell
  Finset + per-cell (drop,red) ChainDimSplit + codim dispatcher. NO banked split precedent — even (2,2,2)
  (Case222Resolution.lean) is hand-built coordinate maps, NOT a ChainDimSplit (fm3 g160) ⟹ from-scratch
  combinatorics whose CORRECTNESS a green build can't catch (any RouteStep value fills the sorry — #64
  green-≠-right, now on R1's combinatorial core). pp2 designs the cert (generalizing (2,2,2) + one more case;
  3 correctness obligations: cover + ⨅-min achieves aoyagiLambda CONSISTENT-with-fm3's-foldDivisors-achiever +
  codim accumulates to C), fm3 transcribes + firms the interface meanwhile. Decorrelated Codex (the green-≠-right
  risk). It's the formal version of pp2's own #26 Route-M blueprint.
- **VACUITY TRAP (fm3 + Codex) → CERTIFIED RouteStep.** The bare RouteStep type is too weak: an arbitrary split
  type-checks but is disconnected from dlnLoss M 0, so rlctAtOn = ⨅ monomialThreshold is UNPROVABLE — a vacuous
  fill is strictly worse than the sorry. Fix: routeStep produces a CERTIFIED RouteStep (per cell: a transport
  datum proving the split factorises the loss + cover fact + node-loss-id). Three-way co-design: pp2 (recipe) +
  crux2 (transport-datum interface) + fm3 (certified type + generic fold guardrail certified-steps ⟹ rlctAtOn=⨅).
- **pp2 #68 CERT LANDED (origin/g183-routestep-dispatcher @1ac5de4).** Confirms fm3's g164 (per-node op = MONOMIAL
  MIN-FOLD, codims = Mval). Refinements: §1.1 LEAF = IsUnit residualCore; §2 the C1-condition codim = Mval M T for
  admissible T (NOT raw cardinality — the (4,3,2) trap); §4 C=∃ reachability; §6 the ValidRouteStep field list.
  fm3 machine-checked the §2 value-side discharge (@dd6bdb5: minAdm_le_Mval_toNat + foldFamily_threshold_ge_of_admWitness,
  green clean-three). VALUE-SIDE COMPLETE + fork-independent (achiever + threshold_ge + the consistency-by-
  CONSTRUCTION contract: design codims so (a) no path undershoots m₀, (b) min-Mval path binding codim = m₀ ⟹
  IsResolutionAtlas ⟹ ⨅ = lambdaCore, NO separate consistency proof — fm3's foldFamily lemmas).
- **MONOMIAL-MIN-FOLD vs ADDITIVE (current lean, PENDING crux2's confirm).** fm3 g164 + pp2 §3(1) + (2,2,2)
  numerics (min(2,3/2)=3/2=lambdaCore) ⟹ R1's per-cell consequence is the MONOMIAL PULLBACK (x_p²·reduced, G2
  node_loss_pivot_factor) folded by MIN, with rlctAtOn_reduced_transport (det=1) between steps — NOT the additive
  schur_recursion_step_sound (= L2's nReg/2 split OR the g134-retracted squeeze lane). So the per-cell datum is
  LIGHTER than the heavy IsSchurStraightenSqueeze (pp2's cert §0 listed both; §3(1) is the live one). DISENTANGLE:
  L2 peels nReg/2 additively ONCE; R1 resolves the core by monomial min-fold. **R1's entire long-pole has
  COLLAPSED to ONE gate: crux2's transport-field confirm** (heavy vs lighter) → fm3 pins ValidRouteStep + builds
  the fold + transcribes. I lean lighter; crux2 has ground-truth, adjudication in flight.
- **hGne CARVE-OUT — DECISION (A) all-s, consistent across rungs.** crux2's refined find: the headline is TRUE at
  the degenerate cases (lambdaCore = 0 for any M_s=0, endpoint OR interior); only the PROOF route
  (rlct_additive_smooth_block needs G≢0) breaks. (A) widen-to-all-s (∀ s, r<H_s) vs (B) interior-only + degenerate
  branch [keeps r=min]. DECIDED (A): the headline scope = INTERSECTION of rung scopes, and R1 is ALREADY all-s
  (fm3 @0cedc7e) ⟹ R1 CAPS the headline at all-s regardless of L2, so (B)'s extra generality (r=min) is WASTED at
  the headline unless R1 also handles the degenerate node (loads the R1 long-pole for a boundary value whose flat-
  core rlctAtOn(const 0)=0 convention is only "plausibly correct", unverified). r = min_s H_s is a NAMED honest
  carve-out (refines paper's r≤min(d⃗); flagged "formula plausibly extends but proof route degenerates + convention
  unverified — deferred"). (B)/r=min is a tracked generality extension needing R1+L2 BOTH — defer as one unit.
- **hMid⟹hGne BRIDGE — MUST BE BUILT (hero=all-proven), split + (b) DISPATCHED.** (a) prod_M ≢ 0 as a polynomial
  when all M_s≥1 — DLN-specific, crux2's. (b) the GENERAL lemma "nonzero MvPolynomial over ℝ ⟹ zero set Lebesgue-
  null (≈ ae-ne-zero)" — decoupled, the heavy ~150-250 LoC piece, DISPATCHED to a fresh lean-formaliser (worktree-
  isolated, background): searches Mathlib first, else builds Fubini-to-1D + 1D IsolatedZeros by #vars induction.
  crux2 threads (A)'s L2 skeleton with hGne as a named obligation + does (a) + pins the (b)-interface (the scalar-
  entry form). NOT roadmapped-as-unproven — provable, not a 2nd citation.
- **HEADLINE FIDELITY AUDIT (background reviewer).** Decorrelated audit of the most load-bearing STABLE claim:
  aoyagi_learning_coefficient — non-circularity of aoyagiLambda (= paper's C/2, not the rlct tautologically),
  the ⨅-keying over optimalSet, loss fidelity, the hMid carve-out honesty, axiom hygiene (only monomial_rlct).
- **#28 CONSOLIDATION note:** canonical atlas = crux2's route-m-atlas threshold_ge/achiever form; fm3's
  ResolutionAtlas.lean is the STALE stratum/threshold_eq form (fm3's bridge correctly targets the canonical).
- **★ HEADLINE FIDELITY AUDIT — SURVIVED (decorrelated reviewer + 2 Codex consults; artefacts codex-rv/).** The
  most load-bearing STABLE claim, aoyagi_learning_coefficient, is FAITHFUL on every axis: (Q1) NON-CIRCULAR —
  aoyagiLambda is the integer-QIP combinatorial closed form (Lambda.lean imports ONLY Mathlib, structurally
  cannot reference rlctAt/dlnLoss; bottoms out in [−r²+r(H₀+H_last)]/2 + ½·(Adm M).inf' Mval); the headline is a
  real analytic→combinatorial bridge, not a tautology. (Q2) ⨅-KEYING faithful — global learning coefficient over
  optimalSet (= loss zero-set); rlctAt = honest sSup-of-integrable-exponents. (Q3) LOSS = squared Frobenius
  ‖prod−B‖². (Q5) AXIOMS clean — #print axioms = [propext, sorryAx, Classical.choice, Quot.sound]; the sorryAx is
  EXACTLY the 3 named rungs (R1@1022 / L2@955 / D1@978) + the single cited axiom monomial_rlct@120 (S2); no leak,
  θ/order held separate (opaque rlctOrderAt, off-path). (Q6) NAMED right (λ=C/2, not bare codim). VERDICT: faithful,
  honest, non-tautological. Residual (LOW): add a one-line aoyagiLambda_nonneg to retire the ENNReal.ofReal clamp.
- **★ (A)→(B) REVERSAL (audit-driven; I was wrong on (A)).** The committed headline is NON-STRICT (hr : ∀ s, r ≤ H s,
  matching the paper's r ≤ min(ud)). The audit + Codex VERIFIED the boundary r=H_s is TRUE — (3,1,3),r=1 → rlctAt =
  5/2 = aoyagiLambda (Morse-Bott rank-5, flat core); (1,1),r=1 → 1/2. So strict ∀s r<H_s is a PROOF-CONVENIENCE,
  not soundness; adding it NARROWS below the paper (under-claim). My (A) "R1 caps the headline at all-s" was
  CIRCULAR (assumed the strict scope it justified). DECISION: headline stays NON-STRICT (paper-faithful), vindicating
  crux2's (B) instinct. RECONCILIATION (no rework): the RUNGS keep their non-degenerate/all-s domain (decomposition
  needs G≢0); the HEADLINE doesn't inherit strict hMid — it CASE-SPLITS: non-degenerate (all M_s≥1) → rungs;
  degenerate (some M_s=0) → a NEW direct-Morse lemma (#70). Until #70 fills, the degenerate boundary is a NAMED
  obligation (honest sorry), NOT a narrowing. **CONVENTION subtlety (the mechanism):** rlctAt(F≡0)=⊤ (team sSup
  convention), so at the boundary the decomposition nReg/2 + rlctAtOn(core) gives ⊤ — FALSE; #70 routes AROUND it,
  computing rlctAt(deepest)=nReg/2 directly via the rank-nReg Morse-Bott quadratic (vanished-core dirs flat → 0).
  (Supersedes the earlier "(A) all-s, r=min carve-out" bank above — that was the pre-audit call; corrected to non-strict.)
- **★ g159 RESOLVED — LOCAL-DIFFEO (germ), not global homeo.** cobuild-sub34 flagged regAbsorb is NONLINEAR
  (E = X1+X2+X1X2+…, not a shear like coreAbsorb) ⟹ a GLOBAL self-homeo construction hits the g159 wall.
  RESOLUTION: rlctAt is a GERM (Rlct.lean: sSup over ∃ U ∈ 𝓝 w0), so the reparametrization π (regAbsorb /
  coreAbsorb) need only be a LOCAL diffeo at w0 (PartialHomeomorph), NOT a global Homeomorph. The nonlinear
  regAbsorb's higher-order terms (X1X2…) vanish at the basepoint ⟹ dE(w0) = the invertible linear part ⟹ local
  diffeo by IFT ⟹ bounded-unit Jacobian on a nbhd ⟹ the peel applies. So crux2's abstract peel lemma (#71,
  consumed by both regAbsorb_rlct + coreAbsorb_rlct) must be stated for a LOCAL diffeo at w0 ("π PartialHomeomorph
  / dπ(w0) invertible + bounded-unit Jacobian near w0 ⟹ RLCT invariance"), NOT a global self-homeo. This is the
  general resolution of the g159 global-≃ₜ-from-local wall — it was never needed; local suffices because rlctAt
  is a germ. (cobuild-sub34 owns the MAP + dE(w0)-invertible check; crux2 owns the LOCAL peel #71.)
- **R1 per-node datum: light-vs-heavy CONFLICT being reconciled (controller-flagged).** Literal tension: pp2 g188
  says NO IsSchurStraightenSqueeze on R1's path (all R1 nodes = LIGHT monomial pullback node_loss_pivot_factor;
  the heavy IsSchurStraightenSqueeze = L2's deepest-gauge node); crux2 told fm3 R1's "Schur node" consumes
  schur_straighten_squeeze_exists / "presentation in IsSchurStraightenSqueeze." Likely crux2's interface predates
  pp2's g188 light correction. NAIL before fm3 commits the certified RouteStep datum field (else wrong-type
  rework). Reconciliation in flight (crux2 ↔ pp2 ↔ fm3; pp2 exercising node-reduction on (3,3,2), C5→C2+C1 no new
  lemma, single-step verified, multi-step pending). The R1 transport-field gate = this resolution.
- **★ BUILD MODE (2026-06-22, cont'd) — architecture fully resolved, parallel builds.** Every conceptual wall
  is dissolved (split (e), measure-zero route, light R1 datum, non-strict headline, g159 local-diffeo). Now building:
  - **(b) MvPolynomial lemma DONE + INTEGRATED + build-verified** @68ef083 (DLNFibre.Core.MeasureTheory.
    PolynomialZeroSet: `MvPolynomial.volume_zeroSet_eq_zero` + `ae_eval_ne_zero` + `measurableSet_zeroSet`,
    green clean-three, 8248 jobs). The #69 formaliser's bonus-commit-before-standdown was exactly crux2's
    route-1 lemma — the route whipsaw (MvPoly→matrix→addHaar→MvPoly) landed on what was already built. Module
    committed but UNWIRED in the single-writer aggregator (crux2's L2 import gates it transitively).
  - **Measure-zero ROUTE = 1 (MvPolynomial), crux2's final call** (after the addHaar detour): (b) lemma DONE;
    crux2's (c) = the single-P encoding (P=∑(prod-entry)², eval z P = dlnLoss M 0 via Matrix.map_mul, P≠0 from
    the witness) → ae_eval_ne_zero at p:=P closes the bridge's last sorry. Queued behind #44.
  - **L2 peel = ROUTE 2 (LOCAL), interface LOCKED** (#72, crux2's `rlctAtOn_boundedUnit_localHomeomorph`,
    raw-data form, sig validated green): the global #71 peel (proper+surjective) didn't take cobuild-sub34's
    IFT local diffeo (OpenPartialHomeomorph); the local peel is the germ-correct object (Mathlib c-o-v is
    InjOn-local). **#72 PROVEN @e6a0fd2 (crux2, sorry-free clean-three) — the g159 wall is fully CONSUMED for
    BOTH coreAbsorb_rlct + regAbsorb_rlct; RLCT-transport machinery DONE.** cobuild-sub34 wires coreAbsorb_rlct
    + regAbsorb_rlct against it (π/πsymm/Dπ + dE(w0)=id ⟹ bounded-unit). regAbsorb = IFT OpenPartialHomeomorph
    (HasStrictFDerivAt.toOpenPartialHomeomorph, dE(w0)=id verified). Only remaining L2 analytic content =
    cobuild-sub34's det-bound (det(I−VY)⁻ᴹ⁰ continuity + =1 at w0); then role split partition (gaugeDecode seam)
    + the (c) single-P connect + loss_squeeze/assembly.
  - **R1 (#39): fm3 UNBLOCKED — proceeding on the LIGHT datum** without waiting for crux2's formal ack (its
    (2,2,2)-code grounding is authoritative: zero IsSchurStraightenSqueeze, step1A=pivotBlowupOn, pullback
    y0²·Q; + pp2 g188 + numerics = 3 confirmations). Pinning the light ValidRouteStep datum field
    (node_loss_pivot_factor + det + rlctAtOn_reduced_transport) + fold + transcribe pp2's recipe, parallel to L2.
  - **Slot-grouping seam**: crux2 owns the role-partition (replaces equivOfCardEq; reg=invertible pivots
    {X1,Y2,Z1}, core=T, by r-threshold); cobuild-sub34 owns gaugeDecode/IsGaugeSliceDecode + matches the index
    map crux2 sends. OPEN gates: crux2's #72 local-peel proof (critical path), the #44 assembly, fm3's R1
    assembly, then D1 (gated on #44) + #70 (degenerate boundary). No conceptual walls, no 2nd citation, no
    operator surface.
  - **PROGRESS (cont'd, post-8cf721a):**
    - **#44 ROLE-RESPECTING SPLIT DELIVERED @c7a28fb (crux2, sorry-free)** — deepestSplit_exists now uses the
      concrete `deepestRoleIndexEquiv` (NOT arbitrary equivOfCardEq): rThresholdSplit → layerEntrySplit →
      flatIdxLayerProd/roleSplitIdx (core slot = FlatIdx(deepestM), TYPE-FORCED) → card_regGaugeIdx →
      deepestRoleIndexEquiv (Fin(flatDim H) ≃ Fin nReg ⊕ (Fin(flatDim M) ⊕ Fin nGauge), middle = T-core). The
      "biggest split risk" (the FlatIdx bijection) is RETIRED; the slot-by-role precision pin is SATISFIED
      (core=T, reg/spec=gauge X/Y/Z — what the absorptions read). Remaining #44(i) = the gaugeDecode +
      IsGaugeSliceDecode witness (seam: crux2 supplies gaugeDecode from deepestRoleIndexEquiv, cobuild-sub34
      owns IsGaugeSliceDecode).
    - **g161 (cobuild-sub34, Codex xhigh + sympy) — the (e) counterexample, TRIPLE-CONFIRMED.** The RAW
      loss_squeeze (∑(split w).1² = raw gauge coords) is FALSE: at (2,1,2),r=1 with x2=1/(1+ε)−1, ∏C=diag(1,0)
      so loss=0 while raw=Θ(ε²) — lower bound fails ∀c₁>0. regAbsorb→E makes it true (loss=e²+y²+z²+(z1y2)²
      ≍ ∑E²+core). Vindicates (e): loss_squeeze MUST be through E (the BEDROCK bar on crux2's DeepestGaugeChart
      edit — green over raw = green-≠-right). Decorrelated-confirmed by pp2's own L=2/L=3 (leak ∈ ideal(E),
      two-sided squeeze; no counterexample). Nothing built on the false form (no rework).
    - **R1 light interface IN LEAN (fm3)** — ReducedTransport bundled (consumes crux2's rlctAtOn_reduced_transport
      sig), descent clean-three. R1's structural backbone landed; remaining = the fold + transcription of pp2's
      recipe (the routeStep dispatcher).
    - **Measure-zero ROUTE 1 FINAL (crux2 converged).** The free MvPolynomial lemma (@68ef083) flips the cost:
      Route 1 (consume it + the ~60-120 LoC P-encoding) is now LIGHTER than Route 2 (~150-250 LoC addHaar). (c)
      = single-P encoding (P=∑(prod-entry)², eval z P = dlnLoss M 0 via Matrix.map_mul + prodAux-over-MvPoly
      mirror, P≠0 from witness, ae_eval_ne_zero at p:=P). Off the critical path (the bridge's final hGne
      discharge); crux2 keeps #44 priority, interleaves the encoding. Escape hatch: if the mirror walls, switch.
    - **★ #65 hMid⟹hGne BRIDGE CLOSED @4b4a4cf (crux2, sorry-free clean-three).** The prodAux-mirror was
      tractable (~100 LoC, NO escape hatch): `prodPolyAux` (a SEPARATE ring-generic mirror of prodAux — NOT
      making prodAux ring-polymorphic, which would break its ℝ call-sites) + `prodPolyAux_map` (eval commutes
      via Matrix.map_mul) + `prodPolyAux_eq_prodAux` + `corePoly`/`eval_corePoly` (eval z (corePoly M) =
      dlnLoss M 0 (flatSymm z)); assembly: corePoly≠0 from the witness ⟹ ae_eval_ne_zero at p:=corePoly ⟹
      {dlnLoss M 0 ∘ flatSymm = 0} null ⟹ hGne. **The L2 hGne discharge — the one tracked from-scratch heavy
      lemma, the "everything-proven-except-S2" requirement — is DONE.** The measure-zero arc (formaliser
      dispatch → route whipsaw 1→2→1 → Route 1 + mirror) landed; Route 1 vindicated.
- **★ SPINE MAP (#40 re-audit, crux2; Skeleton builds GREEN 2671) — the assembly roadmap to green.** The headline
  `aoyagi_learning_coefficient` (Skeleton:1594) is PROVEN-CONDITIONAL (`rw deepest_point_reduction; exact
  product_reduction`), hanging on 4 λ-sorries:
  1. `deepest_regular_core_normal_form` (Skeleton:1016) — the L2 VALUE-form = the CONVERGENCE NODE, fanning into
     (a) crux2's deepest_regular_core_reduces (value-free, sorry-free EXCEPT the chart, carries hGne) + (b) R1
     value rlctAtOn(core)=ofReal(lambdaCore) (= resolution_charts ▸ A1) + (c) hGne discharge (#65 DONE + #70
     boundary). crux2 PRE-STAGING it as a conditional lemma (one-line fill when the gates land).
  2. `deepest_gauge_squeeze_exists` (DeepestGaugeChart:287) = #59 (cobuild-sub34's chart) → feeds 1(a). In build:
     regAbsorb/coreAbsorb MAPs + gaugeDecode + the instance; the bi-invariant-V adapter (rlctAtOn_comp_localDiffeo)
     = crux2's; general-L squeeze gate CLEARED (pp2 + sympy); det-bound DONE (DeepestGaugeDiffeo).
  3. `resolution_charts` (Skeleton:1106) = R1 core = ⨅, OPEN only on fm3's RouteMAtlas (#39) → feeds 1(b). fm3
     BUILDING (cover_le/cover_ge_div + the certified routeStep dispatcher transcription of pp2's g183-g190 cert).
  4. `rlctAt_deepest_le_of_optimal` (Skeleton:1062) = D1 ≥-leg (#42), PROVEN-CONDITIONAL @8d0fd21 (gated on #62's
     hAtV), NOT yet wired into Skeleton. Path: #44 (deepest chart) → #62 build (cobuild-sub34 extends to basepoint
     v) → D1 hAtV discharges → wire into Skeleton. Downstream of #44+#62.
  OFF λ-path: `aoyagiTheta_eq` (Skeleton:1582) = A2 θ-count, secondary (separate deliverable).
  PROVEN GREEN: A1 (lambdaCore_eq_clean, reg_shift_add_core), product_reduction wiring (modulo normal_form),
  deepest_point_reduction ≤-leg + assembly, the headline composition; the §5(5)▸§5(3) bridge on fm2/route-m-atlas.
  NET: headline → 4 gates (#59 cobuild-sub34 / #39 fm3 / #70 held / #42-D1 downstream of #44+#62), converging at
  the L2 normal_form node. NO new math owed by crux2 — assembly-ready.

**Phase.** The general-M monomial route is the live path (the per-node squeeze is OFF-path — blow-up gives
an x_p²·Q product, not the squeeze's additive sum; no measure-preserving recursion produces the monomial
Jacobian weight). The pen-and-paper / design side is **complete and corrected** (pp2 arc g132→g153, + g138 §1
C1 prose fixed). What remains is pure Lean: three concurrent grinds against a settled design, no open mechanism.

**The λ headline** `aoyagi_learning_coefficient` (Skeleton) is proven modulo three named rungs; A1, the top
assembly, the transport/shift machinery are proven. The headline-given-atlas chain is proven, green, S2-free
(`RouteMAtlas` unifies `IsRouteMCover` + `IsResolutionAtlas`; `routeM_rlctAtOn_eq_lambdaCore`). The three rungs:
- **R1** `resolution_charts` — fm3 #39: the `RouteMTree` dispatcher (classify + schur/pass/left/right state +
  descent) + cover-facts (`cover_le`/`cover_ge_div`) + achiever. `cover_le` (the path-composite CoV integral)
  is the one evidence-then-switch spot (WF.fix vs plain-inductive).
- **L2** `product_reduction` — crux2: APPROVED SPLIT (2026-06-22) into value-free `deepest_regular_core_reduces`
  (rlctAt deepest = nReg/2 + rlctAtOn(dlnLoss M 0) 0) + R1-value composition (▸). #50 = consuming side
  (S1 spectator-peel + sub-5/6/7 + assembly); #51 = the XL chart-existence.
- **D1** `rlctAt_deepest_le_of_optimal` (≥-leg) — downstream of L2's gauge chart (the 6-step wiring once the
  general-`IsDeepLayers` chart lands).

**C1 mechanism (SETTLED, g152/g153).** Per-node C1 = blow-up (x_p² weight, exceptional (k,h)=(1,card−1)) +
**det-1 triangular Schur peel** (w:=D−b·a, the #37 change) + recurse. The peel is NEEDED (g152: {S=0}={D=b·a}
is BILINEAR; pivotBlowupOn only hits coordinate subspaces — the peel makes it {w=0} first). The peel is det=1
MP at ANY rank (g153: unipotent block-triangular block-shear, rides measurePreserving_lemma2, no Jacobian
weight, no bounded-unit lemma); Σdrop=2 (ChainDimSplit.measure_drops). The same triangular peel appears one
level up at the g150 deepest-point gauge chart (there det-UNIT, non-MP). NOT the squeeze, NOT lemma2Fwd.

**g150 gauge chart (CORRECTED).** Reduced core = gauge-normalized ‖T̃_1···T̃_L‖² (product Schur complement),
NOT raw ‖∏T_s‖² (on {E=0} the cross-term becomes invertible gauge factor (I−V·Y)^{-1}). nReg = r(H₀+H_last−r).

**Cert sharpening (cobuild-sub34 + Codex, decorrelated, 2026-06-22).** The raw-chain squeeze ‖T·S‖² is FALSE
for matrices (g=(I−VY)⁻¹ maps a TS=0 dir to TgS≠0, ratio→∞) — independent re-derivation of why the core must
be T̃; the g-absorption IS the non-MP content. The cert framing refines: "exact split, not a squeeze" →
"exact only in T̃-coords; the raw-chain squeeze is false."

**sub-3/4 ROUTE — RESOLVED (2026-06-22): R-SQUEEZE; the XL chart-existence COLLAPSES.** crux2 (structure owner)
decided R-squeeze after reading cobuild-sub34's g152 finding. DeepestGaugeChart is trimmed: drop the global
`chart`/`Dchart`/`hasDeriv`/`jac_unit` + the `loss_form` EQUALITY; replace with a `loss_squeeze` datum
(c₁Φ ≤ dlnLoss∘flat ≤ c₂Φ near the deepest point, Φ = ∑reg² + dlnLoss M 0(core)); keep nGauge/split/split_mp/
split_zero. WHY: (1) the honest gauge chart is only a LOCAL diffeo at w0 (inverse uses A⁻¹/(I−VY)⁻¹, blows up
off w0) — a global homeo over-reaches; rlctAtOn is local, the squeeze is local-by-construction; (2) reuses ONLY
blessed infra — rlctAtOn_squeeze (the GeneralR1Recursion `schur_recursion_step_squeeze` pattern) + #52 +
rlct_additive_smooth_block; no global-chart construction, no weightedThreshold_transport; (3) crux2's proven
sub-6 SURVIVES (it computes rlctAtOn Φ; the squeeze only changes how sub-5 reaches Φ). NET: the XL sub-3/4
chart-existence (~600-1500 lines of cutoff-extension block algebra) is DROPPED — it collapses to ONE obligation:
the matrix-core comparability ‖T·(I−VY)⁻¹·S‖² ≍ dlnLoss M 0 (GAUGE-NORMALIZED T̃, NOT raw ∏T — raw is FALSE for
matrices). Ownership: crux2 = structure re-shape + sub-5 (Params→flat MP + rlctAtOn_squeeze); cobuild-sub34 = the
comparability (#53/#54/#55) against the trimmed loss_squeeze field. Handoff coherence: #55's raw-∏T framing
(|‖P11‖²−‖∏T‖²| ≤ K∑E²) is valid only if that leak bound holds; else state the comparability in T̃ form directly
— pinned by crux2's loss_squeeze field shape. (Route arc: squeeze → chart [on cutoff-satisfiability] → R-squeeze
[on the GeneralR1Recursion precedent + the collapse]; resolved by crux2's owner-call. Ledger lesson: bank live
decisions as "current lean, pending X", not as settled.)

**Current execution (three grinds):**
- fm3 #39 (R1 dispatcher + cover-facts) on origin/fm3/routem. hMid threaded into resolution_charts (@6f4e70f) —
  carve-out now threaded BOTH sides (fm3 R1 + crux2 @081cf51 L2/headline). **R1 SEAM (decided): crux2 = per-step
  straighten/additive-descent (banked ChainDimSplit); fm3 = blow-up cover / ⨅-min-over-pivot-branches — BOTH
  needed (the ⨅ is the branching-min, NOT a single-chain telescope; Codex's "telescope replaces cover" too
  strong). REBASE: fm3 drops its parallel RouteState (a sync liability) → rebases the descent onto crux2's
  ChainDimSplit, keeps the cover-branching on top** (de-dups the recursion-state; aligns w/ crux2's
  GeneralR1Recursion docstring). crux2 answers fm3's 3 ChainDimSplit-interface Qs + extends it if needed. fm3
  proceeding on the fork-independent MonoData→(d,k,h) threshold lemma meanwhile (good — didn't grind a duplicate
  recursion). Achiever = `_le_regularSeq` at j₀ (card=m₀ min-ratio axis) + threshold_ge, bundled by
  of_mult_and_achiever. (#44 split = crux2's #64 — collision resolved; cobuild-sub34 imports deepestSplit_exists.)
- crux2 #50 (value-free reduction) on origin/fm2/deepest-gauge-chart (@c1ce00f/@7573c0b): CONSUMING SIDE
  FULLY PROVEN (clean-three) — sub-2, sub-5 (`deepest_squeeze_transport`), sub-6, sub-7, the assembly
  `deepest_regular_core_reduces`; + 4 reusable Foundations lemmas (spectator-peel #52, continuous_dlnLoss,
  weightedThreshold_weight_unit_invariant, rlctAtOn_mono/rlctAtOn_squeeze re-homed GeneralR1Recursion→
  S1NonMPTransport). GATED on ONLY sub-3 (cobuild-sub34's comparability). STRUCTURE FIX in flight (cobuild-sub34
  caught it at instance-production): the trimmed loss_squeeze was OVER-CONSTRAINED — split MP + hardcoded Φ-core
  = dlnLoss M 0(paramsEquivFlat M ...) forces the RAW core, which g153 refuted (C1C2C3=blockdiag[1,−ε⁴]: loss=ε⁸
  > 0 = Φ). FIX (A, determined): add `coreEmbed` field (the g-absorbing UNIT-Jacobian reparam) + Φ-core =
  dlnLoss M 0(coreEmbed ...); split stays MP (sub-5/6 INTACT, verified line-by-line), sub-7 gains the unit-peel
  via the PROVEN weightedThreshold_weight_unit_invariant. L2 claim HOLDS (unit-Jacobian ⟹ core RLCT =
  rlctAtOn(dlnLoss M 0) 0). crux2 implementing. hGne carried as a local hypothesis → TRACKED for spine-wiring;
  gap #2 measurability CLOSED (Codex g151). crux2 NEXT → D1≥ wiring skeleton (below).
- cobuild-sub34 #51 (the COLLAPSED sub-3 = matrix-core comparability, GAUGE-NORMALIZED T̃): chart-collapse
  CONFIRMED; matrix bedrock #53 BANKED green (twofactor_block_product, schur_P11_decomp [P11=R+leak, R=T̃],
  frobenius_fromBlocks). OPEN soundness Q gating the loss_germ transcription — **split_mp vs T̃-core**: can an MP
  `split` deliver the T̃ core (crux2's `ofExactGerm` stands as-is), or is a non-MP `coreEmbed` field needed
  (cobuild-sub34)? DECIDED via the g153 litmus (C1C2C3=blockdiag[1,−ε⁴]: Φ=ε⁸ → MP-deliverable, crux2 right;
  Φ=0 → coreEmbed needed). Note: cobuild-sub34's "MP ⟹ linear reindex" inference is too strong (MP ≠ linear; a
  nonlinear volume-preserving split is possible, gauge slot compensating the (I−VY) det). Worktree workspace/dgc-sub34. pp2 backup.
- **D1 #42 ≥-leg (`rlctAt_deepest_le_of_optimal`):** #57+#60 RESOLVED. D1(a) "deepest = min-rlct over optimalSet"
  is L1-SEPARABLE (NO 2nd citation, only-S2 SAFE), and the needed primitive **P1 (RLCT ray-semicontinuity) is
  LIGHT** — ~10 lines from the team's OWN rlctAt def (#60 @4995532: an admissible U₀∈𝓝 0 swallows the ray points
  s·v ⟹ sSup_le; + banked L1-a g162). g160's "heavy P1 / Varchenko" was an OVERESTIMATE (pp2 had routed via
  general Watanabe semicontinuity), corrected. NO Mathlib gap, NO operator surface. KEYING = ⨅-over-optimalSet
  (Skeleton:1505, the FAITHFUL learning coefficient; NOT the weaker deepest-point value). crux2 fills the D1 ≥-leg
  via L1-a (scaling, elementary, its weight-peel) + L1-b (P1) + the bridge, route = ROUTE 1 (core-level, confirmed
  by crux2 + pp2). OPEN (find-confound, crux2 to PIN in the fill): route 1's ≥ needs rlctAt(deepest) ≤ rlctAt(v)
  for ALL v incl non-rank-exact — does it decompose rlctAt(v)=n/2+core_v (needs L2-at-v = a wrapper) or bound
  DIRECTLY via the scaling-ray (pp2's "no charting v", wrapper-free)? crux2 claims wrapper-free — confirm the
  mechanism, don't gloss non-rank-exact v. #112 wiring cert done; skeleton origin/fm2/d1-deepest-min.

**TRACKED SOUNDNESS / PRECISION ITEMS (controller holds):**
1. **hGne / non-degeneracy hypothesis** (L2+R1) — STATED headline carve-out; FORM CORRECTED interior→ALL-s. ANY reduced width M_s=H_s−r=0 (interior OR endpoint) ⟹ prod_M≡0 ⟹ dlnLoss M 0≡0 ⟹ rlctAtOn=⊤ ≠ finite lambdaCore — breaks BOTH R1's identity AND L2's smooth-block. (fm3's interior-only lock was INCOMPLETE; crux2's pre-thread catch: endpoint M_0=0 [r=H_0, B full row rank] / M_L=0 are reachable + break it too.) **Headline gains `∀ s, r < H_s`** (ALL s; all reduced widths ≥ 1) — fenced as OUR FORMALISATION CARVE-OUT (refines the paper's realisability r≤min(d⃗) [non-strict], main.tex:1874; NOT verbatim-Aoyagi; my "Aoyagi-faithful" → "our carve-out"). hMid was threaded at the interior-only form (crux2 @081cf51 5 spine theorems + fm3 @6f4e70f R1 resolution_charts) — being RE-THREADED to all-s (crux2 L2/headline + fm3 R1). **The `hMid ⟹ hGne` BRIDGE is HEAVY (#65, crux2), NOT small** = (all-M_s≥1 ⟹ prod_M ≢ 0 as a poly) + (nonzero poly ⟹ zero-set Lebesgue-measure-zero). Mathlib lacks the multivariate form (only 1-D IsolatedZeros) → buildable from-scratch via Fubini-to-1D-slices + IsolatedZeros (induction on dim), a STANDARD fact. MUST be built (provable, not S2 → "everything proven"; NOT roadmapped-as-unproven). If it walls/multi-day → Codex consult or scope + co-builder. A fidelity WIN; NOT an operator surface; prominent honest caveat on "DLNs mildly singular." (Optional: DLN-preprint deep-read on Aoyagi's genericity.)
2. **D1(a) deepest=min-rlct** — **CORE PROVEN IN LEAN** (crux2 @152ef0d, zero sorries, clean-three): L1-a `rlctAtOn_ray_scaling_invariant` + L1-b `rlctAtOn_lsc_at_origin` + `deepest_le_of_homogeneous_core`. So "deepest = min-core" is LEAN-REAL (proven, NOT cert-claimed), value-free, NO Aoyagi Thm 2, NO heavy primitive — **the critical citable-constraint risk is fully dissolved + GREEN; only-S2 HOLDS.** (P1/L1-b was ~10 lines from the team's own rlctAt def; g160's "heavy P1" overestimate fully corrected.) Keying = ⨅ (faithful, Skeleton:1505). The full-B bridge `deepest_le_of_optimal_via_L2` is BUILT + PROVEN (@8d0fd21, modulo the explicit `hAtV` = L2-at-general-v hypothesis — pinned, not glossed). **D1 ≥-leg = core-P1 (PROVEN) + bridge (PROVEN-conditional) + #62 L2-at-general-v (DESIGN DONE, build pending).** #62 DESIGN (pp2 g173, decorrelated w/ Codex): the **CONSTANT active-block split** — peel N_active = r(H_0+H_L−r) = nReg (constant on the fibre; NOT the maximal Morse split, which makes n_v non-constant = Aoyagi-Thm-2 content, the trap pp2 caught in my framing), leaving the SAME core F0=‖∏S_s‖² at basepoint D(v); core-P1 dominates ⟹ deepest ≤ v. So **NO Aoyagi Thm 2, NO 2nd citation — only-S2 holds for the FULL D1.** (Cheaper direct-LB probed + rejected: naive pointwise LSC false.) #62 BUILD = cobuild-sub34 extends its #44 deepest chart to basepoint v + core basepoint D(v) (block_elim on the rank-r PRODUCT, not per-layer) + crux2 split-at-v, AFTER the deepest #44. The critical core-P1 (deepest=min) PROVEN; D1 design-complete, only the #62 build remains.
3. **split_mp + coreAbsorb's core OBJECT** (#44 sub-3) — resolved in TWO litmus passes (controller-directed g153 litmus, both find-confounds before the build): (1) MP-split can't do the non-MP g-absorption ⟹ crux2 added the `coreAbsorb` self-homeo (#58). (2) g153 litmus THROUGH coreAbsorb: the per-layer UNIT `T_s·(I−V_sY_s)⁻¹` gives Φ=0 at the g153 point (loss=ε⁸ ⟹ upper squeeze fails) — UNSOUND; the correct per-slot object is the per-layer SCHUR complement `S_s = T_s − Z_s(I+X_s)⁻¹Y_s` (the middle factor carries the −zy the unit misses; ∏S_s = R|_{E=0} = cobuild-sub34's #54 R; sympy-verified ∏S=−ε⁴, ‖·‖²=ε⁸=loss ✓). **RESOLVED + 3-WAY ALIGNED:** crux2 fixed coreAbsorb unit→Schur S_s (@87ef302), pp2 corrected its g150 cert (g172 @f8ea2eb), cobuild-sub34's #54 R — all three now pin the per-layer Schur S_s. The #44 gate is CLEARED. **sub-3 (#59) is a MULTI-PIECE build, not a one-step transcription** (honest calibration): the comparability ALGEBRA is banked (5 green lemmas), but the structure references concrete maps, so it needs (a) `coreAbsorb` (Schur S_s self-homeo — cobuild-sub34, building) + coreAbsorb_rlct + loss_squeeze wiring [cobuild-sub34's algebra]; (b) **`split`** (gauge-slice MP reindex flat ≃ₜ DeepestSplit, the MeasurableEquiv + MP proof — the HEAVY piece, the L2 long-pole; **crux2 owns it**, its paramsEquivFlat/S1 infra closest). The two long-poles = R1 #39 [fm3] + the #44 split [crux2], parallel. **#28 NOTE:** canonical g150 core = per-layer Schur S_s (g172 @f8ea2eb supersedes the unit gloss); the "(I−VY)⁻¹ gauge factor / unit" gloss was the mis-spec (slipped in TWICE — #56 exact-overclaim + this per-layer gloss; honest object is consistently the Schur complement). L2 CLAIM held throughout (only the map's def changed).
4. **exact-vs-squeeze** — CORRECTED to SQUEEZE: cobuild-sub34's Lean #54 (`core_comparability_squeeze`) has c₁=(2(1+t²))⁻¹, c₂=2+2t² (c₁=1/2,c₂=2 at w0 — c₁<c₂ even at the basepoint; leak BOUNDED by t²∑E², not absorbed). The frobenius split loss=∑E²+‖P11‖² is exact (lemma 3), but the P11→R core-identification is a genuine SQUEEZE — the "exact" framing would couple reg+core (2⟨R,leak⟩), breaking sub-6's separation. FINAL RESOLUTION (pp2 g175 @eb53d70, exact algebra): it was a FRAME confusion, NOT opposite truth-values. **RAW gauge-block coords → SQUEEZE** (c₁<c₂→1 at w0; the Lean datum, core_comparability_squeeze, no c-o-v built). **After a Morse/splitting c-o-v φ → EXACT** (c₁=c₂=1; φ exists because the correction is O(reg²·core), no pure-core term — completes the square; φ unformalized). So #48's "exact" was TRUE in the φ-frame; g155's squeeze-downgrade TRUE in raw coords — BOTH right, the confusion was leaving the frame IMPLICIT (not an overclaim, as I'd recorded). Lean uses the SQUEEZE (sidesteps φ); `ofExactGerm` (c₁=c₂=1) dischargeable-in-principle (build φ) but UNNECESSARY — a non-required constructor. canonical g155 = @001fa37 (squeeze, the Lean datum).

**CANONICAL CERT LINEAGE (for #28 — pp2's authoritative tips, 2026-06-22):**
- g138 design (C1 = blow-up + det-1 triangular peel + recurse): **origin/g138-c1-peel-prose @0823917** ← canonical
- g140 ι-pin: origin/g140-both-steps @2f80d44
- g134 (S-min): origin/g134-surjectivity-sketch @e18c00e
- g147 achiever: origin/g147-achiever-cert @6e6b00d
- g148 i₀ re-spell (2-node (2,2,2)): origin/g148-222fix2 @34c1d6c
- g150 gauge chart: g150-fix @50251296 (T̃) → g172 @f8ea2eb (per-layer Schur S_s) → g174 @3e817ef (full-product ‖R‖²) → **origin/g175-exact-vs-squeeze-frames @eb53d70** ← canonical (the 4-level RLCT-equivalent hierarchy + the frame distinction)

**RECURRING PRECISION LESSON (bounded-unit-peel + NAME THE FRAME — hold for future core-object specs):** repeatedly the honest loss-core object was reached by peeling a BOUNDED UNIT, and in RAW coords the comparability is a unit-SQUEEZE (c₁<c₂, tight at w0), peeled by `rlctAtOn_unit_invariant_aux` (NON-MP): (i) #48 "exact" (frame-implicit) → raw squeeze; (ii) g150 per-layer UNIT T̃_s → per-layer SCHUR S_s; (iii) g172 ∏S_s → FULL-product ‖R‖² (R=∏S_s·g). PATTERN: don't write the unit-peeled reduced form as the LITERAL core; the literal core carries a bounded unit. AND — NAME WHICH COORDINATE FRAME an "exact" claim lives in: "exact" (after a Morse/splitting c-o-v) and "squeeze" (raw coords) are BOTH right in their frames; the confusion was leaving the frame implicit (g175). Lean builds the raw SQUEEZE; `ofExactGerm` (c₁=c₂=1) is dischargeable-in-principle (build φ) but UNNECESSARY — don't reach for it.
- g152/g153 C1-peel: origin/g152-c1-peel @0006f3a (also folded into g138-c1-peel-prose)
- g155 general-v squeeze cert: **origin/g155-squeeze-downgrade @001fa37** ← canonical (SQUEEZE; g155-exact-precision b3c51db SUPERSEDED)
- D1 #57 prove-or-surface (deepest=min-rlct L1-separable, NO 2nd citation; P1/P2 landscape): origin/g160-d1-update @89f5915
- #44 squeeze structure (chart DROPPED, coreAbsorb + coreAbsorb_rlct; consuming side proven): origin/fm2/deepest-gauge-chart @b4229e0; sub-3 = cobuild-sub34's #53/#54 on origin/fm2/deepest-gauge-chart-sub34
- S-min value (canonical ResolutionAtlas, 3-conjunct): origin/cover/resolution-atlas-value @1c4b9b5
- bridge/atlas: RouteMBridge origin/fm2/route-m-bridge @472433b; RouteMAtlas origin/fm2/route-m-atlas @31063ec
- consolidation base: origin/integration/routeM-wip @0afee3a (g129 toolkit; has OLD 4-conjunct ResolutionAtlas —
  pull S-min from @1c4b9b5 instead)

**#28 plan (controller, at core-green):** consolidate onto expedition/aoyagi-full — RouteMAtlas = local core
branch; pick g150-gauge-chart-fix (T̃) + g138-c1-peel-prose + S-min @1c4b9b5 (3-conjunct, NOT the 4-conjunct on
routeM-wip); dedup Mval_nonneg; flush this synthesis. At merge, fold pp2's g140 gloss ("inductive RouteMTree"
→ "the WF.fix atlas's leaves (nested Σ/Sum)" — fm3's encoding is WF.fix, not a materialized inductive; ι +
achiever unaffected). PR only after the full general-M `aoyagi_learning_coefficient` is sorry-free (operator:
no PR until the hero task is done).

## Prior read (2026-06-21): ★ R1 EXECUTION — S1.5 sorry CLOSED (6→5) @1304cf2; (2,2,2) route PINNED ★

**Milestone @`1304cf2` (pushed origin, rv-2 auditing):** the S1.5 wire is in — `rlct_additive_smooth_block`
now `exact …_aux` (closes a sorry, **6→5**), axioms `[propext, Classical.choice, Quot.sound]` (no sorryAx,
no monomial_rlct). `resolution_charts` **re-scoped to the CORE form** `rlctAt M (dlnLoss M 0) (0:Params M)
= ⨅ i, monomialThreshold (d i)(k i)(h i)` (rlctAt, deepest=0 — replaces the old false full-loss form);
`resolution_charts_case111` realigned to it, STILL axiom-free (the genuine M=(1,1,1) instance). Only declared
axioms in-tree: `monomial_rlct` (S2) + `opaque rlctOrderAt` (θ-seam). 5 sorries, all in Skeleton (the rungs).

**Measure engines all axiom-clean** (verified by explicit build + #print axioms): Fubini `_aux` (S1.5),
G5-step `g5_flat_cover` (#52), `rlctAt_mono`, `product_min_rlct` (#56), `product_min_rlct_of_ne` (#57).

**R1 design COMPLETE — (2,2,2) deeper-point pin RESOLVED (pp + decorrelated Codex, identical):** the δ-pivot
chart's "unit" U=ξ²+η²+(bξ+r)²+(bη+s)² is a nondeg smooth-4-block (Hessian det 16) vanishing EXACTLY at
{ξ=η=r=s=0} = the deeper stratum **B=0** (fm SPECIFY-catch, chart-exact §8 caveat). Route = **STEP-3
sub-blowup** (option b); the δ-pivot was never a leaf — its 4 step-3 children ARE part of the **stable 24-leaf
set** (8 unit d=2, k=![1,1], h=![3,2] + 16 block d=3, k=![1,1,1], h=![3,2,3], all RHS 3/2; ⨅=3/2=lambdaCore(2,2,2),
θ=1). **Soundness DISCHARGED:** deeper stratum B=0 has codim 4 > minMval 3 ⟹ its exceptional ratio 2 > binding
3/2 ⟹ NEVER binds — chart-exact form of "centers=admissible strata, no center beats min". Full Jac = **α³·ρ²**
(α³ = step-1 A-blowup). Durable in r1-222-cover card §δ-CHART-DEEPER-POINT-PIN + §δ-BRANCH-BUILD-ROUTE-FORK.

**Route-fork adjudicated (controller call):** the product_min-skip route is SOUND (shear unimodular even with
b free; rlct(U)=2; positivity-OK) but **heavier** — it needs a NEW weighted-product-split lemma (because #56
is **TRIVIAL-weight** and the δ-leaf carries the α³ρ² Jacobian). step-3 is lighter for (2,2,2) (uniform monomial
machinery, no new lemma). The weighted-split is a reusable **general-M down-payment** → **DEFERRED** (general-M
gated on G3 = roadmapped, not the active target). ⟹ build (2,2,2) δ-branch via step-3; #56 serves trivial-weight
call-sites only ((2,1,2) #55 TBC).

**Green-gate GAP found + fixing:** `lake build DLNFibre` builds only the aggregator's closure → not-yet-consumed
engines (S1ProductMin #56, S1G5 #52, ParamsFlat) escaped it (caught via "S1ProductMin.olean does not exist" on
axiom-check). Built them explicitly (green; #56 axiom-clean). fm to (a) import stable engines into the aggregator
+ (b) restore AxCheck.lean. Lesson banked. "Green build" ≠ "every module compiles."

**Since the milestone (trunk now @930a6a0, all pushed):** rv-2 AUDIT **PASS** on @1304cf2 (S1.5 wire / re-scope /
case111 — decorrelated, validated the min-on-core + n/2-via-Fubini decomposition). **Green-gate gap CLOSED**
(@73c52f9 + @930a6a0): all 9 measure engines now imported by the aggregator + **AxCheck.lean restored**
(emits `#print axioms` every build — 5 results clean, headline sorryAx). **#57** `product_min_rlct_of_ne`
gated @2e8dc4c. **#58** pivot-blow-up atom gated @930a6a0 (pivotBlowup/Deriv/_det=(x 0)^n/_injOn, parametric
n — serves all 3 (2,2,2) blow-up nodes). Lesson banked: green `lake build <lib>` covers only the aggregator
closure (orphan engines escape).

**Active (trunk @536740b; LADDER 2/3 — (1,1,1) + (2,1,2) DONE + axiom-free):**
- **(2,1,2) #55 — DONE @536740b, axiom-free.** `case212_rlct = [propext, Classical.choice, Quot.sound]` (AxCheck);
  6→0: product-MIN heart (`product_min_rlct`), both block-RLCT bridges (EuclideanSpace↔Pi via
  `PiLp.volume_preserving_toLp`, in-seat), coord-split (the (1,1,1)-`entryME` pattern), `prod212_entry`
  (lean-formaliser). Merged + aggregator/AxCheck-wired. rv-2 auditing. Audits PASS so far: milestone/#58/#61/#52.
- **(2,2,2) #54** — fm-2, on flat `Fin 8→ℝ` (carrier **FORCED**: product `(Fin4→ℝ)²` lacks `IsAddHaarMeasure`).
  Node toolkit done/near: #58 (C¹/det/InjOn full-block), #61 (argmax cover), #64 (spectator), #65 (hmeas),
  #67 (argmaxCellOn flat-subset cover) — all gated; + `pivotBlowupOn` det (fm-2's +91 WIP, green+sorry-free,
  gating pending fm-2's confirm) → **#69 g5_pivotNode** (single reusable node, in progress). **#68 per-leaf
  VALUE lemmas DONE (fm half of #54).** REMAINING: pivotNode → 24-leaf 3-deep assembly (+ φ_L2 splice) + the
  **#66 seam** — route (ii): fm-2's OWN explicit m.p. `Params≃ᵐFin8` via `piCongrLeft` + an explicit a00..b11
  bijection (order pinned by construction, sidesteps the noncomputable equivFin). **Measure-instance verify-first
  flagged:** the piCongrLeft m.p. must land on Params's *actual* MeasureSpace instance (= rlctAtOn's), via the
  generic reindex lemma — not a parallel canonical-Pi measure. rv-2 audits the seam (the silent-hole point).
- **Case222 wrapper** (fm) — thin (2,2,2) validate headline, gated on #54's result. **pp** on-demand.
**Roadmapped (operator-gated scope):** G3 (general-M wall), #19 keystone (#37/#45/#46), weighted-product-split
(general-M). **Fixed-M ladder = active target: (1,1,1) DONE · (2,1,2) DONE · (2,2,2) #54 (the last rung).**

## Prior read (2026-06-20): ★ CONTRACT IS BEDROCK @296d3e4 — structural-proof phase OPEN ★

**rv-2 FINAL re-audit @`296d3e4` CLEAN → BEDROCK DECLARED.** The 9-issue fidelity arc is CLOSED. The contract
is genuine bedrock: domain PROVABLY complete (hr middle-width + hL L=0, systematic corner sweep proved no
10th hole), keystone clean, A1-clean + L1 genuinely proven (no sorryAx, not vacuous), headline assembles
axiom-clean through D1▸L2, S2 the ONLY citation (no leak), every rung name=content/non-vacuous. `git diff
2ee02b2 296d3e4` is hL-ONLY (zero drift). The rock the structural proofs now stand on.

The 9 issues (all caught by proof-attempts/decorrelated checks BEFORE anything built on them, all fixed):
6 in the original adversarial pass (L1 vacuous, L2 over-claim, D1 under-claim, S1.1 measure, R1 analyticity,
S1.5 analyticity); 7th deepestPoint false (middle-width) → hr; 8th lambdaCore weak existential → strengthen
(#19, sequenced); 9th deepestPoint false (L=0) → hL. Two sweeps closed the vacuity + domain classes wholesale.

Two honest residuals (NOT bedrock defects — off the criterion): deepestPoint_exists is a `sorry` (fm
mid-proof — a PROOF obligation, not a statement defect); A1 lambdaCore (#19) + A2 weak existentials (flagged,
off the headline path, strengthen sequenced).

### Earlier status (pre-bedrock, retained for the arc):
Two structural rungs landed during the contract phase. Honest status:

**Landed / green:**
- **Keystone `paramsEquivFlat`** (`Params H ≃ᵐ (Fin N → ℝ)`, measure-preserving) — fm-2 @`d7b1ba3`
  (Route A++). **rv-2 PASS (bedrock-clean):** isolated `/tmp` green-gate (2851 jobs, no shared-tree race),
  ParamsFlat ZERO sorries, axioms `[propext, Classical.choice, Quot.sound]` (no sorryAx/stray), NO leaked
  global instance (threads by `rfl`; bare `Matrix` still has no MeasurableSpace), flatDim correct by decide.
  Unblocks the (1,1,1) bridge, S1.1's use-site, R1's measure facts. (Nit: unused `forall_true_left` in
  `measurePreserving_piCurry` — fm-2 cleans on next touch.)
- **A1 `clean_eq_printed`** — fm, committed @`c234651` (genuine ℚ identity, rv-2 9324-case verified). KEEP.
- **A1 `lambdaCore_eq_clean`** — fm, committed @`f8233f2` (worktree-rung0-defs, sorry 13→11) — but it's the
  **WEAK existential (8th fidelity issue)**: closed by FREE CHOICE (ℓ=1, m=![1,(min Mval).toNat], needs only
  min≥0) — proves NOTHING about M, NOT Aoyagi Lemma 3. fm flagged it (good). DECISION: strengthen to genuine
  Lemma 3 (lambdaCore M = clean form at Def-3-selected widths, m BOUND to M; ~200-line balanced-split
  exchange). OFF the headline critical path (headline uses aoyagiLambda directly) ⇒ SEQUENCED after L1; weak
  proof KEPT with loud docstring flag as honest interim. pp DELIVERED the genuine statement (card
  `threads/14-r1-design/a1-statement-card.md`): `∃ ℓ ∈ {1..L}, lambdaCore M = cleanCore ℓ (sortedSmallest M ℓ)`
  — `m` PINNED to M's ℓ+1 smallest reduced widths (genuine: forced by (M,ℓ)). ⚠️ NOT an extremum: `min_ℓ`
  AND `max_ℓ` are BOTH FALSE (pp refuted Codex's "cleanest" via M=[1,1,4] / [2,2,2]) — formaliser must keep
  the `∃ℓ`. Verified 1360/1360. fm formalizes #19 (replace weak stmt+proof) AFTER deepestPoint_exists (off
  critical path). Def-3 sidestepped entirely.
- **L1 `block_elimination`** — fm @`fb65243` (worktree-rung0-defs), GENUINE explicit block-normal form (not
  the vacuous rank claim), ~220 lines via adapted-basis (`Basis.sumQuot` + `basis_toMatrix_…`). sorry 10→9.

**Weak-existential sweep (rv-2, complete):** exactly 2 weak rungs — A1 `lambdaCore_eq_clean` + A2
`aoyagiTheta_eq` (both on the fix list). L1, deepestPoint_exists, R1 GENUINE. Discriminator banked (lessons):
`∃ x, LHS(data)=f(x)` is WEAK iff f free-covers a CONCRETE LHS (x choosable free of data), GENUINE iff the
LHS is OPAQUE/pinned (witness must encode data). R1 genuine despite A1-shape (rlctAt = opaque sSup). No
surprises lurking — fidelity class fully catalogued.

**The 7th bug (caught by fm's proof attempt, MISSED by the bedrock audit):** `deepestPoint_exists`
(`Nonempty {w // IsDeepLayers H r B w}` under `hB : B.rank = r` ALONE) is FALSE — H=(3,1,3), r=2,
B=diag(1,1,0): the MIDDLE width H 1=1 bottlenecks the product to rank ≤1<2 ⇒ empty fibre ⇒ Nonempty FALSE.
The HEADLINE is then false too (⨅ over ∅ = ⊤ ≠ finite). Root cause: "rank B=r ⟹ r≤H s" holds only for the
OUTER widths. **Fix (decided): add `(hr : ∀ s : Fin (L+1), r ≤ H s)`** to deepestPoint_exists + deepestPoint
+ deepestPoint_isDeep + product_reduction + deepest_point_reduction + aoyagi_learning_coefficient. It is also
the well-definedness domain of `aoyagiLambda` (M⁽ˢ⁾=H⁽ˢ⁾−r needs r≤H⁽ˢ⁾). **FIXED + MERGED @`2ee02b2`** (hr
threaded through all 6 decls, headline assembles, deepestPoint_exists kept as sorry under new sig; contract
now TRUE, no empty-fibre ⊤). 7th bug closed. **9th issue (L=0 corner):** even WITH hr, false for L=0 (empty
product = identity ⟹ fibre needs B=I; `L=0,H=![2],r=0` has hr✓ but empty fibre) → fix `(hL : 1 ≤ L)`
(L=0 = no network = out-of-model; verified sufficient 484/484). Same DOMAIN-UNDER-SPECIFICATION class as the
7th. fm applying hL + proving deepestPoint_exists (one pass, then I merge). rv-2 commissioned a SYSTEMATIC
DOMAIN-CORNER SWEEP (catch the domain-hole class wholesale, like the weak-existential sweep) + HOLDS the
final contract PASS until hr+hL merges + sweep clean. (Fidelity-issue tally: 9 — all caught before proofs
build on them; the contract is converging to genuine bedrock.)

**rv-2 re-audit @2ee02b2 + DOMAIN-CORNER SWEEP (done):** hr-fix PASS (build green 2851, 10 sorry, axioms
clean, witness CONSTRUCTED for (1,1,1)/r=0 per the standing rule; A1/L1 genuinely proven, no sorryAx; L1 not
vacuous). 9th bug (L=0) INDEPENDENTLY confirmed (decorrelated counterexample). **Sweep result: NO further
hidden corner beyond L=0 — `hr ∧ hL` CLOSE the existence/headline domain COMPLETELY** (r=0→origin OK;
hr-equality boundary OK; only L=0 uncovered). ⇒ once hL lands + the final re-audit runs, the contract domain
is PROVABLY complete (no 10th domain hole lurking) = BEDROCK. The domain-bug class is closed.
Full rung×corner matrix (rv-2): R1 `resolution_charts` is SAFE at L=0 with NO hr/hL (the ONE unguarded
rung — at L=0 dlnLoss is constant ⇒ `rlctAt=⊤` either way, R1's ∃ discharges via `ι=Empty`, ⨅∅=⊤); all
other rungs (S2/S1.x/L1/A1/A2) clean at every corner (L=0, r=0, r-extremal, zero-width, d=0). So R1 needs
NO domain hypothesis — good for its formalisation. **Convention noted:** `rlctAt(≡0 loss)=⊤` in this dev
(rv-2 proved it; literature leaves F≢0's RLCT undefined) — BENIGN (the ≡0 case only at hL/analyticity-
excluded corners; the headline's rlctAt is for a non-≡0 loss, vanishing AT the deepest point not identically,
so the convention never taints the headline). Docstring note on `rlctAt` queued for convention-honesty.

## Live status (per-track)

- **fm-2 (measure track)** — keystone (d7b1ba3) + bridge (b342cd2, axiom-free) + continuity-to-ParamsFlat
  (fb50adc) ALL DONE; measure track COMPLETE. **NOW on the real S1.1 `weightedThreshold_transport`** (heavy
  transport rung; infra banked: continuity homeomorphism + 2-sided box-iff + sSup). Then the deepestPoint r>0
  telescoping (dependent-Fin, routed here post-S1.1). Commits to expedition; rv-2 green-gates behind. Trunk
  @`fb50adc`.
- **fm (algebra track)** — branch `worktree-rung0-defs` (Skeleton-only), based @1bb9e31 (I merge forward;
  no rebase needed — Skeleton independent of keystone). A1-clean + A1-lambdaCore(weak) + L1 + hr-fix DONE +
  MERGED @`2ee02b2`. NOW on `deepestPoint_exists` PROOF (reuses L1 adapted-basis) → then #19 lambdaCore-
  strengthen (waits for pp's genuine statement). **Trunk @`296d3e4`: keystone + A1 + L1 + hr + hL; Skeleton
  sorry 9.** hL MERGED; rv-2 running the FINAL bedrock re-audit (domain now provably complete → closes the
  9-issue fidelity arc). **deepestPoint_exists FULLY PROVEN + MERGED @`9402bba`** (axiom-clean, no sorryAx;
  the r>0 prodAux telescoping CLOSED — fm de-risked the algebra + delegated the HEq cast-wrangling to a
  formaliser + reviewer subagent; statement byte-identical; rv-2 re-auditing). Critical-path rung DONE (feeds
  D1). Skeleton sorry 10→9. **fm now on #19 proof** (genuine lambdaCore, ~200-line balanced-split exchange).
- **pp (design)** — R1 design DELIVERED + 2 increments (binding-divisor correction; value-match downgrade).
  Standing down on-demand; re-engage for R1 value-match execution when fm's L1 lands.
- **rv-2 (review)** — green-gating keystone d7b1ba3; queued: re-audit the hr-corrected contract. Decorrelated.

## Integration topology (current)
expedition/aoyagi-full = integration trunk (fm-2 commits here directly). worktree-rung0-defs = fm's Skeleton
branch (I merge → expedition). Files DISJOINT (fm-2: ParamsFlat/Case111; fm: Skeleton) — contract change is
Skeleton-LOCAL (verified: no refs to deepestPoint/headline/L2/D1 outside Skeleton). Merges are clean. MAIN
working tree has no Lean WIP between fm-2 commits. Controller green-gates via rv-2 (isolated builds) to avoid
the shared-tree build race.

## PROOF-MODULE PATTERN (S1.1+) — eliminates Skeleton contention
Heavy rungs that are Skeleton sorries are proven STANDALONE in Foundations modules, then I WIRE each into
Skeleton single-writer (`exact <lemma> …`, verbatim statement). S1.1 `weightedThreshold_transport` →
`Foundations/S1Transport.lean` (fm-2, option B approved); S1.3/4/5 likewise if fm-2 takes them. Result: fm
owns Skeleton's INLINE rungs (deepestPoint, #19 lambdaCore); fm-2 owns Foundations PROOF-modules; I do the
1-line Skeleton wires at integration. Zero fm↔fm-2 Skeleton collision + it's the per-rung modular split
(build-time), done as-needed rather than big-bang. The wired lemma's statement must match Skeleton's verbatim.
**Refinements (rv-2 full-trunk catch @92a1101):** (1) the proof-module lemma gets a DISTINCT name (`_aux`/
`_impl`) — same FQN as the Skeleton contract decl = duplicate-declaration landmine at wire-in; wire =
`Skeleton.<rung> := <rung>_aux …` (verbatim statement still unifies). (2) a Foundations proof-module is
ORPHANED from the root `DLNFibre.lean` closure until wired (Skeleton imports it) — so the DEFAULT
`lake build DLNFibre` SKIPS it (gate WIP via explicit module-builds; `scripts/sorries` globs so counts it,
but the root build doesn't compile it). The FULL-trunk `lake build DLNFibre` (not module-scoped) is the gate
that catches orphans + collisions — run it at integration, not just the module build.

## 10th fidelity issue — S1.1 bare equality FALSE (analytic-implication gap; fm-2 caught @6dbc880)
The bare-hypothesis Skeleton `weightedThreshold_transport` EQUALITY is FALSE — the reverse `≥` fails two ways:
(1) **surjectivity gap** (w*∉range π ⟹ π⁻¹{w*}=∅ ⟹ RHS=⊤≠finite LHS) → needs `hsurj : Surjective π`;
(2) **Luzin-N gap** (hderiv off-E doesn't make π(E) null; a Cantor-staircase π sends null E→positive π(E), an
F-singularity there adds LHS mass the off-E CoV misses) → needs `hImE : volume (π''E)=0`. The Skeleton
docstring ASSUMED "π(E) null via Luzin-N" but the hyps don't encode it (Mathlib Luzin-N needs DifferentiableOn
ℝ π E). **NEW CLASS** — not a domain-corner (the sweep cleared S1.1's corners) but an analytic-IMPLICATION gap
(hyps don't imply the conclusion), only the proof attempt surfaces it — even on the IsAddHaarMeasure-pinned
statement. fm-2 ESCALATED (didn't silently fix) + delivered both sorry-free: `weightedThreshold_le_transport`
(unconditional ≤) + `weightedThreshold_transport_of_surjective_image_null` (full = under hsurj+hImE, conclusion
defeq Skeleton). FIX: add hsurj+hImE to Skeleton S1.1 (LOCALIZED — doesn't ripple to D1/L2/R1 statements, which
don't expose π; their PROOFS supply the hyps, both hold at the R1 resolution use-site: chart surjective +
exceptional divisor null). Pending rv-2 decorrelated confirm (7th/9th protocol) → fm wires
(`exact …_of_surjective_image_null` + import + the 2 hyps, Skeleton single-writer). R1 design note: R1's
per-chart S1.1-transport invocation must supply hsurj (chart onto nbhd) + hImE (exceptional divisor null).
**rv-2 CONFIRMED (decorrelated + Codex)** both gaps (π=exp surjectivity; π=id+Cantor-staircase Luzin-N) +
fm-2's 2 lemmas PASS; Codex Q3 resolved (hsurj+hImE COMPLETE, no 4th gap). Executing: fm wires S1.1 (+ S1.4).

## S1 batch status (proof-module pattern, fm-2 owned modules → fm wires)
- **S1.1** `weightedThreshold_transport_aux` (S1Transport.lean @20ab62a) — PROVEN under hsurj+hImE (10th issue,
  CONFIRMED). fm wiring (add 2 hyps + `exact` + import; also resolves orphan FLAG 1).
- **S1.4** `rlct_germ_local_aux` (S1Local.lean) — PROVEN, bare statement SOUND (no gap). fm wiring (`exact` + import).
- **S1.3** `rlct_unit_invariant` — **11th fidelity issue:** bare statement FALSE without `Measurable u`
  (non-measurable u → u·F non-measurable → not Integrable → rlctAt=sSup∅=0 ≠ rlctAt F). Fix `Measurable u`
  **rv-2 CONFIRMED** (decorrelated + Codex; Vitali-set counterexample, `IntegrableOn⟹AEStronglyMeasurable`
  crux Lean-verified). `AEMeasurable u` is the minimal hyp but `Measurable u` is the contract choice (cleaner,
  use-site-safe — analytic unit continuous). fm-2 PROVEN `rlct_unit_invariant_aux` under it (S1Local.lean,
  axiom-clean); fm wires (add Measurable u + exact). **All 3 S1 _aux ready to wire: S1.1/S1.4/S1.3** (fm batch).
- **S1.5** `rlct_additive_smooth_block` — **12th fidelity issue (DEEPER):** the disjoint-block additivity is
  FALSE two ways (non-measurable G [gap-class]; G≡0 ⟹ rlctAtOn(0²)=⊤ ⟹ RHS=n/2+⊤=⊤≠LHS [≡0-convention]) AND,
  even fixed, needs heavy Laplace-asymptotic machinery (Mathlib-gap); can't be cited. fm-2 delivered the honest
  substrate @`2cb79cc` (sorry-free: `rlctAtOn_zero_eq_top` [also discharges #24 docstring], `smoothBlock1D_rlct`
  n=1; the false aux NOT carried as a sorry). rv-2 confirming the counterexamples. **L2-ARCHITECTURE STRATEGY
  routed to pp** (additivity-with-hyps vs R1-on-full-loss-subsumed vs smooth-block-alone restatement — how L2
  combines regular ⊕ core). fm-2 proving the smooth-block VALUE `rlctAtOn(Σxᵢ²)=n/2` (general n, needed
  regardless; Mathlib-gap radial integrability). This is a design node, not just a hyp-gap.
  **RESOLVED (pp + Codex, l2-architecture-card):** DROP additivity AND R1-on-full-loss (the latter needs mixed
  principalization of (x,m) — heavier; F=Σx²+core is a SUM not monomial×unit). **Restate S1.5 to the
  smooth-block FUBINI LEMMA:** `rlctAt(Σxᵢ² + core)` in a core normal-crossing chart `= n/2 + min_j(h_j+1)/(2k_j)`.
  PROOF LIGHT (no Laplace): `∫(|x|²+s)^{-c}dx = C·s^{n/2-c}` (radial x=√s·ρ, Beta, finite iff c>n/2) + Fubini
  (s=core≥0) ⟹ core RLCT at shifted exponent ⟹ n/2 + λ_core. Chart-form core=monomial is nonzero-a.e. +
  measurable ⟹ dodges BOTH gaps by construction. APPLIED PER-CHART in R1: λ_full = min_chart(n/2 + λ_core) =
  n/2 + ½ min_t Mval. So L2's regular⊕core = Fubini-lemma + R1-core-resolution + min-over-charts (NOT a
  standalone additivity). fm-2 proving the Fubini lemma; fm restates+wires Skeleton S1.5.
  **Fubini ROUTE (fm-2's call):** the smooth-block case is genuinely CLOSED-FORM (NOT Laplace — Laplace only
  for general both-arbitrary additivity, not ours). Route B (iterated-1D: n=1 Fubini `∫(x²+s)^{-c}=C·s^{1/2-c}`
  iterated, stays on Params-flat product measure) likely cleaner than Route A (radial via
  `integrable_fun_norm_addHaar` [Mathlib HAS it, corrects the earlier gap-flag] + EuclideanSpace-Haar bridge).
  **UPDATE: general-n single-block n/2 PROVEN** (`smoothBlockND_rlct` rlctAtOn(Σxᵢ²)=n/2 on EuclideanSpace,
  S1SmoothBlock.lean @505e0a2, axiom-clean, 201 LoC — the Mathlib-gap was NOT real, radial `integrable_fun_norm_addHaar`
  + ball-truncation + rpow-iff). The FUBINI lemma (the +core combination = n/2+λ_core) is the s>0 EXTENSION of
  that radial machinery (`∫(‖x‖²+s)^{-c}=C·s^{n/2-c}`, Fubini, + monomial-core threshold) — CLOSED-FORM (NOT
  Laplace), in flight (fm-2). S1.3 also PROVEN + ON TRUNK now (S1Local 0-sorry @505e0a2).
  **FUBINI DE-RISK (fm-2 SPECIFY + Codex):** the exact radial identity holds ONLY at ε=∞; finite-ε (RLCT nbhd)
  is asymptotic-only + Mathlib has NO parametric radial integral. So directions SPLIT: ">=/integrability LIGHT"
  (a.e. comparison + Integrable.mul_prod + radial_ball_iff, ~4-6 sublemmas); "<=/non-integrability" (the CUSP
  lower bound — pp re-adjudication SHAVED to ~5-7 sublemmas via EXACT ball-volume `vol{‖x‖²≤s}=V_n·s^{n/2}`
  [measure_ball/addHaar_ball — NOT a parametric radial integral, dodges the gap]; monomial divergence finish).
  **≥ DIRECTION DONE (fm-2, S1Fubini.lean, 110 LoC, axiom-clean, module-green 2676):** `cmpF` (split engine
  `(s+t)^{-(a+b)}≤s^{-a}t^{-b}`) + `joint_integrableOn_weighted` (a.e. cmpF comparison + Integrable.mul_prod +
  volume_eq_prod). rv-2 PASS (#40, axiom-clean, right condition, hGne faithful). Off-Skeleton; controller wires
  into the aggregator at the equality. **≤ DIRECTION fully de-risked** (every atom + Step A `[‖x‖²≤G](2G)^{-c}w ≤
  |F|^{-c}w` handling BOTH G>0 antitone + G=0 hygiene-corner, cuspVol exact `vol{‖x‖²≤s}=ofReal(√s^n)·Vₙ`,
  notIntegrable_rpow, joint_lintegral_top sig — all in scratch; remaining = mechanical Tonelli + factor +
  hcore_top⟹⊤). **STATEMENT-SHAPE DECISION (load-bearing, supersedes the (i)-vs-(ii) routing Q AND the card §B
  "explicit monomial core"): (A) ABSTRACT-CORE SHIFT THEOREM.** fm-2 found the standalone multivar monomial
  divergence `∫_box ∏|y_j|^{a_j}=⊤` is NOT the ~30-LoC elementary fact first estimated — Mathlib has the pi-product
  factorization only for the FINITE/integrable case, not a lintegral=⊤ divergence (custom pi-Tonelli = heavy).
  So BOTH the standalone build (heavy) and S2-reuse (axiom-import) are dodged by stating S1Fubini ABSTRACTLY:
  `rlctAt(Σxᵢ² + core) = n/2 + rlctAt(core)` — the pure "+Σx² shifts the RLCT by exactly n/2" shift theorem, with
  the core's integrability (≥, hGne+hy) and divergence-at-shifted-exponent (≤, hcore_top) as EXPLICIT hypotheses
  (symmetric, honest, dodge both 12th-finding levers by construction). The monomial+S2 obligation MOVES to R1's
  per-chart use-site: R1 supplies rlctAt(core)=S2's ⨅axisRatio for its resolved monomial, and hcore_top follows
  from that value by the sSup definition (NO hand-built multivar integral). Strictly cleaner — S1Fubini stays
  axiom-clean + monomial-machinery-free, the shift is its sole content, and S2 lands exactly where it belongs
  (the monomial RLCT). pp confirming the R1 use-site discharge (3 hyps + cover-composition) in parallel. **λ_core=0
  EDGE (rv-2):** the c=a+b split (b>0) covers c<n/2+λ_core only for λ_core>0; the λ_core=0 regime routes through
  `smoothBlockND_rlct` (=n/2) directly — fm-2 handles in the equality-lift (likely vacuous at the deepest point
  where the core is genuinely singular, but kept general). The <= IS NEEDED (R1 UPPER = binding-chart divergence;
  S2 alone doesn't cover the SUM Σx²+monomial — +Σx² shrinks the integrand so divergence is non-trivial). So R1
  is heavier than first scoped (Fubini-per-chart + multiplicity-control R1.2 + cover R1.6) but all designed +
  tractable, and the abstract shift makes the Fubini-per-chart step a clean plug-in.
**Use-site obligation (tracked):** hsurj+hImE (S1.1) + Measurable u (S1.3) must discharge at D1/R1 (resolution
charts: surjective onto nbhd, exceptional-image null, analytic unit measurable). The bare-under-specification
gap-class is RECURRING across the analytic rungs — caught reliably by the proof attempts + escalation.

## R1 design BANKED (pp, thread 14) + R3b DECISION + value-match DOWNGRADE
- **Value/atlas split.** VALUE `rlctAt(‖∏C‖²)=½·min_t Mval(t)` (pinned by codim S(t)=Mval, thread-03) vs
  explicit CHART ATLAS (Aoyagi affine blow-ups).
- **Binding-divisor mechanism** (pp self-corrected the wrong "telescoping" framing): per branch, ONE blow-up
  of the residual-block-zero center (codim EXACTLY Mval(t)) is the binding divisor (k,h)=(1,Mval−1), ratio
  ½·Mval; min over branches = ½ min_t Mval = λ. (Telescoping per-rank-drop would give ½·min(cᵢ) = TOO SMALL.)
- **VALUE-MATCH DOWNGRADE (pp §8, verified L=3):** the headline's value-match does NOT need the full atlas —
  only the minimizing branch's binding divisor, produced by **iterated L1 to the residual block (REUSES fm's
  L1 + deepestPoint_exists machinery)**. Route: (i) iterate L1 → codim-Mval residual block; (ii) residual =
  codim-Mval coord subspace (thread-03); (iii) blow up → divisor-ratio lemma → ratio ½·Mval [UPPER bound,
  L1-reuse, cheap]; (iv) cover/exhaustiveness inequality over strata [LOWER bound, the residual real work].
  Full normal-crossing atlas DEFERRED (only to strengthen the statement beyond value-level). R1's "mountain"
  status partly downgraded.
- **Residual-block claim NAILED (pp §8, general-L; verified L=2,3,4 + decorrelated Codex):** after the
  pivot split, the residual cutting S(t) is a REGULAR SEQUENCE of length EXACTLY Mval(t) — not
  over-determined (the full interval rank-pattern r_{ab}, a≥2, adds NO independent generators; inner
  constraints are CONSEQUENCES), not coarser. So {residual=0} is a clean smooth codim-Mval(t) coordinate
  subspace ⇒ binding divisor (k,h)=(1,Mval−1), ratio ½·Mval(t), rigorous at general L. STRUCTURE: the
  residual is NESTED Schur-blocks R₁..R_L (R_j = D_j−C_jA_j⁻¹B_j per layer), `S(t)∩chart = {R₁=…=R_L=0}`,
  Σ|R_j|=Mval — jointly coordinates ⇒ one smooth center. CAUTION: a final-PRODUCT residual alone cuts the
  COARSER {∏=0} (union over profiles), NOT S(t) — must use ALL R_j. CAVEAT (Codex): ratio ½·Mval holds at a
  GENERIC point of the minimizing stratum (nongeneric suffix-vanishing points need more blow-ups but don't
  affect the value-match). pp self-caught + dropped a wrong "inner intervals stay generic" sub-claim (what
  holds is codim=Mval exactly, which is all the mechanism needs).
- **Codex correction adopted:** prefix-stratum partition right for the VALUE but too coarse for a literal
  atlas (charts refine by full rank-pattern); R1↔Adm is VALUE-level, NOT a chart bijection.
- **R1 LOWER BOUND + complete decomposition (pp, done) — MULTIPLICITY-CONTROL finding (pre-execution catch):**
  UPPER (≤ ½ min Mval) = ONE binding-divisor chart (cheap, L1-reuse). LOWER (≥ ½ min Mval) needs the FULL
  cover + a sharp finding: **the lower bound CANNOT come from codim alone** — the divisor ratio `(h_E+1)/(2k_E)`
  depends on F's VANISHING ORDER k_E, not codim (counterexamples: `rlctAt(x^{2k})=1/(2k)<½·codim`; `(x²+y²)²`:
  1/2≠1). So **R1.2 = MULTIPLICITY CONTROL** (`h_E+1 ≥ k_E·min Mval` per divisor), HOLDS for our core via
  regular-sequences⟹k_E=1 but PROVEN per-divisor, NOT a codim shortcut. DECOMPOSITION (execution-ready): R1.1
  chart family[L1] + R1.2 multiplicity[NEW] + R1.3 codim=Mval[thread-03] + R1.4 Fubini-per-chart + R1.5
  S1.1-min-over-cover + R1.6 cover/exhaustiveness[NEW] + R1.7 S2. NEW lifts = R1.2 + R1.6 (the real lower-bound
  work). Route: complete explicit resolution + per-divisor monomial check (one-citation-clean); SoS+codim DEAD.
  Subtleties: strata-not-components (Z=⋃S(t)); local-vs-global codim (origin sees min Mval); properness (w/ S1.1).
  pp+fm EXECUTE when S1.1+Fubini land (close); R1.2 first.
- **DECISION R3b** (self-contained, one-citation). R3a (cite LR `rlct=codim/2`, arXiv:2411.19920) OUT:
  violates one-citation scope (codim = THE new content) + Aoyagi-independence. Surfaced to operator as
  informational/override-able.
- **No hidden hypotheses** (Codex §4): char-0, positive widths, r≤H s (=the hr fix). Toric/Newton route DEAD.

## WIN — λ-citation ELIMINABLE — now DEMONSTRATED END-TO-END (bridge @`b342cd2`)
The (1,1,1) bridge `case111_rlct_eq_monomialThreshold` is CLOSED sorry-free (fm-2) ⇒ **`case111_rlct` is the
FIRST fully sorry-free + axiom-free end-to-end RLCT result** (`#print axioms = [propext, Classical.choice,
Quot.sound]`, NO sorryAx, NO monomial_rlct, NO native_decide). So λ is PROVABLY axiom-free for (1,1,1) — the
WIN is no longer just probed, it's demonstrated. General case = labour (no wall). Reviewer-agent fidelity
survived; rv-2 green-gating decorrelated. **Banked REUSABLE S1.1 infra (general in H):**
`continuous_paramsEquivFlat`/`_symm` (flattening is a HOMEOMORPHISM), `prod_paramsEquivFlat` (coord-product
preserved), `prodBoxSymm_rpow_integrableOn_iff` (2D 𝓝0 box-iff) — feeds the real S1.1 + R1. Only θ-order
stays the genuine analytic seam (S2 order-half).

## #19 genuine A1 statement — MERGED to trunk @`7986597`, rv-2 PASS, GREEN
Weak free-choice existential REPLACED by pp's candidate-d: `∃ c ≤ L, 1 ≤ c ∧ lambdaCore M = cleanCore c
(sortedSmallest M c)` (m PINNED via `sortedSmallest` = M's c+1 smallest reduced widths). **rv-2 PASS** (genuine
per discriminator; matches pp's ACHIEVER, NOT an extremum — verified 19600 cases, min_c/max_c refutations
reproduced; sortedSmallest faithful). 8th issue resolved at the STATEMENT level on trunk. Skeleton compiles
green (2534 jobs). Proof = sorry (~200-line balanced-split exchange, off-critical-path) — fm sinking it next
(gate OPEN). **Skeleton sorry 9→10 — correct + honest: a genuine sorry replaced the vacuous weak PROOF.**
Also merged: deepestPoint r=0 + Dblock_rank (r>0 telescoping still sorry, fm's). Cosmetic lints in fm's code
(show→change @534, deprecated Finset lemma @706, <;> @738) — non-blocking, fm cleans on next touch.
**#19 PROOF progress:** Step 1 `balancedSplit_min` PROVEN (balanced split minimises Σq²; e9e251d, reusable).
ROUTE-GAP found (proof attempt, again): card step-3 "per-c lower bound" was the FALSE `min_c` reading
(cleanCore NOT monotone in widths — `[1,2,4]`vs`[1,2,7]`: 2 vs −2; min_c/max_c refuted) — STATEMENT still
correct+total, only the ROUTE needs reframing to: per-T bound on T's OWN breakpoint widths (via balancedSplit_min)
+ **PERM-INVARIANCE of lambdaCore** (`lambdaCore M = lambdaCore M∘σ`, ~200-line Adm-cone exchange) + sorted-M.
#19 OFF the headline path — fm doing the S1 WIRES (S1.1/S1.3/S1.4, critical-path) FIRST.
**#19 keystone PARKED (decision d):** fm probed it — perm-invariance of lambdaCore is a MIN-LEVEL no-bijection
wall (Adm cones + Mval-multisets genuinely DIFFER under σ — 560/1700 & 1140/1700; holds only AT the min ⟹
multi-hundred-line explicit minimizer characterization, no slick transport). OFF-headline-path (headline uses
aoyagiLambda's min-def, closes sorry-free WITHOUT #19's proof). **THEN UN-PARKED via ROUTE B (fm, 2df8bf4):**
cleanCore depends only on the width MULTISET (Σm², Σm symmetric), so #19 needs NO global perm-invariance — a
LOCAL achiever analysis (T* breakpoint-multiset = sortedSmallest, via multiset-symmetry) + the per-T lower
bound (balancedSplit_min, DONE) suffices. ~200 lines, perm-invariance-FREE (avoids the wall, not solves it),
3900/3900. **pp VALIDATED + reframed (a1-route-reframe.md):** perm-inv = COROLLARY of the sorted-form
characterization (`lambdaCore M = lambdaCore (sort M)`), NOT proven via the Adm-cone bijection (saves the
beast). Residual hardness = the SMALLEST-WIDTHS-FORCING sub-lemma (on sorted M the minimizer's breakpoint
widths = the ℓ*+1 smallest, FORCED over every T via the `(M^S−H)` factors) — MUST be per-T-over-Adm-cone, NOT
a widths-extremum (exactly where the false min_c lived; the trap). UPPER (achiever) + LOWER (per-T
balanced-split + forcing). fm executing route B. So #19 is now a clean bounded build. fm sequence: wire
S1.1+S1.4 → #19 route B → R1/L2/D1
(critical-path beats off-path as Fubini lands for R1).

**S1 WIRES — S1.1 + S1.4 CLOSED + GREEN-GATED on trunk @`7258a36` (fm `aacdc7a`, FF-merged + full `lake build
DLNFibre` GREEN, 2855 jobs).** Skeleton sorry 10→7. Both rungs INDEPENDENTLY axiom-clean (controller `#print
axioms`): `weightedThreshold_transport` (S1.1, +hsurj+hImE [10th]) and `rlct_germ_local` (S1.4) = `[propext,
Classical.choice, Quot.sound]` — no sorryAx, no monomial_rlct. Orphan FLAG resolved for S1Transport+S1Local
(now in Skeleton's import closure). **7 remaining sorries:** S1.3 rlct_unit_invariant (138 — wire next,
Measurable u [11th] blessed + _aux proven), S1.5 rlct_additive_smooth_block (169 — awaits fm-2's Fubini lemma),
L2 (882), D1 (896), R1 (921), #19 lambdaCore (1055), A2 (1196). rv-2 auditing S1.1/S1.4 + the Fubini ≥ half.
NEXT (fm): wire S1.3 → then D1 `deepest_point_reduction`. S1Additive/S1SmoothBlock/S1Fubini stay orphans until
S1.5/L2 wire them (controller adds S1Fubini to the aggregator at that point).

**#19 CHECKPOINT (fm @`88cf38e`, worktree-rung0-defs) — ENGINES PROVEN + ROUTE CORRECTED + KEYSTONE PARKED (decision b).**
Two engines axiom-clean: `balancedSplit_min` (lower-bound engine `Σ balancedSplit² ≤ Σqᵢ²` at fixed sum;
re-derived solid after trunk syncs, `43b443e`) + `cleanCore_perm` (cleanCore multiset-symmetry, route-B crux,
`cfeec6f`). **ROUTE CORRECTED AGAIN (fidelity catch, now in the lambdaCore_eq_clean docstring):** the route-B
"per-c lower bound / min_c" framing is FALSE (M=[1,1,4]); AND Codex's first "single-c achiever rule
(aᵢ ≤ ⌈Sᵢ/i⌉)" is ALSO FALSE (278/3900 fail). The CORRECT rule (0 failures exhaustive widths 0..3 L≤4 +
3900/3900 widths 1..5): `c* = largest c with the CUMULATIVE predicate ∀1≤i≤c, aᵢ ≤ ⌈Sᵢ/i⌉` on sorted M, plus
the exact per-T identity `Mval = Σₖ gapₖ·(wₖ−Hₖ)` over strict-descent positions. **KEYSTONE PROPER = a dedicated
multi-session lift (~250-350 lines), NOT a bounded sub-thread:** two sub-lemmas on unsorted M — (1) per-T lower
bound (descent-set **dependent-Fin reparametrisation** of each T + complete-square + balancedSplit_min) +
(2) achiever construction + Adm-membership. The dependent-Fin descent reindexing is the genuine hard bulk (the
minimizer's breakpoint widths aren't literally sortedSmallest — they coincide only at c*; the "perm-invariance
wall" persists at this level). **DECISION (b): PARK the keystone, ROADMAP it** — it is WELL-SET-UP (genuine
statement + 2 engines + corrected cumulative-predicate route all banked → a dedicated tide later, after the
headline / when capacity); #19 is OFF the headline path (headline uses aoyagiLambda's min-def directly). **fm
PIVOTED to CRITICAL-PATH:** S1 wires (S1.1/S1.3/S1.4) → D1 `deepest_point_reduction` → R1 EXECUTION (with pp,
when Fubini lands) → L2 → T. Bounded #19 engine-nibbling (e.g. the per-T Mval identity) is FILL only, never over
the critical path.

**#19 ROUTE ADVANCE (fm @`85b0077`, supersedes the dependent-Fin descentSet plan — much cleaner):** the
**EDGE-VARIABLE TRANSFORM** `q_j = M⁽ʲ⁺¹⁾ + (u_j − u_{j+1})` on the FIXED level sequence — a fixed-`Fin L`
reparametrisation, NO dependent-Fin descentSet reindex (that was the hard bulk; dissolved). Exhaustively verified
(0 failures L≤4). NEW engines axiom-clean: `karamata_sq` (Karamata-for-squares via Abel summation, general/
reusable), `edge_identity` (`2·Mval = Σ(edgeQ)² − Σ(Mseq)²`), + QFeasible positional prefix bounds (Adm ⟹
QFeasible). **#19 now reduces to ONE clean gate** (in the docstring): the **smallest-k-sum majorization**
(`∀k, Σ(k smallest edgeQ) ≤ Σ(k smallest Y)` ⟹ karamata_sq). Mathlib v4.29 has NO Karamata/Schur/k-smallest API
(confirmed) ⟹ ~150-250 lines new combinatorics; proven irreducible (pointwise-after-sort FALSE q=[1,3]vs[2,2];
prefix/tail split undershoots — convexity essential). **STILL PARKED (decision b, reaffirmed 3rd time):** the gate
is a DEDICATED TIDE LATER (after the headline), even better set-up now (edge-transform + karamata_sq + QFeasible
all banked = one self-contained majorization theorem). fm REDIRECTED to the pending critical-path Skeleton tasks
(S1.3 wire + the 13th-finding restatement, which it had skipped for this #19 work) → then D1. Process note logged:
don't dispatch sub-formalisers per task (seat-reuse) + no further cycles on parked #19.

## Measure-side architecture — ROUTE A++ (DECIDED; now ACTUALLY green)
Matrix-wall paid-ONCE + contained by interface discipline. `Params.volume`=nested Measure.pi is **rfl**; fiber
instance = section-local `instance` (NOT a global Matrix instance, NOT a goal-type `letI` — elaboration order).
**Σ-form throughout via `piCurry.symm`, never `curry`/`×`** (`MeasurableEquiv.curry` has NO measurePreserving
companion in Mathlib; `piCurry` does); final reindex `Σ…≃Fin N` via `equivFin`; `measurePreserving_pi` =
piCongrRight MP, pass μ,ν explicitly. (pp corrected an earlier overclaim — it had verified type-level +
individual lemmas but the MP body was sorry'd; now the FULL body compiles EXIT=0 v4.29. Decision unaffected,
firmer.) These gotchas are REUSABLE for S1.1 + R1 measure facts. Downstream states facts on `Fin N → ℝ`, pulls
back via `integrableOn_comp_preimage` — never re-touch Matrix.

## Rung map (scoped)
- DONE: keystone paramsEquivFlat (d7b1ba3); A1 clean_eq_printed (c234651, to merge).
- NEXT (fm): hr statement-fix [contract-critical] → lambdaCore_eq_clean → L1 → deepestPoint_exists proof.
- NEXT (fm-2): (1,1,1) bridge (#12) → then S1.1 (heavy) + S1.3/4/5.
- THEN: L2 (needs L1+S1.5) · D1 (needs S1) · R1 value-match (needs L1 + S1.1; pp re-engaged) · A2 (θ-seam, post-R1).
- Assembly T: assembles from D1+L2 (+ hr threaded).
- Two hard builds remain: S1.1 + R1's cover-inequality (lower bound).

## STATUS @ 2026-06-21 ~01:30 (trunk @c32b694; Fubini @e2a3f0c)
- **S1 WIRE BATCH COMPLETE — S1.1/S1.3/S1.4 ALL CLOSED + green-gated + axiom-clean** (@c32b694; build green 2855,
  Skeleton 6 sorries; rv-2 PASS on S1.1/S1.4, S1.3 audit queued). The S1 transport/locality/unit substrate is DONE;
  only S1.5 (Fubini) remains of S1. 6 sorries: S1.5, L2, D1, R1, #19, A2.
- **R1 EXECUTION LAUNCHED** (pp leads math, fm formalises): pre-Fubini parts first — R1.1 chart construction
  (L1-reuse) + R1.2 multiplicity-control (`h_E+1 ≥ k_E·min Mval` per divisor, NOT codim shortcut); R1.4
  (Fubini-per-chart) plugs fm-2's shift theorem when the lift lands; obligations folded in (unit-absorption via
  S1.3, hcore_top endpoint, min-over-cover factorises n upstream-fixed). The mountain.
  - **R1.2 ROUTE — VERDICT: route B REFUTED → route-A-CONCRETE (pp + decorrelated Codex, INDEPENDENTLY IDENTICAL +
    witnesses).** ⚠️ CORRECTS my prior "L1-pivot charts resolve it" bank — that reading is WRONG. **THE DECIDER:**
    a residual product of length q≥2 has ‖∏C̃‖² with ordinary VANISHING ORDER 2q (NOT 2); regular changes (= L1)
    PRESERVE ordinary order ⟹ **L1-alone can NEVER expose the core as a smooth coordinate-square block** (route B
    is FALSE). The product-structure concern I gated on was REAL + it KILLS B. WITNESSES: (1,1,1) F=c₁²c₂² (monomial
    NC, only easy case); (1,2,1) F=(a₁b₁+a₂b₂)² (singular quadratic cone, first non-monomial); (2,2,2) F=‖AB‖²
    ord_0=4, Hessian ZERO, codim-3 irreducible, rlct=3/2 via radial/angular blow-up. So a **genuine BLOW-UP is
    REQUIRED + multiplicity-control is NON-VACUOUS** (k=1 on the EXCEPTIONAL divisors, post-blow-up, via the
    pos-def-REAL initial form — over ℂ fails at (x²+y²)²). **BUT not the abstract-infra mountain: route-A-CONCRETE**
    = explicit POLYNOMIAL blow-up charts (A=tA'; (2,1,2)=(x,xy,z,zw); etc.) with vanishing Jacobian on the
    exceptional locus, **S1.1 carrying the change-of-variables** (its hsurj+hImE hyps are EXACTLY for the blow-up's
    non-injectivity / null exceptional image — the 10th-finding design was built for this). NO Mathlib blow-up
    primitive. R1 = MEDIUM (explicit-poly-chart resolution + S1.1 + non-vacuous mult-control + cover). fm: do NOT
    build (B); the validate-small φ's (φ=id (1,1,1); explicit-poly (2,1,2)/(2,2,2)) ARE route-A-concrete charts.
    Codex sharpenings folded: (#2) R1.2 stays BARE (divisor inequality), assembly
    applies 1.unit-absorption → 2.monomial_rlct → 3.R1.2 → 4.S1Fubini SEPARATELY; (#3) Mval = CORE codim (reduced
    widths), assembly = **n/2 + B/2** (don't double-count the regular n). **fm seeded with R1.2a/b** (axisRatio
    arithmetic, zero-dep) + the route-independent (1,1,1) gate (xcheck vs `case111_rlct`); pp designing R1.1 charts
    validate-small-first ((1,1,1)→(2,1,2)→(2,2,2), symbolically verified). Climb order: R1.2a/b → R1.3 codim →
    R1.1 charts → R1.6 cover → assembly.
  - **14th FIDELITY FINDING (pp, load-bearing) — `resolution_charts` ORPHANED + MIS-SCOPED → RE-SCOPE to CORE
    (controller APPROVED):** (1) it's consumed by NOTHING (product_reduction doesn't call it ⟹ R1 was about to be
    built proven-but-unplugged); (2) it states the FULL-loss RLCT = ⨅ monomialThreshold (a MIN), but the full-loss
    RLCT = n/2 + ½·min Mval (a SUM — the reg n/2 is ADDITIVE via Fubini, not a min-direction) ⟹ FALSE for r>0; the
    (1,1,1) validate case had r=0 (n=0) so it didn't exercise the reg-term. FIX: re-scope to `rlctAt(core) wstar =
    ⨅ monomialThreshold` (R1's genuine content), and WIRE the assembly into product_reduction:
    `dlnLoss(deepestPt)` →[block_elimination] reg⊞core →[S1Fubini] n/2+rlctAt(core) →[resolution_charts(core)]
    n/2+⨅monomialThreshold →[A1] n/2+½·min Mval = aoyagiLambda. Clean separation: **R1 = core resolution; L2 =
    the assembly (split+Fubini+R1+A1); A1 = arithmetic.** The re-scope is REQUIRED for composition (S1Fubini takes
    rlctAt(core)). pp pins the corrected stmt + the `core` (∏C^(s)) object → fm restates + wires product_reduction;
    R1.1 charts resolve the CORE ‖∏C‖² (NOT full dlnLoss). Supersedes the stale-docstring item (whole stmt re-scoped).
- **S1.5 restatement+wire deferred to ONE pass** at fm-2's Fubini lift-close: I relay the complete signature
  (hGmeas + hGne + `[ProperSpace]`/`[IsFiniteMeasureOnCompacts]` instances) → fm restates + wires `exact` in one go.
- **FUBINI n=1 EQUALITY PROVEN** (fm-2, S1Fubini.lean @e1cf73c, 564 LoC / 17 thms, ALL axiom-clean): `step_rlct :
  rlctAtOn(x²+H)(0,y0) = ½ + rlctAtOn H y0` (H≥0, Measurable H, hHne germ-a.e.≠0; core space ProperSpace +
  IsFiniteMeasureOnCompacts). The **hardest analytic content of the whole expedition is DONE** — both directions:
  ≥ (step_rlct_ge: integrability split + sSup-lower-bound, ENNReal split idiom, admissible_downset); ≤
  (step_rlct_le: the cusp — step_lintegral_top contrapositive + core_adm_of_joint_adm open-witness wrapper via the
  {H≤R²}∪{H>R²} split; NO continuity needed for measurable H, the resolved subtlety). Measure-route B (1-D
  interval vol, no addHaar/EuclideanSpace bridge — lighter; cusp proven ONCE + reused per induction). **✅ S1.5
  ENGINE COMPLETE @ad1f313 — `rlct_additive_smooth_block_aux` (general-n shift `rlctAtOn(Σxᵢ²+G²)=n/2+rlctAtOn(G²)`)
  DONE + controller-VERIFIED axiom-clean (builds 2644 jobs, [propext,Classical.choice,Quot.sound], no sorryAx / no
  monomial_rlct).** The HARDEST analytic content of the expedition is proven (both dirs + cusp + down-set + sSup +
  λ_core=0 + the finPeel/chartN measure-preserving iteration). Minor: unusedSectionVars lint on [BorelSpace Y]
  (cosmetic). REMAINING for S1.5: fm wires `exact rlct_additive_smooth_block_aux` into the restated Skeleton
  statement (Skeleton-import pulls S1Fubini into the closure) → green-gate → rv-2 audit. **The whole S1 analytic
  substrate (S1.1/S1.3/S1.4 wired + S1.5 engine proven) is now COMPLETE.**
- **R1 DIFFICULTY MAP (pp general-atlas design + honest correction):** **R1.3 = LIGHT** — codim is a ℕ COUNT
  identity (∑ residual block sizes = Mval), NOT the determinantal-codim theorem; **Mathlib v4.29 gap GONE**
  (decorrelated-Codex + verified). **R1.1 = MEDIUM** (pivot recursion on L; base L=1 = smooth block via
  smoothBlockND_rlct, step = explicit-poly blow-up + recurse). **R1.6 (general cover) = THE MOUNTAIN** — the
  headline EQUALITY needs the LOWER bound (rlct ≥ ½min Mval), which needs the COVER complete (no missed worse
  divisor; codim-shortcut FALSE per x^{2k}/(x²+y²)², D1 doesn't give per-point LB) ⟹ critical-path, no shortcut.
  pp HONESTLY corrected its own "R1 medium" drift → R1.6 is where the difficulty concentrates; general-M may be a
  GENUINE WALL.
  - **R1.6 SHARP BOUNDARY + HEADLINE-REACH DECISION (pp detailed cover design + decorrelated Codex; controller
    adjudicated):** FIXED-M = INTRICATE-STANDARD, **provable now** (resolution = finite tree depth ≤L−1, unrolled
    to a finite explicit leaf-chart list; cover = finite sum, ONE Mathlib single-c-o-v per leaf; (2,2,2)=24 charts;
    NO recursion infra). GENERAL-M = **RESEARCH-WALL** (decorrelated-identical pp+Codex): n/tree/φ_i depend on M ⟹
    needs the recursion-as-a-theorem = the two missing-infra obligations **G3 (strict-transform tracking over
    arbitrary rank vectors) + G5 (gluing iterated c-o-v into ONE global integral identity; Mathlib has SINGLE
    c-o-v only)**. The cover is UNAVOIDABLE for the lower bound (Codex Q3 FACT; codim-shortcut false).
    **DECISION: (1) fixed-M LADDER near-term + (2) general infra (G3+G5) ROADMAPPED; (3) axiomatize-cover RULED OUT**
    (breaks one-citation / awkward-middle). LADDER (each a complete axiom-clean-mod-S2 headline instance +
    validates a machinery piece): (1,1,1) monomial [no cover] → (2,1,2) **Fubini-PRODUCT** [disjoint vars separate,
    NO blow-up — pp refinement] → (2,2,2) first TRUE cover [24 charts] → up the M-ladder. **DELIVERABLE FRAMING:**
    the full machinery (S1·Fubini·R1-fixed-M·A1·assembly) + the headline PROVEN for ladder cases; the FULLY-GENERAL
    headline = those + the named G3+G5 research obstruction (honest partial, NOT a false general claim). Assessing
    whether **G5 (abstract c-o-v-tree-gluing) is separable + buildable now** as a down-payment on the general lift.
    **OPERATOR SCOPE FLAG:** the general-M headline is gated on the G3+G5 research-infra lift — surfaced for the
    operator's steer (attempt the lift vs deliver ladder+roadmap); proceeding with the ladder meanwhile (no stop).
  - **(2,2,2) FULL COVER CLIMBED + VALIDATED (pp, exact-symbolic):** two nested blow-ups (faithful to Aoyagi
    Lemma 2/Thm 3): step-1 blow up {A=0} (4 charts, x-divisor ratio 2) → Lemma-2 regular split → step-2 blow up
    (3 charts, s-divisor ratio 3/2 = binding). **GENUINE HOLE caught+closed (validate-small working):** the 3
    step-2 charts are NOT uniform — E-/F0-pivot residuals are positive units (clean monomial×unit leaves), but the
    **δ-pivot residual U(origin)=0 is a SMOOTH-4-BLOCK** (v²+w²+G'²+H'²), so the δ-leaf = x²s²·(Σ⁴y²), NOT
    monomial×unit. Closed by CHECKING (not assuming): block rlct = 2 ≥ binding 3/2 ⟹ s-exceptional still binds at
    3/2 = ½·Mval(deepest), θ=1. Cover SOUND. **FIDELITY → Option A (BLESSED, fixed-M):** monomialize the smooth
    block (ratio-preserving — the cone Σⁿy² blows up to exceptional ratio EXACTLY n/2 = its rlct), so RHS
    `⨅ monomialThreshold` stays LITERALLY TRUE + leaves uniform. **DESIGN REFINEMENT:** the atlas has a THIRD
    block-monomialization layer ((2,2,2) is NOT 4×3=12 simple leaves; δ-branch subdivides into a 4-chart Σy²
    blow-up). **A-vs-B for GENERAL-M (open, part of the tractability verdict):** Option A's 3rd layer may COMPOUND
    G3/G5; Option B (block leaves bounded directly via smoothBlockND_rlct+Fubini, no extra layer, heterogeneous
    cover sum) reuses existing machinery — pp weighing as part of the general-M verdict. (2,1,2) confirmed NOT a
    cover (Fubini-product, disjoint vars, rlct=min(1,1)=1=½·Mval — separate small lemma).
  - **LOWER-BOUND SOUNDNESS SETTLED (pp + decorrelated Codex) — the general result is now mathematically PROVEN
    (on paper), so G3+G5 is pure FORMALIZATION labour, NOT open math.** The worry: a weakly-decreasing
    NON-admissible (t_L≠0) stratum with Mval < min_Adm (e.g. (2,2,2) t=(1,1), Mval=1 < min_Adm=3) — if blown up,
    exceptional ratio 1/2 < 3/2 would BREAK the LB. RESOLUTION: on {∏C=0} the product has rank 0 ⟹ **t_L=0 ALWAYS
    on the zero-locus ⟹ non-admissible strata are NEVER centers** (admPred's t_L=0 = "in the zero-locus"); every
    exceptional is admissible, k=1, h=Mval(t)−1, ratio ½·Mval(t), min over Adm ⟹ the bound. So the LB is
    structurally TRUE via the flag-resolution. **Codex Q4 lct-shortcut REJECTED as a trap** (rlct=½·lct(I)): (1)
    real-vs-complex unproven coincidence, (2) 2nd citation + breaks Aoyagi-independence (Lehalleur–Rimányi/
    multiplier-ideals), (3) black-boxes R1's content — cross-check only, NOT a proof path. So the headline-reach is
    now: **general theorem PROVEN on paper (decorrelated-sound); general Lean formalization = G3+G5 construction
    labour (roadmapped); fixed-M ladder formalized.** Operator scope flag refined: the lift is formalization-labour
    of a SETTLED result, not open research.
  - **G5-ABSTRACT SEPARABLE + BUILDABLE NOW (pp, checked vs Mathlib) → wall reduced to G3 alone.** G5 = `∫⁻_U|F|^{-c}
    = Σ_leaves ∫⁻(|F∘φ_i|^{-c})|Jac φ_i|` = [lintegral cover-additivity] ∘ [single c-o-v per chart], by finite
    induction on the depth-≤L−1 tree. Both Mathlib FACTS: single c-o-v = `lintegral_image_eq_lintegral_abs_det_
    fderiv_mul` (Jacobian.lean:1189) — over **lintegral (ℝ≥0∞) ⟹ NO integrability side-conditions** (the key; the
    threshold integrand is ∞ above rlct, ℝ≥0∞ handles it); + cover-additivity. ONE friction (not a wall): the lemma
    wants InjOn (blow-ups injective only OFF the null exceptional) → ADAPTER: apply to chart-minus-exceptional, the
    exceptional is null (`addHaar_image_eq_zero_of_det_fderivWithin_eq_zero`). Intricate-standard, REUSABLE. **DECISION:
    BUILD G5-abstract (assigned fm-2, the measure specialist) — it's needed for the (2,2,2) cover's ∫=Σ∫ anyway (a
    G5-instance), reusable, and ISOLATES G3.** RESIDUAL (honest): **G3 (strict-transform tracking over arbitrary
    rank vectors — quiver-determinantal geometry Mathlib lacks) STILL the genuine general-M research piece**;
    G5-abstract isolates it, does NOT dissolve it. Refined roadmap: **general headline = ladder instances +
    G5-abstract (BUILT) + G3 (named open obstruction).**
    - **#52 SIMPLIFIED (pp, g5-abstract-statement.md): the LADDER needs only the SINGLE-STEP lemma** `∫⁻_U g =
      Σ_i ∫⁻_{V_i\Z_i} |det fderiv φ_i|·g∘φ_i` (finite a.e.-disjoint null-cover) — NO abstract rose-tree datatype.
      The (2,2,2) cover = finite compositions of the single-step lemma (A-blowup 4 ∘ step-2 3 ∘ block 4 = 24
      leaves). The abstract-tree form is DEFERRED to general-M (part of the G3 roadmap, not the down-payment).
      Mathlib anchors all checked (lintegral_image_eq_lintegral_abs_det_fderiv_mul + addHaar_image null + lintegral
      set-additivity); ℝ≥0∞-not-Bochner load-bearing. So #52 is the reusable single-step atom, tractable now.
      SEQUENCING: fm → (2,1,2) [product-MIN, no G5 dep] ∥ fm-2 → #52 single-step; then fm → (2,2,2) instantiates it.
- **13th FIDELITY FINDING (fm-2, proof-attempt-as-audit):** the committed Skeleton `rlct_additive_smooth_block`
  (line 169) is stated BARE (no hygiene on G) and is LITERALLY FALSE — germ-vanishing G² (or G≡0) ⟹ RHS=n/2+⊤=⊤,
  LHS=n/2; Lean-provable from `rlctAtOn_zero_eq_top` (S1Additive:67). The docstring ADMITS false but the SIGNATURE
  is bare = self-contradictory contract (the 12th finding's restatement was documented, never executed in the sig).
  FIX (controller-decided, fm executes single-writer, keep sorry): add `Measurable G` + a germ-non-vanishing hyp.
  **CONTROLLER CALL: hHne (G²≠0 a.e. near y0), NOT fm-2's hGfin (rlctAtOn(G²)<⊤) — hGfin is UNSOUND.** They are
  INDEPENDENT (not equal as fm-2 believed): hGfin admits a FALSE case. AIRTIGHT WITNESS (controller-derived,
  n=1,Y=ℝ,y0=0): G(y)=y·[y>0] ⟹ G²=y²·[y>0]; rlctAtOn(G²)(0)=1/2<⊤ (hGfin HOLDS) but LHS rlctAtOn(x²+G²)(0,0)=1/2
  (the y≤0 slice is pure x², ∫(x²)^{-c} diverges for c≥1/2, CAPPING the joint) ≠ RHS 1/2+1/2=1 ⟹ equality FALSE
  under hGfin. hHne excludes it (G²=0 on positive measure ⟹ ¬hHne). hGfin ALSO over-excludes true cases (G²=1:
  rlctAt=⊤, equality ⊤=⊤). So hGfin is wrong both ways; hHne is the sound hyp AND what fm-2's step_* already carry
  (the H=0 corner + cmpF a.e.-positivity). fm-2 ACCEPTED hHne. **EXACT LOCKED FORM** (relayed to fm; restate
  batched with S1.3, keep sorry): `(hGmeas : Measurable G) (hGne : ∃ U ∈ 𝓝 y0, ∀ᵐ z ∂(volume.restrict U), G z ≠ 0)`
  (germ form, G≠0 a.e. ⟺ G²≠0 a.e.). **FINAL COMPLETE SIG (fm-2 pinned, relayed to fm):** instances
  `[PseudoMetricSpace Y][MeasureSpace Y][ProperSpace Y][IsFiniteMeasureOnCompacts (volume)][OpensMeasurableSpace Y]`
  (the down-set needs them; NOT SigmaFinite as first guessed) — STRENGTHENING IS REQUIRED (the proof needs them ⟹
  a weaker Skeleton sig breaks the `exact _aux` wire; the "keep [TopologicalSpace] general" alt does NOT work).
  RHS `(n:ENNReal)/2 + rlctAtOn (fun y => G y^2) y0`. fm restates (batch w/ resolution_charts re-scope + (1,1,1)
  gate). USE-SITE: core's Y = Fin d→ℝ provides all 4 instances (bridge if Params-typed). R1's monomial ∏|y_j|^{2k_j}
  discharges hGne (≠0 off null coordinate hyperplanes). fm-2's proof _aux lands at iteration-close (one dependent-Fin
  snag: finPeel.continuous_invFun, no math depth) → fm wires `exact`.
- **R1 USE-SITE CONFIRMED (pp + Codex identical): CLEAN to relocate (confirms A) + 2 obligations folded into R1:**
  (1) **unit-absorption** — R1 chart core = unit·∏|y_j|^{2k_j}, so R1.2's S2 invocation MUST first absorb the
  nonvanishing unit via `rlct_unit_invariant` (S1.3), THEN S2 on the pure monomial (THE main hidden gap; Jacobian
  same); (2) **hcore_top endpoint** — free from the down-set property for strict c'>λ, +monomial-endpoint fact if
  literal ∫=∞ at λ (fm-2 pins which). min-over-charts CLEAN (n=r(H¹+H^{L+1})−r² upstream-fixed ⟹ factorises).

## GENERAL-M TRACTABILITY VERDICT (pp + decorrelated Codex) — THE WALL IS G3 ALONE
The definitive headline-reach picture. **A-vs-B (does the block-monomialization layer compound the wall?): NO.**
Codex flagged residual entanglement as FACT; pp LOCATED WHERE IT LANDS — at the T1 unit-termini (harmless:
monomial×unit either way), NOT the split-relevant T2 smooth-block termini (there the exceptional is pulled out
front ⟹ disjoint ⟹ product-MIN split holds). So: A's block blow-up compounds ONLY G5 (more leaves), no new G3;
B/hybrid (default B, cone-blowup only where entanglement occurs) is lighter for general M (reuses smoothBlockND +
the (2,1,2) product-MIN). **VERDICT: fixed-M (2,2,2) keeps Option A (uniform, execution-ready); general-M uses
B/hybrid; the block layer does NOT compound the wall.** CLIMB-OR-ROADMAP (assessed, not assumed): lower bound
SETTLED · G5-abstract BUILDABLE (down-payment, task #52) · block layer non-compounding ⟹ **G3 (explicit
flag-resolution / strict-transform for arbitrary M = quiver-determinantal geometry Mathlib lacks) is THE ONE
genuine research-wall — ISOLATED + NAMED.** ⟹ CLIMB fixed-M ladder + BUILD G5-abstract; ROADMAP G3. **Honest
general headline = ladder instances + G5-abstract + G3 (single named open obstruction)** — the best possible
roadmap shape (one well-scoped wall, not diffuse difficulty). OPERATOR SCOPE FLAG sharpened: general-M gated on
G3 ALONE. METHOD LESSON (pp, logged): when a decorrelated model flags a failure mode as FACT, the value is often
"locate WHERE it lands," not "abandon" — an obstruction confined to where it doesn't matter is a refinement, not
a refutation (dual of the Q4-trap: both = interrogate the SCOPE of the model's claim).

## G3 SPEC — the named wall, sharpened to its internal crux (pp, g3-spec-the-named-wall.md)
G3 = the EXPLICIT combinatorial flag-resolution of {∏C=0} (route-A-concrete, explicit poly charts — **NOT general
Hironaka**). Claim: for every M, a finite rose tree of explicit charts with (G3.1) coordinate-subspace stratum
centers, (G3.2) **strict-transform = smaller chain product [THE CRUX]**, (G3.3) leaves bottom out, (G3.4) cover
up to null, (G3.5) binding ratio (k=1, h=Mval−1) ⟹ rlctAt = ½·min_Adm Mval = lambdaCore.
**DONE vs OPEN:** G3.1 designed (R1.3 ℕ-count), G3.4 designed (cover + lower-bound settled), G3.5 done (R1.2a/b +
k=1 validated). **G3.2 (the in-chart residual re-identifies as a smaller matrix-chain product — the iterated
"Schur-complement-of-a-matrix-chain is a smaller chain product" fact) is THE genuinely-open crux.** CRITICAL:
**Aoyagi PROVES G3.2 on paper (pp.15-21) — so G3 is a FORMALIZATION gap, NOT open math.** The dedicated-tide build:
explicit pivot-chart φ+Jacobian → the Schur-complement lemma (G3.2, substantial) → recursion (terminates) →
cover+ratio wiring → glue with G5-abstract. Multi-rung tide.
**HONEST HEADLINE SHAPE — LOCKED:** PROVEN = the fixed-M ladder + the general machinery (S1/L1/L2/D1/A1/A2/
G5-abstract); ROADMAPPED = G3 (crux G3.2 = Aoyagi pp.15-21 to formalize). One well-scoped, paper-proven,
formalization-only wall — the cleanest possible roadmap (a known proof to formalize, not open research).
**OPERATOR SCOPE (sharpened):** the general-M headline is gated on the G3.2 Lean construction — a dedicated tide;
everything else proven/buildable. Choice: deliver now (ladder + machinery + G3 roadmap) vs commission the G3 tide.
**G3.2 AS A PRECISE LEMMA + ON-RAMP (pp, final sharpening):** G3.2 = "if the leading t₁×t₁ minor of the partial
product is a unit in a pivot chart, UNIMODULAR row/col changes give ∏(QCQ)=diag(E_{t₁}-regular, ∏C') with C' the
Schur-REDUCED chain (widths M^s−δ_s), and ‖∏C−B‖²=‖reg generators‖²+‖∏C'‖² ⟹ rlctAt=½·reg-dim+rlctAt(‖∏C'‖²),
recurse" = **Aoyagi Thm 3 + the chain-Schur recursion** (verified L=1; well-founded, ΣM^s strictly drops, base =
smooth block). **ON-RAMP: G3.2 REUSES `block_elimination` (L1, DONE) + `product_reduction` (L2)** — it's their
GENERAL-M chained form. So the G3 tide is "**generalize the already-built L1/L2 to an arbitrary-rank-vector
recursion + glue with G5-abstract**," NOT from-scratch resolution infra; the fixed-M product_reduction wiring is
the PROTOTYPE the tide generalizes. The roadmap is genuinely set up: one named wall, a precise lemma, a known
paper proof, AND a concrete on-ramp.

## D1 RE-SCOPED (fm proof-attempt-as-audit) — NOT a light standalone rung
D1 `deepest_point_reduction` is blocked on TWO real deps: (1) the **RLCT-monotonicity lemma** `|G|≤|F| a.e. near
w* ⇒ rlctAt G ≤ rlctAt F` — MISSING + measure-theoretic (the 0^neg a.e.-domination corner: |G|^{-c}≥|F|^{-c} a.e.
where G≠0, reverses at {G=0}); **assigned fm-2** (reusable by L2's per-point argument). fm has the pointwise core
`rpow_neg_antitone`. (2) D1 depends on **L2** (homogeneous-scaling Thm-2 argument needs core-homogeneity, not the
raw mixed-degree dlnLoss B ⟹ per-point core reduction ≈ L2-per-point). So critical-path order is
**S1✓ → [monotonicity lemma + L2(needs R1/Fubini)] → D1**, NOT S1→D1. Rung map corrected.
**fm BLOCKER cleared:** resolution_charts re-scope (#47) was decided but never LANDED in Skeleton — fm landing it
now (pp's core form, BLESSED) + the S1.5 wire (fm-2's verified package) in one batch → green-gate → (1,1,1) gate.

## STATE @ ~03:20 — R1.2 LIGHT confirmed (de-risk) + (1,1,1) gate spec'd; trunk @995a674
- **R1.2 IS LIGHT (pp confirmed, §8 literal):** post the L1/Lemma-2 unit-Jac changes, the residual/reg entries ARE
  coordinates (the changes DEFINE them so — F₂/F₃ are the L1 coord changes) ⟹ ‖reg‖² + residual block = Σ(coord)²
  = smoothBlockND + rlctAtOn_comp_homeomorph. NO IFT, no general reg-seq, no S1.1-diffeo. And the (2,2,2) Option-A
  cover is EVEN LIGHTER — all leaves monomial×unit ⟹ per-leaf = WEIGHTED monomial threshold, NO block-rlct. So
  the fixed-M ladder is cheap throughout; no R1.2 sub-mountain. fm-2's #54 block-rlct under Option A = quick.
- **(1,1,1) gate SPEC'D (pp → fm):** ι=Unit (1 chart), φ=id, |Jac|=1 (so BARE rlctAtOn is correct here — contrast
  the WEIGHTED (2,2,2)); d=2, k=(1,1), h=(0,0); monomialThreshold = 1/2 = lambdaCore(1,1,1) = ½·Mval, θ=2; box =
  Fubini-product = the done Case111Bridge. No cover, no G5 — fm SPECIFYs directly. The R1-batch's last item.
- fm: WIRE rlct_additive_smooth_block ((b) keep+exact, closes S1.5 sorry 6→5) + re-scope resolution_charts + the
  (1,1,1) gate → (2,1,2) [#55]. fm-2: product_min_rlct (#56) → (2,2,2)-measure (#54). pp: on-demand. rv-2: queued.
- **PROPERNESS GAP (fm SPECIFY-catch) → AVOIDED via g5_flat_cover (controller adjudicated):** a single explicit
  blow-up chart does NOT satisfy S1.1 `weightedThreshold_transport`'s GLOBAL `IsProperMap`+`Surjective`. Resolution:
  R1's per-chart transport = the **lintegral c-o-v inside g5_flat_cover** (per-chart `InjOn` off the null exceptional
  only — NO global proper/surj); global coverage = R1.6 (the cover). So `rlctAt(core)=⨅ monomialThreshold` =
  g5_flat_cover (∫=Σ∫) + per-chart weighted-monomial threshold (S2+unit-absorption) + sSup algebra. NOT
  G1/G2/G3-bespoke — g5_flat_cover is the GENERAL version of how (1,1,1) bypassed S1.1. (2,1,2) uses product_min_rlct
  (Tonelli, no transport) ⟹ gap moot there. **S1.1 ORPHAN FLAG:** S1.1 is NOT R1's chart-transport (earlier
  "S1.1 carries the blow-up CoV" was imprecise — g5_flat_cover does) ⟹ revisit whether S1.1 is used by D1/L2 or is
  now an orphan (proven, hsurj+hImE 10th-finding banked, possibly unplugged) — pp checking; name honestly; doesn't block.

## STATE @ ~03:00, trunk @c92501d — R1 DESIGN PHASE COMPLETE; execution remains
- **rlctAt_mono ON TRUNK** (D1/L2 engine; green-gated 2855 jobs, controller-verified axiom-clean). fm built it with
  the **zero-set-inclusion hyp (G=0→F=0)** — BETTER than the hGne alt (pointwise, no a.e. machinery; use-site:
  D1's scaled core has F's zero set). 15th finding (bare monotonicity false, G≡0/F=|x|⁴) caught at SPECIFY by both
  fm+fm-2; fm's fix adopted. (Also merged: R1.2a/b + the #19 engines, banked on trunk.)
- **FIXED-M LADDER DESIGN COMPLETE + CERTIFIED (pp R1 design role DISCHARGED):** (1,1,1) [done] · (2,1,2) [#55,
  product-MIN, min≠sum CERTIFIED via the c=3/2 ∫r^{-2}=∞ divergence test] · (2,2,2) [#54, 24-leaf cover, cover-
  complete 12063/12063, a G5-instance]. Roadmap mapped: lower-bound settled · G5-abstract build-ready (#52) ·
  A-vs-B verdict (wall is G3 alone) · G3 spec (crux G3.2 = Aoyagi pp.15-21 formalization gap). **Residual = pure
  formalization labour** (fm + fm-2 execute) + the G3 tide if commissioned.
- **EXECUTION UNITS:** fm → the R1 BATCH (S1.5 wire + resolution_charts core re-scope + (1,1,1) gate) FIRST [still
  not landed — fm redirected to it 3×; recurring fm→adjacent-work drift], then #55 (2,1,2) + #54-assembly; fm-2 →
  #52 G5-step + #54-measure; pp → on-demand (G5 questions / assembly / G3 tide). rv-2 → S1.5 PASS done; queued.
- **G5-ABSTRACT FLAT-COVER DONE (#52, fm-2 @48b9468, axiom-clean):** `perChart` (single-step c-o-v on V\N + null
  drop) + `g5_flat_cover` (∫⁻_U=Σ∫⁻ over a finite a.e.-disjoint chart-cover, lintegral_biUnion_finset₀). The (2,2,2)
  cover = this **composed 3×** (nested levels 4∘3∘4), NOT the abstract tree (deferred to G3). Over ℝ≥0∞ ⟹ no
  integrability hyps.
- **product_min_rlct HYP UNIFIED (pp):** positivity-guard (both ∫⁻>0) + disjoint + measurable, NOT "vanish only at
  0" (over-strong, excludes monomials) ⟹ ONE lemma covers block×block (2,1,2) + monomial×block (δ-leaf) +
  monomial². The (2,1,2) tool IS the δ-leaf tool. S1.5-PASS = the L2/additivity SUM-engine (NOT the δ-leaf PRODUCT).

## Next tick (state @ ~02:30, trunk @da24204)
**S1.5 FUBINI ENGINE COMPLETE @ad1f313** (controller-verified axiom-clean) — whole S1 substrate proven. R1 lower-bound
soundness SETTLED (general result PROVEN on paper). **(2,2,2) cover EXECUTION-READY** (pp, 24 leaves, cover-complete
12063/12063, a G5-instance). **G5-abstract BUILDABLE + assigned fm-2** (Mathlib lintegral c-o-v; reduces general wall
to G3 alone). Headline-reach DECIDED+flagged: fixed-M ladder now + G3 named obstruction.
LIVE: (1) **fm** — Skeleton batch (S1.5 `exact` wire + resolution_charts core re-scope + product_reduction wiring) +
the (1,1,1) gate → report green-gate. (2) **fm-2** — G5-abstract (cover-gluing lemma) + (2,2,2) per-chart measure
pieces. (3) **pp** — (2,1,2) Fubini-product design (completes the ladder design). (4) **rv-2** — audit the S1.5 engine
(#50) + queued wires. Then: fm formalises the (2,2,2) cover (pp leaf-list + fm-2 G5-abstract) → L2 (=block_elim+
S1Fubini+R1-core+A1) → D1 → T (fixed-M headline). #19 PARKED. G3 = the one named general-M research obstruction.
Watch the fm→#19 pull (parked 3×). Don't stop in a blocked state.

### (prior next-tick) state @ ~02:00
TWO BIGGEST RISKS RETIRED: Fubini n=1 equality PROVEN (@e1cf73c) + R1 route VALIDATED (A-concrete, B refuted).
Remaining = execution + assembly. **Re-scope PINNED** (pp → fm): `resolution_charts(M) = rlctAtOn(dlnLoss M 0)(0)
= ⨅ monomialThreshold` (reduced widths M = core) + product_reduction wiring chain (block_elim → S1Fubini n/2 →
resolution_charts-core + S2 + A1 → aoyagiLambda). **λ_core=0 edge HANDLED** (fm-2, core_admissible_zero, no
λ_core>0 hyp). Iteration keystone `rlctAtOn_comp_homeomorph` banked (@f254397).
INTEGRATE as they land: (1) fm-2's Fubini ITERATION (Fin-peel homeomorph + Σ-peel) → general-n
rlct_additive_smooth_block → report final sig → fm restate+wire (ONE pass) → I aggregator-wire S1Fubini +
green-gate → rv-2 audit. (2) R1 CLIMB (validate-small-first): fm closes the **(1,1,1) gate** (φ=id chart + S2 +
arith, NO general geometry, xcheck `case111_rlct`) → (2,1,2)/(2,2,2) explicit-poly charts; pp designs the GENERAL
atlas R1.1/R1.3(codim=Mval, heavy)/R1.6(cover) in PARALLEL (math validate-small'd via witnesses). fm also restates
resolution_charts (core) + wires product_reduction. (3) L2 → D1 → T. #19 PARKED. Critical path: Fubini-iteration
+ R1-(1,1,1)-gate → general R1 atlas → wire product_reduction → D1 → T. rv-2 decorrelated (R1 = heaviest audits).
Watch the fm→#19 pull (parked 3×). Don't stop in a blocked state.
