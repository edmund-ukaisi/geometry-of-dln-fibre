# Compass — aoyagi-engine

*Seeded at genesis; amended at council #1 (2026-07-17, two independent elder seats, both ADOPT —
counsels in threads/00-genesis/council-1/). ≤2 pages.*

## The live question (REFRAMED by operator steer, 2026-07-18)
Build Aoyagi's resolution-of-singularities mechanism (DLN 2023) **FULLY and FAITHFULLY as a
free-standing library** — her objects, her invariants (sharing/support INCLUDED, never deferred
for being off some consumer's path), her construction §5 end-to-end — independent of downstream
consumption. THE DESTINATION IS THE LEARNING COEFFICIENT THEOREM (`aoyagi_learning_coefficient`
unconditional). `∀ M, RouteMBoxThresholdFinite M` (hbox) is ONE adapter from the library — the
current default path — and her direct λ-computation (the content we currently CITE) is a
candidate second path; if it proves shorter, the hole is DITCHED. The old razor "defer what is
not finiteness-load-bearing" is RETIRED: fidelity to HER mechanism is the bar; what her paper
builds, we build. **The hard part, named: the coverage theorem (Layer C)**
— the one genuine new proof; holds a lane from genesis. **Second cost center (not transcription):
the Layer-B tree build** — divisor-sharing bookkeeping + case-step invariant preservation in Lean,
with NO worked inner precedent (RR4 precedents the OUTER plumbing only; its SchurCore/front-peel
core is documented non-generalizing at depth ≥ 3, RR4.lean:12–21). Layers A/D are transcription
over banked substrate.

## Settled forks, WITH WHY
1. **Transform-only over integrate-early** (2026-07-17, operator-directed). WHY: the target
   exponent is exactly tight at binding cells — zero slack — so any lossy factorization is *false*
   there, not merely weak. Every predecessor failure was a lossy split; every survivor was exact.
   Witnesses: `battery/w-naked-weight-111.py`, `w-naked-weight-4444.py`.
2. **Her construction, not a route-specific residual resolution.** WHY: the naked wall-weight is
   REAL (it kills the plain-undecorated-IH route — `routeMBoxThresholdFinite_of_decoratedPeel` is
   SOUND-BUT-DEAD, AxCheck:1012–13); Aoyagi's construction never forms it *naked* because the
   divisor-sharing coupling is tracked through every chart. Same content as fork 3. The
   predecessor's own tracked-coupling route (`routeMBoxThresholdFinite_of_decoratedDescent`,
   conditional on `DecoratedDescent`, AxCheck:1006) is the insight this engine constructivizes.
3. **Divisor-sharing data is mandatory in the tree — bound at TYPE strength.** WHY: at corank ≥ 2
   the carried monomials couple; threshold-only summaries provably break. The tree datatype carries
   divisor-support as TYPED FIELDS (a flattening "simplification" is a type error, not only a
   battery failure — P1). Witnesses: `battery/g-coupled-binding-334.py` (minAdm(3,3,4)=8, coupled
   path only), `battery/g-delta-flatten.py`.
4. **Def 3 as printed is broken** (verified typo). Use the geometric `½·min_t Mval(t)`.
   Witness: `battery/g-def3-broken.py`.
5. **The engine's sole output is hbox** — one Prop (`RouteMBoxReduction.lean:165`, verified
   verbatim). Consumer stack proven (`aoyagi_learning_coefficient_gen`, clean-three).
6. **DecoratedDescent disposition (CLOSED: TOMBSTONED at adoption, tick 7 — routeMBoxThresholdFinite_of_decoratedDescent + node decorated-descent-route superseded → engine-route).** Two live
   routes to the identical ∀M Prop is the P6 duplicate-skeleton failure. EITHER the coverage
   theorem constructively witnesses `DecoratedDescent` (the engine then discharges the
   predecessor's conditional route — architect checks type-fit and reports), OR the decorated hole
   toward hbox is tombstoned in the adoption commit. Not both live.

## Non-local invariants (division of labor — ONE owner per obligation)
- The engine OWES `∀ M, RouteMBoxThresholdFinite M`; DELEGATES: the ≤/achiever half (banked
  natively upstream — transcribing Eqs (1)–(5) is scope creep toward θ, fenced), θ (out of scope),
  cite-1/RlctPayoff (out of scope).
- **Layer B** owes charts + invariant preservation + exponent ledger at the CURRENT arity's deepest
  stratum ONLY; everything reducible goes to the IH via the theorem4 reduction. *A Layer-B lemma
  that integrates anything is off-contract* (verbatim in the driver docstring).
- **Layer C (coverage)** owes coverage + no-smaller-ratio AT THE TRACKED CELLS ONLY. It may consume
  the banked cover/null toolkit; it may NOT consume rlct = c* (circularity guard). No-smaller-ratio
  is a UNIVERSAL claim: not "established" without a decorrelated hunt for an untracked
  smaller-ratio divisor (the expedition-level kill-condition; an empty hunt = scoped evidence).
- **theorem4-localization** owns the NON-DEEPEST REDUCTION: an EXACT reduction to a strictly
  smaller instance — NEVER a reweighted-residual bound. Threshold preservation pin:
  `nReg + minAdm(M') ≥ minAdm(M)` via the minAdm-as-minimum property (inf'_le / minAdm_le_Mval
  class) — **NOT `MinAdmMono`** (opposite direction; a name-similarity formaliser trap, caught at
  covdesign D2). Deepest domination ALREADY BANKED hypothesis-free
  (`deepest_le_of_homogeneous_core`, DeepestMinRlct.lean:157); far points via the exact
  homogeneity-scaling CoV. ADJUDICATED: DISSOLVE (cert-d2); shape-check CONFIRMED at (2,2,4) (tick 17 — pure homogeneity domination, degree 2L, no chain-IH wanted).
  OPEN LEG: L≥3 coupled non-origin points discharge via the banked domination, NOT a chain-IH.
  Acyclicity verified (domination calls nothing; CoV strictly drops; disjoint owners).
- **region-glue** owns the ASSEMBLY only: finite covers gluing chart-local reads + the reduction's
  output into hbox. SETTLED EXACT (covdesign addendum): the SEPARATED leaf integrand is correct at
  corank ≥ 2 — the divisibility chain makes each true leaf a single dominant monomial × unit — so
  region_glue never consults `support`; its load-bearing precondition is `IsFullMonomialization`.
  ELDER AMENDMENT (rev-1) + r2-LANDED SHAPE: the leaf CoV is FACTORED `chartMap = ψ ∘ β`
  (EngineObligations LeafJacobian) — β the explicit monomial blow-up (`|det Dβ| = ∏|u|^{divExp−1}`,
  abs-value — finding 7; HasFDerivAt only, integrated DIRECTLY, no inverse) and ψ a bounded-unit
  local diffeo with FULL inverse data (feeds rlctAtOn_boundedUnit_localHomeomorph). The transport was
  never meant to eat the singular factor — that was the r1 laundering break (`|det Dπ|=|u|` has no
  lower bound at u=0); β carries the singular vanishing, ψ the regular gauge/shear (ψ-inverse
  constructibility on the exceptional fibre reviewer-VERIFIED). The Morse core is genuinely singular,
  contributes resRank/2 to the min; `resRank ≥ minAdm` remains a TRUTH-WITNESS THEOREM of the tide,
  now carried via the terminalExponents resRank fold + the exponent hooks (never assumed). r2
  residuals (non-blocking, close-during-tide): srcBox.Nonempty is weaker than nonempty-interior
  (strengthen when the tide builds the attaining leaf); a.e.-injectivity off a null set replaces full
  InjOn (blow-up charts aren't injective on the exceptional fibre); divCoord/resCoord injective +
  disjoint. IsFullMonomialization unaffected.
  CHARTBRIDGE STRENGTHENING (2026-07-18, elder-ratified; statement-soundness fix, counterexampled).
  region_glue is UNPROVABLE from ChartBridge as stated — an UNBOUNDED srcBox sector chart
  (F=y₁²+y₂², a≥3: β(u,v)=(u,u^(a−1)v) on |v|≤|u|^(−(a−2))) satisfies every leaf clause while the
  radial integral diverges on the advertised c'<a/2 range; the missing source width is exactly the
  lost power. FIX (weakest sufficient, both analyses): per-leaf MeasurableSet srcBox ∧ bounded in a
  flat cube (∃R>0, srcBox ⊆ flatCube M R). Satisfiable — real Aoyagi charts are bounded boxes;
  discharged at rung 4. NONEMPTY-INTERIOR is NOT needed; the r2 srcBox.Nonempty residual stays
  non-blocking. MeasurableSet is also the direct prerequisite of the area-formula read (fork 8
  revision) — the two fixes reinforce. Coverage lane unaffected (it owns the image cover and supplies
  bounded sources; if the natural covering source is unbounded, take a bounded refinement covering a
  smaller box + globalize by scaling — assembly-arch-answer §4). OWNERSHIP (one owner): the
  CoV identities (LeafPullback/LeafJacobian — algebraic, Layer-B-legal: a derivative is not an
  integral) are the CONSTRUCTION's; coverage-design owns only image-cover + InjOn; region_glue
  owns ALL integration. g-leaf-chain-separation witnesses DIVISOR separation (re-scoped).
  Witnessed: g-glue-lossy-vs-exact, g-pivot-conull, g-leaf-chain-separation,
  g-chartscover-vacuity (old-shape kill), g-chart-bridge-pullback.

## Settled forks (continued — council #2, carrier restructure, 2026-07-17)
7. **Edge-labelled carrier** (council of two, convergent + architect's probe-backed witness).
   WHY: the unary invariant provably cannot pin the paper's parent-referencing case-1(1) merge;
   per-chart substitution is DATA no Prop supplies; leaf-terminating charts lose case labels.
   bChain stays a TYPED FIELD (adjudicated). Spec: Edge{case, localSub, child}; StepRel relational;
   ChartBridge = upstairs-open image cover + InjOn + LeafPullback + LeafJacobian; chartDom removed;
   leaf chartMap = DERIVED fold; tStar attainment via an emitted path; lex termination for the
   construction recursion. → StepRel scope adjudicated at fork 9 (existence-consistency now;
   faithful stepUpdate = tide rung 1).
8. **Q5 route (b): banked-RLCT-transport + ONE scaling-bridge lemma** (both seats, corrected
   merits). WHY: fresh-composer vs banked-reuse — the 0-sorry LOCAL-homeomorph transport
   (rlctAtOn_boundedUnit_localHomeomorph) fits blow-up charts (proper, not globally injective);
   the only new analytic lemma is ∫_{εK}F^(-c') = ε^(N−2Lc')∫_K with its homogeneity input banked;
   one-sided ≤ suffices; source-match (Aoyagi reads the RLCT off the resolution — (b) IS her move).
   RECORD CORRECTION carried: the original fork framing was FALSE on both sides (ParamsFlatLinear
   banks the normed instances — controller-verified; and the transport CONSUMES fderiv). Both
   routes go through flat coords; the choice was reuse-vs-rebuild. (a) stays a live fallback only if the chart
   hypotheses prove undischargeable — the transport-family cone is VERIFIED fully sorry-free
   (cartographer #1: the '2 sorries' were docstring words; only RouteMSJTransport carries 1,
   the general-composer piece).
   GUARDS: circularity (the transport gives INVARIANCE only — no path may consume rlct=c* /
   cited_aoyagi_dln); no-laundering (transport hypotheses DISCHARGED from the construction, never
   relocated to fresh holes); edge data = the monomial ledger, never opaque derivative fields.
   MECHANISM REVISION (2026-07-18, elder-ratified; glue seat + decorrelated Codex,
   threads/06-region-glue). Route (b)'s WHY (banked-reuse + weakest-hypothesis + source-match + one
   new lemma) STANDS; the banked lemma reused for the PER-LEAF read changes.
   rlctAtOn_boundedUnit_localHomeomorph is INAPPLICABLE to the repaired LeafJacobian (it wants
   Dψsymm, openness of β''srcBox, and a fixed basepoint — none supplied). The per-leaf read is now
   the Mathlib area formula lintegral_image_eq_lintegral_abs_det_fderiv_mul on srcBox∖N̄ (chain rule
   Dφ = Dψ∘Dβ; needs ONLY the UPPER det bound |det Dφ| ≤ hi·∏|u|^(divExp−1); null image discarded via
   addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero) — both lemmas verified present at
   v4.29. The scaling bridge (landed, clean-three) is RETAINED for small-box→unit-box globalization.
   STRICTLY weaker-hypothesis and MORE banked-reuse than the transport, a closer source-match (it IS
   Aoyagi's monomial-leaf integration); guards unchanged and improved (pure measure theory — no path
   to rlct=c*/cited_aoyagi_dln; hypotheses discharged from ChartBridge/LeafJacobian at rung 4, not
   relocated — AVOIDS the r2 finding-2b laundering). The transport family is not retired (banked,
   sorry-free) — merely UNUSED on the engine's per-leaf path; one live spine (P6).
9. **StepRel scope: existence-consistency now, faithful stepUpdate as the tide's first rung**
   (r2 VALIDATE + elder ratification, 2026-07-18). WHY: the driver provably never consumes StepRel
   — engine_box_threshold_finite rides on ChartBridge + IsFullMonomialization + the exponent hooks +
   banked minAdm; StepRel could be `True` without changing the finiteness certificate (r2 + Codex,
   verified against the code). So the existential child-read is SOUND for finiteness and INSUFFICIENT
   for transition-faithfulness (Codex dummy-divisor schema: a divisor may appear/vanish across an edge
   unrecorded). RULING: docstring downscope stands (StepRel = a per-edge existence-consistency check);
   the FAITHFUL form `child root ledger = stepUpdate parent e` (per-divisor injection +
   unchanged-equality + support propagation + the case-specific update) is the construction tide's
   FIRST rung — NOT a permanent downscope. Right-extension not creep: the tide must compute each
   child's ledger from its parent to build the tree at all, so typed `stepUpdate` IS the construction;
   given it, `StepRel := child = stepUpdate parent e` is discharged rfl-class; it realizes fork 7's
   founding WHY (we PAID for the edge carrier to pin the case-1(1) merge — leaving it weak is an
   over-built structure) and makes case_step_invariant name=content. The recursion's invariant rides
   on the definitional ledger updates, NOT StepRel — so faithful-first must never delay or absorb the
   long pole. GUARDS (Ratification ≠ landing): (i) TESTED at rung 1; if `child = stepUpdate parent`
   isn't the construction's natural definitional shape or the equality balloons, STOP-AND-SURFACE and
   take permanent downscope; (ii) kill-condition = the dummy-divisor witness provably rejected (a
   ¬-theorem, cf. stepRel_rejects_mismatched_case2).
10. **Full-mechanism reframe (OPERATOR-SETTLED, 2026-07-18).** WHY: the deferral ledger (support
   propagation, the p.15 minimality tie-break, the J₁ gap condition, the divProfile T-settings)
   clustered exactly at the named hard part — the sharing bookkeeping that IS her mechanism (fork
   3) — each deferral argued by "not finiteness-load-bearing", the razor for the HOLE, not the
   GOAL. RULING: build her mechanism fully; the deferrals are UN-DEFERRED into the construction
   tide as first-class rungs (genDivExp/support propagation; the divisor-chooser implementing her
   p.15 selection rule — tie-break + gap condition; the per-case divProfile settings). hbox = an
   adapter; her λ-route = a candidate replacement for the cite, to be priced by the paper-map
   recon. The elder office's charge is corrected accordingly.
   RUNG-1 SUB-SCOPING (2026-07-18, elder-ratified). stepUpdate is faithful for the EXPONENT/CLEARING
   ledger (numDiv/divExp/divTilde/cleared), page-verified: case-1(1) merge M'=M+J₁(M^{(S+1)}−J) t̃→J
   cleared-unchanged (p.16); case-1(2) new pivot same increment, t̃=J, cleared+1 (p.17-18); case-2 new
   divisor exponent (M(S)−J)(M^{(S+1)}−J), t̃=J (p.20). TRUTH-WITNESS CATCH: case-2 cleared advance was
   `+= resRows` — WRONG (p.21: J increases by ONE per Case-2 step; += resRows drops the decreasing-
   exponent divisors of the skipped steps, making minAdm∈terminalExponents unsatisfiable); corrected to
   `+= 1`. DEFERRED (fidelity, not finiteness-load-bearing; guard = LeafPullback): support propagation
   (balloons — genDivExp redesign as a named later rung with the coupled-binding/delta-flatten kill-
   condition) and layer(S)-advancement (lives in the construction Phase/State, μ 1st component).
   CARRIER: ℕ mergeIdx + out-of-range no-op ADOPTED over dependent StepSubst n c (avoids dependent-edge
   recursion friction; junk rejected at Prop level per the codebase pattern); eligibility (t̃=cleared+
   runLen) is a cheap Prop conjunct if the no-op acceptance proves certificate-unacceptable — NOT a
   dependent-type refactor. LeafData gains divTilde/cleared (honest total rootLedger).
11. **Roadmap adopted; Path A ratified as the SOLE critical path** (council #3, two independent
   elder seats CONVERGENT, both kernel-verified, 2026-07-18). WHY: the ≤-half
   (routeMCore_box_diverges_achiever_full', 0-sorry general-M; r1_resolution_general_le hbox-FREE)
   is banked; aoyagi_learning_coefficient_gen (HeadlineGenAssembly:55) is conditional SOLELY on
   hbox for L≥2 (both seats direct-read the proof); the ONLY open content is hbox = coverage (R2)
   + region_glue (R3); Path B contains Path A's coverage — not shorter. PRECISION PIN (seat A's
   confound-hunt catch, controller-verified; resolves the seats' one divergence AGAINST the recon's
   gloss): discharging hbox + repointing canonical → _gen yields the UNCONDITIONAL CLEAN-THREE
   aoyagi_learning_coefficient — it kills the sorryAx of the 5 skeleton rungs. It does NOT delete
   cited_aoyagi_dln: the cite was NEVER in the λ cone (grep: only absence-asserting docstrings);
   it lives in the OUT-OF-SCOPE RlctPayoff layer (needs minAdm=codim — the next expedition's
   runway). "Kills the cite for free" was headline-inflation; struck everywhere. GUARDS (seat B):
   _gen's clean-three rests on a #print DIAGNOSTIC (AxCheck:913), confirmed-by-discipline not
   build-enforced — an ENFORCED axiom-gate installs at R5; L=1 reaches the unsuffixed theorem via
   a SEPARATE fold (not _gen). RUNGS ADOPTED: R1 = the FAITHFUL carrier NOW — full-T in the State
   (t̃ DERIVED; T is non-derivable chooser-required data: deferring it is incoherent AND risks a
   μ-descent retrofit) + the genDivExp multiplicity field (ONE faithful node-data pass; propagation
   PROOFS at R4; stop-and-surface if full-T stepUpdate balloons; divProfile T-settings page-verified
   at build); the EngineConstruction "stores ONLY what the measure reads" docstring is STRUCK (the
   retired razor encoded in code). R2 = coverage, own permanent lane; gate = the ChartBridge PROOF
   over the CONSTRUCTED atlas + a DECORRELATED atlas-closure probe (pen-and-paper seat, never the
   builder — in-house witnesses mask gaps, twice proven) + hunt-cert §5 cited by SCOPE, never
   blanket. R3 = region_glue (in flight; field-pass cleared). R4 = genDivExp propagation, OWED
   (kills: g-coupled-binding-334/g-delta-flatten). R5 = wiring + the enforced axiom-gate. R6 =
   Lemma 2 + Theorem 3 (the regular peel, Layer A) OWED FIRST-CLASS under fork 10 — both seats
   reject "value lane suffices" as the retired razor (the value lane gets the NUMBER, not the
   OBJECT) — placed post-spine off critical path, COST-PROBE-GATED (SchurCore depth-≥3 wall,
   rr4-precedent), surfaced to the operator for scope confirmation. θ + Eqs (1)-(5) stay out.
12. **Coverage-commissioning gate: §2 T3-contract RATIFIED; three §3 corrections** (elder-gate4,
   2026-07-18). WHY-RATIFIED: §2's ChartLeaf per-leaf tuple is VERBATIM the landed ChartBridge
   conjunction (8 fields, same order, EngineDefs.lean:79-85 — glue-lane consumption preserved),
   + hledger/hnonempty; weakest-sufficient for the PROVEN region_glue_of_chartBridge (no
   consumer-needs-more); the two prior burns absorbed; the tree-level cover is the FULL pivot
   cover, non-toric — no toric route. CORRECTIONS (Just-Do-It; do NOT block T3 cover
   commissioning, DO gate the build discharge):
   (a) THIRD GAP — admissibility. §3's `divProfile ∈ Adm` as a per-node invariant is FALSE:
   pending ⟹ t̃ = min T > 0 ⟹ last > 0 ⟹ ∉ Adm clause 3 (Lambda.lean:54). WITNESS against the
   LANDED carrier: node334.divProfile = ![1,1] ∉ Adm(3,3,4) (CoRank2Spike:83). CORRECTED:
   per-node invariant = weak-decrease + block-bound ONLY; last-comp-0 is a LEAF property from
   post-final-rollover J=0. leaf-Adm = invariant + leaf-t̃=0. LOAD-BEARING for the exponent-hook
   no-undershoot (Mval ≥ minAdm on Adm) — hbox critical path, not fidelity.
   (b) SHARP TRUTH-VALUE owed a pen-and-paper seat BEFORE the build discharges
   IsFullMonomialization/exponent-hooks: at non-monotone widths L≥3, does the case-2 raw-width
   head-reset (p.20-faithful) reach a leaf with a non-weakly-decreasing profile? And does every
   emitted leaf carry ONLY t̃=0 divisors (IsFullMonomialization's ∀k vs the paper's t̃=0-only
   read-off, p.22)? KILL: a leaf divisor ∉ Adm at M=(2,2,3,2).
   (c) invariant→principalization is UNOWNED → NAMED: it IS T3's discharge of the image-cover +
   per-leaf LeafPullback/LeafJacobian, consuming the total-comparability invariant (cert-2222 c),
   which gets a NAMED build-side carrier (a maintained chain invariant, not only the chooser's
   local minimality). T3's cover proof GOES THROUGH it, never asserts the cover.
   T3: own lane + reviewer + parallel buildTree; gate = ChartBridge PROOF over the constructed
   atlas + decorrelated pnp replay + hunt-cert §5 by-scope + circularity (fork 11 confirmed).
   FIRST RUNG: the per-blow-up LOCAL covering lemma at corank≥2 (prove the uniform event, fold
   the cases), then the fold, then invariant→principalization.
   12(b) RESOLVED (pnp-atlas cert-nonmono-2232 + Codex replay, 2026-07-18): BOTH sub-questions
   AGAINST the current predicates. (i) The p.20 raw-width head-reset reaches a non-Adm t-tilde=0
   leaf label at (2,2,3,2) - a VERIFIED TRANSCRIPTION DEFECT (the label uses raw width where the
   exponent uses the running-min; the paper's own Mval formula conflicts 6-vs-4; same class as
   Def-3; ledger: theory/aoyagi-2023-reproduction/verify-case2-rawwidth-defect.md). RULING FIX-A:
   the Case-2 head-reset caps at the RUNNING-MIN - battery-confirmed to restore label==exponent,
   Adm-clean atlas, min==minAdm; the fork-12(a) Adm argument then goes through unchanged.
   (ii) Leaves CARRY t-tilde>0 divisors (exponents can be < minAdm - red herrings fenced by the
   paper's t-tilde=0 read-off, p.22): IsFullMonomialization + the exponent-hooks/terminalExponents
   READ-OFF RESTRICT to t-tilde=0 divisors - an unrestricted forall-k is stronger than the paper
   and FALSE. The ChartBridge ANALYTIC tuple is UNCHANGED (T3 supplies leaves whose divCoord/
   divExp enumerate the t-tilde=0 divisors; the t-tilde>0 monomials fold into residualCore -
   proving the squeeze on each chart's sector is T3's burden, correctly placed). The VALUE was
   never at risk (min==minAdm at every probed instance); the predicate SHAPES were. The 'third
   page-reading surface' warning (tick 46) and the full-mechanism reframe are both vindicated:
   the defect is invisible at monotone widths and every L<=2 instance - only the faithful full-T
   carrier at the non-monotone L=3 instance could expose it.
13. **The concrete-oracle unit's shape** (elder-gate5, 2026-07-18). monomialization_terminates =
   assembly [DONE - buildTree/WF.fix + rootLedger_buildTree/base/stepRel_all/WeakDecInv-
   preservation] + T3 [rung-3 pre-staged] + THE CONCRETE ORACLE: a TOTAL ConState -> ConDecision
   transcribing the pnp SIMULATOR (validated at 4 instances). RUNGS: o1 strengthened
   StateInvariant - READ OFF the simulator's maintained set (WeakDecInv [landed] + CompChainInv +
   J<M(S+1) live-layer + cleared<=layerCap [landed]); weakened 4x already - get it right FIRST.
   o2 the decision function - dispatch + eligible-minimal chooser + d_center pivotComplete
   emission (page-pinned; the simulator is the symmetric-quotient PROFILE projection, blind to
   geometric fan-out). TYPE-totality is FREE (junk-state terminal fall-back; ConDecision requires
   eligibility not minimality); the content is CONE-GOODNESS via WF-induction over the invariant
   cone. o3 leaf-Adm = WeakDecInv + block-bound(leaf) + leaf-t-tilde=0 (from J=0/no-pending); the
   B' coherence tie landed. o4 CompChainInv PRESERVATION - the unattempted brick; consumes
   chooser MINIMALITY (the (3,0,1) mechanism); THE PAPER DOES NOT CLEANLY PROVE the chain
   invariant (defect record) - WE prove it. o5 exponent hooks - SPLIT: the <=-half (no-undershoot)
   from leaf-Adm + banked Mval>=minAdm-on-Adm [BUILD]; the IN-half (minAdm IN terminalExponents)
   + liveAttainment = a REALIZATION/stratum-completeness claim ('profile-set contains Adm', =
   cert-atlas-probe-2222 (a) from the build side) - OWNER ASSIGNED: BUILD (the realization needs
   the construction's internal path structure, which T3 never sees; T3 owns image-coverage only).
   NON-LOCAL CONTRACT: o1(CompChainInv) <-> o4(preservation) <-> o2(min-EXISTENCE) is a MUTUAL
   induction (chain => min exists => picked => minimality => preserved) - design + prove TOGETHER
   (the simulator's def4_min comparability-violation fallback is the exact hole the invariant
   closes). SEAT: architect formalises (deepest carrier context); o4's uniform arbitrary-L math
   gets a PEN-AND-PAPER CERTIFICATE FIRST (decorrelated); T3 parallel on the contract shape,
   real-atlas composition gated on o2 (the shear-reconciliation the coupling point). KILLS
   (batteries exist): o1/o4 = any reachable incomparable eligible pair (comp_violations, 0/4 so
   far); o3 = a leaf not in Adm (0 post-FIX-A); o5-IN = an instance where the t-tilde=0
   profile-set differs from Adm (== at all 4). PRE-COMMIT CLARIFIER: the simulator extension at
   higher-L non-monotone instances ((2,2,3,3,2), (3,2,4,2)) - comp-violations + profile-set==Adm
   at unexplored depth, BEFORE the architect's long seat commits.
   13(Q3) RESOLVED - the rollover is a CHARTLESS TREE EDGE (elder-gate6, 2026-07-18; ratifies
   the tick-129 provisional A). The concrete build FALSIFIED the tick-118 absorb ruling: an
   absorbed rollover breaks StepRel's rfl-class equality (child rootLedger post-rollover
   cleared=0 vs stepUpdate's pre-rollover prediction). RULING: a 4th StepCase.rollover +
   stepUpdate relabel clause (numDiv/divExp/divProfile UNCHANGED, cleared := 0), localSub = id.
   FAITHFUL per pp.19-21 page-read: the case step PRODUCES the (S,J+1) statement (p.20 indexes
   the new pivot u_{S,J+1} BEFORE any boundary check), THEN the p.19/21 boundary check RELABELS
   to (S+1,0) ('the inductive statement with S increased by one') - a genuine node reached by a
   chartless transition (the C' and P/Q shears live INSIDE the case step; tick-127 pure-(a)
   page-confirmed). REJECTED: (B) compose-into-the-step (breaks one-StepCase=one-ledger-op +
   name=content: a case2 edge would sometimes reset cleared); (C) relabel-inside-StepRel (loses
   rfl-class - the blocker's own cause). REQUIRED CONDITION (fork-9 mandate): the rollover edge
   carries an AT-EXHAUSTION guard (cleared > runMinWidth-class; the exact comparison pinned OFF
   THE SIMULATOR-VALIDATED ORACLE DISPATCH, not page off-by-one) as a StepRel conjunct + an
   early-rollover kill-witness. WHY: without it StepRel accepts an early rollover stranding
   pending divisors - a ledger-consistent non-Aoyagi tree caught only by ChartBridge's semantic
   falsity, the exact infidelity class fork 9 rejects at the ledger. NOT load-bearing for o3's
   proof (rides on construction invariants) - lands alongside, never blocks. The intermediate
   (S,J+1) node is a branch never a leaf (IsFullMonomialization unaffected); the guard is a
   separate conjunct (ledger equality stays rfl-class). Blow-up-only aesthetics yield to ledger
   faithfulness: the tree's nodes are the paper's inductive statements, S-increment included.
   13(o5-IN) RESHAPED (2026-07-19; elder-gate7 RATIFIED tick 152; two-way: cert §8 Codex confirm
   + independent pnp derivation): the realization target 'profile-set contains Adm' is FALSE for
   the built tree — REFUTED BY ARGUMENT, chooser/branch-independent (occ_above tops at r_S−1, so
   a level-r_S divisor is invisible to case-1 under ANY pick; the pick-x-branch exhaustion on the
   witness is spot-confirmation). Witness M=(3,3,4,2,3): (2,2,2,0),(3,2,2,0) in Adm stranded at
   t-tilde=2 forever. Gap iff interior bottleneck (0 mismatch/791); the 4 pre-committed kill
   instances were ALL bottleneck-free (shallow-instance confound — see standing counsel). Exact
   characterization (0 counterexamples, 847 exact-recursion instances, cross-validated on the
   original sim): P(M) = { a in Adm : Clearable(a) }, Clearable = every post-birth descent layer
   S with a^S < a^{S-1} has a^{S-1} < r_S. SAME width-drop-strand mechanism as the p.15
   full-chain defect (cert-compchain-o4 Part 1) — one mechanism, two faces (earned: 0/791 ==
   18/18, two independent certs). K2 does NOT fire: minAdm in P is PROVED (cert §3
   envelope-splice: envelope prefix contributes 0 to Mval, so every non-clearable profile has a
   strictly cheaper admissible sibling; cross-checked 847/847). THE SURVIVING BRIDGE: min over P
   == min over Adm from (P subset Adm [leaf_mem_Adm, PROVED]) + (minAdm in P [cert §3, PROVED])
   — the paper's lambda formula stands; its implicit stratum-completeness does not (4th verified
   read-off defect; ledger WRITTEN: verify-realization-gap-defect.md). o5-IN Lean target = minAdm
   in terminalExponents ONLY (name must denote attainment — minAdm_mem_terminalExponents-class,
   never profileSet_eq_Adm-class); no '⊇/== Adm' conjunct anywhere (hold order stands). REIFY-NOW
   (elder-gate7 amendment): the Clearable predicate + the STATEMENT 'P(M) = Clearable-Adm' land
   WITH the spine as a SEPARATE named sorried library-surface theorem (defect explicit in its
   docstring; the library's typed honest name for what its tree realizes — a docstring is
   defeasible, a type is not); NOT a conjunct of IsFullMonomialization (that re-inflates the
   false promise). GUARD: statement now, PROOF at R7 — reify-now must not pull the
   descent-invariant proof onto the spine.

## Landmarks (8; elder-ratified) — why these
- `mint-repoint` — the destination. · `hbox-root` — the one owed Prop.
- `engine-route` — founding route; its gate is the first live test of the harness.
- `resolution-tree` — the key definition; typed sharing fields are the design crux.
- `coverage-theorem` — the key lemma / the hard part; permanent lane.
- `theorem4-localization` — **promoted at council #1**: owns the non-deepest reduction (the seam
  where the disease re-enters); previously an unowned three-way pointer.
- `exponent-ledger-bridge` — the analysis↔banked-combinatorics seam; the form-A-vs-slack trap
  (`g-tightness-formA`: truth scans cannot separate tight from slack) earns its slot.
- `rr4-precedent` — the OUTER-plumbing precedent + threshold-reachability at (r,r,4); NOT an inner
  precedent (SchurCore walls at depth ≥ 3). Honest form: the composition is 0-sorry.

## Standing counsel
- Fund the general chart-tree CoV composer as a library lane (P8) — typed consumers exist.
- Battery gaps CLOSED (covdesign D1): g-glue-lossy-vs-exact.py, g-pivot-conull.py,
  + g-coverage-sharing-killcond.py (mis-tracked sharing invents a spurious low-ratio divisor —
  (2,2,1) and (3,3,4) exact witnesses).
- The exhaustiveness hunt: run Tier B/C per cert-d4 BEFORE the coverage tide; a monomial-only
  hunt passes vacuously — never accept one as the gate. SURVIVED (tick 12, hunt-cert §5 — 5
  decorrelated legs, 0 undershoots; cite that scope, never blanket 'established').
- Watch transcription-level decoupling: a transcriber "simplifying" the carried monomial data is
  fork vocabulary; the sharing maps are the content (typed, per fork 3).
- Survey banked state before commissioning ANYTHING (3 redundant commissions last run).
- SCOPE vs SEQUENCING (the corrected-razor discipline, council #3). The finiteness razor is
  RETIRED for SCOPE — what the faithful library CONTAINS is fixed by fidelity to her paper, not a
  consumer's path. It stays legitimate ONLY for SEQUENCING — what LANDS FIRST is the critical
  path; sequencing is never silent abandonment. Recurrence test: any "optional / not-critical-path
  / value-lane-suffices / the-certificate-never-reads-it" on a NAMED piece of her mechanism is the
  old failure mode — surface it, never adopt it silently.
- The R2 atlas-closure gate must be DECORRELATED from the atlas builder (council #3, both seats):
  in-house nice-instance witnesses MASKED gaps twice (resRank fold; srcBox boundedness). The
  builder's spike is build-side de-risk; the GATE reads the independent seat.
- KILL-SET ADEQUACY for universal claims (elder-gate7, 2026-07-19; general rule in
  docs/policies/expedition-map.md § battery): every pre-committed kill set must exercise each
  KNOWN failure mechanism. This expedition's known-mechanism list: (i) interior-bottleneck
  width-drop (∃ 3≤S≤L, r_S < r_2 — witnesses (3,3,4,2,3), (2,2,1,1)); (ii) L≥4 non-monotone
  depth ((2,2,3,3,2) — the min-vs-max exposer; width-drop alone misses it). Binds R2/R4/R7 gates.
  COMPLEMENT, not replacement: a green pre-committed battery is NEVER sufficient for a universal
  claim — the gate reads a decorrelated hunt (that is what actually caught the realization gap:
  pnp-o5's independent scan, not the battery). Provenance: the "== Adm at all 4" kill sat green
  while false at 84/351 (all 4 instances bottleneck-free; 2nd shallow-instance confound).
- MATHEMATICAL SENSE OVER CASE ANALYSIS (operator, 2026-07-18): case analysis is a VERIFICATION
  instrument, never the theory-building instrument — chasing per-case fidelity finds local minima.
  Understand the mechanism at its conceptual altitude first (what the induction IS doing: iterated
  blow-ups monomializing the ideal, one uniform idea whose "cases" are charts; why the invariant
  holds; what λ reads off geometrically), THEN transcribe; build the uniform object and DERIVE the
  cases, not the reverse. When a case-by-case grind feels authoritative but shapeless, stop and
  re-derive the global structure.
- OBLIGATION-STATEMENT DISCIPLINE (3rd instance, 2026-07-19): THRICE an obligation was
  FALSE-AS-STATED for want of a hypothesis the true construction supplies FREELY — (1) the resRank/2
  Morse threshold (resRank fold), (2) srcBox boundedness/measurability, (3) monomialization_terminates
  at L=0 (the base conjunct forces the root to STEP; at L=0 conRoot is a leaf — found by t03 at the
  E-wire, fixed by the hL : 0<L ripple, tick 157; hL is the nondegenerate-chain hypothesis, distinct
  from width-positivity which route (B) proved unnecessary). Common root: an obligation
  quantifying over an ABSTRACT carrier field (a bare exponent list, a bare Set) inherits a gap the
  real object (a genuine Morse residual, a bounded chart box) always closes. Both were caught by a
  DECORRELATED counterexample, NOT the in-file satisfiability witness — the witness used a benign
  concrete instance that happened to satisfy the missing constraint, MASKING the gap. PROPHYLACTIC
  (before the region_glue discharge lands): a deliberate pass over EVERY abstract carrier field
  region_glue transitively consumes — chartMap, srcBox, terminalExponents, residualCore, the image
  cover, divProfile — asking "what does the real chart supply that this field does not force?".
  Weakest hypotheses that suffice, never weaker than the analytic consumer needs (bedrock: usable
  form). An in-file nice-instance witness is necessary, never sufficient; the adversarial hunt is the
  gate.
