# Compass — aoyagi-engine

*Seeded at genesis; amended at council #1 (2026-07-17, two independent elder seats, both ADOPT —
counsels in threads/00-genesis/council-1/). ≤2 pages.*

## The live question
Transcribe Aoyagi's worked-out resolution (DLN 2023, §5) into a Lean engine producing
`∀ M, RouteMBoxThresholdFinite M`, clean-three, no Aoyagi hypothesis. Current load-bearing
sub-question: **the skeleton** — the tree datatype (typed sharing fields) + all obligations as
holes wired to the verbatim hbox anchor. **The hard part, named: the coverage theorem (Layer C)**
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
6. **DecoratedDescent disposition (open at council #1; closes in the adoption commit).** Two live
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
  homogeneity-scaling CoV. ADJUDICATED: DISSOLVE (cert-d2; architect shape-check pending).
  OPEN LEG: L≥3 coupled non-origin points discharge via the banked domination, NOT a chain-IH.
  Acyclicity verified (domination calls nothing; CoV strictly drops; disjoint owners).
- **region-glue** owns the ASSEMBLY only: finite covers gluing chart-local reads + the reduction's
  output into hbox. SETTLED EXACT (covdesign addendum): the SEPARATED leaf integrand is correct at
  corank ≥ 2 — the divisibility chain makes each true leaf a single dominant monomial × unit — so
  region_glue never consults `support`; its load-bearing precondition is `IsFullMonomialization`.
  ELDER AMENDMENT (rev-1 ratification): the leaf form is monomial × (bounded unit OR disjoint
  Morse core) — the Morse core is genuinely singular, contributes resRank/2 to the min, and
  `resRank ≥ minAdm` is a THEOREM of the tide (truth-witness obligation, never assumed); the
  separation conclusion stands; IsFullMonomialization is unaffected. OWNERSHIP (one owner): the
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
   construction recursion.
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
  hunt passes vacuously — never accept one as the gate.
- Watch transcription-level decoupling: a transcriber "simplifying" the carried monomial data is
  fork vocabulary; the sharing maps are the content (typed, per fork 3).
- Survey banked state before commissioning ANYTHING (3 redundant commissions last run).
