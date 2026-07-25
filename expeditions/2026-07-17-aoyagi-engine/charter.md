<!-- CHARTER — the fixed invariant core of this expedition.
     READ THIS FIRST, every wake / every convening / every brief. Elder owns it; controller commits.
     EDIT IN PLACE, NEVER APPEND. Hard cap ~1 page. If it grows, it decays like the logs did.
     History lives in journal.md / compass.md; TRUTH lives here. Compaction distills TO this, never away.
     Checkpoint: 2026-07-25 (ROUTE RE-ADOPTED — route-P/two-object RETIRED at the gate-routeB WALL
     (GateRouteB222); the ONE-OBJECT re-route ADOPTED, operator GO). §1-B rewritten to the one-object
     recursion; A/C/D/E unchanged. §1 FINAL — operator-confirmed 2026-07-21. -->

# Charter — aoyagi-engine

## §0  The frame (goal #0 — the thing that dissolves the drift)
We are building **Aoyagi's resolution-of-singularities machinery as reusable mathematics**, stated at
**full generality** — objects useful *outside* the headline. The learning-coefficient theorem
(`aoyagi_learning_coefficient`) is a **corollary and a test**, NOT the objective. Steering by the
headline is what produced the drift (twice): it makes *reaching the headline cheaply* the gradient,
which rewards re-derivation, MVP shortcuts, and category-wrong charts. Steer by the objects.

**"Done" for an object = the four-part blueprint bar (VERIFIED, never assumed):**
- **(i) GENERALITY.** Shown the object COLD (no headline), an independent mathematician agrees it is a
  natural/canonical object at the RIGHT generality — weakest hypotheses that suffice, in usable form.
  "The headline needs it" is not a reason; that motivation alone FAILS.
- **(ii) STRIKE-ABLE LEAVES.** Every proof leaf bottoms out at a statement we'd bet true and can sketch
  (hard proof-ENGINEERING, not new math); a leaf hiding open math is DECOMPOSED until the open part is
  ISOLATED and honestly NAMED a frontier leaf — never disguised as strike-able. The
  engineering-vs-new-math boundary is itself a deliverable.
- **(iii) COMPLETENESS / RISING SEA.** Blueprint the WHOLE object, not the headline's slice; a complete
  blueprint DISSOLVES critical-path guessing (leaves parallelize; you cannot mis-identify a critical path
  you are building all of). The structural antidote to MVP/headline-steering.
- **(iv) SOUNDNESS / NO SMELL.** Every statement is mathematically SOUND: true, correctly quantified (no
  missing hypothesis that makes it false, no spurious one that makes it vacuous), name = content — a
  mathematician reading the STATEMENT (not the proof) does not wince. DISTINCT from (ii): (ii) is about
  the remaining PROOF, (iv) about the STATEMENT — a leaf can be strike-able yet its statement subtly
  false (the worst case; "a sorry with a wrong statement misleads" — fix wrong statements first).

## §1  The objects (the goals). FINAL — operator-confirmed 2026-07-21.
- **A. RLCT ideal-invariance (Aoyagi Lemma 1), TWO-SIDED.** `rlct(Σfᵢ²)` depends only on the ideal `⟨fᵢ⟩`
  (both inclusions). Foundational — legalises every ideal-preserving step. STATUS: LANDED sorry-free (wave 1) — two-sided + weighted
  (`rlctAt/wrlctAt_sumSqFam_eq_of_germ_eq`, `Core.Aoyagi.IdealInvariance`), junk-0-guarded
  (`LocallyNullZeros`; Lean's `rpow 0^(−c)=0` demands it — guards dischargeable for
  polynomial/analytic families, `Waypoint`).
- **B. The product-ideal resolution** `⟨∏C⟩ = ⟨diag(b₁,…,b_M)⟩` — Aoyagi's Cases-1/2 (S,J) recursion,
  **IDEAL-LEVEL** (unimodular Schur-clearing `Q,P` maintain `⟨A⟩=⟨diag(1,Δ)⟩` with polynomial cofactors;
  the `b_i` accumulate; the block-elim cross-term drops as a product of generators — **NO coordinate
  substitution, NO degree-1 support-tracking**). corank≥2 = the SAME step iterated (coupling carried in `Δ`).
  STATUS (2026-07-25, ROUTE ADOPTED — the ONE-OBJECT re-route, cite-free BUILD, operator-GO + elder-gated):
  - ROUTE-P RETIRED — the TWO-OBJECT architecture (banked `buildTree`/ledger + post-hoc geometric charts
    bridged by symmetry-transport) WALLED at a decorrelated de-risk gate (`GateRouteB222.lean`, clean-three,
    branch `expedition/aoyagi-engine-gate-routeB`; 4 concordant confirmations — transport-group ⊥ cover-set,
    AND the chart↔leaf bridge UNBUILT + UNSTATABLE with banked assets). Mechanism + WHY in compass F9.
    SUPERSEDED ≠ REFUTED: the SPINE math (L-A/L-B/L-C Schur-clearing, b-chain, two-sided `hideal`) SURVIVES,
    consumed UNCHANGED.
  - COMMITTED = the ONE-OBJECT recursion (`reroute-plan.md`): a single `StageState` carries geometry AND
    ledger (`StepData`, via the SAME `stepUpdate` driving `buildTree`) in LOCKSTEP. Both walls dissolve
    STRUCTURALLY (the artifact was the two-object SPLIT, not a patch): siblings BORN pivot-generically from
    ONE constructor (`blockBlowupMap` pivot-parameterized + `maintenance_step_two_sided` pivot-generic, both
    verified), never transported (→ O1 gone); each leaf's ledger IS a `buildTree` leaf ledger by the shared
    transition, so `AtlasRealizesExponents`' value-only match is DEFINITIONAL via a bounded lockstep lemma
    (→ O2, the "unbuildable bridge", never arises). Aoyagi's own construction ORDER (charts+exponents
    together, worked.tex:609–625).
  - RESIDUAL to `exists_coreResolution:311` = the one-object recursion built end-to-end: `StageState` + the
    pivot-generic step constructor + the geometry-valued WF fold (over `conRel_wf`, the 9×-proven idiom) +
    the per-stage cover. Rung-gated **R0–R6** (`reroute-plan.md §3`). NOT OPTIONAL; SPINE verified
    sound+general, but render-bounded ≠ built.
  - RESIDUAL RISK, NAMED: **R3 (the geometry-valued WF fold) is THE risk** — the 9×-proven WF idiom is
    COMBINATORIAL; threading analytic charts + both `RegionRepresents` + cover-inflation through it is
    unproven + dependent-type-heavy (front-loaded de-risk fired). "definitional via a bounded lemma" ≠
    proven; R2 general-d cover box-inflation is rendered, not built.
  - STOP-FALLBACK (standing, at EVERY rung boundary): a wall on any rung → OBJECTS-ONLY close, citing
    `cited_aoyagi_lower_ax` (Watanabe upper + Aoyagi exact — PERMITTED; charter-faithful #94, §0: the
    objects A–E ARE the objective) — a charter landing, not a defeat; ADOPTING it is operator-gated.
    GUARDRAIL-0 (this week's lesson): NO geometry outside the step constructor.
- **C. Monomial-ideal RLCT** `= ½·min (h+1)/(2k)` (Newton polyhedron), in full generality. STATUS: LANDED sorry-free (wave 1) —
  the S2 boxed rule is a THEOREM under Aoyagi's own divisibility chain (`DivChain` guard excludes
  the coupled counterexample; `Measurable unit` delta), `Core.Aoyagi.MonomialRLCT`. The coupled
  case's remaining owed part is B's alone (the atlas min-over-charts CoV + the monument), not C's.
- **D. Codimension geometry** `codim{∏C=0} = minAdm = cCodim`, θ (top-component count),
  permutation-invariance (type-A quiver / Ext). STATUS: banked in `Core` (`minAdm_eq_cCodim` axiom-clean;
  θ unconditional) — reinforced by dev's cite-free determinantal geometry.
- **E. Analytic order ρ** (Aoyagi Lemmas 4–5): the RLCT / zeta-pole MULTIPLICITY — **NOT** the quiver
  (C,θ)-count. STATUS: **OPENED, SCOPED** (operator, 2026-07-21: "we build machineries, wisely, and
  understanding. So go. Build it." — the Rising-Sea expectation that the surrounding machinery may
  dissolve the headline's remaining hardness, recorded as the opening's rationale). The COMBINATORIAL
  half — θ = a(ℓ−a)+1 via Lemma 4's two-condition count over the built tree/foldState spine (register
  P6, re-priced M) — is IN BUILD; the ANALYTIC pole-order identification (zeta multiplicity — Mathlib
  lacks meromorphic continuation) remains monument-class, explicitly DEFERRED: the opening is scoped,
  not total. Statements pass elder ratification before any proving.
- Reductions R0/R1 (deepest point; product reduction → core): BUILT (bookkeeping).
- **Corollary/test:** `aoyagi_learning_coefficient_via_engine = C/2`. HONEST STATUS: the payoff is
  **CITE-FREE** (NO `cited_aoyagi`/`cited_watanabe` axiom in the cone — AxCheck-verified: cone =
  `{propext, sorryAx, Classical.choice, Quot.sound}`) **BUT carries `sorryAx` from the ONE geometric
  monument `exists_coreResolution:311`; it is NOT CLOSED.** "Cite-free" is NEVER reported detached from
  "sorryAx-via-monument, not closed." `hbox` is B's analytic shadow, never a separate goal.

## §2  The progress bar (what may be *called* progress)
A progress claim is valid ONLY if it names **(a)** the §1 object it discharges AND **(b)** the legal
construction-category (§3). A green build, a closed leaf, a passed gate, or a re-derivation that
discharges **no** §1 object is **NOT progress** — it is motion. The controller re-states the object +
category before reporting progress; the elder gates every route and every progress-claim against §0–§3.

## §3  Standing math-warnings (the drift, named — the highest-suspicion classes)
- **THE GEOMETRY IS NOT THE IDEAL IDENTITY — a `Resolution` needs `hideal` (the scope-correction,
  2026-07-24, geo-atlas-wire; the NEWEST drift).** `Chart.hideal_fwd`/`hideal_bwd` (`⟨(∏C)∘g⟩=⟨diag b⟩`,
  dom-wide) are MANDATORY fields; L6 (Jacobian) + L7 (cover) are NECESSARY-NOT-SUFFICIENT — they do NOT
  inhabit the `hideal`. The render's final scope-calibration OMITTED `hideal` from the residual,
  conflating "hideal math-verified (the L-A/L-B spine)" with "hideal Lean-inhabited" — that omission was
  the drift. A progress claim on "the geometric atlas" that does not account for the coupled `hideal`
  Lean build is motion. **RENDER-VERIFIED ≠ LEAN-INHABITED**; and the coupled hardness MIGRATED from the
  (dissolved) maintenance wall to L7's UN-PROBED coupled `hcover` — "the wall is bypassed" does NOT mean
  "the coupled hardness is gone." Probe corank≥2 `hcover` decorrelated BEFORE the full build.
> **RETIRED-AS-SUPERSEDED (2026-07-24, operator GO on the re-architect): the geometric-substitution-fold
> drift class.** The coordinate FOLD (`FoldStepInvAt`, `blockBlowupCoordQuot` divide-by-pivot, degree-1
> support-tracking, `couplingClear`, the WALL/KILL/#95/#98/#69) is RETIRED — the drift, not the object.
> SUPERSEDED ≠ REFUTED: those invariants were true where they held; the ENCODING drifted. Under option
> (b) the fold's `foldResid_case11` re-shape (#69) is MOOT — the fold is retired, not repaired.
> **ALSO RETIRED (2026-07-25): the two-object post-hoc-chart + symmetry-transport architecture (route-P),**
> WALLED at `GateRouteB222` (compass F9; transport-group ⊥ cover-set + unbuildable chart↔leaf bridge).
> GUARDRAIL-0: NO geometry is constructed outside the one-object step constructor — no composite-then-fan,
> no transported siblings. Re-entry at design time is the drift; guardrail-0 refuses it.
> **CONCRETE LEAN TRIPWIRE (R3 cover-wiring, the Lean-level form of guardrail-0/F9):** the banked PRE-reroute
> skeleton `Corank2Chart334.lean:122-123` proposes the survivor fan as *the K-symmetry ORBIT of gWrap* — that
> IS the retired O1 two-object transport (gate-routeB WALL, F9). R3 MUST born the survivor charts from
> `StepConstructor.bornSiblings` (per-pivot, transport-free); NEVER wire the cover through the K-orbit
> skeleton. Wiring the cover as a K-orbit re-enters O1 = DEAD ROUTE. Born-not-transported is the invariant;
> the K-orbit skeleton is a tombstone, not a tool.
- **The recurring category error (KEPT + VINDICATED — the PROOF the ideal route is forced):** no
  det-1 / a.e.-injective chart diagonalises the loss on an open set (each `(∏C)ᵢⱼ` is a nonzero poly,
  ≢0 on a dense open; exact diagonalisation forces ≡0, a non-open det-0 projection). The value LOWER
  bound is therefore **not** a chart change-of-variables — it is IDEAL-level. **STATE THE RESOLUTION FOR
  THE OBJECT** — the ideal identity `⟨A⟩=⟨diag(b)⟩` (polynomial cofactors), NEVER a coordinate-support
  predicate. A value-computing chart passes det/cover/measure gates and fails at the consumer, late.
- **The b-chain is LOAD-BEARING for the MAINTENANCE, not only the read-off.** `b₁|b₂|…|b_M`
  (worked.tex:484) is what makes the non-unit `diag(b)` step an IDEAL EQUALITY — the divisibility absorbs
  the block-elim cross-terms (L-B, rev-render-verified). Do NOT treat the b-chain as read-off bookkeeping.
- **The cite is not the proof.** The in-library kill-target is `cited_aoyagi_lower_ax` (½·codim ≤
  rlctGlobal(lossDLN)). GOAL: PROVE it via A+B+C and DELETE it. Citing it — or reporting any payoff that
  rests on it — discharges NO §1 object; it is motion. Endpoint: `aoyagi_learning_coefficient` cite-free
  AND sorry-free (both — cite-free alone is the `via_engine` state today, not "done").
- **Reuse dev's determinantal-geometry RESULTS for D (proved, cite-free); do NOT adopt L&R's
  quiver-representation THEORY** (Gabriel / orbit-closures / Ext-codim / the (C,θ) fibre-geometry) as a
  subject to build — the paper's OTHER programme, outside the RLCT-value scope.
- **NO minimum-viable-ing a named hard part** (esp. coupled-B). "Toric-trivial / elementary / bounded"
  clean headlines are UNVERIFIED until probed with decorrelated exact-algebra at the KNOWN failure cases
  (coupled corank≥2). The build is a FULL reproduce, never MVP'd; the tractability probe is a CHECK on a
  committed build, never a gate that scopes the object down.
- **The V-lower-lighter route is the F1-MIRAGE (3rd cycle — RETIRED).** V-UPPER (minimiser chart value
  `=½Mval`; `a_E=1`, `h_E=Mval−1`) is COMPLETE-GENERAL and bankable (deletes the Watanabe-ish upper cite).
  V-LOWER as a *lighter* lower bound is the mirage retracted THREE times (Phase-2 #1 primary-source; the §298
  re-attack; the pnp): "forward-only" was BACKWARDS — from-below IS the reverse (`⟨δx,δy⟩` witness). The
  mirage conflated "avoid the exact-principality monument `⟨I⟩=⟨b₁⟩`" (TRUE — avoided; the lower bound needs
  only the WEAK reverse) with "avoid the reverse entirely" (FALSE — the weak reverse = per-divisor
  no-over-vanishing = route P's DISTINCT realization residual, still needed). The lower bound is route P. Do
  NOT re-propose V-lower-as-lighter without a decorrelated probe exhibiting a genuinely-lighter per-divisor
  bound at coupled corank≥2 (none in 3 cycles).
- **The source-fidelity discipline (fidelity arc, 2026-07-23 — the deepest drift). Two composed gates:
  def-fidelity at BAKE time, paper-first at DEFECT time.** *BAKE:* a spine DEFINITION bakes only behind a
  source-fidelity certificate — the source construction and the Lean def, traced on the SAME concrete
  witness (incl. a WIDE witness), then DIFFED. A battery must exercise the LEAN def, never only a hand
  model of the intended math. *DEFECT:* when a statement-class defect surfaces, STEP 1 is the source read
  at the defect's location — has she already resolved this? For a fidelity project the prior is strong.
  Only then commission elaboration — which VERIFIES her answer, never de-novo-designs an object the source
  already has.

## §4  Durability
Read first, every cycle, by every role. Elder is sole author (holds the abstract-object frame; gates
against §0–§3); controller commits. `CLAUDE.md` points here. This file is what survives log growth.
