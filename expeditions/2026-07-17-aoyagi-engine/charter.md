<!-- CHARTER — the fixed invariant core of this expedition.
     READ THIS FIRST, every wake / every convening / every brief. Elder owns it; controller commits.
     EDIT IN PLACE, NEVER APPEND. Hard cap ~1 page. If it grows, it decays like the logs did.
     History lives in journal.md / compass.md; TRUTH lives here. Compaction distills TO this, never away.
     Checkpoint: 2026-07-24 (PHASE CHECKPOINT — rev-render landed + geo-atlas-wire scope-correction).
     Operator GO on the ideal-route re-architect; option-(b) build (the coupled hideal) scoped, not yet fired.
     §1 FINAL — operator-confirmed 2026-07-21 ("detag permitted"). -->

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
  STATUS (2026-07-25, ROUTE ADOPTED — route P, cite-free BUILD, elder-gated):
  - FOLD route RETIRED (§3); V-lower-lighter RETIRED as the F1-mirage (§3, compass F8).
  - COMMITTED ROUTE = P: the two-sided `hideal` (`⟨(∏C)∘g⟩=⟨diag b⟩`, BOTH ways, dom-wide) = Aoyagi's
    terminal normal crossing, reproduced over `buildTree` via the L-A/L-B/L-C Schur-clearing spine (flat
    Lean `Resolution` of leaf charts = her inductive recursion flattened; FAITHFUL — flat-vs-inductive is a
    Lean choice, not a math divergence). NO exact-principality MONUMENT: the lower bound needs only the WEAK
    reverse (per-divisor no-over-vanishing `ord_v(I) ≤ (h_v+1)/min`), NOT the uniform collapse `⟨I⟩=⟨b₁⟩`.
    Spine (L-A block-elim any corank / L-B (S,J)-maintenance, b-chain absorbs the reverse cross-terms / L-C
    terminal) rev-render+Codex verified sound+general.
  - The value engine rides the TWO-SIDED form (`IdealInvariance:447`; `Resolution` mandates
    `hideal_fwd`/`hideal_bwd`, `ProductResolution:114-116`). Route P subsumes V-upper. **Route P has TWO
    residuals:** (1) the (S,J) TWO-SIDED MAINTENANCE (L-A/L-B → terminal normal crossing) — INCLUDES the
    realization / no-over-vanishing as its REVERSE half (`hideal_bwd` = `AtlasRealizesExponents`; NOT a
    separate F-order axis); (2) the COVER (domain coverage) — GREEN via route-a (hcover + pnp converge).
    Realization ⊂ maintenance, DISTINCT from the cover (the `⟨δx,δy⟩` witness: chart present, coverage fine,
    F over-vanishes). The realization is PAPER-RESOLVED general-L (Aoyagi's own (S,J) two-sided maintenance,
    Cases 1&2, per her abstract — WITH the expedition's T-F totality drop; worked.tex:663's "deeper-mixed
    open end" is the EXPEDITION's thread-28 caveat, NOT Aoyagi's): detail-at-scale REPRODUCE-AND-VERIFY,
    #124 instance-verified GREEN at (3,3,3,2,2)/L=4 (ONE instance — confidence-up, NOT general-proof). The
    general-L Lean reproduction is the build labour (paper-resolved ≠ built).
  - DE-RISKS: (a) [PIVOTAL, LIVE] the corank-2 TWO-SIDED END-TO-END first-brick gate (`hideal_fwd`+
    `hideal_bwd` dom-wide + realization at (3,3,4) + full-fan cover atom, green-BOTH → START the full
    `buildTree` build); (b) [DISCHARGED] the deep-mixed realization monument-risk — paper-first
    (worked.tex:663 = expedition caveat, not Aoyagi's) + #124 instance-GREEN; the general-L reproduction
    folds into the build labour. RED-flip on the corank-2 gate (a), or a general-L reproduction stall in the
    build, → OBJECTS-ONLY close. Residual to `exists_coreResolution:311` = the two-sided `hideal`
    reproduction (L-A/L-B/L-C over `buildTree`, incl. the reverse/realization) + full-fan cover. NOT
    OPTIONAL; paper-resolved ≠ built.
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
