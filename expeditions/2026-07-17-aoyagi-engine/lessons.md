# Lessons — aoyagi-engine (append; promote-or-decay at close)

Inherited at genesis (predecessor + retro, already promoted into policy/brief — recorded here so
the trail is local):
- Truth witness at pin time (obligation-2: false for days, killed by a one-line integral).
- Exact-steps-only where the budget is tight (every lossy split was false at binding cells).
- Survey banked state before commissioning (3 redundant commissions in the predecessor).
- Verify a teammate actually stopped before spawning a successor (checkpoint ≠ stop).
- Non-isolated spawned subagents must never git-op a shared tree (a `reset --hard` destroyed live
  work once); explicit worktrees per seat here.
- Verify formulas against the paper PAGE IMAGE, never extracted text (a false "typo" came from
  garbled extraction; a real typo [Def 3] survived it).
- Pin lemmas by STATEMENT, not name-vibes: the compass pinned `MinAdmMono` for threshold
  preservation; the correct pin is the minAdm-as-minimum property (inf'_le class) — opposite
  direction. Caught at covdesign D2 before any formaliser grabbed it. (2026-07-17)
- A monomial-only exhaustiveness hunt is VACUOUS for blow-up coverage claims (extremal valuations
  are non-monomial/incidence); gates need coord-changed + weighted-center tiers. (covdesign D4)
- A "coordinate-changed" hunt WITHOUT shear-exposing the product-vanishing conditions is as vacuous
  as a monomial hunt — the hunter must fix the instrument before trusting it (hunt-t03 caught the
  spec's false-pass and replaced grid sampling with an exact continuous-weight LP). (2026-07-17)
- Python RAW strings keep backslashes: an rf"..." map edit wrote literal \" into claims.yaml,
  breaking the parse — banked broken because the pre-commit hook was NOT installed in the worktree
  (hooks need core.hooksPath per checkout). Hook now installed; validate after EVERY map edit.
  Caught by the reviewer, not by me. (2026-07-17)
- An `inferInstance` probe WITHOUT surveying imports is not evidence of a missing instance: the
  "Params not normed" blocker was closed weeks ago by a 0-sorry module consumed in 13 files
  (ParamsFlatLinear); the probe ran importless and a false "hard fact" nearly forced a route. The
  survey-first rule applies to INSTANCES, not just lemmas. (seat B catch, 2026-07-17)
- An elder-RATIFIED amendment is not landed until a grep/reviewer CONFIRMS it in the statement:
  the resRank fold was ratified at rev-1, recorded in compass, and still absent from
  terminalExponents — caught only by the fresh round's counterexample. Ratification ≠ landing;
  verify amendments like any other claim. (cert-carrier-review, 2026-07-17)
- A relation that never reads the CHILD certifies nothing about transitions: StepRel read only
  the parent + case tag, so any child exponent passed — and the in-file witness "passing" was a
  symptom of the weakness, not evidence of the design. When a predicate is justified BY a specific
  equation (the case-1(1) merge), grep that the equation's variables actually appear. (2026-07-17)
- A "hypothesis-free" green on SHALLOW instances is a confound: the "minimality-free
  SameLevelChainInv" claim passed all L≤3 tests and was REFUTED at the minimal L=4 instance
  (2,2,3,3,2) — the eligible sets at L≤3 are too shallow to expose the dependence. When a
  hypothesis seems droppable, escalate the instance DEPTH before believing it. Caught by the
  claimant itself in finalization. (pnp o4 cert Part 7, 2026-07-18)
- **DIAGNOSE-FIRST, don't race to solve (operator standing rule, 2026-07-20).** When the operator
  asks "what is the issue / why is X / what's the right solution," they want to UNDERSTAND it first —
  diagnose, report, and WAIT for their steer before touching code. I raced on the cordon slowness:
  asked "what's the right solution," I immediately implemented a prune (broke a caller → mis-diagnosed
  → left a 99.9%-CPU zombie audit). The fix wasn't even validated as a fix. Report the diagnosis + the
  known-vs-unknown, then stop. **Why:** racing manufactures churn + wrong fixes + hides the fact that
  the issue isn't understood; the operator's question IS the work at that moment, not the patch.
- **Don't conclude from a KILLED/unfinished run (2026-07-20).** I claimed "the prune didn't fix the
  perf" from an audit I killed at 8:32 while it was still running — a lower bound, not a measurement.
  Both the 32-min and 8-min cordon runs were killed unfinished, so there is NO before/after timing.
  A killed run bounds-below, it does not measure; let it complete (or don't claim the delta). Same
  reasoning-from-incomplete-data family as the shallow-instance confound above.
- **TaskStop kills the wrapper, not the detached child (2026-07-20).** A 32-min `cordon-audit`
  survived its task's TaskStop, burning a core. For a runaway build/audit, `pkill` the process.
- **ADJUDICATION IS NOT THE BUILD — pin the shape, then build (operator-caught, 2026-07-20).** Instances
  NEVER prove a ∀-general statement; a sequence of pen-and-paper adjudications ("verify one more instance")
  is the avoidance dressed as diligence — the exact shape of the coupled-B dodge across expeditions. RULE:
  adjudicate only enough to pin the SHAPE (e.g. single-divisibility-chain vs multi-generator ideal); once
  the shape is determined, the ARCHITECT + FORMALISERS BUILD — the ∀-statement as an honestly-named FRONTIER
  LEAF (a proof target), not adjudicated-away with more instances. A pnp result that WOULD spawn "one more
  instance" instead spawns the build. **Why:** instances characterize, the build proves; a loop of
  characterizations never reaches the theorem. Guard against BOTH failure modes — adjudicate-forever (dodge)
  AND build-on-one-instance (shallow-instance confound); the correct dose is "exactly enough to pin the
  shape, then build." (Operator: "are your fresh teammates dodging the hard part … yet another adjudication?")
- **Don't race to process-cleanup on a "killed" signal — the operator may be relaunching (2026-07-20).**
  On a `cordon-batch` "killed by user" task-notification I applied the detached-orphan-survives-kill lesson
  and killed the `lean`/`lake` procs in its worktree to free cores for the architect — but the operator was
  simultaneously RE-INSTRUCTING the same teammate to continue; my kill may have interrupted its
  operator-directed build. A "killed" agent is NOT necessarily abandoned — the operator may relaunch/redirect
  it. Note orphans and WAIT (the `scripts/lb` semaphore caps runaway workers anyway); do NOT rabbit-hole into
  process forensics + killing. When the operator is actively managing a teammate, go hands-off: no cross-talk,
  no touching its worktree/procs. Same stay-out-of-the-grind + diagnose-first-don't-race family.
- **An unpushed agent branch is NOT banked — the VM death cost us the blueprint (2026-07-21).** Teammate
  briefs said "commit on your branch, do NOT push (the controller integrates)". The VM died; every unpushed
  worktree branch vanished — including the architect's entire A–E blueprint (~430 LoC + its repair,
  2f9ddd66b/84871a088). Branch pushes are PRE-AUTHORIZED (standing instruction) — withholding them bought
  nothing and risked everything. RULE: any teammate producing a substantial artifact (a module, a cert with
  batteries, >~50 LoC) pushes its worktree branch to origin ON COMMIT — integration review is unchanged
  (the controller still gates what enters the expedition branch); the push is a BACKUP, not an integration.
  Controller: put "push your branch" in every build-seat brief; on receiving a report, verify the branch is
  on origin before relying on it. (Mitigation that saved us this time: a pre-death flush banked the
  integrated cordon chain + all certs; only the never-pushed architect branch died.)
- **Instance work requires a COVERAGE CLAIM; no representativeness without one (operator-caught,
  2026-07-21).** The d=(1,2) rung was selected as "smallest instance where the machinery runs" but SOLD
  as "genuinely singular" — false (N=1 coreGen is linear: zero recursion steps, no coupling, no
  singularity; it validated the record plumbing only). The gap: the kill-set selection discipline
  (explicit, verified structural criteria for WHICH failure axes an instance exercises) applied to
  adjudication seats but not to validation rungs. RULE: any instance artifact carries an explicit
  coverage line — "exercises axes {…}; does NOT exercise {…}" — verified before any representativeness
  claim; an instance without one is a plumbing test and must be billed as exactly that. COROLLARY: no
  validation instances on a monument path — generalize from the paper + ∀-certificates, use instances
  only as falsifiers/satisfiability-witnesses/decide-anchors; the first singular instance falls OUT of
  the general build as a showcase, never precedes it as a rung. (The expedition's own data concurs: the
  universal-in-D leaf-2 was CHEAPER than the instance-reuse route it replaced.) **Why:** point analysis
  without a generality argument overfits — the template teaches the wrong instincts precisely when the
  instance is unrepresentative, and the mislabel travels further than the artifact.
- **The free-edge leaf design was the monument's churn engine (process self-audit, operator-prompted,
  2026-07-22).** The leaves quantify over a free `TreeEdge`; the paper has no free edges. Every one of
  ~10 statement-defect rounds was the same event: a free field (center extent, pivot placement, shear
  support, coefficient window, nextState transition) admits an instance the construction never produces;
  a seat catches it; one of Aoyagi's constraints gets re-derived as a bolted-on hypothesis, at a full
  catch→ruling→re-bake round each. The field audit's own closure statement names the destination the
  design should have started from: the pin set is the BRIDGE-FREE SHADOW of `IsRealBranch` — the
  free-ed generality had no second consumer and converged to construction-pinning anyway. RULE: state
  proof-carrying skeleton leaves over the CONSTRUCTION's objects (or carry the full construction pin as
  ONE hypothesis) unless a named second consumer wants the abstraction; speculative per-field generality
  on a monument path buys adjudication rounds, not reuse. (Cost containment that DID work: statement-lock
  + stop-on-suspect meant zero proof lines were written against a moved statement.)
- **Elaborate-then-render beats render-then-adjudicate — the controlled comparison (2026-07-22).** The
  E-lane had the #42 encoding certificate (a worked template) BEFORE its build: three parallel tracks,
  every rfl bridge held, zero rework. The monument rendered without a template: ten defect rounds. The
  pnp-elab retrofit (fold-recursion template: certified Schur step, four transition laws incl. a
  no-J-advance case nobody had asked about, a simulator reproducing minAdm on four instances, 14
  pre-mortems) produced in hours what the reactive rounds circled for a day. RULE (operator
  clarification, now in the role file): pen-and-paper's primary function is ELABORATION — the fully
  worked template the render seats build from, blind to the Lean — not adjudicating shortcuts around
  detailed work. Every substantial render unit gets a template first.
- **Statement authorship belongs to the proof owner; direction to the elder (2026-07-22).** Two defects
  of the round were in the ELDER's own rendered sentences (the ∀ℓ per-layer form that failed its own
  induction gate; the earlier amended-pin literal). The division that worked and is now the rule:
  the elder rules the OBJECT (direction, page fidelity, weakest-that-inducts), the PROOF SEAT locks the
  exact rendered form, and batteries check both sides (the breaker dies AND the construction's child
  passes) before anything bakes.
- **The two-seat render pipeline (architect dictates, render seat types) added hops, not judgment
  (2026-07-22).** arch-C ↔ foldstate-render: the gate function earned its keep repeatedly (false
  docstring, stale fragments, transcription drifts), but the split seat contributed hands only, and the
  message hops between them were where the oscillation/crossing noise lived. Gate checks here are
  mechanical and objective (build, grep, forced #print, text-vs-ruling diffs) — safe as a second PASS in
  one seat, with the decorrelated second READ staying in a different seat (elder) and the controller
  re-verifying at integration. Next harness: one architect seat that renders then gates its own render.
- **Echo volume is a real cost (2026-07-22).** A meaningful fraction of the round's messages were
  content-free holds/acks/state-echoes, each resuming an agent for nothing. Ack-protocol exists to
  prevent LOST messages, not to require ceremonial ones: acknowledge state CHANGES; never resume a
  correctly-holding seat to tell it it's correctly holding.
- **Briefs drew on controller memory, not the map's reuse artifact (operator-surfaced, 2026-07-22).**
  Spawn briefs were in-spirit template-compliant (target, worktree, gates, discipline, report shape) but
  the what-you-must-know section (CONSUME/STAGED banked lemmas, dead routes, battery members) was
  hand-composed from the controller's context every time — `scripts/expedition brief <node>` never ran,
  and no codebase-shape artifact existed to draw from. It worked (e.g. the QIP water-filling pointer that
  collapsed the sorted-box sub-development came from controller memory) — but that is the controller being
  lucky-good where the system should be reliable. FIX: the cartographer now owns a maintained
  CODEBASE-SHAPE artifact (cluster map + dependency arteries + reuse index + frontier line,
  map/overlay/codebase-shape.md) as the source briefs draw from; use the generated-brief path where map
  nodes exist. SECOND deviation to note honestly: the template's "no peer-to-peer coordination" was
  deliberately relaxed for integration mechanics (seat↔seat channels) — it saved controller hops but is
  also exactly where the crossing/oscillation noise lived; next harness should scope peer channels to a
  declared interface (one topic, one pair, controller cc'd) rather than open-ended.

## The sufficiency check must cross-check STATED hypotheses against every lemma the soundness argument invokes (2026-07-22, hpos miss)

arch-C's derived-lemma sufficiency check ruled realBranch_terminal_edgeδ sound via "terminal ⟹
rollover ⟹ cleared ≥ 1 ⟹ δ = false by widthMinUpto_pos" — but widthMinUpto_pos requires
`hpos : ∀ k, 0 < d k`, and the STUB didn't carry it. The argument was right; the statement it
certified didn't contain the argument's premises. seat-L3T2's SPECIFY (proof-seat stress-test)
caught it with a concrete counterexample (d 0 = 0). Same family as the free-field and
cover-sufficiency misses: a checker that reasons about a statement without diffing the
statement's hypothesis list against the invoked lemmas' hypothesis lists. **Rule: when a
sufficiency/soundness argument cites a named lemma, list that lemma's hypotheses and check each
one is present in (or derivable from) the stub's stated hypotheses — mechanically, not from
memory.** The decorrelated proof-seat read remains the backstop; the elder's degeneracy
discriminator (does the conclusion degenerate at the boundary the dropped hypothesis excludes?)
is the fix-once scoping tool.

**Extension (same day, second instance — the SHAPE dimension):** the multiAffine edge-form miss.
The sufficiency check verified the stub TRUE-as-stated but never cross-checked its OUTPUT SHAPE
(the parent's residual, at the edge) against the consumers' NEED (the child's slot property) —
so a true, well-hypothesized stub was still undischargeable by every consumer. The rule extends:
at the stub-mint gate, check BOTH directions — (i) hypotheses: each invoked lemma's premises
present in the stub (the hpos instance); (ii) shape: the stub's conclusion instantiable to what
each named consumer actually consumes (node/edge, parent/child, the exact carrier). Where the
gate-holder cannot verify a consumer's internals, route the shape question to the proof-seat
consumer BEFORE the mint — the decorrelated proof-seat read caught both instances.

**Third instance (same day — the induction-BASE case): the node-form multiAffine root gap.** The
elder's node-form ruling certified the statement "inductable (root = coreGen, one factor per
layer...)" — the root argument NEEDS e linear, and he_lin was in the argument but not the
statement; seat-L3T2's SPECIFY refuted it with e u = u³ (he0 holds, he_lin fails — the
counterexample pins the exact missing premise). The rule sharpens: **"inductable" is not a
shape-check — enumerate the induction's cases (BASE included) and diff each case's premises
against the stated hypotheses**, exactly as rule (i) does for invoked lemmas. Also the
architectural lesson: a node-form derived off bare provenance RE-DERIVES the base case,
silently relocating hypotheses that the carried-invariant formulation keeps where they belong
(the fold's root, L5). Prefer step-form descent off the carried invariant when consumers already
hold it.

## The guard-domain family (3 instances) → the elder's STANDING RENDER CHECK (2026-07-23)

hpos (terminal_edgeδ), he_lin (the node-form root), hlayer (the step-form boundary) — one
family: an induction sketch's implicit domain assumption not carried into the statement's type.
The elder's proposed standing check, now adopted at every stub mint: **every derived stub's
statement must be true on the FULL quantifier range of its binders, or carry the guard that
scopes it.** The discriminating question per binder: enumerate the boundary configurations of
the quantified structure (layer = N, cleared = 0, empty support, rollover-degenerate d) and
check the conclusion at each — a statement that fails at a reachable boundary either gains the
guard (if the boundary belongs to another regime's owner: hlayer — cheap, consumers already
inhabit the domain) or is the wrong shape (if the guard would exclude the intended domain:
he_lin — reshape instead). seat-L3T2's SPECIFY discipline (refute-before-prove at the
boundaries) is the enforcement mechanism; three-for-three it caught what the authoring sketch
glossed.

## A delta-read gate is NOT a closed gate — pair it with PROOF-PRESSURE before claiming "closed" (2026-07-22)

The seven statement bakes each passed an elder delta-read (internal consistency: name=content,
weakest-hypothesis, the guard-domain family). I called the statement layer CLOSED on that basis. It
was not. When the proof seats ran the ACTUAL proofs against the baked statements, three grounded
holes surfaced that every delta-read missed:
- **boostReady** — the CanonicalSchurStep conjunct is SUPPORT-only (`∀ u k, shearφ u k ≠ 0 → …`),
  VACUOUSLY true for identity shear. A delta-read checks the conjunct reads sensibly; it does not
  ask "what is the WEAKEST model satisfying this predicate?" — which is exactly what a proof (or a
  refutation-minded Codex) does. The predicate admitted R_bad; boostReady is false on it.
- **L7** — the pivot value-pin (single canonPivotOf) makes the cover statement FALSE (ε·e_q escapes
  the shared outermost root blow-up). A delta-read verified the pin was consistent; it did not run
  the cover argument, which needs the pivots FANNED.
- **descent δ=1** — the strict transform of a hslot-satisfying residual can be the constant 1; the
  cofactor structure isn't in the hypotheses. Only writing the proof exposed it.

THE PATTERN: a value-pin asymmetry (center/pivot got VALUE pins; the shear got only a SUPPORT pin)
and an over-pin (pivot pinned to one choice when the cover needs a fan) both READ fine in isolation
and only fail under proof-pressure. THE RULE: "statement-locked" earns "closed" only after a PROOF
(or a decorrelated refutation-minded instrument tasked to find the weakest satisfying model) has run
against it — not after a consistency delta-read alone. Operationally: before declaring a statement
layer closed, each baked statement must have either (i) a landed proof, or (ii) a SPECIFY from the
seat that will prove it, confirming the hypotheses suffice against a concrete adversarial model. The
delta-read is necessary, not sufficient. (Corollary: the frame-in/hypothesis-out decorrelation is
strong but not immune — the elder + seat-L4's pre-Codex flag CONVERGED on a proof-side reading and
BOTH missed the vacuity; the third, refutation-tasked instrument (Codex) caught it. Keep a
refutation-minded instrument in the loop, not only convergence-seeking ones.)

## Definitions need SOURCE-FIDELITY gates, not just consistency gates — and batteries must consume the LEAN DEF (operator-caught, 2026-07-23)

The unfaithful-shear episode was NOT undiscoverable: the paper's construction — the per-chart Q,P
normalization WITH the deeper-factor compensation A^(S+1)→Q⁻¹-conjugated — was worked out in the
source AND in the repo's own worked.tex (:443-457, :565-567, the recoordinatized ∏C^(s)) the whole
time. Two process holes let the divergence live for weeks:

1. DEFINITIONS WERE NEVER SOURCE-DIFFED. The gate structure reviewed STATEMENTS hard (delta-reads,
   guard probes — 6 catches) but treated spine DEFINITIONS (foldResid, canonShearOf, IsRealBranch)
   as data needing only internal consistency. The available check — transcribe the source step on a
   witness, trace the Lean def on the same witness, DIFF — was never run at def-bake time. It is
   exactly what pnp-transport ran post-hoc (oracle_trace + honest_clear vs the fold), which caught it.
2. THE KILL-BATTERY TRACED A HAND MODEL, NOT THE DEF. case11_boost_readiness.py verified the math on
   the model Z·B·diag(1,Δ)·Q⁻¹ — WHICH INCLUDED the Q⁻¹ (the model was faithful to the paper). The
   Lean fold lacked it. The battery consumed the model, so the decorrelated instrument green-lit the
   right MATH while the definition diverged from it. A battery that does not consume the actual
   definition is a rigorous check of the wrong object.

THE RULE (standing, both directions):
- Every SPINE-DEFINITION bake carries a SOURCE-FIDELITY CERTIFICATE: a pen-and-paper elaboration of
  the source construction on ≥1 concrete witness + an exact trace of the LEAN definition on the same
  witness, diffed term-by-term. (The N_p round now does this by construction; the rule makes it
  permanent.) Fingerprints like "representation NOT taken; no redesign" in a def's docstring are
  DEFERRED-DECISION MARKERS — each one needs an owner and a re-open trigger, not just a note.
- Kill-batteries and worked models must EXERCISE THE LEAN DEFINITION (via a faithful transcription
  generated FROM the Lean, or a trace harness), never only a hand-built model of the intended math.
  Model-vs-def agreement is itself a check to run, not an assumption.

## Paper-first defect diagnosis — step 1 is "has the paper already resolved this?" (operator, 2026-07-23)

The 10th/11th catches (cap-escape; the missing b-chain in the carried invariant) prove the rule by
their own record: the b-chain was in the paper (worked.tex:571/616/626), worked out, AND verified
by our own N_p certificate §3 per-step ("N_p reproduces Aoyagi's b-chain and M_{s,k}") — the
carried invariant just never transcribed it. The descended-block shape on wide instances is her
M_{s,k} bookkeeping — readable directly from her recursion. Both defects were transcription gaps
of PAPER-RESOLVED content; neither was new mathematics. Yet the controller's diagnostic response
fired empirical traces, candidate-field designs, Codex consults, and consumer tables in parallel,
with the worked.tex read sitting as one input among five instead of the FIRST.

THE RULE (standing; the defect-time counterpart of the def-fidelity gate): when a statement-class
defect surfaces, STEP 1 is the source read at the defect's location — what does the paper do here,
what is HER object, has she already resolved this? Only then commission elaboration (traces,
candidate designs, decorrelated consults), which then serve as FIDELITY VERIFICATION of her answer
and as the acceptance battery — never as de novo design of an object the source already has. For a
formalisation-fidelity project the prior is strong: most statement defects are under-transcription
of resolved source content, and the source is the cheapest, most decisive instrument. Composition:
def-fidelity gate (charter §3) governs BAKE time; paper-first diagnosis governs DEFECT time.
(Charter fold-in is the elder's, flagged 2026-07-23.)

## Def-facts in rulings carry a def-verification or an "unchecked inference" flag — the reflexive def-fidelity lesson (elder-authored root cause, 2026-07-23)

The ruling's first §2 stated the frame mechanism BACKWARDS ("foldResid's argument is post-shear;
the birth-corner coordinate is frame-correct"). Root cause, in the elder's own words: the ruling
asserted a DEF-LEVEL fact from the elder's model of the fold (it composes through pathMap), NOT
from a def-verification; seat-L4D's foldG_eq_pathMap check showed PRE-shear (a combination, not
a coordinate). The charter §3 def-fidelity gate applies REFLEXIVELY to the adjudicator: a ruling
that asserts a def-level fact must cite the def-check, or explicitly flag the assertion as
INFERENCE-TO-BE-CHECKED. Convergence is not verification — the elder's intuition and the
post-shear reading agreed with each other; only the third, MECHANICAL instrument (the def-trace)
broke the tie. Same family: the controller pairing lesson (artifact-first, brief-second —
commit amendments BEFORE briefs quote the artifact), which governs the propagation timing; this
one governs the assertion's provenance. The ruling's CONCLUSIONS survived (F-value/combination
was independently right); only the stated mechanism was backwards — caught before any statement
locked, by the compounding holds.

## Ruling-churn propagation — the two-halves lesson meeting at the FROZEN SPEC (elder + controller, 2026-07-23)

The §8 adjudication was fast and multi-datum: four elder self-corrections (the field, the
frame, the criterion, the block mechanism), EACH forced by data arriving in sequence (the R3
discovery, the def-facts, worked.tex:445, Lemma 2, the block verdict) — not avoidable error.
What WAS avoidable: the interim states carried premature "FINALIZED" labels, which made them
look mergeable and outpaced the long-turn seats — arch-C rendered a full, high-quality
implementation of the RETRACTED field because its launch brief anchored while five re-scope
messages sat processed-but-not-adopted in its queue.

THE COMPOSED RULE, two halves meeting at the frozen spec:
- ELDER-SIDE: in a fast multi-data-point adjudication, hold "FINALIZED" until ALL gating data
  is in; deliver interim rulings as explicitly PROVISIONAL with the pending data NAMED; the
  FROZEN SPEC (one numbered section, e.g. §8(i)) is the only artifact seats act on.
- SEAT-SIDE (controller-enforced): seats render ONLY against the frozen spec — never interim
  messages, never the launch brief — and every re-scope of a long-turn seat is gated on an
  ACK-AND-RESTATE (the seat re-derives the scope in its own words before continuing; message
  delivery is not scope adoption; the anchor wins unless broken by re-derivation).
Both halves are the same antidote: ruling-churn must terminate at ONE named contract before
any seat spends a turn on it. Related: artifact-first/brief-second (propagation timing) and
def-facts-with-def-checks (assertion provenance) — the three together cover authoring,
propagating, and consuming a fast-moving ruling.

## Briefs name their sources by exact path — "the paper" is ambiguous here (operator, 2026-07-23)

This repo carries TWO source papers: L&R 2024 (CLAUDE.md's headline, the *fibre-geometry* paper) and
Aoyagi 2023 (this expedition's subject, the *resolution/RLCT* paper). A brief that says "the paper"
resolves differently per reader — the #63 audit drifted to an L&R sweep exactly this way. **The
brief-giver owns the ambiguity, not the reader**: every commission/brief that references a source
names it by exact file path (paper-sources/..., theory/aoyagi-2023-reproduction/...) and, where the
risk exists, names what is OUT of scope. Applies to every paper reference in every brief.

**Record correction (operator, same date):** the elder's "L&R printed-rlcm off-by-one" finding is
WITHDRAWN as an erratum candidate — L&R's θ is the count of top-dimensional fibre components, NOT
the rlcm (pole multiplicity, Aoyagi's a(ℓ−a)+1); two different quantities, no discrepancy, no
authors' correspondence. Conflating quantities that share a formula's neighborhood is the same
class of error as the source ambiguity above: name the OBJECT, not just the formula.

## (B) ≠ (D): name the PROPERTY an instrument tests, not just the object (L4D, 2026-07-24)

The capstone obstruction survived 25 instruments because they all tested property (B) (degree ≤ 1
per coordinate) while the wall needs property (D) (center-sub-ideal membership) — and (B) does not
imply (D). A render that "re-checked the batteries" would have re-proven (B) and shipped the (D)
hole. **Why:** a battery's PASS certifies exactly the property it computes, and near-miss
properties feel interchangeable in prose ("multilinear-clean" read as "supported on the center").
**How to apply:** every battery row and every claim card names the PROPERTY as a formula (the
ideal, the degree bound, the membership — not an adjective); when a consumer needs property P,
check the instrument history for P ITSELF, not for its neighbors; a verification claim without its
formula is treated as unverified.

## Witnesses are chosen by the AXIS they exercise, not by size (pnp-cap, 2026-07-24)

The width-cap defect survived every prior battery because all witnesses were width-NON-increasing
— the cap bites only when d[ℓ] > min(d₀..d_{ℓ−1}), and (3,2,2,2), though "wide", never trips it;
(2,3,2,2) is the minimal witness that does. A witness that cannot falsify the claim is a spurious
PASS generator. **Why:** each def guard/case corresponds to an axis of the input space; a battery
covers a claim only if some witness crosses each axis the claim's guards read. **How to apply:**
when mandating witnesses, name the AXIS each one exercises (width-increase, depth, multi-coupling,
interior-vs-corner pivot, …) and check the claim's guards for axes with no crossing witness; "wide"
or "big" is not an axis.
