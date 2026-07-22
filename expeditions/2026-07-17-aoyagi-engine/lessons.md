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
