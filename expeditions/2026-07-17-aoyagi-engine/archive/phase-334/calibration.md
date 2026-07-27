# Calibration — aoyagi-engine (navigator office)

Predicted-vs-actual per major node; brick durations vs estimates; lanes idle against gates that
already opened. Seeded at navigator pass #1 (2026-07-17, the design→build phase transition). This is
the navigator office's single-writer artifact; the controller merges it from `--nav`.

## Design phase (genesis → validated carrier) — the actuals

| node / event | genesis prediction | actual | delta |
|---|---|---|---|
| carrier (resolution-tree) | typed sharing datatype, one adoption pass | `validated` in ~1 day (genesis 17:55 → validate ~20:12), **2 review rounds** | on-time; the 2nd round was the equilibrium cost of the C1/C2 criticals |
| skeleton shape | **6-obligation fan-out** (engine-route needs 7 nodes) | review r1 **collapsed 4 obligations into `monomialization_terminates`** via the `CanonicalResolution` bundle → **2 holes** (construction + `region_glue`) | **MAJOR**: the anticipated parallel-obligation build is a **serial long-pole** build. Re-plan the build loop around it (pass #1 disposition). |
| coverage (the named hard part) | "holds a lane from day one" (own tide) | designed (cert-d3) + **hunt SURVIVED** (5 decorrelated legs, 0 undershoots); PROOF now a **conjunct of the construction hole**, not its own lane | hard-part tracking must shift from "oldest open hole age" to "distinguished, separately-witnessed sub-target inside the construction tide" |
| route adoption gate | council + skeleton + battery | 2×ADOPT + fit-example elaboration + battery 12-green + fork-6 TOMBSTONE | ran clean; fork-6 (DecoratedDescent) resolved by the pre-agreed tombstone rule (would re-import the refuted decorated-peel object) |
| review-to-equilibrium | AUDIT gate, ≥1 round | **2 rounds** (r1 VALIDATE-WITH-CHANGES: 2 CRITICAL + 4 MAJOR; r2 VALIDATE), within cap 4 | **WIN**: the "unprovable-socket" disease (junk-leaf under-determination) caught at the **carrier gate, pre-tide**; the predecessor caught the same class **3 days post-pin** |
| hunt (coverage no-smaller-ratio) | decorrelated hunt as the universal-claim gate | SURVIVE; scope stated in `threads/03-hunt/hunt-cert.md §5`; map cites scope-by-pointer, **not** blanket-established | gate honoured; residual scope parked (angular beyond (2,2,2,2), 3rd+ blowups, (4,4,4,4) full, optional D-module check) |

## Standing calibration notes (carry into the build loop)

- **The bundle changed the DAG.** `coverage_theorem` / `exponent_ledger_bridge` / `reduction_layer` /
  `case_step_invariant` are now **proved projections** of `resolutionOf_spec` — their content lives
  inside the ONE construction hole `monomialization_terminates`. There is no 4-way parallel tide to
  commission; the parallelism in the build loop is between the **construction long-pole** and the
  **shorter satellite lanes** (region_glue design, the de-risk witness, the P8 library lane).
- **`region_glue` is a sorry-propagation node, not a build-time-blocked one.** Its proof consumes
  `resolutionOf_isFullMonomialization` (a proved projection of the *sorried* `resolutionOf_spec`), so
  it is buildable against the statement-locked construction — but its current signature is a
  **PLACEHOLDER** (rev finding 2: the chart↔integrand CoV bridge is absent; signature will gain
  hypotheses). Its TIDE waits on a design-first pass, **not** on the construction.
- **Truth-witness-at-pin-time is owed on the new bundle.** The `CanonicalResolution` predicate (5
  conjuncts) is a post-repair obligation shape; the in-file witnesses (`witNode`/`witLeaf`/`witTree`)
  show component non-vacuity, **not** a full `∃ t, CanonicalResolution M t` at a concrete `M`. Standing
  rule 2 (brief) + rev finding 4 both call for a finite-M witness (e.g. the (r,r,4) class) before the
  generic construction is trusted.

## Open at pass #1 (feed the next pass)

- theorem4-localization: adjudicated DISSOLVE (cert-d2) but "architect shape-check pending" — and the
  **architect stood down + worktree reaped (tick 8)**. Shape-check has no live owner. (Gate-verif gap.)
- Map hygiene: `resolution-tree` node status = `validated` but its `notes` still describe round-1
  "validation WITHHELD" — stale note contradicts the field. (Controller-owned fix.)

## Next trigger
Navigator pass #2: the build→assembly phase transition (the construction hole discharged, both
projections + region_glue landing into `engine_box_threshold_finite`), OR the assistants cadence
(~60 canonical commits / ~4 h activity since genesis; ~40 at pass #1), OR a crux lane going serial.

## Design phase 2 (restructure arc: tick 18 → tick 37) — actuals (navigator pass #2, 2026-07-18)
| node/event | pass-#1 expectation | actual | delta |
|---|---|---|---|
| carrier shape | validated (r2, tick 15) — treated settled | RE-OPENED by lane-2 vacuity (tick 18) + architect Codex review (tick 19) → edge-labelled RESTRUCTURE, council of two, fresh r1 VALIDATE-WITH-CHANGES (2 CRITICAL) → repair → r2 VALIDATE (tick 37) | MAJOR under-estimate: genesis assumed the node carrier; true carrier cost ~4 review rounds (2 initial + 2 restructure), not 1-2. The council's forecast that the carrier is the design crux was CORRECT. |
| green-checkpoint calibration | green family ≈ trustworthy | tick 34: restructure landed GREEN + battery-green + gate-green, yet rev-carrier found 2 CRITICAL statement defects | STANDING CORRECTION: a green+battery family is NOT statement-validated; only adversarial review (reviewer+Codex) + truth-witness-at-pin-time catches the socket disease. Never flip an obligation to discharged on green elaboration alone. |
| architect self-reports | trust with spot-check | 5 overstatements journaled (AxCheck bare names; cosmetics-immediately; line-96 strike; three-vs-four modules; repair left UNCOMMITTED) | STANDING DISCOUNT: architect completion claims get controller- OR reviewer-verified before counting — a calibrated prior, not incidents. |

Pass-#1 "Open" items updated: theorem4 owner-gap CLOSED (tick 17, shape-check confirmed at (2,2,4));
map-hygiene stale-note item FIXED.

## Next trigger (superseded — see below)
Navigator pass #3: the monomialization_terminates flip (assembly phase), OR a crux lane going
serial, OR cadence.

## Strike wave (blueprint v4.2 integration → the 8-leaf ladder; 2026-07-21) — actuals (navigator pass #11)

| node / event | prediction (source, pre-event) | actual | delta / lesson |
|---|---|---|---|
| blueprint verify-to-equilibrium | equilibrium within the review cap (cap-4 convention; design-phase analog ran 2 rounds) | **3 codex rounds** (v3 structural kills → v4 hypothesis kills → v4.1 one quantifier → v4.2 clean) + elder end-to-end ratification + controller ground-truth (closure 3753 green, kill-path cite-free) | within cap; the round COUNT is stable across phases (~2–3 to equilibrium) — budget 3 rounds for (C)'s statement gate, not 1 |
| wave-1 lane ranking | lane 2 (C, MonomialRLCT) = longest pole; lane 4 (corollary) = **shortest** (lane-4 carrier-bridge ledger entry, pre-strike: "may be the SHORTEST, re-rank at strike opening") | re-rank CONFIRMED: lane 4's owed ℝ≥0∞ carrier hop **dissolved** (membership bridges + `rfl` GlobalBridge); all three wave-1 seats (A / C / bridge) landed and merged same-day; 14 roots banked (→321+) | HIT for the pre-strike calibration entry — the one lane priced by a territory-read beat the two priced by feel; price lanes by signature-reads before every wave |
| lane-2 statement locks (Object C) | locked leaves provable as stated (twice-reviewed at blueprint) | leaves (2)+(3) **FALSE as stated** — missing `Measurable unit` (D=1 counterexample); seat STOPPED, minimal fix blessed, landed same tide | the lock discipline worked as designed (provability-check-before-grinding); same D3/hWmeas class as prior kills — reviews hardened A's chain and missed C's unit. Interior/junk-value hypothesis audits must run per-OBJECT, not per-chain |
| seat-B (Object B strike leaves) | 5 leaves in one tide (dispatch scope) | **3/5** + reusable A-API; remainder honestly re-priced as two dedicated builds (mon-cov, mon-rec) with named owed infrastructure | honest partial — the re-price at first contact (not at rendezvous) is the behavior to keep; the 2 remainders were both real monuments |
| monument 1 (atlas CoV) | convergent sketch priced buildable (mon-cov dispatch) | landed sorry-free **exactly on the sketch** (InjOn-off-null area formula + off-origin S2 + subcover); engine value chain went clean-three AUTOMATICALLY | HIT — when the sketch names its three infrastructure pieces first, the pricing holds; contrast the cert-priced rows below |
| monument 2 Lean-realization (thread-31 cert Stage-1) | cert playbook: build the recursion as defs (single-tide-shaped stages) | survey-first: the combinatorial half **already existed** kernel-clean (salvage adapter, ~4000 lines NOT duplicated); adapter landed as BOOKKEEPING, net sorries ZERO, sorry SHARPENED to the pure geometric obligation | the cert's Lean-cost pricing was optimistic AND its Stage-1 was redundant — certificates price math, not the banked tree. SURVEY-FIRST before pricing any monument stage |
| the geometric obligation (the remaining leaf) | implicit single-monument pricing at cert handoff | recalibrated **~5% single-tide odds** (mon-geo + decorrelated codex) → multi-tide; decomposed to the 8-leaf ladder with one genuine simplification (hchain ⟹ principality ⟹ M'=1); cert's "pure-monomial g" per-chart claim FLAGGED → thread-33 resolved corrected-(a) (unit ≡ 1 stands, right conclusion wrong reason, addendum not silent rewrite) | the honest-recalibration event of the wave: NO fake progress banked while re-scoping; the ladder adapts, setpoint unchanged. The flagged-claim→pin→addendum chain is the template for L4's statements |
| d=(1,2) instantiation route | reuse literal-Fin-2 blow-up at `Fin (flatDim ![1,2])` | **cast wall** (propositionally-=2, syntactically distinct → whole-Resolution reindex transport, the "two tides" class); dodged STRUCTURALLY: leaf-2 built universal-in-D (~80–150 est.), instantiation transport-free | the recurring cost driver is index/cast transport, never the math; "universalize the statement, instantiate free" is now the standing antidote (bake into (C)'s leaf statements) |
| rung (B) seat-d12 | ~150–250 lines, L⁻¹-composition the contained risk | LANDED (both theorems clean-three; first fully-proven LC instance; banked) — [single-source: controller relay, post-snapshot; pass #12 re-verifies] | contained-risk pricing held; confirm line-count + duration at pass #12 for the asymmetry ledger |
| review latency (endgame rule) | reviewers shadow builds, not follow | rev-cov-fidelity + rev-monument-adapter both spawned AT landing; PASS/SURVIVED with 2 precision escalations applied pre-integration | held — keep commissioning L4's reviewer at first bank |
| office cadence | mandatory at phase transitions | **LAPSED** (passes #3–#10 never ran; design→build transition uncovered); pnp pre-adjudication seats were dispatchable from the honest-recalibration tick but idled until pass #11 — a lane idle against an open gate | the parallelisation steer arrived from the operator, not the loop; pass triggers are now event-pinned (#12 = (C)→wave, before first commissioning) |

### Standing note — the pricing asymmetry (adopted into (C)'s statement gate)
Across the wave, **geometric/analytic legs priced from math certificates ran UNDER** (thread-31 Stage-1; the earlier "just Lemma 1, toric-trivial" drift; design-phase carrier 4 rounds vs 1–2) while **wiring/bookkeeping legs priced from feel ran OVER** (lane-4 shortest; adapter shrank to salvage; leaf-2 dissolved a "two-tide" wall). Compensator, standing: price from the STATEMENT SHAPE (casts, index transports, `WellFounded.fix`, dependent widths) after a survey-first pass; universalize to dissolve transport; expect L4 optimistic and L1/L8 pessimistic when planning wave slack.

### Corrections applied at pass #11 (for the record)
Banking gap closed (+5 atom entries → 341 batch); card states fixed (the `git show --stat` catch: a claimed card edit was a silent sed no-op — commit-message-vs-disk now a named class); the three "queued" elder ratifications had RUN but were unrecorded (C-delta ratified, A machine-diffed, `_root_` clean, GlobalHomog natural) — queued-without-recording is the journal-side twin of the sed no-op class.

### Next trigger
Navigator pass #12: the (C)→wave transition, BEFORE the first wave commissioning (mandatory, no-skip); event-triggered earlier if L4 goes serial >1 tide without a banked sub-leaf, or on any pnp-case1/pnp-cover verdict that reshapes leaf statements.

## L5-SPECIFY success (rung-C PROVE-wave opening; 2026-07-22) — nav-13 (pass #13)

| node / event | prediction (source) | actual (git @ 0f6d6192e) | delta / lesson |
|---|---|---|---|
| census at convening | brief anchor "41 = 16 live + 25 fossil" | scripts/sorries = 43 = 18 live + 25 fossil; controller already corrected 41→43 (1c535e164) | brief anchor was the stale overlay figure; +2 live = Case1Wire (wall' + boostReady). Overlay/claims.yaml census notes (41/MonumentAtlas 14/cone 10) STALE — refresh at next overlay trigger |
| five-bake gate discipline | staging→elder→controller each | ALL FIVE two-channel confirmed (staging commits exist + bake msg "elder OK on <staging>" + journal verify); hpos defect caught POST-bake (gate working) | NO CHANGE — commendable; legible from git alone |
| M4 (the ★ core) | construction labour, own lane | SPECIFY clean; R1/R2 fork ruled R2 then DISSOLVED (DivBirthInv ConState-native) — cheap version, seat-L6 building | de-risked; two decorrelated reads converged on the bridge-free path |
| M7 (canonShearOf) | "pending assignment (nav-13 advises)" | UNASSIGNED — substantial, on L5 critical path, decorrelated, risk-free | START NOW, SPECIFY-first (shear pin resolved) — the one idle-capacity-vs-open-gate gap |
| realBranch_multiAffine | node-form baked (966959855) | STATEMENT baked; PROOF ("the deepest obligation") UNOWNED; conjB/conjunct-2 delegate to it | statement-baked-reads-as-progress; name a prover before pricing L5 |
| Case2Delta0 | retire candidate (brief) | CONFIRMED orphan — zero consumers tree-wide; superseded by case-generic stepInv_child_delta0 | retire → live 18→17 (EXECUTED 76632574d) |
| distance-to-summit | 8 leaves close ⟹ exists_coreResolution clean-three | verified (summit + drivers + adapter proved-from-leaves); L5 (leaf_stepInv_of_path) = longest link (fold convergence); boost + L7 = highest variance | price L5 only once M7 + multiAffine have owners |

### Next trigger
Navigator pass #14: wall closing (case1 sorry-free) OR M4/M7 landing OR L5-assembly going serial >1 tide; else assistants cadence.
