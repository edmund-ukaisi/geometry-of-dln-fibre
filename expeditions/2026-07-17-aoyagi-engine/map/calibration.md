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
