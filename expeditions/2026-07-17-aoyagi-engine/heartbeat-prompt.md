# Heartbeat — 2026-07-17-aoyagi-engine

Main quest (operator-reframed 2026-07-18, PRIORITY framing): **Aoyagi's mechanism built FULLY as
a free-standing library** (her objects + invariants incl. sharing, end-to-end, conceptual-altitude
first — cases derived, never chased) → THE LEARNING COEFFICIENT THEOREM (`aoyagi_learning_
coefficient` unconditional, clean-three). hbox (`∀ M, RouteMBoxThresholdFinite M`) = adapter path
(A), default; her native λ theorem = path (B), replaces the cite; DITCH the hole if (B) prices
shorter. Every commission, council charge, and review bar carries THIS framing, not the hole's.

## Memo (controller-edited, ≤10 lines — keep current)
- **READ `charter.md` FIRST, every wake** — it is the fixed invariant core (goals = Aoyagi's machinery
  as reusable objects; the headline is a corollary/test; the progress bar; the standing math-warnings).
  Gate every progress-claim and every route against it. This heartbeat memo is operational state, NOT
  the goal frame — the charter is.
- phase: **BLUEPRINT-v3 → VERIFY-TO-EQUILIBRIUM → STRIKE (operator go 2026-07-21, operator AWAY).** The
  operator delegated the blueprint sign-off to the verification process: build v3 (enriched spec = journal
  tick 43x; architect, PUSH-on-commit), then cross-check from MULTIPLE angles, MULTIPLE times — (i) paper-
  fidelity review vs worked.tex + page images, (ii) an independent Codex COUNTEREXAMPLE HUNT on every
  frontier statement (the v2 killer: unconstrained CoV/Jacobian + axis-only C — hunt that class hardest),
  (iii) elder ratification vs charter §0–§3, (iv) build green + kill-path cite-free + cordon green.
  Iterate architect↔checks until NO load-bearing finding survives; only then OPEN THE STRIKE PHASE
  (map/claims re-root on A–E at opening; parallel tides on strike-able leaves; frontier seats on frontier
  leaves under the pin-the-shape-then-build stopping rule). AT OPENING run the LONG-RANGE PARALLELISATION
  SCOUT (operator steer 2026-07-21): map which lines are genuinely INDEPENDENT (→ parallel seats — thread
  independence is REGULARISING, each line keeps the others honest) vs which share substrate (→ build the
  shared part ONCE as its own thread + intermediate @[blueprint] waypoints between the Mathlib floor and
  the leaves — valuable, but forecasts are scaffolding NEVER gospel: verify before designing around one). Do NOT stall waiting for the operator at
  blueprint-ready — that gate is delegated. STILL operator-gated: PR merge, dev→main, destination/DoD
  changes; §1-FINAL tag comes off on their recorded confirm (pending). VM died 2026-07-21: fresh VM,
  losses + recovery = journal tick 43x; unpushed agent branches are NOT banked — every seat pushes on commit.
- **The progress bar (before reporting progress):** name the charter §1 object it discharges AND its legal
  §3 category; a green build / closed leaf / re-derivation that discharges no object is motion, not progress.
- Controller in `.claude/worktrees/aoyagi-engine/root`; NEVER touch expedition/aoyagi-full anything.
- Teammate isolation = EXPLICIT worktrees; lean/.lake = packages-only share (NEVER full symlink).
- `git worktree add` RE-PINS this session's cwd to the new worktree (2 recurrences) — re-issue
  EnterWorktree(root) immediately after every worktree creation; placement check catches it.
- BRANCH-HIJACK GUARD (incident 2026-07-18): seats must NEVER `git checkout`/`switch` in root —
  every seat brief mandates its OWN worktree for its branch. Controller: EVERY commit batch begins
  with the assertion `[ "$(git branch --show-current)" = expedition/aoyagi-engine ]` (a seat's
  checkout in root silently redirected 3 ticks of controller commits onto its branch; pushes of
  the frozen ref "succeeded" — the placement check must check the BRANCH, not just the cwd).
- Obligations STATED (tick 37); case-step-lemmas faithful-flip waits on the full-fidelity items.
- Standing rules: exact-steps-only; truth witness at pin time; Def-3 never transcribed.
- ELDER OWNERSHIP (operator, 2026-07-20): the ELDER authors both `charter.md` (the fixed invariant core)
  and `compass.md` (the fork-history); the CONTROLLER commits + pushes (branch discipline) — do NOT edit
  either yourself, commit the elder's edits (git add that file only, on the elder's "ready" signal). The
  charter is edit-in-place / never-append / ≤1pg; the compass is the growing history and owes a deep
  compaction pass (elder's first re-chartered task).
- CONTROLLER SHELL GUARDS (recurring self-bugs): NEVER gate a chain on `validate | tail` (tail
  masks the exit code — bank only via a grep-for-'0 error' gate); the hooksPath was dangling
  (pointed at the MAIN checkout's absent scripts/hooks — repointed to THIS worktree's, verified
  the hook exists); every commit batch starts with the branch assertion.

## Protocol (per wake)
0. Verify placement: `.claude/worktrees/aoyagi-engine/root`, branch `expedition/aoyagi-engine`
   (controller.md resp. 0). Recover first if not. ALSO verify the heartbeat cron is armed (`CronList`) —
   recurring jobs auto-expire after 7 days and die with a VM; if absent, RE-ARM (hourly, off-minute,
   durable, this exact prompt). The system must self-heal its own pulse.
1. Re-ground if fresh/compacted/unsure: **`charter.md` FIRST** (the invariant core — goals, objects,
   progress bar, math-warnings), THEN the State bundle — this file, map/STATUS.md, compass (history),
   journal tail, threads. (`priorities.md` is RETIRED for this expedition — a forwarding stub only;
   ranking lives in the map, current focus in this memo.) The charter overrides any stale framing.
2. Tick: ingest → re-anchor (brief + compass) → triage priorities → delegate (briefs via template
   + `scripts/expedition brief`) → integrate (journal append + map + STATUS) → surface →
   review-to-equilibrium.
3. Office cadence: ~60 commits or ~4 h activity since last pass → convene; phase transition →
   navigator mandatory; route adoption / skeleton revision → elder + gate.
   ENDGAME STANDING OFFICES (operator, 2026-07-19 tick 266): elder-standing + carto-standing
   are LONG-RUNNING seats (context kept; charge them via SendMessage, never respawn fresh
   while they live). Cadence raised: a comprehension/wiring pass ~every 3-4 ticks through the
   endgame — elder for math-rightness (generalisation level, right objects vs spiky,
   next-expedition runway), cartographer for wiring/overlay truth (checklist freshness,
   gate-orphans, forwarding pointers). Route adoptions still gate through the elder.
4. COMPREHENSION CADENCE (operator, 2026-07-19): every ~5 ticks — and at every phase
   transition — run a CALIBRATION ENTRY: pick a load-bearing question about the territory,
   write the mathematical EXPECTATION first (with confidences), then read the actual Lean,
   record hit/miss + what-it-changes in strategy/calibration-ledger.md. An idle pulse with
   nothing to integrate IS the natural slot (drift-glance tick → calibration tick). Roughly
   every third question routes through an office instead of self-checked: cartographer for
   map/reuse expectations, elder for direction/comprehension audits (the elder may audit the
   controller's own strategy artifacts — invited, not resisted). Altitude note per phase
   transition (strategy/); the close synthesis reads the ledger + altitude notes first, the
   journal chronology second. Misses are the product — record them plainly.
5. Flush before yielding. In-repo only — never `~/.claude` global memory; remind teammates.

Teammate reports + operator messages wake you automatically — don't poll. This heartbeat is a long
(≥20 min) idle pulse; on an idle wake with nothing new, drift-glance and re-sleep.
IDLE-STALL GUARD (operator-caught, tick 236): a seat's "continuing…" at turn-end is an INTENT,
not a state — idle seats resume ONLY on a message. At every drift-glance: if a live-lane seat is
idle with a CLEAN tree and its last report declared continuing-intent → SEND THE WAKE (idle +
clean + continuing = stalled, not working). Seats are briefed to end such turns with an explicit
"WAITING FOR WAKE".
Stop at CLOSE, or when the operator pauses.
