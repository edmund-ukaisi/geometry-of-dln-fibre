# Expeditions

A policy for running research as multi-agent **expeditions**: one **controller**
(an Agent Teams team lead) orchestrating role-specialist **thread** teammates
around a central question. Theory-adapted from the patterning expeditions-v2
architecture. The disposition it runs under is in [`../../CLAUDE.md`](../../CLAUDE.md).

## What an expedition is

A structured investigation with a central question tied to the research direction
(the DLN-fibre / type-A quiver programme). It runs for some duration, spawns
threads dynamically, and produces an exposition (and a final synthesis) at close — whether
the question is answered, refuted, refined into a successor, or abandoned.

One expedition is one substantial chunk (a paper-section's worth), not one lemma.
The thread is the working unit; a formalisation thread (tide) is the fine unit.

## Architecture (Agent Teams)

- **Controller** — the team lead and sole delegator. Holds the strategic state
  (`brief.md`, `priorities.md`, `synthesis.md`), does meta-level planning and
  integration, and delegates execution. Does not do thread grunt-work in its own
  context.
- **Threads** — role-specialist teammates, each running its typed loop. Leaf
  executors: they execute and decide within their loop but cannot spawn agents; a
  thread needing a helper sends the controller a `REQUEST_SPAWN`.
- **Reviewers** — teammates the controller spawns to audit a thread's output or a
  claim (see [`review.md`](review.md)). A reviewer can call `local-codex-consult`
  for an independent Codex opinion. A thread never reviews itself.
- **Operator** — the human. Injects taste by editing `priorities.md` (the
  highest-authority signal) and can seize a thread to drive it directly.
- **Seats, not per-task hires.** Reuse a bounded set of named seats (one
  `formaliser`, one `pen-and-paper`, one `reviewer`, …) across tides rather than
  spawning a fresh teammate per task — synchronous subagents do not self-terminate,
  so per-task names pile up in the roster. Stand every seat down explicitly at
  expedition close.

Communication is the Agent Teams mailbox (turn-based, non-blocking). Run with
`CLAUDE_CODE_EXPERIMENTAL_AGENT_TEAMS=1`; one team per expedition; cwd is this
harness directory.

### Isolation, merging, and long compiles

- **Each teammate works in its own git worktree.** Isolation removes the shared-tree hazards *by
  construction*: a stale or misdirected command (a `revert`/`checkout` that crossed in flight) cannot
  reach another agent's tree, writers never collide on the same files, and a reviewer audits a
  **frozen** checkout that cannot shift under it mid-audit. Spawn with `isolation: "worktree"`.
  - *Lean / heavy-build contingency:* a fresh worktree gets its own build dir, so dependency oleans
    (Mathlib, ~GBs) would rebuild per worktree. **Share the dependency build** — reuse/symlink
    `.lake/packages` across worktrees — so only the project's own small oleans rebuild per worktree.
    With that, worktree-per-teammate is nearly free; without it, the build-duplication tax can
    outweigh the isolation benefit for light tasks.
  - *Caveat — the controller must NOT itself be in a worktree.* Teammate `isolation: "worktree"` yields
    *distinct* per-teammate worktrees only if the controller session runs from the **main checkout**. If
    the controller is itself in a worktree, spawned isolation-worktrees **collapse onto the controller's**
    (all teammates share one) — isolation becomes nominal. When that happens, run teammates **serially**
    in the shared worktree under a **one-builder/committer-at-a-time rule**: at most one agent building or
    committing at once (a second concurrent `lake build` corrupts the shared `.lake`; two commits race the
    git index); a read-only auditor (no build, no commit) may run alongside the one builder; and rungs
    touching the same file serialize. The centralized-merge integrity still holds, but the parallelism is lost. (a past Stage-3 run: the controller was launched in a worktree, so all
    teammates shared it; the inherently sequential P1→P2→P3 chain made serial fine. Launch the controller
    from the main checkout to get true isolation.)
- **The controller is the sole merger.** Teammates commit only to their own worktree branches; the
  controller is the only agent that integrates — `fetch → merge → resolve conflicts → green-gate
  (build) → commit`. This gives **one coherent integration state the controller alone owns** (so
  "what is committed / is the tree green" is never ambiguous — a chief source of async-coordination
  confusion), and resolves any conflict in one place with the full picture. Partition work by module
  (single-writer-per-file, e.g. the Lean aggregator) to keep conflicts rare. This is the
  "contributors on branches, controller as maintainer" model: a teammate racing ahead becomes a safe
  *merge decision*, not a shared-tree hazard.
- **Run long compiles (`lake build`, large test/CAS suites) as non-blocking background processes.** A
  blocking multi-minute build stalls the agent's turn and *widens the window for message crossing*;
  backgrounding it keeps the agent responsive and lets completion notify rather than block. This
  matters most for the controller's per-merge green-gate build, which must not serialize the whole
  team behind it.
- **Subdirectory conventions don't auto-reach teammates.** A teammate loads `CLAUDE.md` cwd-up-to-root
  at startup, but a *nested* `CLAUDE.md` (e.g. `lean/CLAUDE.md`) loads only **on-demand** when it reads
  a file in that subdir — not at startup, and not re-injected after `/compact`; the built-in
  `Explore`/`Plan` agents skip `CLAUDE.md` **entirely**. So **reference subdir conventions explicitly in
  the spawn prompt** ("read `lean/CLAUDE.md` before any Lean work") or carry them in a `skills:`-referenced
  skill (loaded at startup). There is no per-spawn cwd override — the only isolation lever is
  `isolation: worktree`, which still starts at the repo root.

## Controller tick

1. **Re-ground (when you need to)** — on a fresh session, after a compaction, or whenever you are unsure of the current state, read the full re-ground list (§ State, compaction, and recovery). On a warm tick, read only the delta — `priorities.md` + the reporting thread's `thread.md`. Grounding is cheap; prefer it to guessing.
2. **Ingest** — mailbox (thread reports, `REQUEST_SPAWN`), finished jobs, operator edits.
3. **Re-anchor** — reread `brief.md` and the research direction; restate the single most decision-relevant question.
4. **Triage** — maintain `priorities.md`: rank live observations / threads / claims by value-of-information and directed suspicion; mark each pursue / park-unclear / drop / escalate.
5. **Delegate** — spawn or instruct threads; spawn reviewers.
6. **Integrate** — update `synthesis.md` against the research direction (drift guard); precision-check thread output (name = content; is the load-bearing step proved or merely assumed? — § Supervising the formaliser); create or refactor the relevant `expositions/` doc when a result crystallises (respecting operator-`stable` docs).
7. **Surface** — escalate operator-facing items, ranked.
8. **Review to equilibrium** — on a critical finding, loop fix → re-review until stable (cap 4 rounds).

## priorities.md — the taste ledger

A ranked ledger at the expedition root; the place the operator injects judgment.
The controller proposes a ranking by value-of-information (how much does the next
action change across an item's resolutions?) and directed suspicion (from
`lessons.md`), and flags low-confidence calls. The operator edits it directly.

Two states the ledger forces:
- **Nothing unranked** — every observation is differentiated.
- **"unclear-but-keep-going" is first-class** — a live ambiguity is parked, not collapsed into a premature conclusion or dropped.

## Threads

Type is chosen at spawn and selects the sub-machine. Any type can reach `ABANDONED`
(record the reason).

- **explore** — `OPENED → LONGLIST (what to compute/derive) → TRIAGE → COMPUTE/DERIVE → CHECK → NOTICE/INTERPRET → STEP_BACK (loop or close)`. Forms and sharpens **claims** with explicit kill-conditions (see [`claims.md`](claims.md)) and stress-tests them. `CHECK` confirms computations are sane.
- **formalisation (tide)** — `OPENED → SPECIFY → PROVE → AUDIT`. Runs the `lean-formalisation` skill. **AUDIT** is a no-skip gate: `scripts/sorries` clean **and** a reviewer confirms the Lean statement matches the claim (fidelity).
- **infra** — `OPENED → SPECIFY (interface/spec) → BUILD → TEST`. For harness / computation tooling; run by the formaliser role or a purpose-spawned teammate (no dedicated infra agent yet). **TEST** is a no-skip gate: the spec's tests pass and the read states what each test demonstrates.

`REQUEST_SPAWN` (ask the controller for a reviewer/helper) fires from `CHECK` / `AUDIT` / `TEST`, where fresh eyes are most valuable. Its fields: requester, requested role/function, target artifact, question, blocking/non-blocking, expected output.

Thread `status` in `threads.md` is one of `open` / `in-progress` / `blocked` / `review-pending` / `closed` / `abandoned`.

## The maturity gradient

A claim flows **explore → stable claim → formalisation (tide)**. A new claim is
tide-eligible at status `survived` or `refined`; an established/published result at
`verified` (light verify-against-source) — see [`claims.md`](claims.md). The universal
non-skippable gate is the formalisation AUDIT.

## Supervising the formaliser

The controller relates to the formaliser as a supervisor to a strong graduate student — two duties
beyond delegation.

- **Precision-check.** Read every formaliser result against [`precision.md`](precision.md): do the
  Lean *name* and *statement* denote exactly what is proved? Are **Proved / Assumed / Cited /
  Deferred** separated? In particular, is the **load-bearing** step — the one that makes the claim
  mean what it says — actually proved, or merely *assumed* (an assumed-reduction-style hypothesis) and named
  as the open target? A result whose name asserts more than its content is renamed or restated, not
  shipped.
- **Push for the real maths.** When the load-bearing step is assumed/deferred, that step is the next
  target — not a parked successor filed while declaring victory ([`precision.md`](precision.md)
  § completeness corollary). Help the formaliser get to it: supply the mathematics, decompose the
  proof into rungs (a ladder of concrete cases toward the general lemma works well), pin the precise
  statement, pair on the hard step, insist on rigour.
- **Judge against bedrock.** Hold formaliser output to the bedrock taste ([`bedrock.md`](bedrock.md)): a
  green, sorry-free, **axiom-clean** build is necessary, never sufficient. *Conceptual* slop — technically
  correct but subtly wrong — is by construction what the builder cannot self-check (it compiles), so it is
  caught here, by supervision + decorrelated audit, guided by a sense of beauty. The controller's judgement
  against this taste takes **precedence**; where a result is not yet bedrock, restate it, re-scope it, or send
  it back. Read `bedrock.md` when integrating formaliser work or convening an audit.

**Supervisor, not slave-driver.** Push on the load-bearing maths; respect genuine blockers and the
agent's effort. Do not loop a stuck proof past its cap, demand, or punish — calibrate, encourage,
and re-scope when something is genuinely hard. Distinguish a **load-bearing** gap (push) from a
**genuinely-separate** extension (legitimately future; bounding it is good scope discipline).

**Be ambitious; don't pre-defer within-reach work.** Set the target at the **edge of the team's
reach**, not below it. Drop scope only for a *genuine* blocker (missing theory, infeasible cost, real
risk to proven work) — never to save effort or make the close look tidy. Pre-emptively deferring
sound, reachable work is the visible-progress instinct one level up; the review bar (audits, precision
checks), **not** pre-emptive deferral, is the filter. The controller should be *more* ambitious than
the teammates, not less.

## Mediating a positive/negative pair (the refutation dialectic)

Some questions run as a **positive/negative pair** — a seat hunting a counterexample (a `witness`) and a
seat proving a scoped no-go (an `obstruction`). The controller **mediates** the back-and-forth toward the
sharp dividing line ([`bedrock.md`](bedrock.md) § the refutation dialectic); the pair does not merely run in
parallel and report two one-sided results.

- **Drive the loop.** A counterexample from one side becomes a *narrow-the-theorem* task for the other; a
  theorem becomes a *hypothesise-a-reasonable-strengthening-and-hunt* task for the first. Decide each handoff
  on judgement; the deliverable is the converged boundary, not a lone witness or a padded weak theorem.
- **Two task modes — name which you are issuing, to control biasing:**
  - **decorrelated** (a correctness gate or an independent attack): give the *config / question* and
    **withhold the expected answer and the other seat's hypothesis** — "compute X from scratch and report
    your value first." The same *frame-in / hypothesis-out* rule as a Codex consult.
  - **build-on** (a dialectic step): give the other side's result as *established fact* — "this
    counterexample holds; find the weakest hypothesis that excludes it."
  Leaking the expected answer into a *decorrelated* check launders bias and wastes the independence you were
  buying. (A peer-to-peer reproduction is decorrelated too — the seats may message, but the controller sets
  the mode.)
- **This is a hardening duty.** Stopping at the first counterexample or the first weak theorem is the
  visible-progress instinct on the theorem frontier; push the pair to the exact characterization.

## Coordination under async messaging

Agent-Teams messages between controller and teammates are delivered **asynchronously with no ordering
guarantee** — directives and reports cross in flight. The discipline that keeps crossing from doing
damage:

- **Address directives to a committed hash, not "the current tree."** "At `<sha>`, do X" survives late
  delivery; "revert the uncommitted changes" is dangerous once the state has moved.
- **Never issue a destructive command (`revert`/`checkout`/overwrite) asynchronously** — prefer "stop
  and show me." A teammate that *verifies state before acting* and surfaces a contradiction instead of
  executing a stale command is doing exactly right (it caught a destructive near-miss in
  a past expedition).
- **Under a hold, the teammate pitches the idea + cost and waits for an explicit go** — it does not
  build ahead and report after. (Authorized tasks are fine to execute.)
- **Green-gate every commit and commit often** — so the worst case is a *stale instruction*, never
  lost or broken work; each good state is banked.
- **Throttle cadence while a hold is outstanding** — a stream of fast follow-ups is where crossing
  compounds.

### Hub-and-spoke — the finished-agent discipline

Peer-to-peer coordination among *finished* agents is where async crossing turns into a self-sustaining
noise cascade. In a past endgame ~7 done agents stayed alive and cross-messaged to re-confirm committed
work, de-conflict, and chase misattributed relays; with queue-lag and task-replays each stale message
triggered defensive cross-checks that themselves landed stale — zero new work, real token/cycle cost, the
committed tree intact throughout. The shape that holds:

- **Done → report + stand down.** A teammate that has delivered and committed its piece reports completion
  to the controller and then stands down / requests shutdown. It does **not** stay on-call by default — the
  on-call value (a possible later review) rarely exceeds the noise, and a fresh seat re-spawns turnkey when
  a specific need arises (context lives in the committed code + docs).
- **The controller shuts down done agents** rather than leaving them idle-on-call.
- **All coordination routes through the controller (the hub).** No teammate↔teammate cross-talk — the sole
  sanctioned spoke-to-spoke channel is a *tight live collaboration* (a builder and its reviewer on one
  in-flight piece).
- **Break a cascade with an artifact ID, not more prose.** When queue-lagged messages replay a settled
  reconciliation, one broadcast of the committed **SHA / file md5** ends it — an artifact identity is
  independently verifiable and timeless; "it's done, trust me" is not.
- **Verify a serious relayed claim on ground truth before acting.** "landed" / "fabricated" / "clobbered"
  from a peer is checked against disk/git first; a claim that contradicts established ground truth is
  reconciled before it is believed. Never relay-and-act.

## Gates (non-skippable)

- formalisation cannot reach done without AUDIT; infra cannot without TEST. The controller reads the AUDIT alongside a **precision + bedrock check** (§ Supervising the formaliser): the name/statement denotes exactly what is proved, the load-bearing step is proved or named as the open target, and the result clears the bedrock bar ([`bedrock.md`](bedrock.md) — non-vacuous, hygienic, characterized, fenced). A green, sorry-free, axiom-clean build is necessary, never sufficient.
- a **universal / negative / exhaustiveness** claim ("holds for all", "no counterexample", "the case-split is complete") is not treated as **established** until a **decorrelated counterexample hunt** has attacked it and failed — an empty hunt is *scoped evidence* (state what was searched), not a proof; review confirms the cases shown, the hunt surfaces the case missed ([`bedrock.md`](bedrock.md) § the refutation dialectic). And **cited scripts are re-run** to confirm they reproduce their headline (not a relayed verdict; watch the script that reconstructs a *different* object than the one claimed) ([`bedrock.md`](bedrock.md) §Non-vacuity).
- the expedition cannot CLOSE without a final controller integration deciding *close*.
- a critical reviewer finding floors a review-to-equilibrium loop.
- the **bedrock check is run by an independent `hardener`** ([`../../.agent-team/roles/hardener.md`](../../.agent-team/roles/hardener.md)), not only the controller — a decorrelated principles/taste pass (distinct from the correctness audit) at each gate and at step-back, surfacing overclaims, holes-vs-extensions, *and the right extensions* (→ Just-Do-It if within reach, else roadmap). The controller integrates its findings and holds precedence; a critical hardener finding floors a loop like a reviewer finding.
- one blocking signal-and-wait: the close-phase PR **merge** — opening the close PR (≤ 1 per expedition) is controller-authorized, but the merge, at which the expedition record (exposition + synthesis + Lean) lands as a shared artefact, is operator-gated (see [`../../CLAUDE.md`](../../CLAUDE.md) § Branch discipline).

## Files

```
expeditions/<date>-<slug>/
├── brief.md         central question + closing criterion
├── priorities.md    the taste ledger (controller proposes; operator edits)
├── threads.md       index: status / type / one-line subject per thread
├── synthesis.md     controller's internal integrative ground (current read + drift-guard; not a deliverable)
├── lessons.md       methodological learnings (append-only)
├── expositions/     human-facing docs (controller-curated; draft = fluid, stable = human-read/protected)
└── threads/<NN>-<slug>/thread.md   brief + notes + read, one per thread
```

Agent Teams runtime state (team config, mailbox, task list) lives outside the repo under `~/.claude/teams/<team>/` and `~/.claude/tasks/<team>/`.

## State, compaction, and recovery

The repo docs are the expedition's **durable memory**. The controller's and teammates'
in-context state, and the Agent-Teams runtime (mailbox, per-team task list under
`~/.claude/`), are **volatile** — lost on context compaction or session restart. Two rules
follow.

**Write to survive compaction.** The controller flushes its working read to `synthesis.md` and
`priorities.md` at each tick (and before any long or risky operation), so a post-compaction
controller loses at most the last tick's un-flushed thinking. Teammates flush progress to their
`thread.md` for the same reason. `threads.md` is the durable thread-status ledger; the team
task-list is a runtime convenience that mirrors it. Never hold decision-relevant state only in
context or only in the mailbox — land it in a doc.

**Read to re-ground.** Re-ground — read the full list below — on a fresh session, after a
compaction, or **whenever you are unsure of the current state**. Grounding is cheap; prefer it to
guessing. On a warm tick (you have reasoned continuously since your last read), read only the
**delta**: `priorities.md` (the operator may have edited it out-of-band) and the reporting
thread's `thread.md`.

**Re-ground full-read list** (paths from the harness root; `<exp>` = the expedition dir):

- `docs/policies/expedition.md` — your full contract (this file: tick, gates, recovery)
- `<exp>/brief.md` — the central question
- `<exp>/priorities.md` — the taste ledger / decision queue
- `<exp>/synthesis.md` — your current integrative read
- `<exp>/threads.md` — thread-status ledger
- `<exp>/lessons.md` — methodological learnings
- `<exp>/expositions/` — any in-progress draft you were writing

`CLAUDE.md` is auto-loaded (always present — not in the list). Read `claims.md` / `review.md` /
`precision.md` / `writing-style.md` / `statement-cards.md` / `codex-consultation.md`,
`theory/setup.md`, and `lean/CLAUDE.md` when their action arises. A freshly spawned teammate orients from its spawn brief
plus the durable docs it points at. After a full restart the runtime team may be gone
(cross-restart persistence is unverified); re-ground from the list and re-spawn teammates — the
docs are the source of truth, the team is reconstructible.

**Cadence (read / write).**

| Doc | Written · when | Read · when |
|---|---|---|
| `brief.md` | controller · setup, `REFINE_QUESTION` | controller on re-ground; each thread on spawn |
| `priorities.md` | controller every tick; operator anytime | controller every substantive tick (operator's async channel) |
| `synthesis.md` | controller every tick (flush) | controller on re-ground; distilled into expositions |
| `threads/<NN>/thread.md` | the thread · during work + at close | controller on integration; reviewer on audit |
| `expositions/` | controller · result-crystallisation + close | humans on review; controller when distilling |
| `lessons.md` | controller / threads · on a learning (append) | controller on re-ground |

So `synthesis.md` is *written* every tick (the recovery substrate must stay current) but *read*
only on re-ground; expositions move at the slower crystallisation cadence — they are the
deliverable, not the memory.

## Loop prompt

The executable wrapper of the tick — instantiated per expedition at SETUP (`<exp>/loop-prompt.md`)
and, when an unattended heartbeat is wanted, run via `/loop`. Keep it short: it re-issues
identity, the re-ground list, and the decisions, and points at the full contract
(`docs/policies/expedition.md`) — the first doc read in full on re-ground.

````markdown
# Controller loop — <expedition-id>

You are the controller (team lead) of the `<expedition-id>` expedition.
Main quest: <central question, one line>.

Run ONE tick per wake.

## Re-ground when you need to
On a fresh session, after a compaction, or whenever you are unsure of the current state, read
these in full (grounding is cheap — prefer it to guessing):
- docs/policies/expedition.md   ← your full contract (tick, gates, recovery)
- <exp>/brief.md                ← the central question
- <exp>/priorities.md           ← the taste ledger / decision queue
- <exp>/synthesis.md            ← your current integrative read
- <exp>/threads.md              ← thread-status ledger
- <exp>/lessons.md              ← methodological learnings
- <exp>/expositions/            ← any in-progress draft you were writing
(CLAUDE.md is auto-loaded. Read claims.md / review.md / precision.md / bedrock.md / writing-style.md /
 statement-cards.md / codex-consultation.md, theory/setup.md, lean/CLAUDE.md when their action arises.)
If warm and sure, read only the delta: priorities.md + the reporting thread's thread.md.

## Tick
re-anchor to the quest → triage priorities.md (VOI × suspicion) → delegate (spawn/instruct
threads, spawn reviewers) → integrate into synthesis.md + precision-check / supervise the formaliser
(name = content; push the load-bearing maths, don't defer it) + create/refactor an exposition at
result-crystallisation → surface operator items → review-to-equilibrium on a critical finding.

## Flush before yielding
Land new state in synthesis.md / priorities.md (thread progress in thread.md). **In-repo only —
never write to `~/.claude` global Claude memory** (CLAUDE.md § Memory); remind spawned teammates of
the same (the harness will prompt them to save memories there; they must not).

## Wake
Teammate reports + operator messages wake you automatically — don't poll. This loop is only a
long (≥20 min) idle heartbeat; on an idle wake with nothing new, drift-glance and re-sleep.

Stop at CLOSE, or when the operator pauses.
````

### The heartbeat (scheduled tick)

The loop prompt is fired by a **scheduled heartbeat** so an unattended expedition keeps advancing on its own:
a **durable hourly cron** (`CronCreate`, prompt *"Controller tick — run ONE tick per `<exp>/loop-prompt.md`"*),
or `/loop`. It is the **operator-away autonomous driver** — *not* a substitute for event wakes: teammate
completions and operator messages already wake the controller automatically, and while you are actively driving
in-session you don't wait on it. The heartbeat exists to cover the genuinely-**idle** gaps (waiting on nothing
the harness will notify you about, or between units of work when the operator is away) so the expedition does
not stall.

- **An idle firing is a checkpoint, not a no-op.** When the tick fires with nothing new since the last, that is
  exactly the moment to **regroup, orient, and check in**: re-ground (`priorities.md` / `synthesis.md` /
  `threads.md`), drift-glance against `brief.md`, look in on in-flight teammates / open PRs / the build state,
  and surface anything operator-facing — then re-sleep. Treat idle time as orientation time.
- **Cadence + hygiene.** Pick an **off-minute** (not `:00`/`:30`: schedulers across the fleet fire on the round
  minute, so an off-minute avoids self-inflicted synchronized load). Make it **durable** only if it must survive
  a session restart, and note the **~7-day auto-expiry** (re-arm a longer-running expedition). **Stop the cron at
  close** — and when several expeditions run in parallel, leave the *other* expeditions' heartbeats alone (touch
  only your own).

## Close

Final controller integration → finalise the exposition(s) (the human/paper-facing
deliverable) and a last internal `synthesis.md` pass → commit on the expedition branch →
open the close PR (≤ 1 per expedition, controller-authorized per
[`../../CLAUDE.md`](../../CLAUDE.md) § Branch discipline), then signal-and-wait for the
operator-gated merge. The exposition is the markdown chunk that feeds the
paper; the formalised claims are its anchors.

## Expositions

`expeditions/<id>/expositions/` holds the **human-facing** docs — the legibility deliverable
(purpose and the correct > elegant > efficient ordering: [`writing-style.md`](writing-style.md)).
They are distinct from `synthesis.md`, the controller's *internal* ledger that assumes repo
context.

- **Controller-curated, by taste.** The controller starts a doc when a reader-facing piece
  coheres — the whole expedition, a sub-result, or a cluster of threads. Not one per thread; the
  expedition has at least one, and a sub-unit earns its own only when rich enough.
- **Draft docs are fluid.** While `status: draft`, the controller may freely restructure a doc —
  including a massive refactor (split / merge / rewrite) — as understanding improves. Do not be
  precious about draft structure.
- **Stable docs are protected.** Once the **operator marks a doc `status: stable`** (read and
  blessed), the controller treats it as fixed: additive or careful edits only, no churn. A
  massive refactor of a stable doc requires the operator to re-open it (`stable` → `draft`).
- **Cadence.** Create or update at result-crystallisation (a claim verified + formalised +
  reviewed) and at close — not every STEP_BACK.
- **Promotion.** When a topic matures across expeditions, a stable exposition is synthesised into
  the cross-expedition library `theory/expositions/<topic>.md`.

## Anti-patterns

- Controller executes a thread in its own context (rabbit-holes; defeats delegation).
- A thread reviews itself instead of `REQUEST_SPAWN` (no fresh eyes).
- A critical finding gets one pass, not equilibrium.
- `priorities.md` left flat, or a live ambiguity collapsed/dropped.
- A formalisation/infra thread reaching done bypassing AUDIT/TEST.
- Threads spawned without integration (the synthesis loses the question).
- Massive-refactoring an operator-`stable` exposition, or leaving a crystallised result with no human-facing doc.
