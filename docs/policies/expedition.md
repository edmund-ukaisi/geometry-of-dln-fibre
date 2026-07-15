# Expeditions

A policy for running research as multi-agent **expeditions**: one **controller**
(an Agent Teams team lead) orchestrating role-specialist **thread** teammates
around a central question. The disposition it runs under is in [`../../CLAUDE.md`](../../CLAUDE.md);
the design principles it implements are [`principles.md`](principles.md) (cited as P1–P9);
the plan layer it maintains is the expedition-map ([`expedition-map.md`](expedition-map.md)).

## What an expedition is

A structured investigation with a central question tied to the research direction.
It runs for some duration, spawns threads dynamically, and produces its durable record — the map,
the journal, the formalised claims — and a closing synthesis, whether the question is answered,
refuted, refined into a successor, or abandoned.

One expedition is one substantial chunk (a paper-section's worth), not one lemma.
The thread is the working unit; a formalisation thread (tide) is the fine unit.
An expedition moves through **phases**: genesis → digestion/adjudication → the
build loop → close.

## Phases

- **Genesis.** Instantiate the scaffold (§ Files), the map with `meta.roots` + the goal node(s),
  the battery seeded from the source's worked examples, `heartbeat-prompt.md`.
- **Digestion / adjudication.** Digest the source (or, for an open problem, the problem terrain);
  adjudicate the forks that can be settled now. **Deliverable contract — a settled fork emits three
  artifacts, immediately (promotion lag ≈ 0; P6):**
  1. its **skeleton increment** — the adjudicated decomposition as a driver + obligation-record in
     Lean, sorried, on canonical, wired toward the headline (the *pull*; the obligation-record
     pattern is churn-robust: statement detail moves freely under a stable fork-level shape);
  2. its **witnesses into the battery** — kill-conditions as executable scripts, not sentences (P1);
  3. its **toolkit spec** — the domain-general machinery the new holes' types name, funding a
     parallel **library lane** (P8: domain-general machinery survives route churn; route-glue does
     not; "Mathlib-worthy" is an immediate integration obligation, never a side branch).
  For an open problem this phase never ends — forks settle progressively and the skeleton ratchets.
- **Build loop.** The controller tick (below), threads, gates — with the **convening joints**:

  | joint | convened | mechanism |
  |---|---|---|
  | route adoption / skeleton revision | elder (+ council at major forks) | route-adoption gate ([`expedition-map.md`](expedition-map.md) contract 9) |
  | scope-drop / pre-deferral / "simplification" of a named hard part | elder (consult before deciding) | written counsel into the record |
  | phase transition (design→build, build→assembly, pre-close) | navigator (no-skip) | disposition table before the first commissioning wave |
  | universal / coverage / exhaustiveness claim | decorrelated hunt | § Gates |
  | tide completion | reviewer | AUDIT |

  A gate is a convening device; the alternative to a gate is not trust — it is an unconvened
  moment (P2).
- **Close.** § Close, plus the calibration delta (predicted vs actual per major node — feeds the
  calibration ledger) and the lessons pass (promote-or-decay: a lesson that recurred moves up into
  a role file or the brief template; the rest stays in `lessons.md` and is allowed to fade).

## Architecture (Agent Teams)

- **Controller** — the team lead and sole delegator and **the only actor**. Holds the strategic
  state (`brief.md`, `priorities.md`, the map's `claims.yaml` as its single curated writer), does
  meta-level planning and integration, and delegates execution. Does not do thread grunt-work in
  its own context.
- **Threads** — role-specialist teammates, each running its typed loop. Leaf
  executors: they execute and decide within their loop but cannot spawn agents; a
  thread needing a helper sends the controller a `REQUEST_SPAWN`.
- **Reviewers** — teammates the controller spawns to audit a thread's output or a
  claim (see [`review.md`](review.md)). A reviewer can call `local-codex-consult`
  for an independent Codex opinion. A thread never reviews itself.
- **Offices** (controller assistants) — read-only advisory seats convened fresh from durable
  state: **cartographer** (memory), **navigator** (planning), **elder** (comprehension/direction).
  § Controller assistants.
- **Operator** — the human. Injects taste by editing `priorities.md` (the
  highest-authority signal) and can seize a thread to drive it directly.
- **Seats, not per-task hires.** Reuse a bounded set of named seats (one
  `formaliser`, one `architect`, one `pen-and-paper`, one `reviewer`, …) across tides rather than
  spawning a fresh teammate per task — synchronous subagents do not self-terminate,
  so per-task names pile up in the roster. Stand every seat down explicitly at
  expedition close.

Communication is the Agent Teams mailbox (turn-based, non-blocking). Run with
`CLAUDE_CODE_EXPERIMENTAL_AGENT_TEAMS=1`; one team per expedition; cwd is this
harness directory. Spawn briefs are built from
[`.agent-team/teammate-brief-template.md`](../../.agent-team/teammate-brief-template.md) — the
epistemic sections (standing decisions, battery, traps, consume/staged) are generated via
`scripts/expedition brief <node>`, so a seat is never convened without the settled forks that touch
its question in-window (P2, P3).

### Isolation, merging, and long compiles

- **Each teammate works in its own git worktree.** Isolation removes the shared-tree hazards *by
  construction*: a stale or misdirected command (a `revert`/`checkout` that crossed in flight) cannot
  reach another agent's tree, writers never collide on the same files, and a reviewer audits a
  **frozen** checkout that cannot shift under it mid-audit. Spawn with `isolation: "worktree"`.
  Naming + cleanup: [`worktree-branch-hygiene.md`](worktree-branch-hygiene.md).
  - *Lean / heavy-build contingency:* a fresh worktree gets its own build dir, so dependency oleans
    (Mathlib, ~GBs) would rebuild per worktree. **Share the dependency build** — reuse/symlink
    `.lake/packages` across worktrees — so only the project's own small oleans rebuild per worktree.
    With that, worktree-per-teammate is nearly free; without it, the build-duplication tax can
    outweigh the isolation benefit for light tasks.
  - *Caveat — the controller must NOT itself be in a worktree.* Teammate `isolation: "worktree"` yields
    *distinct* per-teammate worktrees only if the controller session runs from the **main checkout**. If
    the controller is itself in a worktree, spawned isolation-worktrees **collapse onto the controller's**
    (all teammates share one) — isolation becomes nominal. When that happens, run teammates **serially**
    in the shared worktree (one active editor at a time): the centralized-merge integrity still holds, but
    the parallelism is lost.
- **The controller is the sole merger.** Teammates commit only to their own worktree branches; the
  controller is the only agent that integrates — `fetch → merge → resolve conflicts → green-gate
  (build) → commit`. This gives **one coherent integration state the controller alone owns** (so
  "what is committed / is the tree green" is never ambiguous — a chief source of async-coordination
  confusion), and resolves any conflict in one place with the full picture. Partition work by module
  (single-writer-per-file, e.g. the Lean aggregator) to keep conflicts rare. This is the
  "contributors on branches, controller as maintainer" model: a teammate racing ahead becomes a safe
  *merge decision*, not a shared-tree hazard. The green-gate also carries the map's ride-alongs:
  survey refresh, full validator, anchor compile, battery.
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

1. **Re-ground (when you need to)** — on a fresh session, after a compaction, or whenever you are
   unsure of the current state, read the **re-ground bundle** (§ State, compaction, and recovery) —
   constant-size by design. On a warm tick, read only the delta — `priorities.md` + the reporting
   thread's `thread.md`. Grounding is cheap; prefer it to guessing.
2. **Ingest** — mailbox (thread reports, `REQUEST_SPAWN`, `MAP_DELTA` proposals), finished jobs,
   operator edits.
3. **Re-anchor** — reread `brief.md` and the elder's `compass.md`; restate the single most
   decision-relevant question.
4. **Triage** — maintain `priorities.md`: rank live map nodes by value-of-information and directed
   suspicion; mark each pursue / park-unclear / drop / escalate.
5. **Delegate** — spawn or instruct threads (briefs via the template + `expedition brief`);
   spawn reviewers; convene offices at their joints.
6. **Integrate** — apply accepted `MAP_DELTA`s to `claims.yaml`; append the tick's narrative to
   `journal.md`; refresh `STATUS.md` (`expedition status`); precision-check thread output
   (name = content; is the load-bearing step proved or merely assumed? — § Supervising the
   formaliser).
7. **Surface** — escalate operator-facing items, ranked.
8. **Review to equilibrium** — on a critical finding, loop fix → re-review until stable (cap 4 rounds).

## Controller assistants (the offices)

Read-only advisory seats that augment the controller's executive function — the functions that
decay under interrupt load and context turnover (P2). **An office, not a session**: no long-running
instance (fake persistence, correlation hub); each is convened fresh from its durable artifact and
stands down. Office = charter (role file) + one per-expedition artifact + convening triggers.

| office | function | artifact | convened |
|---|---|---|---|
| **cartographer** | memory: what exists, what died, what is it called | `map/` overlay + index | cadence; anomaly digs |
| **navigator** | planning/inhibition: the parallelisation audit, gates-ran, avoidance | `map/calibration.md` + numbered passes | **mandatory at phase transitions**; cadence |
| **elder** | comprehension/direction: the question, the whys, the counsel | `compass.md` | **mandatory at route adoption / skeleton revision**; cadence |

Shared contract: read-only against the build (each office's own artifact excepted — single writer);
pull state themselves from git/tree/map, never from the controller's summary (decorrelation is the
value); output a numbered disposition artifact the controller accepts / re-sequences / moots
item-by-item — propose, never act; "no change needed" is a first-class verdict; no global memory.
**Scale gate**: not instantiated on small expeditions (≲100 expedition Lean files / ≲200 journal
blocks / ≲1 week) — there the controller holds the offices itself and `compass.md` is a section of
`brief.md`. **Cadence**: every ~60 canonical commits or ~4 h, whichever first (commit-count tracks
state change, not tempo), self-perpetuating (each pass names the next trigger; passes numbered in
the journal so a lapsed cadence is operator-visible).

## priorities.md — the taste ledger

**What it is for:** the operator's asynchronous taste channel — the one file the operator is
expected to edit, and the controller's own ranked triage. It answers "what should get the next
lane?", which no computed view can (STATUS reports state; priorities encodes *judgment* over it).
A ranked ledger at the expedition root (≤ 30 lines): entries are **map node ids**, each with a
one-line disposition (pursue / park-unclear / drop / escalate). The controller proposes the ranking
by value-of-information and directed suspicion (from `lessons.md` and the dead-route registry),
flags low-confidence calls, and re-reads the file every substantive tick (the operator may have
edited it out-of-band; operator edits are the highest-authority signal).

Two states the ledger forces:
- **Nothing unranked** — every observation is differentiated.
- **"unclear-but-keep-going" is first-class** — a live ambiguity is parked, not collapsed into a premature conclusion or dropped.

## Threads

Type is chosen at spawn and selects the sub-machine. Any type can reach `ABANDONED`
(record the reason).

- **explore** — `OPENED → LONGLIST (what to compute/derive) → TRIAGE → COMPUTE/DERIVE → CHECK → NOTICE/INTERPRET → STEP_BACK (loop or close)`. Forms and sharpens **claims** as map nodes with executable kill-conditions ([`expedition-map.md`](expedition-map.md) § battery) and stress-tests them. `CHECK` confirms computations are sane.
- **formalisation (tide)** — `OPENED → SPECIFY → PROVE → AUDIT`. Runs the `lean-formalisation` skill. **AUDIT** is a no-skip gate: `scripts/sorries` clean **and** a reviewer confirms the Lean statement matches the claim (fidelity) **and** checks hypothesis-fit against the artifact's intended consumers as named in the map (a lemma can be sound, faithful, non-vacuous — and still not enough for what the plan says it discharges; sufficiency-for-consumers is part of the audit, not assumed — P3).
- **blueprint (architect)** — `OPENED → ELABORATE (signatures/defs/wiring compile against verbatim
  anchors) → GATE (route-adoption: elaboration + battery) → HANDOFF (holes typed, named,
  node-linked)`. Run by the `architect` role ([`../../.agent-team/roles/architect.md`](../../.agent-team/roles/architect.md)).
  Definition of done = *elaborates and is wired*, explicitly NOT sorry-free; the GATE is the
  non-skippable step. Candidate decompositions live on the architect's branch; canonical carries
  one adopted spine per fork.
- **infra** — `OPENED → SPECIFY (interface/spec) → BUILD → TEST`. For harness / computation tooling; run by the formaliser role or a purpose-spawned teammate. **TEST** is a no-skip gate: the spec's tests pass and the read states what each test demonstrates.

`REQUEST_SPAWN` (ask the controller for a reviewer/helper) fires from `CHECK` / `AUDIT` / `TEST`, where fresh eyes are most valuable. Its fields: requester, requested role/function, target artifact, question, blocking/non-blocking, expected output.

Thread `status` in `threads.md` is one of `open` / `in-progress` / `blocked` / `review-pending` / `closed` / `abandoned`.

## Maturity

Claim/notion/route maturity is the map's ladders ([`expedition-map.md`](expedition-map.md)
§ Maturity ladders), which absorb the former claims-card statuses: a **new** claim is tide-eligible
at `adjudicated` (stress-tested, cert with witnesses); an **established** (published/cited) claim's
adjudication is the light verify-against-source. The universal non-skippable gate is the
formalisation AUDIT — a light path to the tide never weakens it. Refuted nodes stay (with their
battery witness): they are the trail, and the battery re-tests every open route against them for
free.

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
the teammates, not less. **Scope-drops, pre-deferrals, and "simplifications" of a named hard part
are elder-consultation items** (§ Phases, convening joints): the elder reviews recent scope and
ambition decisions on its cadence, and the controller consults it before making one.

## Mediating a positive/negative pair (the refutation dialectic)

Some questions run as a **positive/negative pair** — a seat hunting a counterexample (a `witness`) and a
seat proving a scoped no-go (an `obstruction`). The controller **mediates** the back-and-forth toward the
sharp dividing line ([`bedrock.md`](bedrock.md) § the refutation dialectic); the pair does not merely run in
parallel and report two one-sided results.

- **Drive the loop.** A counterexample from one side becomes a *narrow-the-theorem* task for the other; a
  theorem becomes a *hypothesise-a-reasonable-strengthening-and-hunt* task for the first. Decide each handoff
  on judgement; the deliverable is the converged boundary, not a lone witness or a padded weak theorem.
  Certified witnesses land in the **battery** (P1) — a refutation stored as a test binds every future
  author who never read the cert.
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
- **A teammate's *requests* route through the hub too.** In the rare case a teammate needs to coordinate
  with another thread, or judges that a new teammate should be spawned for a different piece, it raises that
  with the controller — it does not reach across to a peer or spawn on its own. The controller decides and
  dispatches.
- **Break a cascade with an artifact ID, not more prose.** When queue-lagged messages replay a settled
  reconciliation, one broadcast of the committed **SHA / file md5** ends it — an artifact identity is
  independently verifiable and timeless; "it's done, trust me" is not.
- **Verify a serious relayed claim on ground truth before acting.** "landed" / "fabricated" / "clobbered"
  from a peer is checked against disk/git first; a claim that contradicts established ground truth is
  reconciled before it is believed. Never relay-and-act.

## Gates (non-skippable)

- formalisation cannot reach done without AUDIT; infra cannot without TEST. The controller reads the AUDIT alongside a **precision + bedrock check** (§ Supervising the formaliser): the name/statement denotes exactly what is proved, the load-bearing step is proved or named as the open target, and the result clears the bedrock bar ([`bedrock.md`](bedrock.md) — non-vacuous, hygienic, characterized, fenced). A green, sorry-free, axiom-clean build is necessary, never sufficient. The bedrock/taste pass is a **reviewer function** ([`review.md`](review.md)), decorrelated from the builder.
- **Route adoption and skeleton revision** pass the route-adoption gate ([`expedition-map.md`](expedition-map.md) contract 9): the composition skeleton elaborates against the consumed nodes' *verbatim* statements (anchor pins — never a docstring or cert paraphrase; P3), and every carried hypothesis is evaluated at the battery. The elder is convened (a council of two, independently, at major forks). A route document's sufficiency verbs ("suffices", "bypasses", "mechanical") without witness pointers are lint (P5).
- a **universal / negative / exhaustiveness** claim ("holds for all", "no counterexample", "the case-split is complete") is not treated as **established** until a **decorrelated counterexample hunt** has attacked it and failed — an empty hunt is *scoped evidence* (state what was searched), not a proof; review confirms the cases shown, the hunt surfaces the case missed ([`bedrock.md`](bedrock.md) § the refutation dialectic). And **cited scripts are re-run** to confirm they reproduce their headline (not a relayed verdict; watch the script that reconstructs a *different* object than the one claimed) ([`bedrock.md`](bedrock.md) §Non-vacuity).
- the expedition cannot CLOSE without a final controller integration deciding *close*.
- a critical reviewer finding floors a review-to-equilibrium loop.
- one blocking signal-and-wait: the close-phase PR — the expedition record (map + journal + Lean) becomes a shared artefact.

## Files

```
expeditions/<date>-<slug>/
├── brief.md              central question + closing criterion            (controller · setup)
├── priorities.md         taste ledger: ranked map-node ids, ≤30 lines    (controller proposes; operator edits)
├── compass.md            the elder's counsel: the question, settled forks
│                         + whys, load-bearing facts, ranked uncertainties,
│                         standing build-the-general-machinery calls; ≤2pp (elder office)
├── journal.md            append-only narrative, tail-read only — designed
│                         decay; NEVER holds load-bearing status (P9)      (controller · every tick)
├── heartbeat-prompt.md   re-ground protocol + controller memo ≤10 lines  (controller edits memo)
├── threads.md            index: status / type / one-line per thread      (controller)
├── lessons.md            methodological learnings (append; promote-or-
│                         decay at close)                                 (anyone · on a learning)
├── discuss-at-close.md   operator-facing items, D-### ids                (controller)
├── map/                  the expedition-map (see expedition-map.md):
│   ├── claims.yaml         the plan of record                            (controller, sole curated writer)
│   ├── battery/            executable witnesses                          (append: controller/cartographer)
│   ├── overlay/            cards, dead routes, naming pointers           (cartographer)
│   ├── survey/             computed; gitignored                          (tooling, rides green-gate)
│   ├── calibration.md      predicted-vs-actual ledger                    (navigator office)
│   └── STATUS.md           the sole materialized view, ≤40 lines         (tooling: `expedition status`)
└── threads/<NN>-<slug>/thread.md   brief + notes + read, one per thread
```

Retired from the previous scaffold (forwarding: git history + `overlay/naming.md`): `synthesis.md`
(split into `journal.md` + `STATUS.md` + `compass.md` — the frontier must never live inside the
decay layer), `loop-prompt.md` (→ `heartbeat-prompt.md`), hand-maintained built-indexes and
endgame-lane trackers (→ the map + overlay).

Agent Teams runtime state (team config, mailbox, task list) lives outside the repo under
`~/.claude/teams/<team>/` and `~/.claude/tasks/<team>/`.

## State, compaction, and recovery

The repo docs are the expedition's **durable memory**. The controller's and teammates'
in-context state, and the Agent-Teams runtime, are **volatile** — lost on context compaction or
session restart. Two rules follow.

**Write to survive compaction.** At each tick (and before any long or risky operation): append the
tick's narrative to `journal.md`, apply map edits, run `expedition status`, and update the
heartbeat memo if the phase or top decision changed. Teammates flush progress to their `thread.md`.
Never hold decision-relevant state only in context or only in the mailbox — land it in an artifact
at the right binding strength (P1): a decision in the skeleton/map, a refutation in the battery, a
status in STATUS.md — narrative (and only narrative) in the journal.

**Read to re-ground.** Re-ground on a fresh session, after a compaction, or whenever unsure.
The **re-ground bundle is constant-size by design** (the journal is *never* read in full — tail
only; archaeology is an on-demand dig, not recovery):

- `docs/policies/expedition.md` — your full contract (this file)
- `<exp>/brief.md` — the central question
- `<exp>/heartbeat-prompt.md` — the protocol + your own memo to yourself
- `<exp>/priorities.md` — the taste ledger (the operator may have edited it)
- `<exp>/map/STATUS.md` — the frontier, owners, open gates
- `<exp>/compass.md` — the question's state, settled forks, counsel
- `<exp>/journal.md` — tail (last 2–3 entries) only
- `<exp>/threads.md` — thread-status ledger

`CLAUDE.md` is auto-loaded. Read `expedition-map.md` / `review.md` / `precision.md` /
`bedrock.md` / `writing-style.md` / `codex-consultation.md` / `lean/CLAUDE.md` when their action
arises; `expedition view decision <id>` for any node about to carry a decision (P7: gestalt from
the map, truth from the territory). A freshly spawned teammate orients from its spawn brief
(template + `expedition brief <node>`). After a full restart the runtime team may be gone;
re-ground from the bundle and re-spawn teammates — the docs are the source of truth, the team is
reconstructible.

**Cadence (read / write).**

| Doc | Written · when | Read · when |
|---|---|---|
| `brief.md` | controller · setup | re-ground; each thread on spawn |
| `priorities.md` | controller every tick; operator anytime | every substantive tick |
| `journal.md` | controller every tick (append) | tail on re-ground; archaeology on demand |
| `map/` + `STATUS.md` | per § Files owners | STATUS every tick; views at decisions |
| `compass.md` | elder at convenings | re-ground; before any route adoption |
| `heartbeat-prompt.md` | controller (memo section) | every heartbeat firing |
| `threads/<NN>/thread.md` | the thread · during work + at close | controller on integration; reviewer on audit |
| `lessons.md` | anyone · on a learning (append) | brief-template injection; close pass |

## Heartbeat

The unattended cadence wrapper. The cron/loop message is **constant and tiny** — it never changes,
so it cannot rot: *"You are the controller of `<expedition-id>`. Read `<exp>/heartbeat-prompt.md`
and act on it. One tick per wake."* Everything mutable lives in the file:

````markdown
# Heartbeat — <expedition-id>

Main quest: <central question, one line>.

## Memo (controller-edited, ≤10 lines — the costliest lines in the system: keep them current)
- phase: <…>   top decision in flight: <…>
- <the 3–5 things post-compaction-you must not lose>

## Protocol (per wake)
1. Re-ground if fresh/compacted/unsure: the bundle (expedition.md § State) — brief, this file,
   priorities, map/STATUS.md, compass, journal tail, threads.
2. Tick: ingest → re-anchor (brief + compass) → triage priorities → delegate (briefs via template
   + `expedition brief`) → integrate (journal append + map + STATUS) → surface → review-to-equilibrium.
3. Office cadence check: ~60 commits or ~4 h since the last cartographer/navigator/elder pass →
   convene; phase transition → navigator mandatory; route adoption → elder + gate.
4. Flush before yielding (§ State). In-repo only — never `~/.claude` global memory; remind teammates.

Teammate reports + operator messages wake you automatically — don't poll. This heartbeat is a long
(≥20 min) idle pulse; on an idle wake with nothing new, drift-glance and re-sleep.
Stop at CLOSE, or when the operator pauses.
````

## Close

Final controller integration → the calibration delta (predicted vs actual on the major nodes, into
`map/calibration.md`) → the lessons pass (promote-or-decay) → a last journal entry → commit on the
expedition branch → signal-and-wait before opening the close PR. The deliverable is the expedition
record itself: the map (with its battery and anchors), the journal, and the formalised claims.
Reader-facing write-ups, when wanted, are commissioned by the operator separately — they are not a
standing close obligation.

## Anti-patterns

- Controller executes a thread in its own context (rabbit-holes; defeats delegation).
- A thread reviews itself instead of `REQUEST_SPAWN` (no fresh eyes).
- A critical finding gets one pass, not equilibrium.
- `priorities.md` left flat, or a live ambiguity collapsed/dropped.
- A formalisation/infra thread reaching done bypassing AUDIT/TEST.
- Threads spawned without integration (the journal loses the question).
- **A route adopted on a sufficiency paraphrase** — "X discharges Y" with no compiled witness; the
  five-fork failure shape (P3). Elaborate the edge or stamp it UNWITNESSED.
- **Load-bearing status held in the journal** — the frontier drowning in the decay layer; status
  lives in STATUS.md/the map, narrative in the journal (P9).
- **A settled fork left unskeletoned** — promotion lag is measured in re-litigations (P6).
- **Selling-register verbs in a route document without witness pointers** ("mechanical", "just
  wiring", "bypasses") — the fork vocabulary; lint it, then prove it or strike it (P5).
