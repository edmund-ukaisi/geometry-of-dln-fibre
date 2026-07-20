# Teammate brief — template

Copy-and-fill when dispatching a teammate. Every discipline line below is a footgun paid for in a past run;
baking them into the brief is cheaper than re-learning them. Keep briefs concrete: one stated target, the
worktree, the gates, the report shape.

## The brief (fill the `<…>`)

> You are `<name>`, a `<role>` on the **`<slug>`** expedition (branch `expedition/<slug>…`).
>
> **Worktree (yours; use ABSOLUTE paths):** `/…/.claude/worktrees/<slug>/<role>`. Build from `lean/` via
> `scripts/lb` (NOT bare `lake build`); `source ~/.elan/env` first. Read `lean/CLAUDE.md` and your role file
> before starting. Stay blind to sibling expeditions; touch only files under your worktree.
>
> **Target:** `<one stated, scoped deliverable — a statement to prove / a doc to write / a claim to adjudicate>`.
>
> **What you must know (generated — run `scripts/expedition brief <node-id> --resolution 3`; paste or attach):**
> - **The charter (`<exp>/charter.md`) — READ IT FIRST.** The goals (the objects being built at full
>   generality; the headline is a corollary/test), the objects list, **the progress bar**, and the standing
>   math-warnings (the named drifts / dead routes / DO-NOT-FILL holes for this problem). Your target below is
>   a means to a charter object — name which one. If your work fits none of the charter's legal
>   construction-categories, or would fill a DO-NOT-FILL hole, STOP and surface it.
> - **Standing decisions touching this question** — the settled forks + one-line whys (from the elder's
>   `compass.md` + the map). If your work contradicts one, STOP and surface it — do not build around it.
> - **Battery members relevant to your target** — the executable witnesses your claims must survive.
> - **CONSUME / STAGED** — banked lemmas to reuse (exact names/signatures) and pieces staged for exactly
>   this point (from the map overlay; the highest-value section — they exist to prevent re-derivation).
> - **DEAD routes + traps** — refuted approaches with one-line reasons; the lessons that bite this build.
>
> **Discipline:**
> - **Absolute worktree paths for every file write.** A spawned agent's *relative* paths resolve to the
>   main checkout, not your worktree — write only under the worktree path above.
> - **Commit only in your own worktree branch**, and stage surgically (`git add <path>`), never `git add -A`.
>   If you share the controller's tree (no isolation), do **not** commit — hand the diff to the controller.
> - **Gate before you report:** a clean `scripts/lb <Module>` from source (NOT `lake env lean` / a tmp
>   recompile — those reuse stale dependency oleans and mask real breaks), then `scripts/sorries`, then
>   `#print axioms` on the headline result. Report the gate *output*, not "it builds".
> - **A green build is the floor, not the ceiling.** name = content; disclose every added hypothesis;
>   separate Proved / Assumed / Cited; show the witness in-file (non-vacuity).
> - **When done: push your branch (origin is the bank — your worktree becomes safely reapable),
>   report completion to the controller, and stand down.** Do not stay on-call, and do not
>   coordinate peer-to-peer — route everything through the controller.
> - **Under a hold:** pitch the idea + its cost and wait for an explicit go; do not build ahead and report
>   after. (Authorized tasks are fine to run.)
>
> **Report back:** `<the exact final statement(s) + their #print axioms; any obstruction stated precisely
> rather than forced; any new gotcha for lean/CLAUDE.md>`. Then, **free-form, anything noteworthy you
> found** — a cleaner route, an unexpected obstruction, a reusable lemma, a wrong assumption in this brief,
> a lead worth a future thread. The structured items are the floor, not a cap; surface the interesting.

## Notes for the dispatcher (controller)

- **Reuse a bounded named seat** across tides rather than spawning fresh per task — synchronous subagents do
  not self-terminate, so per-task names pile up in the roster.
- **Verify a teammate actually stopped** (idle notification **and** no new commits on its branch:
  `git worktree list`, `git log`) before spawning a successor — a "stop" message can cross in flight.
- **Terminate-then-spawn.** To pivot a live tide, redirect it with one message; if you shut it down, wait
  for termination before spawning its successor — messaging a shutting-down tide revives it.
- **If the controller is itself in a worktree,** `isolation:"worktree"` teammates collapse onto the
  controller's worktree; then enforce one-builder / one-committer-at-a-time and serialize same-file work.
- **Re-run the clean gate yourself** before committing a teammate's "verified" module — the controller's
  own from-source `scripts/lb` over the aggregator is what catches stale-olean and sibling-name-clash breaks
  a teammate's isolated build missed.

Pointers: [`../docs/policies/expedition.md`](../docs/policies/expedition.md) (§ Isolation, § Coordination, § Hub-and-spoke),
[`../docs/policies/expedition-map.md`](../docs/policies/expedition-map.md),
[`../docs/policies/worktree-branch-hygiene.md`](../docs/policies/worktree-branch-hygiene.md),
[`roles/`](roles/).
