# Controller loop - aoyagi-rlct

You are the controller of the `aoyagi-rlct` expedition.

Main quest: formalise Aoyagi's 2023 DLN learning-coefficient computation
from Aoyagi's paper alone, citing only the general normal-crossing-to-RLCT
extraction theorem unless a real probe shows another boundary is necessary.

Expected cwd:
`/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/aoyagi-rlct`.
If you are in the main checkout, switch to this worktree before continuing.
Do not use the quiver paper or quiver Lean branch as source evidence or proof
input.

Tooling discipline: every command, file read, file edit, and subagent prompt
must use this absolute worktree root. At the start of a tick or thread, confirm
`git rev-parse --show-toplevel` prints exactly the expected cwd. If it does not,
stop and move to the worktree before doing any expedition work.

## Re-ground when needed

On a fresh session, after compaction, or whenever unsure, read these in full:

- `docs/policies/expedition.md`
- `expeditions/2026-06-18-aoyagi-rlct/brief.md`
- `expeditions/2026-06-18-aoyagi-rlct/priorities.md`
- `expeditions/2026-06-18-aoyagi-rlct/synthesis.md`
- `expeditions/2026-06-18-aoyagi-rlct/threads.md`
- `expeditions/2026-06-18-aoyagi-rlct/claims.md`
- `expeditions/2026-06-18-aoyagi-rlct/theorem-ledger.md`
- `expeditions/2026-06-18-aoyagi-rlct/lessons.md`
- `expeditions/2026-06-18-aoyagi-rlct/expositions/`

Read `docs/policies/claims.md`, `docs/policies/precision.md`,
`docs/policies/bedrock.md`, `docs/policies/review.md`, and
`docs/policies/statement-cards.md` when claims or reviews arise. Read
`lean/CLAUDE.md` before any Lean work.

Source:
`paper-sources/aoyagi-2023-consideration-of-learning-efficiency-of-dln/aoyagi-2023-neural-networks-preprint.pdf`.

## Tick

Confirm the worktree root, then re-anchor to the quest. Triage `priorities.md`.
Ingest thread reports. Update `theorem-ledger.md` and `claims.md` whenever a
source statement or Lean theorem changes status. Delegate next bounded thread.
Integrate into `synthesis.md`. Precision-check names and statements. Push
Aoyagi-specific load-bearing maths; do not pre-defer elementary steps. Spawn
reviewers and hardeners for broad theorem names and the final theorem. Before
assigning a substantial Lean tide, confirm there is a pen-and-paper
reproduction artifact and a separate checker verdict for the calculation it
formalises.

## Flush before yielding

Land new state in `synthesis.md`, `priorities.md`, `threads.md`, `claims.md`, and
`theorem-ledger.md` as appropriate. Thread progress belongs in the thread's
`thread.md`. Do not write persistent memory outside the repo.
