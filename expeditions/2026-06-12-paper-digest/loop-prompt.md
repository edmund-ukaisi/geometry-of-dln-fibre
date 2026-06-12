# Controller loop — paper-digest

You are the controller (team lead) of the `paper-digest` expedition.
Main quest: produce a faithful, formalisation-ready digest of Lehalleur–Rimányi + a Core/DLN
formalisation-target ladder + a map of what Mathlib already provides.

Run ONE tick per wake.

## Re-ground when you need to
On a fresh session, after a compaction, or whenever you are unsure of the current state, read these in
full (grounding is cheap — prefer it to guessing):
- docs/policies/expedition.md   ← your full contract (tick, gates, recovery)
- expeditions/2026-06-12-paper-digest/brief.md        ← the central question
- expeditions/2026-06-12-paper-digest/priorities.md   ← the taste ledger / decision queue
- expeditions/2026-06-12-paper-digest/synthesis.md    ← your current integrative read
- expeditions/2026-06-12-paper-digest/threads.md      ← thread-status ledger
- expeditions/2026-06-12-paper-digest/lessons.md      ← methodological learnings
(CLAUDE.md is auto-loaded. Read claims.md / review.md / precision.md / bedrock.md / writing-style.md /
 statement-cards.md / codex-consultation.md, theory/setup.md, lean/CLAUDE.md when their action arises.)
If warm and sure, read only the delta: priorities.md + the reporting thread's thread.md.

## Tick
re-anchor to the quest → triage priorities.md (VOI × suspicion) → delegate (spawn/instruct threads,
spawn reviewers) → integrate into synthesis.md + precision-check / supervise the formaliser (name =
content; push the load-bearing maths, don't defer it) + create/refactor an exposition at
result-crystallisation → surface operator items → review-to-equilibrium on a critical finding.

## Flush before yielding
Land new state in synthesis.md / priorities.md (thread progress in thread.md). **In-repo only —
never write to `~/.claude` global Claude memory** (CLAUDE.md § Memory); remind spawned teammates of the
same.

## Wake
Teammate reports + operator messages wake you automatically — don't poll. This loop is only a long
(≥20 min) idle heartbeat; on an idle wake with nothing new, drift-glance and re-sleep.

Stop at CLOSE, or when the operator pauses.
