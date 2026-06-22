# lessons.md — `perm-invariance` (append-only)

Seeded from voigt-discharge + rlct-payoff:
- SIZE hard pieces before building (the roadmap's "genuine lift, NOT free" on Cor 5.10 is an explicit flag).
- Serial Lean-writers when the controller is in a worktree; file-scoped `git add` + `git pull --rebase` before push.
- Decorrelated Codex / pen-and-paper catches secretly-false routes (the rlct Polynomial-curve, the strict flat-chain).
- A stuck step deferred twice → fresh decisive tide + decorrelated certificate on the EXACT sub-goal.
- Green build is the floor; AUDIT (fidelity) + name=content + non-vacuity witness every result.
- Honest Cited boundary: cite established external theorems as named, carried interfaces (never global axioms);
  prove the genuinely-new content. Here: aim zero-cited for the combinatorial invariance.
- Recovery-substrate hygiene: all thread artefacts under the expedition dir; threads.md current; dates = commit
  dates; `git diff --check` clean; no scratch `.lean` under the library tree.

## 2026-06-22 — subagent cwd hazard (the homing incident)
- Background SUBAGENTS launch with cwd = the repo's PRIMARY (main) worktree, NOT the controller's worktree,
  regardless of the controller's cwd or EnterWorktree. Their RELATIVE Write/Edit-tool paths resolve to the
  main tree. In a multi-session repo where main = another live session, this POLLUTES that session's tree.
- Pen-and-paper seats were unaffected: they create files via bash `cd <worktree> && …`, which honours the cd.
  Only Write/Edit-TOOL relative paths mis-home.
- MITIGATION: controller writes Lean himself (absolute paths) when main is a live foreign session; OR instruct
  agents to use ONLY absolute paths under the target worktree + self-check `git -C <main> status` for leaks.
  Detect a mis-home by job-count mismatch (foreign aggregate ≠ your branch's) + `find <repo> -name <file>`.
