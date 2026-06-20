# lessons.md — `rlct-payoff` (append-only methodological learnings)

Seeded from the voigt-discharge expedition (carry the meta-process, not the content):

- **Size hard pieces before building.** Every feared "multi-week sub-library" in voigt-discharge that
  was *sized first* (L4a, L5, the AG route, L2b★) dissolved into a bounded build via the right route;
  the ones that genuinely were sub-libraries were surfaced early instead of discovered mid-grind. A
  recon/pen-and-paper sizing pass is the cheapest insurance.
- **Serial Lean-writers when the controller is in a worktree.** Teammate `isolation: worktree` collapses
  onto the controller's worktree, so only ONE Lean-writer at a time. File-scoped `git add <path>` +
  `git pull --rebase` before every push (a `git add -A` once swept a concurrent tide's file).
- **A step deferred twice → don't keep yielding.** Bring a fresh decisive tide + a decorrelated Codex
  consult on the EXACT stuck sub-goal (the `hA` matrix-Kähler `D(U⁻¹)` unblock: Codex self-compiled the
  tactic; the diagnosis "no inverse-collapse, do a normal-form match" was the real key).
- **Decorrelated Codex / pen-and-paper catches secretly-false routes.** Codex flagged the Polynomial-curve
  R2★ route as false (`(1+tφ)⁻¹ ≠ 1−tφ` over `k[t]`) — the dual-number route was correct. Frame-in /
  hypothesis-out.
- **Green build is the floor, not the ceiling.** Every capstone got a fidelity AUDIT + a hardener
  bedrock pass (decorrelated) before the operator signal. Name = content (no `rlct`-overclaim on a
  codim result); caveats co-located (the `[CharZero]` scope); non-vacuity witness in-file.
- **Controller stays executive.** Delegate object-level to seats; integrate / green-gate / flush
  synthesis every tick; surface only at completion or a genuine blocker/scope-surprise.
- **Recovery substrate hygiene** (PR #4 review lessons): keep ALL thread artefacts under the expedition
  dir (not top-level `threads/`); keep `threads.md` current; date headings to the real commit date;
  `git diff --check` clean (no trailing whitespace in artifacts); no scratch `.lean` under the library tree.
