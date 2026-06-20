# threads.md — Aoyagi-Full thread ledger

Durable thread-status index. Status ∈ open / in-progress / blocked / review-pending / closed / abandoned.

| NN | type | seat | status | subject |
|----|------|------|--------|---------|
| 01 | design | pp | closed | Rung 0a: foundational defs + goal skeleton → `design-spec.md` (bedrock-quality; merged 25b825b) |
| 02 | formalisation | fm | in-progress | Rung 0b: encode `DLNFibre.DLN.RLCT.Foundations.*` + named-sorry skeleton + the one S2 axiom |
| 03 | design (parallel) | pp | in-progress | Spine-risk probe: resolution charts for (1,1,1)/(2,1,2)/(2,2,2); confirm chart exponents = Adm. Read-only + /tmp; reports to controller |

## Seats (reuse across tides; stand down at close)

- `pp` — pen-and-paper (design / definitional fidelity / decorrelated Codex). No Lean. [idle after 01]
- `fm` — formaliser (Lean encoding). Works in the shared worktree `rung0-defs` (serial; controller merges).
- `rv` — reviewer (fidelity / soundness; Codex second opinion). [for 0c]
- `hd` — hardener (precision / bedrock / taste; decorrelated). [for 0c, on encoded Lean]

## Topology / merge flow (controller-in-worktree fallback)

Editing happens in the shared worktree `.claude/worktrees/rung0-defs` (branch `worktree-rung0-defs`);
controller merges `worktree-rung0-defs → expedition/aoyagi-full` in the main checkout + pushes to origin.
Serial teammates (isolation collapses onto the controller's worktree). `.lake/packages` symlinked from
the main checkout so lake builds in the worktree without rebuilding Mathlib.
