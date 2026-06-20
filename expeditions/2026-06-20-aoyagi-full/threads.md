# threads.md — Aoyagi-Full thread ledger

Durable thread-status index. Status ∈ open / in-progress / blocked / review-pending / closed / abandoned.

| NN | type | seat | status | subject |
|----|------|------|--------|---------|
| 01 | explore→design | pen-and-paper + formaliser | open | Rung 0: pin goal skeleton + foundational defs (`rlctAt`,`rlctOrderAt`,`dlnLoss`,`aoyagiλ`); fidelity-review vs ground truth |

## Seats (reuse across tides; stand down at close)

- `pp` — pen-and-paper (design-space math, definitional fidelity, decorrelated Codex). No Lean.
- `fm` — formaliser (Lean encoding; works in a worktree synced to the expedition branch).
- `rv` — reviewer (fidelity / soundness audits; Codex second opinion).
- `hd` — hardener (precision / bedrock / taste; decorrelated).

(Spawn lazily; not all seats are needed yet. Rung 0 = pp + fm + rv/hd review.)
