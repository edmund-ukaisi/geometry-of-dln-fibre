# threads.md — Aoyagi-Full thread ledger

Durable thread-status index. Status ∈ open / in-progress / blocked / review-pending / closed / abandoned.

| NN | type | seat | status | subject |
|----|------|------|--------|---------|
| 01 | design | pp | closed | Rung 0a: foundational defs + goal skeleton → `design-spec.md` |
| 02 | formalisation | fm | review-pending | Rung 0b: encoded `DLNFibre.DLN.RLCT.*` + skeleton + 1 S2 axiom; green; merged `58bc1c3` |
| 03 | design (parallel) | pp | closed | Spine probe: `codim S(t)=Mval` proven general L; θ=a(ℓ−a)+1; stratification R1 architecture |
| 04 | design (parallel) | pp | closed | D1 scope: cite Aoyagi 2013 **Thm 2**; light rung; depends on L2; reuses S1 |
| 05 | design (parallel) | pp | in-progress | S1 scope: RLCT change-of-variables/invariance linchpin (D1/R1/S2 all consume it) |
| 06 | review | hd + rv | open | Rung 0c: fidelity + bedrock audit of the encoded foundations (gate before dependent rungs) |

## Seats (reuse across tides; stand down at close)

- `pp` — pen-and-paper (design / fidelity-math / decorrelated Codex). No Lean. On thread 05 (S1 scope).
- `fm` — formaliser (Lean). Idle (Rung 0b done). Works in shared worktree `rung0-defs` (serial; controller merges).
- `rv` — reviewer (fidelity / soundness; Codex). [thread 06]
- `hd` — hardener (precision / bedrock / taste; decorrelated). [thread 06]

## Merge flow (controller-in-worktree fallback)

Editing in shared worktree `rung0-defs` (branch `worktree-rung0-defs`); controller merges →
`expedition/aoyagi-full` (main checkout) + pushes. Serial editing teammates. `pp` runs read-only (no
collision). Green-gate (`lake build DLNFibre`) every merge. `.lake/packages` symlinked.

## Encoded foundations (merged 58bc1c3)
`Foundations/{Loss,Rlct,Lambda}.lean` + `Skeleton.lean`. 9 named-sorry rungs (S1×2, L1, L2, D1, R1,
A1×2, A2) + 1 axiom `monomial_rlct` (S2, narrowed to the bare weighted-monomial-integral fact). Defs
axiom-clean. `aoyagiLambda` = min-over-Adm (ground truth enforced at build). `rlctOrderAt` = honest
`opaque` placeholder (θ-seam). Statement card: `threads/02-rung0b-encode/statement-card.md`.
