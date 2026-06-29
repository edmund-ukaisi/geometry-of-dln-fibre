# Threads — `dimension-stack`

Index: NN / type / subject / status. Per-thread notes in `threads/<NN>-<slug>/thread.md`.

| NN | type | subject | status |
|----|------|---------|--------|
| 00 | scout (recon) | AG-foundations library ladder — what to grow to Mathlib-grade | **closed** (2026-06-28) — ladder in [`priorities.md`](priorities.md) |
| 01 | lean-formaliser (rung 0) | de-risk: throwaway generalisation of `NullstellensatzCodim` → exact minimal hyps for the field-general core | **closed** (2026-06-29) — CONFIRMED: core is `[Field k] [Finite σ]`, clean 3-band split; consumers' `[IsAlgClosed]` dead weight; verdict in [`priorities.md`](priorities.md) R0 outcome |
| 02 | lean-formaliser (R1) | extract integral-extension dimension invariance → `Core.Dimension.Integral` | **closed** (`f447c0ce`) — 9 decls re-homed (byte-identical statements) to `Core.Dimension.{Integral,Basic}`; 8 consumers re-pointed; green 3819 / sorry-0 / axiom-clean; reviewer + Codex PASS. Card: `threads/02-integral-dim/statement-card.md` |
| 03 | lean-formaliser (R2) | polynomial-ring catenary + monic positioning → `Core.Dimension.Catenary` | **closed** (`574a9056`) — `height p + dim(R/p) = n` (`@[stacks 00OS]`) + monic-positioning crux (private Mathlib substitution re-derived in-repo, Codex xhigh PASS); 7+aggregator consumers re-pointed (4 transitive, L2); green 3819 / sorry-0 / axiom-clean. Card: `threads/03-catenary/statement-card.md`. **Re-gate PASS (3819) + crux-review PASS (04).** |
| 04 | reviewer (crux audit) | R2 fidelity: verbatim private-substitution copy + "any field" generality | **closed** — **PASS-with-notes**: verbatim copy byte-faithful (only `T` de-privatised); any-field generality sound (zero closure/char/cardinality hyps); minor non-blocking (card tag-claim + 2 dangling `§` refs → folded into R3). Verdict: `threads/03-catenary/review.md` |
| 05 | lean-formaliser (R3) | finite-type-domain catenary (L4d) + closed-point corollaries → `Core.Dimension` | **in flight** |

## Roadmap (future expeditions — not this one)
orbit-geometry capstone de-`Tuple` (recon entry 3); type-A Gabriel/`Ext` (4); q-series (5); mathlib4 upstream
PR; shared-package extraction.
