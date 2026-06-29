# Threads — `foundation-lift`

**Multi-phase foundation-lift II** (P1 components & local dim → P2 determinantal & elimination → P3
smooth/cotangent), driven autonomously, **one PR per phase** (stacked branches), async operator review.
Per-thread notes in `threads/<NN>-<slug>/`.

| NN | type | subject | status |
|----|------|---------|--------|
| 00 | scout (recon) | coverage recon — validate the 3-phase ladder vs `origin/dev` + Mathlib | **closed** (2026-06-29) — ladder in [`priorities.md`](priorities.md); corrected the audit (P1's general content is `TopDimMinPrimes*`; P3 is one module; `SmoothPointRegular`/`NoetherMonicPositioning`/`rank_map_eq_of_injective`/`minimalPrimes` already done) |
| 01 | lean-formaliser (P1-R1) | extract `minimalPrimes_sInf_of_finite_of_isPrime` SPIKE → `Core/MinimalPrime/Finite` | **closed** (`2ab2995a`) — `Ideal.minimalPrimes_sInf_of_finite_of_isPrime`, `[CommSemiring]`+finite+prime; sibling-clash cleared; green 3820 / axiom-clean; review waived (not a crux). Card: `threads/01-minimalprimes-spike/statement-card.md` |
| 02 | lean-formaliser (P1-R2) | re-home localization `≤`-half `ringKrullDim_localization_le` → `Core/.../Localization` | **in flight** |

## Roadmap (future — not this expedition)
mathlib4 upstream PRs (built internal-first); shared-package extraction (ReLU second consumer);
`GenericFreeness`/`PrincipalOpenComorphism` (fold opportunistically); ⑤'s smooth-Jacobian was subsumed by #14.
