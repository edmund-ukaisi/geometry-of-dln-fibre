# Threads — `foundation-lift`

**Multi-phase foundation-lift II** (P1 components & local dim → P2 determinantal & elimination → P3
smooth/cotangent), driven autonomously, **one PR per phase** (stacked branches), async operator review.
Per-thread notes in `threads/<NN>-<slug>/`.

| NN | type | subject | status |
|----|------|---------|--------|
| 00 | scout (recon) | coverage recon — validate the 3-phase ladder vs `origin/dev` + Mathlib | **closed** (2026-06-29) — ladder in [`priorities.md`](priorities.md); corrected the audit (P1's general content is `TopDimMinPrimes*`; P3 is one module; `SmoothPointRegular`/`NoetherMonicPositioning`/`rank_map_eq_of_injective`/`minimalPrimes` already done) |
| 01 | lean-formaliser (P1-R1) | extract `minimalPrimes_sInf_of_finite_of_isPrime` SPIKE → `Core/MinimalPrime/Finite` | **closed** (`2ab2995a`) — `Ideal.minimalPrimes_sInf_of_finite_of_isPrime`, `[CommSemiring]`+finite+prime; sibling-clash cleared; green 3820 / axiom-clean; review waived (not a crux). Card: `threads/01-minimalprimes-spike/statement-card.md` |
| 02 | lean-formaliser (P1-R2) | re-home localization `≤`-half `ringKrullDim_localization_le` → `Core/.../Localization` | **closed** (`3ad47fe7`) — `Core/Dimension/Localization.lean`; verbatim re-home, `@[stacks]` declined (corollary-only); green 3820 / axiom-clean; review waived. Card: `threads/02-localization-le/statement-card.md` |
| 03 | lean-formaliser (P1-R3) | re-home affine-domain trdeg-sandwich no-drop → `Core/Dimension/Localization` | **closed** (`16cd40f2`) — 4 no-drop lemmas (incl. the per-prime `ringKrullDim_localizationAway_eq_of_fg_domain` R5 needs) folded beside R2's ≤-half; `AffineLocalizationNoDrop.lean` deleted; green 3819 / axiom-clean. Card: `threads/03-affine-no-drop/statement-card.md` |
| 04 | lean-formaliser (P1-R4) | extract `TopDimMinPrimes` core (`bijOn_comap`, `ncard_eq_of_ringEquiv`) → `Core/MinimalPrime/TopDimensional` | **closed** (`9a922438`) — 6 decls `[CommRing]`-only; count = ring-iso invariant (unconditional); `TopDimMinPrimes.lean` deleted, 16 consumers re-pointed; green 3819 / axiom-clean. Card: `threads/04-topdim-core/statement-card.md` |
| 05 | lean-formaliser (P1-R5, **CRUX**) | extract transport `TopDimMinPrimes{Localization,Poly,Radical,Bridge}` onto R4 core → `Core/MinimalPrime/*` | **closed** (`9b66a95f`) — 4 modules `Core/MinimalPrime/{Localization,Polynomial,Radical,Bridge}`; per-prime `hper` preserved verbatim (not global — DVR-at-uniformizer); P1-boundary re-gate green 3819 / axiom-clean. Card: `threads/05-topdim-transport/statement-card.md`. **Pending crux-review (05r).** |
| 05r | reviewer (crux audit) | P1-R5 per-prime `hper` shape + transport soundness + P1 assembly | **in flight** |

## Roadmap (future — not this expedition)
mathlib4 upstream PRs (built internal-first); shared-package extraction (ReLU second consumer);
`GenericFreeness`/`PrincipalOpenComorphism` (fold opportunistically); ⑤'s smooth-Jacobian was subsumed by #14.
