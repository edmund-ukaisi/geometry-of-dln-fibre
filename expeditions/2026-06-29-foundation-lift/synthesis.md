# Synthesis — `foundation-lift` (foundation-lift II)

*Accumulates as rungs/phases land. Opening shape: [`brief.md`](brief.md) + [`priorities.md`](priorities.md).*

The second **build-the-buildable** expedition: lift three more batches of project-local-but-general
`DLNFibre.Core` modules to Mathlib-grade, in phases — **P1** components & local dimension (`TopDimMinPrimes*`
+ localization no-drop), **P2** determinantal & elimination algebra (graph ideals + matrix-rank), **P3**
smooth/cotangent (`CotangentJacobian`) — each its own PR, driven autonomously on stacked branches off
`origin/dev` `00fb7238` (PR #14). Built on #14's dimension stack; same machine + lessons L1–L4.

## Tick log
- **2026-06-29 — kickoff.** Coverage recon closed (corrected the audit: P1 = `TopDimMinPrimes*` not
  `SigmaComponents`/`ThetaComponentCount`; P3 one module; `SmoothPointRegular`/`NoetherMonicPositioning`/
  `rank_map_eq_of_injective`/`minimalPrimes` already done in #14). Worktree on `expedition/foundation-lift-p1`
  off `origin/dev`, build warmed (430M, trees identical). Scaffold + cron set. P1-R1 dispatched.
- **2026-06-29 — P1-R1 LANDED** (`2ab2995a`). The minimal-primes SPIKE re-homed to
  `Core/MinimalPrime/Finite.lean`: `Ideal.minimalPrimes_sInf_of_finite_of_isPrime` (minimal primes of a
  finite prime-family `sInf` = inclusion-minimal members), with a bonus hypothesis-weakening
  `[CommRing]→[CommSemiring]` (build-confirmed). Sibling-clash cleared, re-gate green 3820, axiom-clean,
  L3-clean. Review **waived** (low-risk warm-up — review reserved for the three crux rungs). → P1-R2 dispatched
  (localization `≤`-half).
- **2026-06-29 — P1-R2 LANDED** (`3ad47fe7`). `ringKrullDim_localization_le` re-homed verbatim to
  `Core/Dimension/Localization.lean` (co-located with #14's `Dimension/` family; R3 lands here too). `@[stacks]`
  declined (Stacks carries it only as a corollary — name=content). Formaliser green 3820, axiom-clean, L3-clean.
  **Gate-cadence recalibrated (L5):** under sustained box load, controller re-gates at phase boundaries + crux
  rungs (not every low-risk re-home); intermediate verbatim re-homes ride the formaliser's fresh green + the
  boundary re-gate. → P1-R3 dispatched (affine-domain trdeg-sandwich no-drop).
- **2026-06-29 — P1-R3 LANDED** (`16cd40f2`). The four affine-domain no-drop lemmas
  (`ringKrullDim_eq_trdeg_of_fg_domain`, `trdeg_localization_eq`, `ringKrullDim_localizationAway_eq_of_{fg_domain,avoids_top_prime}`)
  folded into `Core/Dimension/Localization.lean` beside R2's `≤`-half; `AffineLocalizationNoDrop.lean` deleted;
  5 consumers re-pointed. Green 3819, axiom-clean. **R5 crux detail captured:** the per-prime `hper` is a
  hypothesis discharged once-per-top-prime via R3's `ringKrullDim_localizationAway_eq_of_fg_domain` (NOT from
  global no-drop + avoidance — DVR-at-uniformizer); R5 must carry the per-prime shape. → P1-R4 dispatched
  (`TopDimMinPrimes` core).
- **2026-06-29 — P1-R5 LANDED → PHASE-1 CONTENT-COMPLETE** (`9b66a95f`). The four transport rungs →
  `Core/MinimalPrime/{Localization,Polynomial,Radical,Bridge}.lean`. **The crux held:** the per-prime `hper`
  on `topDimMinPrimes_ncard_away_eq` is preserved **verbatim** (`∀ p ∈ TopDimMinPrimes A, dim(Away (mk p f)) =
  dim(A⧸p)`), separate from the global `hdim`, not derivable from `hdim + havoid` (DVR-at-uniformizer); the
  discharge stays local in `TopDimMinPrimesW1W2` via R3's lemma. **P1-boundary re-gate green 3819**,
  axiom-clean. The `Ideal.MinimalPrime`-mirroring family now stands: `Finite · TopDimensional · Localization ·
  Polynomial · Radical · Bridge`. Decorrelated crux-review (05r) in flight; on PASS → **PR-P1 opens** (async
  review) and P2 begins.
- **2026-06-29 — PHASE 1 SIGNED OFF → PR #15** (`expedition/foundation-lift-p1 → dev`). Crux-review **PASS**:
  the per-prime `hper` is genuine + byte-faithful, and the non-foldability was Codex-corroborated with the
  explicit counterexample `A = k[t]₍ₜ₎ × k[u]`, `f=(t,1)` (sharpening the per-prime-no-drop memory — the
  *product* shape, not a bare DVR, is what witnesses it). Transport sound, assembly coherent, no blocker.
  P1-boundary re-gate green 3819. → **Rolling into P2 without pausing**: stacked branch
  `expedition/foundation-lift-p2` off P1's tip; P2-R1 (graph-ideal package, the lowest-risk warm-up) dispatched.
- **2026-06-29 — P2-R1 LANDED** (`c7287232`). The graph-ideal elimination package → `Core/MvPolynomial/GraphIdeal.lean`
  (ns `MvPolynomial`): `ker_aeval_eq_graphIdeal` (the multivariate analogue of `Polynomial.ker_evalRingHom`,
  absent in Mathlib v4.29) + quotient-equiv elimination + primality, all `[CommRing]`-general, verbatim re-home.
  `MvPolynomialKerAeval.lean` deleted; only `GraphIdealHeight` re-pointed (transitive consumers `open MvPolynomial`).
  Green 3819, axiom-clean. → P2-R2 dispatched — **the P2 CRUX** (matrix minor-rank `rank_le_iff_forall_submatrix_det_eq_zero`,
  the `←` extraction direction): full re-gate + decorrelated review on completion.
- **2026-06-29 — P1-R4 LANDED** (`9a922438`). The `TopDimMinPrimes` count-engine core → `Core/MinimalPrime/TopDimensional.lean`
  (ns `Ideal`): 6 decls, all `[CommRing]`-only, the count `topDimMinPrimes_ncard_eq_of_ringEquiv` an
  unconditional ring-iso invariant. `TopDimMinPrimes.lean` deleted, 16 consumers re-pointed (selective `open`
  to avoid `map`/`comap`/`height` shadowing). Green 3819, axiom-clean. The per-prime no-drop is NOT here
  (R5's). → **P1-R5 dispatched — the CRUX** (transport rungs; the per-prime no-drop count survival): full
  controller re-gate + decorrelated review on completion.
- **2026-06-29 — P2-R2 LANDED + PR #15 review fixes applied** (`eff28654` rebased / `165e0954`). P2-R2 (the P2
  crux): matrix minor-rank core → `Core/Matrix/RankMinors.lean` — `rank_le_iff_forall_submatrix_det_eq_zero`
  (the `↔` Mathlib lacks) + `rank_map_eq_of_injective`; the `←` minor-extraction kept verbatim at `Fin`/`ℕ`
  generality (broader `Fintype` index = clean follow-up); DLN remainder stays local; green 3820, axiom-clean.
  **Meanwhile, operator review on PR #15** (5 comments — all concurred): dropped 2 unused `[q.IsPrime]`
  (verified), repointed stale `Core.TopDimMinPrimes` prose, softened `TopDimensional` doc to dimension-only,
  `Radical` doc prime→ideal, stripped process-provenance from `Localization` header — applied Lean-only on p1
  (`165e0954`, #15 updated), and **p2 rebased onto p1'** (`09c5cb79`, clean — disjoint files). → P2-R2 crux-review
  (07r) routed + **P2-R3 dispatched** (`GraphIdealHeight`), concurrently. After R3 + 07r: P2 boundary → PR-P2.
