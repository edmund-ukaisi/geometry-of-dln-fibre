# Brief — `fibration-geometry` expedition

## Central question

> **Harden the DLN fibre geometry into a flat, locally-trivial family.**
> Earn the honest source-side `locallyTrivial` of `mult⁻¹(B) → base` over the rank-`= r` open (via the
> prime/residue-field **rank bridge** `rankROpen = {rank = r}`); register the **flatness** payoff and its
> corollaries; certify the **smooth-block** local model at every top-component generic point (the first
> slab of the RLCT runway); and package the whole through a reusable **scheme-bundle API** — building
> whatever Mathlib-level scaffolding is missing along the way.

This is the "geometry side, hardened and cleaner" the operator asked for, scoped as a **hero arc on
well-established mathematics**. The pieces with no pre-packaged Mathlib lemma (the over-field minor-rank
criterion, scheme-level local triviality, the lci local model) are **scaffolding we build**, not walls.

## Why now / the destination

The eventual prize (next expedition) is replacing the cited axiom
`DLN/RlctPayoff.lean RlctInterface.cited_aoyagi_dln`, which *assumes* `rlct(lossDLN) = ½·codim`. That
analytic bridge needs a clean geometric substrate: a flat, locally-trivial family with an identified
smooth locus and a local quadratic (lci) model. **This expedition builds that substrate** and hands over
the RLCT-runway's first slab (the smooth-block upper-bound model), without taking on the analytic layer
itself (Mathlib has zero RLCT/zeta content — that is the next expedition's hero arc, teed up here).

## Recon result that reshaped scope (both scouts, 2026-06-27)

- **The keystone is one bridge, not three problems.** The three "bundle" questions collapse onto the
  prime/residue-field **rank bridge**. `rankROpen` is currently *defined* as the complement of the
  pivot-minor vanishing locus (`FibreBundleLocallyTrivialFull.lean:520`); its docstring flags that
  `rankROpen = {rank = r}` is **not yet a theorem**. Closing it is S1.
- **The keystone is bounded-but-new, reachable.** Mathlib's `Rank.lean` has the "≥" direction
  (`rank_of_isUnit`, `rank_submatrix_le`); the "≤" direction (all `(r+1)`-minors vanish ⟹ `rank ≤ r`
  over a field) is **not** packaged, but it is the **dual of the banked
  `RankMinorCover.exists_invertible_minor_of_rank`** (rank `r` ⟹ ∃ invertible `r×r` minor). We build the
  dual.
- **P2 (rebase to the genuine target `Mat^{=r}`) is dropped.** Our source-side atlas and LR's Lemma-4.6
  bundle are genuinely different objects (LR's is target-side `G_out`-equivariant); and the paper's only
  *used* consequence — the arbitrary-`B` component count — is **already proved**
  (`FibreThetaCountArbitrary.ncard_topDimMinPrimes_fibre_eq_cTheta_dminus_of_rank`). Roadmapped (R4),
  not pursued, unless the goal becomes faithful-Lemma-4.6-as-target-geometry.
- **Flatness coverage is rich.** `AlgebraicGeometry.Flat`, `UniversallyOpen.of_flat`,
  `Module.isLocallyConstant_rankAtStalk`, `freeLocus`/`isOpen_freeLocus` are all in-tree.
- **The RLCT runway's true wall is a singular-locus *lower* bound** (`rlct ≥ codim/2` at every singular
  real point); the smooth-block gives only the upper bound. That lower bound + the analytic layer is the
  next expedition. This expedition certifies the smooth-block (slab 1) and roadmaps the singular split
  (R2).

## The spine — active rungs (this expedition)

Each rung is a tide to bedrock: green, sorry-free, axiom-clean, AUDIT + decorrelated review + hardener
pass, **name = content**.

- **S1 — Rank-bridge keystone. [LANDED — `FibreRankBridge.lean`]** The prime/residue-field rank bridge
  `mem_rankROpen_iff_rank_universalMatrixResidue_eq`: for `P ∈ Spec(sweepSigmaRing)`,
  `P ∈ rankROpen ↔ (universal matrix over κ(P)).rank = r` (full `↔`). The "≤" over-field minor criterion
  was **already banked** (`rank_le_iff_forall_submatrix_det_eq_zero`, `RankLocusClosed`) — reused, not
  rebuilt. Closes the scheme-level **set-of-primes** identity `rankROpen = {P | rank over κ(P) = r}`
  (no structure-sheaf object claimed; vacuously true in the rank-unachievable regime). **Keystone —
  gates S3, S4.**
- **S2 — Smooth-block certificate. [LANDED — `FibreSmoothBlock.lean`]** At a smooth closed point of a
  top-dimensional component, the local **Kähler** module `Ω[A_m⁄k]` is **free**, with
  `rank(Ω) + codim = ambient` — i.e. `rank(Ω) = ambient − codim = dim(component)` (the *relative*
  dimension), pinned to the proved codim `C + δ` (`fibre_smoothBlock_certificate`). ⚠ The
  *conormal* module `I/I²` is the one free of rank `= codim` — a **separate** statement (→ **S2b** /
  roadmap), not this one (brief's earlier "rank = codim" phrasing was a Kähler/conormal conflation the
  tide caught). **RLCT-runway slab 1** (the smooth-locus upper-bound model). Was independent of S1.
- **S3 — Flatness facts. [LANDED (partial) — `FibreFlatness.lean`]** The cheap-flatness verdict
  (cheap on both readings; no miracle/generic) + honest sub-facts: localization flatness, the
  `SchurLoc`-free standard model, scheme `UniversallyOpen`. The brief's literal target
  `Flat π : mult⁻¹(rankROpen) → rankROpen` is **NOT** delivered here — see S4b.
- **S4b — `SchurLoc`-linear (over-base) trivialization + chartwise flatness. [LANDED — `FibreOverBaseTriv.lean`;
  the convergent keystone, hardener PASS]** Upgrades the per-pivot trivialization to
  `Away(chartDsigAt s t) ≃ₐ[SchurLoc] SchurLoc ⊗ sweepFibreRing` over the **honest banked structure map**
  (non-circular, confirmed 2 ways) ⟹ `chartDsigAt_flat_over_schurLoc` (chartwise fibre-family flatness
  **over `SchurLoc`**). Completes S4's over-base content + the S3 flatness, chartwise. ⚠ Flatness is over
  the in-chart Schur ring `SchurLoc`, **not** the literal `Flat π` over `rankROpen` — that needs the
  **chart-base bridge** `SchurLoc ≅ sweepSigmaRing|basicOpen(chartDsigAt)` (roadmap, ahead of R1) + R1.
- **S4 — Honest local product over `rankROpen`. [LANDED (partial) — `FibreLocallyTrivial.lean`]**
  `RankROpenPerPivotLocalProduct` + the pointwise headline `reducedFibre_existsProductChartAt_rankEq`:
  S1 folded in certifies `rankROpen` genuinely IS the residue-field rank-=r locus; the pivot charts
  cover it; each chart's localized ring is a `k`-algebra product `SchurLoc ⊗ sweepFibreRing`. Honestly
  **not** `locallyTrivial` — k-algebra-only + uncocycled. **The load-bearing completion is S4b** (the
  over-base / projection-compatible `O(U)`-algebra trivialization) + R1 (the overlap gluing); a genuine
  fibre-bundle = S4 + S4b + R1.
- **S5 — Capstone bundle headline. [in flight — `FibreBundleHeadline.lean`]** Package S4/S4b into a
  clean reader-facing over-base local-product-with-flatness headline for the DLN fibre family (cover +
  per-pivot `≃ₐ[SchurLoc]` product + chartwise flatness over `SchurLoc`), carrying the base distinction +
  named open items (P-bridge, R1). Concrete — **not** a speculative abstract `IsLocallyTrivialProduct`
  predicate (no second consumer yet; that abstraction is roadmap-only per the extract-when-a-consumer-appears
  rule).

## Roadmap — sequenced future waves (reachable; not walls)

Recorded in `ROADMAP.md`; pulled into a future expedition (or a later wave of this one if momentum holds).

- **R1 — `targetOverlapTransition`:** the full overlap-trivialization cocycle (honest version) —
  completes the bundle's gluing data.
- **R2 — singular-locus = deepest-stratum split:** identify the fibre's singular locus as (the image of)
  deeper-corner strata; prove smooth above / not-smooth on. Full anatomy + the RLCT runway's lower-bound
  start. New Jacobian-rank-drop argument; we build the scaffolding.
- **R3 — `e` rung-2 `LocalizedChartDescent`:** the localized full-`d`-orbit descent (the only reachable
  shape; global/shifted-orbit shapes are false).
- **R4 — `Mat^{=r}` target rebase:** only if faithful-Lemma-4.6-as-target-geometry becomes the goal
  (else redundant — arbitrary-`B` count already proved).
- **R5 (next expedition) — the RLCT analytic bridge:** local quadratic / lci regular-sequence model ⟹
  `rlct = c/2` locally; the singular-locus lower bound; replace `cited_aoyagi_dln`.

## Disposition (operator steer, 2026-06-27)

Run this as a large rising-sea expedition: **keep the vision, let the sea rise.** "Little/no Mathlib
support" is **not a blocker** — these are well-established mathematics and the controller builds the
missing scaffolding via tides. Do **not** treat recon as derisking that gates action; recon sharpens the
target, then we drive. Be *more* ambitious than the teammates; set targets at the edge of reach, drop
scope only for a genuine blocker. The loop-prompt + hourly cron backstop + teammate pings are the
machinery that keeps the tick running unattended (see `lessons.md`).

## Closing criterion

- S1–S5 landed to bedrock (each: green · sorry-free · axiom-clean · AUDIT · decorrelated review ·
  hardener pass), with **name = content** on every headline (the `locallyTrivial` and `Flat π` statements
  denote exactly what is proved; any residual gluing data named as the open target, not overclaimed).
- The smooth-block certificate (S2) stated and handed over as the RLCT-runway slab.
- `ROADMAP.md` updated with R1–R5; the expedition's exposition + a final `synthesis.md` written.
- PR opened against `dev` (signal-and-wait; operator merges).

## Scope fences (NOT in this expedition)

- The RLCT / zeta / Watanabe analytic layer (R5, next expedition).
- The singular-locus lower bound and the deepest-stratum split (R2).
- The `Mat^{=r}` target rebase (R4) and the full overlap cocycle (R1) — unless a spine rung forces them.
