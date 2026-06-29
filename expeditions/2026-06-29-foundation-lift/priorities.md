# Priorities — `foundation-lift` (taste ledger)

Controller proposes by VOI; **operator edits this file directly**. Foundation-first, build-the-buildable
([`../../docs/policies/library-building.md`](../../docs/policies/library-building.md)). All scoping against
`origin/dev` `00fb7238` (PR #14). Recon CLOSED 2026-06-29 (validated the 3-phase grouping + corrected the audit).

## Phase 1 — Components & local dimension  ·  branch `expedition/foundation-lift-p1` (off `origin/dev`)

The general count engine is **`TopDimMinPrimes*`** (the audit's `SigmaComponents`/`ThetaComponentCount` are
DLN-local — exclude). Tags to #14's `Codimension` (`minimalPrimes` API + any-proper-ideal catenary —
already there). All already-green; the work is re-home + Mathlib-grade hygiene.

| rung | item | source | target (mirror) | status |
|------|------|--------|------------------|--------|
| P1-R1 | extract the SPIKE `minimalPrimes_sInf_of_finite_of_isPrime` (minimal primes of a finite prime-family `sInf` = inclusion-minimal members; Mathlib has only the radical-intersection form) | `SigmaComponents.lean:50–78` | `Core/MinimalPrime/Finite.lean` (ns `Ideal`, mirror `Mathlib.RingTheory.Ideal.MinimalPrime`) | **done** (`2ab2995a`; bonus `[CommRing]→[CommSemiring]` weakening; sibling-clash cleared; re-gate green 3820; review waived — not a crux) |
| P1-R2 | re-home the localization `≤`-half `ringKrullDim_localization_le` | `LocalizationKrullDim.lean` | `Core/Dimension/Localization.lean` | **done** (`3ad47fe7`; verbatim re-home, `@[stacks]` declined — corollary-only; sibling-clash cleared; formaliser green 3820; phase-boundary re-gate per L5) |
| P1-R3 | re-home the affine-domain trdeg-sandwich no-drop (`ringKrullDim_eq_trdeg_of_fg_domain`, `trdeg_localization_eq`, `..._localizationAway_eq_of_{fg_domain,avoids_top_prime}`) | `AffineLocalizationNoDrop.lean` | `Core/Dimension/Localization.lean` | **done** (`16cd40f2`; 4 no-drop lemmas folded beside R2's ≤-half; source deleted; green 3819 / axiom-clean) |
| P1-R4 | extract the `TopDimMinPrimes` core (`TopDimMinPrimes`, `bijOn_comap`, `topDimMinPrimes_ncard_eq_of_ringEquiv`) — **a best-warm-up, low-risk, high-reuse** | `TopDimMinPrimes.lean` | `Core/MinimalPrime/TopDimensional.lean` (ns `Ideal`) | **done** (`9a922438`; 6 decls `[CommRing]`-only, count an unconditional ring-iso invariant; 16 consumers re-pointed w/ selective `open`; green 3819 / axiom-clean) |
| P1-R5 | extract the transport rungs `TopDimMinPrimes{Localization,Poly,Radical,Bridge}` onto R4 | those 4 modules | `Core/MinimalPrime/{Localization,Polynomial,Radical,Bridge}` | **done** (`9b66a95f`; per-prime `hper` preserved **verbatim** — `∀ p ∈ TopDimMinPrimes A, dim(Away (mk p f))=dim(A⧸p)`, not weakened to global; re-gate green 3819; **decorrelated crux-review in flight**) — **CRUX: `TopDimMinPrimesLocalization` (per-prime no-drop) → decorrelated review** (re-confirm the per-prime no-drop does NOT fold from global-no-drop+avoidance — DVR-at-uniformizer counterexample; reviewer+Codex+memory recorded this). **R3 flag (the exact shape R5 must carry):** the `hper` consumed by `topDimMinPrimes_ncard_away_eq` is a per-prime hypothesis `∀ p ∈ TopDimMinPrimes A, ringKrullDim (Away (mk p f)) = ringKrullDim (A⧸p)`, discharged once-per-top-prime in `TopDimMinPrimesW1W2` via R3's `ringKrullDim_localizationAway_eq_of_fg_domain` (each `A⧸p` an fg `k`-domain, `f̄≠0`) — NOT from a global no-drop + avoidance. |

**Exclude (stay DLN-local):** `SigmaComponents` (minus R1), `ThetaComponentCount`, `TopDimMinPrimes{W0,W1W2,W2,ChartE,GfibAvoid}`.
**Mathlib:** `minimalPrimes.equivIrreducibleComponents`, `sInf_minimalPrimes`, `finite_minimalPrimes_of_isNoetherianRing`, `IsLocalization.orderIsoOfPrime` exist; the finite-family-`sInf` packaging + the trdeg-sandwich no-drop are genuine gaps.

## Phase 2 — Determinantal & elimination algebra  ·  branch `-p2` (off `-p1`)

Independent of P1 (depends only on #14's `Codimension` catenary). Both halves already maximally general.

| rung | item | source | target (mirror) | status |
|------|------|--------|------------------|--------|
| P2-R1 | extract the graph-ideal package (`graphIdeal`, `ker_aeval_eq_graphIdeal`, `graphIdealQuotientEquiv`, `graphIdeal_isPrime`) — **lowest-risk warm-up** | `MvPolynomialKerAeval.lean` | `Core/.../MvPolynomial/GraphIdeal` (ns `MvPolynomial`, mirror `RingTheory.MvPolynomial.Ideal`) | pending |
| P2-R2 | extract the matrix-rank core (`rank_le_iff_forall_submatrix_det_eq_zero` + supports + `rank_map_eq_of_injective`) | `RankLocusClosed.lean:46–166` | `Core/.../Matrix/RankMinors` (ns `Matrix`, mirror `LinearAlgebra.Matrix.Rank`) | pending — **CRUX: the `←` minor-extraction direction → decorrelated review** (confirm at the stated `Fin`/`ℕ` generality; consider general `Fintype` index). Split DLN remainder (`minorPoly`, `isZariskiClosed_orbitRankLocus`) to stay local |
| P2-R3 | extract/generalise `GraphIdealHeight` (`height_graphIdeal_eq = Nat.card σ`) onto P2-R1 + #14 `Codimension`; confirm minimal hyps | `GraphIdealHeight.lean` | `Core/.../MvPolynomial/GraphIdeal` | pending |

**Mathlib:** univariate `ker_evalRingHom = span {X - C x}` exists (multivariate **absent**); minor-rank characterisation + `rank_map_eq_of_injective` **absent** (genuine classical gaps). R1 ⊥ R2; R3 depends on R1.

## Phase 3 — Smooth points & cotangent dimension  ·  branch `-p3` (off `-p2`)

Single module (`SmoothPointRegular` subsumed by #14). Already `[Field k]`-general.

| rung | item | source | target (mirror) | status |
|------|------|--------|------------------|--------|
| P3-R1 | extract `CotangentJacobian` (cotangent dim = ker of the rectangular point-Jacobian at an arbitrary rational point — more general than Mathlib's smooth-only submersive Jacobian) | `CotangentJacobian.lean` | `Core/.../Smooth/Cotangent` (mirror `RingTheory.Smooth.Cotangent` / `AlgebraicGeometry.Tangent`) | pending — **CRUX: the cokernel-finrank bridge `card σ − rank Jᵀ = finrank ker J` (lines ~272–434) → decorrelated review** (index/transpose bookkeeping) |

**Mathlib:** Kähler/cotangent substrate present (`kerCotangentToTensor_injective_iff`, `tensorCotangentEquiv`, `FormallySmooth.of_perfectField`); the rectangular-point-Jacobian cotangent formula **absent** (Mathlib's is smooth/square only). Build-but-API-sensitive.

## Cross-cutting

- **Build-vs-cite line:** all P1/P2/P3 are buildable detail-at-scale (already green); cite only the SLT analytic core + Aoyagi `rlct = ½·codim` (unchanged).
- **Pre-flight per new top-level name:** `rg` the sibling-clash gate (`lean/CLAUDE.md`) for `graphIdeal`, `TopDimMinPrimes`, `rank_le_iff_forall_submatrix_det_eq_zero`, etc.
- **Apply L2** (transitive-consumer sweep + full-build) and **L4** (codepoint longLine) every rung; **L3** (don't dispatch next rung until prior formaliser's completion notification).
- **Lower-priority (fold opportunistically, not load-bearing):** `GenericFreeness`, `PrincipalOpenComorphism` — leave local unless a rung naturally absorbs them.

## Highest-suspicion (the three crux rungs → decorrelated review)
P1-R5 `TopDimMinPrimesLocalization` (per-prime no-drop) · P2-R2 minor-rank `←` · P3-R1 cokernel-finrank.
