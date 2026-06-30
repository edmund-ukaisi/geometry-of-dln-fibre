# Synthesis — `foundation-lift-iii`

_Accumulates as rungs land. Final synthesis at close._

## Kickoff (2026-06-29)
Third **build-the-buildable** expedition, on `origin/dev` `5bb7adc2` (after #14 dimension stack + FL-II
#15/#16/#17). Central question: package the differential-algebra interface behind the orbit-dimension argument
(`generic differential rank → Jacobian/Kähler rank → trdeg bound → image dimension`) as a Mathlib-grade DLN-free
library (Phase 1), then lift the orbit-dimension capstone — the **differential/cotangent squeeze** (recalibrated
from `dim G − dim Stab`, operator-confirmed) — de-coupled from the DLN `Tuple` encoding (Phase 2, probe-gated).

## Phase 1 — differential-algebra interface (in progress, `fl3-p1`)

**Re-homes landed:** P1.1 (`333a038b`) split `JacobianTrdeg.lean` → `Core/RingTheory/Kaehler/GenericRank.lean`
(generic differential rank + base-change-injectivity + char-0 criterion) + `Core/Dimension/Trdeg.lean`
(`trdeg ≤ rank` wrapper, char-free). P1.5+P1.6-V2 (`1dc6c698`) split `MatrixKaehler.lean` →
`Core/RingTheory/Derivation/Matrix.lean` (derivation calculus) + `Core/LinearAlgebra/BaseChange.lean`
(`finrank_range_baseChange`, V2). P1.3/P1.4 (cotangent–Jacobian + cotangent-localization) verified Mathlib-grade
already, no edit.

**Findings (banked):**

1. **The `[CharZero]` hypothesis on the differential-independence criterion is the *exact* line — `[PerfectField]`
   is FALSE, not merely out of reach.** The perfect-field requirement falls on the rational function field
   `Pf = k(X₁..Xₙ)`, which is perfect **iff** char 0 (for n>0). Counterexample (reviewer + decorrelated Codex,
   independent): `k = 𝔽_p`, `B = 𝔽_p[T]`, `x = T^p` — transcendental over `k`, yet `D_k(T^p) = p·T^{p-1}dT = 0`,
   so the differentials are not independent; lands squarely on the theorem's `[EssFiniteType]` hypothesis set.
   So `CharZero` stays; the genuine char-`p` analogue is a *separate* criterion (separability / `p`-independence
   of `k(xᵢ) → K`), **roadmapped** below — not a chore-deferral. This is the disposition's "earned taste
   judgment that a gap is *not* the right extension."

2. **A layering inversion in the merged #14 stack, fixed by P1.7.** `Dimension/Localization.lean` (foundational)
   imported the orbit-flavored `AffineNoetherRank.lean` (→ `OrbitPullbackDim` → DLN machinery) only to borrow
   the pure char-free `trdeg_eq_of_integral_injective`. P1.7 pushes that fact to a low-level home so both the
   dimension stack and the orbit lemma depend downward onto it, and re-derives the `k[Fin n]⧸p` quotient lemma
   from the general `ringKrullDim_eq_trdeg_of_fg_domain` (it is the `A := R⧸p` instance).

3. **V3 (differential-family-span base-change) is Mathlib's, not ours** — `Module.Flat.linearIndependent_one_tmul`,
   already named + documented inline in `GenericRank`. No extraction (would be an anti-Mathlib re-export); the
   3-way base-change-rank distinctness is recorded in docstrings (V1 entrywise-matrix, V2 linear-map, V3 flat).

## Roadmap (surfaced, not in scope here)
- **Char-`p` differential-independence criterion.** A separability / `p`-independence version of
  `DiffIndepCriterion` over an imperfect base (the `k(xᵢ) → K` subextension separable / formally smooth), to lift
  the char-0 restriction on `trdeg ≤ generic differential rank`. Genuinely-separate new math, not a hypothesis
  relaxation. The DLN payoff is char-0 (ℝ/ℂ), so this is library generality, not application need.

### Phase 1 CLOSE (2026-06-30)
All rungs landed; controller phase-boundary re-gate PASSED (full build 3823 jobs green, sorries 0, axioms
`[propext, Classical.choice, Quot.sound]` on every Phase-1 headline + both DLN payoffs unchanged). The
differential-algebra interface is now Mathlib-grade and DLN-free:
- `Core/RingTheory/Kaehler/GenericRank.lean` — generic differential rank + the char-0 `DiffIndepCriterion`.
- `Core/Dimension/Trdeg.lean` — `trdeg ≤ generic differential rank` (char-free wrapper).
- `Core/RingTheory/MvPolynomial/CotangentJacobian.lean` + `Core/RingTheory/Ideal/CotangentLocalization.lean`
  — Jacobian orientation + cotangent-dim = ker-Jacobian-dim (FL-II, verified).
- `Core/RingTheory/Derivation/Matrix.lean` — matrix-Kähler derivation calculus.
- `Core/LinearAlgebra/BaseChange.lean` — base-change rank (V2), with the 3-way distinctness recorded.
- `Core/Dimension/Integral.lean` — `trdeg_eq_of_integral_injective` (re-homed; layering inversion fixed).
Net library effect beyond the re-homes: a #14 layering inversion repaired, two minimal-hypothesis/name=content
fixes, and one roadmap item surfaced (the char-`p` criterion). PR opened off `fl3-p1` for async review.

## Phase 2 — orbit-dimension squeeze (`fl3-p2`)

**P2.0 probe (scout, 2026-06-30) → VERDICT: PROCEED** ([`threads/p2.0-probe/report.md`](threads/p2.0-probe/report.md)).
The squeeze lifts to a **small hypothesis-carrying engine**, not a full algebraic-group framework. No step is
irreducibly `Tuple`-shaped — the two geometric facts (Maurer–Cartan differential factorisation; dual-number
infinitesimal-action ideal-killing) become **named hypotheses** (H1 `DifferentialFactors`, H2) that the DLN
matrix-tuple code discharges as the first instance. The keystone A4.3 bound restated against the abstract
carrier `AffineGVariety k := (ρ, R, fρ, C0, C1, δ)` scratch-elaborates with no `cochain`/`Tuple` type — the core
feasibility signal. Decorrelated Codex (xhigh) independently concurred on verdict + boundary.

**Engine (the 4 bricks):** B1 `GenericRankBound` (A4.3 ≤, from H1), B2 `AdjointRank` (= Mathlib
`finrank_range_dualMap_eq_finrank_range`, no new statement), B3 `CotangentInjection` + B4 `SmoothCotangentDim`
(A6.1 ≥, from H2 + smooth `k`-rational point + dense `k`-orbit), + the squeeze headline. Rung plan P2.1–P2.6 in
[`priorities.md`](priorities.md); cruxes P2.4 (the H1 `L` carrier signature) + P2.5 (the H2 derivation carrier +
"dense `k`-orbit meets smooth locus" over non-alg-closed `k`) flagged for decorrelated review. Scope discipline:
name=content on H1/H2 (abstract *inputs*, not consequences of a bare orbit map); namespace-mirror so the eventual
Mathlib lift is a file-move.

**Rungs landed:** P2.2 (`64d75981`) layered `AffineGVariety` carrier + orbit-as-image irreducibility (`isPrime_ker_pullback`), DLN re-derived. P2.3 (`303db988`) the `varietyDim 𝒪 = trdeg` anchor (A4.1) on the carrier, `[Finite ρ]` minimal-hyp, DLN re-derived to 3 lines. P2.4 (`0b580992`) the B1 `GenericRankBound` crux.

**P2.4 finding — the forward H1 is undischargeable; the transpose is the honest shape (the guard earned its keep).** The probe §3 forward hypothesis `span_K{D f_x} ≤ range(L ∘ δ.baseChange)` cannot be discharged by the DLN model: `range(L ∘ δ.bc) = L(range δ)`, so `L` only ever sees the coboundary image `range δ ⊊ C1`, but the orbit-coordinate differentials pair the Maurer–Cartan bracket against *single* `C1` entries outside `range δ`. The GUARD-first step (write the DLN discharge before fixing the abstract signature) caught this exactly. The honest, dischargeable form is the **transpose** carrier — `DifferentialFactors (δAdj : C1 →ₗ[k] C0) (L) := span_K{D f_x} ≤ range(L ∘ δAdj.baseChange)` plus a rank-tie `finrank(range δAdj) = finrank(range δ)` — which is the "carry `δAdj`" alternative the probe blessed in §1(iii). DLN discharges it with `δAdj := deltaT M`, rank-tie `= finrank_range_deltaT`; abstract B1 stays clean (V2 + finrank_mono, no `deltaT`); the keystone re-derives signature-unchanged (~70-line monolith collapsed into engine + discharge). name=content preserved — the adjoint + rank-tie are abstract *inputs*, `deltaT`/matrix self-duality stay the DLN detail. _Routed for decorrelated review (crux)._ **Implication for P2.5:** same GUARD-first discipline — pin the (H2) carrier by writing the DLN discharge first; the forward shape may again be the wrong one.

**P2.4 decorrelated review: SURVIVED.** Transpose-H1 honest — non-circular (`δ` enters only via the rank-tie at
the final step; `δAdj` is a free argument), **non-vacuous** (reviewer built a non-DLN witness `R=ℚ[X]`, `δ=δAdj=id`
firing `genericRankBound`), forward-fails diagnosis confirmed against `deformationδ`/`bracketG`, discharge fidelity
PASS (rank-tie *proved* via `finrank_range_deltaT`, not assumed; `deltaT` confined to the DLN file), keystone
byte-identical, re-gate green (3826) + axioms clean; Codex (xhigh) concurred on all four sub-questions. P2.4 is
bedrock.

**P2.5a (B3 `CotangentInjection`) landed (`21908723`).** Unlike H1, the **forward H2 pins cleanly** — the
`InfinitesimalAction` hypothesis carries `dirDeriv`/`c1coord` directly, so the coordinate test recovers `δφ`'s
components (no adjoint, no rank-tie, no `deltaT`). B3 `finrank(range δ) ≤ finrank(cotangent)` is a clean
rank-nullity (`ker cotPairing ≤ ker δ` + `dual_finrank_eq`), `[FiniteDimensional k m.Cotangent]` the only input
(smooth-point deferred to B4). DLN discharge `dlnInfinitesimalAction` re-derives R5 signature-unchanged (dead R3–R5
chain collapsed). Forward-vs-transpose is genuinely model/hypothesis-dependent (L8): H1 needed the transpose, H2
does not. Formaliser self-spawned decorrelated review SURVIVED + Codex; controller code-inspection confirmed
honesty + non-vacuity (the DLN instance is a built witness) → accepted.

_Executing: P2.5b (B4 `SmoothCotangentDim`, the `= varietyDim` half — smooth `k`-point + dense `k`-orbit)
dispatched; controller decorrelated review reserved for it (the non-alg-closed-`k` density sub-crux). Then P2.6
assembles the squeeze._
