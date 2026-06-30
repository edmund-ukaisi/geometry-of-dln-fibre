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

## Phase 2 — orbit-dimension squeeze
_starting: the P2.0 de-`Tuple` probe (the gate). Proceed on a positive probe; halt + surface only if the
argument is irreducibly `Tuple`-shaped._
