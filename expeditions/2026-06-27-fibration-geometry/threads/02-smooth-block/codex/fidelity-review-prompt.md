<task>
I am an INDEPENDENT fidelity reviewer of a Lean 4 + Mathlib theorem. I did not write it.
A controller's loose brief said: "certify the standard-smooth local model: Ω (equivalently the
conormal/Jacobian module) is FREE of rank = codim". The author judged this conflates two
COMPLEMENTARY modules and instead formalised a Kähler statement. I must adversarially verify the
author's mathematical reading and that the Lean statement is faithful, NOT over/under-claiming.

The headline Lean theorem (verbatim, names abbreviated):

  theorem fibre_smoothBlock_certificate [IsAlgClosed k] [CharZero k]
      (d : Fin (N+2) → ℕ) (r : ℕ) (hp : r ≤ d_N) (hq : r ≤ d_0)
      (h : (kostantPartitions d r).Nonempty)
      (B : Matrix (Fin d_N) (Fin d_0) k) (hB : B.rank = r)
      (I : Ideal (sweepFibreRing …)) (hI : I ∈ TopDimMinPrimes (sweepFibreRing …))
      (m : Ideal (sweepFibreRing … ⧸ I)) [m.IsMaximal] [Algebra.IsSmoothAt k m] :
    Module.Free (Localization.AtPrime m) (Ω[Localization.AtPrime m ⁄ k]) ∧
      ∃ n : ℕ,
        Module.finrank (Localization.AtPrime m) (Ω[Localization.AtPrime m ⁄ k]) = n ∧
          (n : ℕ∞) + codimRepCanonical (fibre d B) = (Nat.card (RepCoord d) : ℕ∞)

VERIFIED FACTS (I checked these in the repo; treat as given):
- `Algebra.IsSmoothAt k m := Algebra.FormallySmooth k (Localization.AtPrime m)` (Mathlib abbrev).
- `Ω[R⁄k]` is Mathlib `KaehlerDifferential k R` (module of Kähler differentials of R over k).
- `RepCoord d = Σ i : Fin N, Fin (d i.succ) × Fin (d i.castSucc)`, so `Nat.card (RepCoord d)` is
  EXACTLY the number of matrix entries = ambient affine-space dimension where the fibre lives.
- `codimRepCanonical (fibre d B)` is DEFINED as `Ideal.height (vanishingIdeal (canonicalCoord ''
  fibre d B))` — the genuine geometric codimension (height of the vanishing ideal of the fibre's
  Zariski closure in the polynomial coordinate ring). It is PROVED equal to the closed form
  `(cCodim d r h).toNat + r*(d_N + d_0 − r)` (= C + δ).
- `sweepFibreRing = MvPolynomial (RepCoord d) k ⧸ vanishingIdeal (canonicalCoord '' fibre d
  (normalForm …))`, i.e. the coordinate ring of the rank-r normal-form fibre.
- `TopDimMinPrimes A = {p ∈ minimalPrimes A | ringKrullDim (A⧸p) = ringKrullDim A}`.
- The proof chain establishes: n = ringKrullDim(Localization.AtPrime m) [smooth ⟹ Ω free of
  finrank n with dim(local ring)=n], then ringKrullDim(A_m) = ringKrullDim(A) [local↔global at a
  closed point of a fin-type domain], then since I is top-dim, ringKrullDim(A) =
  ringKrullDim(sweepFibreRing) = varietyDim(fibre), and the catenary
  height(vanishingIdeal) + varietyDim = Nat.card(RepCoord) closes it. The codim of the arbitrary
  rank-r target B is transported to the normal-form fibre's codim by a same-rank invariance lemma.

QUESTIONS (answer each, crisply, distinguishing standard-math fact from inference about the setup):
1. Is the author's reading correct: for a SMOOTH affine variety X ⊆ 𝔸^N over a field, the Kähler
   module Ω_{X/k} is locally free of rank = dim X = N − codim X, while I/I² (conormal) is locally
   free of rank = codim X? Is "Ω free of rank = codim" ever defensible under a standard convention?
2. Is the stated identity `(n : ℕ∞) + codimRepCanonical (fibre d B) = Nat.card (RepCoord d)` a
   FAITHFUL, non-overclaiming rendering of "Ω free of rank = ambient − codim, codim pinned to the
   proved closed form"? Specifically: is there any hidden ⊤/⊥/saturation pitfall in stating this in
   ℕ∞ (extended naturals) with `n : ℕ` rather than Nat subtraction? Could the identity be vacuously
   true (e.g. both sides ⊤)? Note RepCoord is finite, so Nat.card(RepCoord) is a finite nat.
3. THE GENERIC-POINT GAP. The brief said "at a generic point of a top-dimensional component", but
   the theorem takes `m` a MAXIMAL ideal (closed point) with `Algebra.IsSmoothAt k m` as a
   hypothesis, and a companion lemma proves only that SOME smooth closed point EXISTS (dense smooth
   locus of an fp domain over alg-closed k, Jacobson ⟹ closed point in any nonempty open). Is
   stating the certificate at "a smooth closed point" (and existence of one) the honest faithful
   reading, given the local Krull dimension at the GENERIC point ⊥ of a domain is 0 (function field)
   so the "rank Ω = dim local ring" identity would be FALSE/0 there? Is the residual — that the
   produced m is SOME smooth closed point, not a prescribed θ-generic geometric point — a genuine
   limitation that should be flagged (it is flagged as "Deferred"), or does it undercut the claim?
4. Is there any way the theorem is TRUE BUT VACUOUS due to an unsatisfiable hypothesis bundle?
   In particular: with [IsAlgClosed k] [CharZero k], (kostantPartitions d r).Nonempty, B.rank = r,
   I ∈ TopDimMinPrimes(sweepFibreRing), m maximal with IsSmoothAt — is this bundle satisfiable
   (the companion existence lemma addresses m; TopDimMinPrimes nonemptiness is NOT witnessed in-file
   — flag if that is a vacuity risk for the per-point headline vs the existence headline)?
</task>

<output_contract>
Four numbered answers matching Q1–Q4. Each ≤ 6 sentences. For Q1 a crisp conflation verdict.
For Q2 explicitly rule in/out the ℕ∞ vacuity pitfall. For Q3 say whether closed-point is the honest
reading and whether the deferred residual is correctly scoped. For Q4 say whether the per-point
headline is vacuous-risk given TopDimMinPrimes nonemptiness is not witnessed in-file. End with a
2-line "biggest residual fidelity risk" note.
</output_contract>

<grounding_rules>
Distinguish standard algebraic-geometry fact from inference about this specific repo. If a claim
depends on a Mathlib lemma you cannot verify, say so. Do not invent Lean lemma names.
</grounding_rules>
