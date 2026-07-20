<task>
I am reviewing a Lean 4 / Mathlib commutative-algebra lemma. I want a decorrelated
pure-math check of whether one hypothesis is honest (genuinely required, not vacuous,
not circular, not silently baking in the conclusion).

SETUP. A is a commutative ring. f : A. S = Localization.Away f A (i.e. S = A[1/f],
IsLocalization at the submonoid `powers f`). For a commutative ring B define

  TopDimMinPrimes B := { p ∈ minimalPrimes B | ringKrullDim (B ⧸ p) = ringKrullDim B }

(the minimal primes whose quotient realizes the FULL Krull dimension of B — the
"top-dimensional irreducible components", dimension reading). ncard = set cardinality.

THE LEMMA (claimed proved, sorry-free):

  topDimMinPrimes_ncard_away_eq :
    (hdim  : ringKrullDim S = ringKrullDim A)
    (havoid : ∀ p ∈ TopDimMinPrimes A, f ∉ p)
    (hper  : ∀ p ∈ TopDimMinPrimes A,
               ringKrullDim (Localization.Away (Ideal.Quotient.mk p f)) = ringKrullDim (A ⧸ p))
    ⊢ (TopDimMinPrimes S).ncard = (TopDimMinPrimes A).ncard

Here `Localization.Away (Ideal.Quotient.mk p f)` is (A⧸p)[1/ f̄ ], the away-localization
of the integral domain A⧸p at the image of f. So `hper` says: for each top-dim minimal
prime p of A, inverting f̄ in the DOMAIN A⧸p does not drop its Krull dimension.

PROOF STRUCTURE (as actually written). comap (algebraMap A S) is shown to be a bijection
TopDimMinPrimes S → TopDimMinPrimes A.
 - minimal-prime correspondence: minimalPrimes S = comap⁻¹(minimalPrimes A) (IsLocalization).
 - MapsTo direction (comap P ∈ TopDimMinPrimes A for P ∈ TopDimMinPrimes S): uses ONLY hdim
   (NOT hper). Argument: with p = comap P, P = map p, S⧸P ≅ (A⧸p)[1/f̄], and
     dim A = dim S = dim(S⧸P) = dim((A⧸p)[1/f̄]) ≤ dim(A⧸p) ≤ dim A   (localization-le + quotient-le)
   forcing dim(A⧸p)=dim A. (Note: the "≤ dim(A⧸p)" step uses the always-true localization-≤,
   and the SQUEEZE between dim A on both ends forces equality WITHOUT hper.)
 - SurjOn / inverse direction (map p ∈ TopDimMinPrimes S for p ∈ TopDimMinPrimes A): uses hper.
   dim(S ⧸ map p) = dim((A⧸p)[1/f̄]) =[hper] dim(A⧸p) =[hp.2] dim A =[hdim] dim S.

QUESTIONS (answer each, pure math, A an ARBITRARY commutative ring unless noted):

Q1. Is `hper` genuinely REQUIRED for the SurjOn direction, or is it derivable from
    hdim + havoid + the minimal-prime correspondence? Specifically: is the componentwise
    no-drop dim((A⧸p)[1/f̄]) = dim(A⧸p) a consequence of the AMBIENT no-drop
    dim S = dim A plus avoidance, for an arbitrary A? Give a concrete counterexample
    (a ring A, element f, top-dim minimal prime p) where hdim and havoid both HOLD but
    dim((A⧸p)[1/f̄]) < dim(A⧸p) — i.e. where hper FAILS — if one exists. (The docstring
    claims a DVR-at-a-uniformizer type drop; check that intuition concretely.)

Q2. Is `hper` so STRONG that it bakes in the conclusion (makes the lemma trivial/circular)?
    I.e. does assuming hper already presuppose that map p is top-dimensional in S, or that
    the count is preserved? Or is it a genuinely weaker, local per-component input that the
    bijection proof legitimately consumes?

Q3. Sanity on the MapsTo squeeze: is it actually true with NO hper that for P ∈ TopDimMinPrimes S,
    comap P is top-dimensional in A? The squeeze relies on dim((A⧸p)[1/f̄]) ≤ dim(A⧸p) (always true)
    and dim(S⧸P) = dim((A⧸p)[1/f̄]). Confirm no hidden circularity: dim S = dim A (hdim) is the only
    dimension input there.

Q4. Overall: is `topDimMinPrimes_ncard_away_eq` a faithful statement of "away-localization at f
    preserves the count of top-dimensional minimal primes, under avoidance + componentwise no-drop"?
    Any way the three hypotheses (hdim/havoid/hper) could be jointly UNSATISFIABLE in a nontrivial
    case (making the lemma vacuous in practice)? The two intended call sites: A = a f.g. k-domain
    quotient where A⧸p is a f.g. k-domain and f̄ ≠ 0, so the affine-domain no-drop gives hper.
</task>

<output_contract>
  Four numbered answers Q1..Q4, each ≤ 8 sentences. For Q1 give an EXPLICIT counterexample
  (ring, f, p, the two dimensions) or state clearly that none exists and why. End with a one-line
  verdict: hper is {required-and-honest | derivable-so-redundant | too-strong-circular | other}.
</output_contract>

<grounding_rules>
  Pure mathematics; no Lean execution available to you. State any claim you are INFERRING vs.
  one you are CERTAIN of. If a counterexample requires a specific ring (DVR, polynomial ring,
  product), write it down explicitly with its Krull dimensions. Do not trust my proof sketch
  blindly — if the MapsTo squeeze (Q3) is actually unsound without hper, say so.
</grounding_rules>
