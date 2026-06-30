<task>
I am reviewing a Lean 4 / Mathlib commutative-algebra lemma about how the COUNT of
top-dimensional minimal primes behaves under localizing at a single element ("away
localization"). I want a decorrelated mathematical sanity check on whether one
hypothesis is genuinely necessary in PER-PRIME form, or whether it could be silently
folded out of a weaker global hypothesis (which would make the lemma over-strong if
someone "simplified" it that way).

Definitions (pure commutative algebra; A a commutative ring):
- minimalPrimes A = minimal primes of A.
- TopDimMinPrimes A := { p ∈ minimalPrimes A | ringKrullDim (A ⧸ p) = ringKrullDim A }
  i.e. the minimal primes whose quotient realises the full Krull dimension of A
  (the top-dimensional irreducible components of Spec A).
- S = Localization.Away f for some f : A (invert the powers of a single element f),
  with the canonical algebra map φ : A → S.

The lemma (`topDimMinPrimes_ncard_away_eq`) concludes
    (TopDimMinPrimes S).ncard = (TopDimMinPrimes A).ncard
from THREE hypotheses:
  (hdim)   ringKrullDim S = ringKrullDim A                          -- GLOBAL no-drop
  (havoid) ∀ p ∈ TopDimMinPrimes A, f ∉ p                            -- avoidance
  (hper)   ∀ p ∈ TopDimMinPrimes A,
             ringKrullDim (Localization.Away (Ideal.Quotient.mk p f))
               = ringKrullDim (A ⧸ p)                                -- PER-PRIME no-drop

So hper says: for EACH surviving top component p, localizing its domain (A ⧸ p) at the
image f̄ = (mk p f) of f does not drop that component's dimension.

The proof uses hper in exactly one direction: to show that for p ∈ TopDimMinPrimes A
(with f ∉ p), the extension (map φ p) is again top-dimensional in S, via the iso
S ⧸ (map φ p) ≅ Localization.Away (mk p f) over A ⧸ p.

The CLAIM I am auditing: hper is genuinely necessary in this per-prime form and is NOT
derivable from (hdim ∧ havoid). The asserted reason is the "DVR at a uniformizer"
phenomenon: a domain localised at a non-unit can drop Krull dimension, and a global
no-drop on the total ring + avoidance of the top primes does not control the per-
component dimension drop.

Questions:
1. Is hper genuinely independent of (hdim ∧ havoid)? Give a concrete counterexample to
   the implication (hdim ∧ havoid ⟹ hper): a ring A, an element f, where the global
   no-drop holds, f avoids the top-dimensional minimal primes, yet for some top prime p
   the per-prime localization (A⧸p)[1/f̄] DROPS dimension. The DVR-at-uniformizer story
   should be made precise (note a DVR itself is local with a unique top prime ⊥, where
   ⊥-quotient = A and f̄ = f; so the "drop" there is at p = ⊥ — does that already
   witness it, and does havoid even permit f to be a uniformizer? Check carefully).
2. Conversely, are hdim and hper jointly non-redundant, or does hper (per-prime) +
   havoid already imply hdim? I.e. is hdim actually needed as a separate input, or is
   it derivable? (Care: TopDimMinPrimes A could be empty, or ringKrullDim could be ⊥/⊤.)
3. Is the stated SHAPE of hper correct and minimal for the one use (proving map φ p is
   top-dimensional in S)? Is requiring it for ALL p ∈ TopDimMinPrimes A (rather than
   just f-avoiding ones, or just the ones that survive) the right quantification, or is
   it slightly too strong / too weak?
4. Any edge cases where the lemma's CONCLUSION could fail even WITH all three
   hypotheses (e.g. ringKrullDim ∈ {⊥, ⊤}, A not Noetherian, infinitely many minimal
   primes so ncard could be 0 by infiniteness)? Flag whether ncard-of-an-infinite-set
   = 0 conventions create a vacuous-truth trap.
</task>

<output_contract>
Four numbered sections matching the four questions. For Q1 give a fully explicit
counterexample (name the ring, f, the top prime p, and the two dimensions that differ),
or state clearly if you believe the implication actually HOLDS (and prove it). Be
concise; no Lean code needed — pure math. End with a one-line verdict:
"per-prime hper necessary: YES/NO" and "hdim separately necessary: YES/NO".
</output_contract>

<grounding_rules>
This is pure mathematics, so claims should be provable, not empirical. Where you are
uncertain (e.g. about Mathlib's exact ncard/krullDim conventions on edge cases), flag
it explicitly as "convention-dependent" rather than asserting. Distinguish a genuine
mathematical counterexample from a Lean-encoding artefact.
</grounding_rules>
