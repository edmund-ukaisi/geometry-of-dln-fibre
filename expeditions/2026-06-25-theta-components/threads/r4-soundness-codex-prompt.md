<task>
I am adversarially reviewing a Lean4/Mathlib commutative-algebra formalisation. I want a DECORRELATED
mathematical soundness check of two load-bearing lemmas (in standard math, not Lean syntax). Tell me if
either is FALSE, vacuous, or has a hidden hypothesis gap. Be a skeptic; hunt for a counterexample.

CONTEXT: k is a field. All rings are commutative. "fp" = finitely presented; "fg k-algebra" = finitely
generated as a k-algebra. ringKrullDim is Krull dimension. "TopDimMinPrimes A" = the set of minimal primes
p of A with ringKrullDim(A/p) = ringKrullDim(A) (the top-dimensional irreducible components).

LEMMA 1 (the "generic-smoothness domain shortcut"):
  Claim: Let k be ALGEBRAICALLY CLOSED. Let D be a finitely-presented k-algebra that is an INTEGRAL DOMAIN.
  Then D is "smooth at its generic point", i.e. Algebra.IsSmoothAt k (⊥ : Ideal D) holds.
  The proof uses: (a) a Mathlib theorem dense_smoothLocus_of_perfectField — for a REDUCED scheme X with a
  locally-of-finite-presentation morphism X → Spec K, K a PERFECT field, the smooth locus is DENSE in X;
  (b) D a domain ⟹ Spec D reduced and irreducible (nonempty), so the dense smooth locus is nonempty, giving
  SOME prime m with IsSmoothAt k m; (c) a step "a domain fp over k, smooth at some prime m, is smooth at ⊥"
  (smooth locus is open + nonempty; ⊥ is the generic point of the irreducible Spec D, which is in the
  closure of / specialised to by any nonempty open). Alg-closed ⟹ perfect supplies the PerfectField K=k.
  QUESTIONS: Is this genuinely TRUE? Is "fp domain over alg-closed k ⟹ IsSmoothAt k ⊥" sound? Is any
  hypothesis (alg-closed/perfect, reduced, domain, fp) silently doing nothing or silently REQUIRED but
  potentially absent? Could it be VACUOUS (e.g. is IsSmoothAt k ⊥ a trivial/empty statement for a domain)?
  Is there a subtlety with ⊥ being the generic point vs the smooth-locus-nonempty argument? Char-0 is NOT
  assumed for this lemma — only alg-closed. Is that enough (perfect)?

LEMMA 2 (the "per-prime no-drop" that powers a top-dim-component COUNT being preserved under localization):
  Setup: A is a NOETHERIAN fg k-algebra. f : A. We invert f: S = Localization.Away f (= A[1/f]). We want
  (TopDimMinPrimes S).ncard = (TopDimMinPrimes A).ncard, via a bijection comap : TopDimMinPrimes S →
  TopDimMinPrimes A. Two inputs are supplied:
    (i) GLOBAL no-drop: ringKrullDim S = ringKrullDim A;
    (ii) AVOIDANCE: every p ∈ TopDimMinPrimes A has f ∉ p.
  The SURJECTIVITY of the bijection (mapping p ↦ map(p) = p·S) requires showing map(p) ∈ TopDimMinPrimes S,
  i.e. ringKrullDim(S / map(p)) = ringKrullDim(S). The key sub-lemma used PER PRIME p is:
    KEY: "for a fg k-algebra DOMAIN A/p and g = image of f, with g ≠ 0,
          ringKrullDim((A/p)[1/g]) = ringKrullDim(A/p)."
  proved via: dim = trdeg_k for fg affine domains (Noether normalization), and trdeg is invariant under
  localization because (A/p) and (A/p)[1/g] share the fraction field Frac(A/p) (both algebraic over A/p).
  QUESTIONS: (1) Is the KEY sub-lemma TRUE: localizing a fg k-DOMAIN at a single nonzero element NEVER drops
  Krull dimension? (Recall a DVR localized at its uniformizer drops dim 1→0 — does the "fg k-algebra"
  hypothesis genuinely exclude that, i.e. is a DVR ever a fg k-algebra? Why/why not.) (2) Is the per-prime
  no-drop GENUINELY NECESSARY, or does it fold out of the global no-drop (i) + avoidance (ii)? I.e. produce a
  ring A and element f where global-no-drop + avoidance both HOLD but SOME top component A/p DROPS dimension
  on localization at f̄ (so the count would be WRONG without the per-prime input). (3) Is "dim = trdeg for fg
  affine domains over a field" unconditionally true (any char, no perfectness)? Is the localization-trdeg
  invariance argument sound?
</task>

<output_contract>
  Two sections, "LEMMA 1" and "LEMMA 2". For each: a one-word verdict (TRUE / FALSE / VACUOUS /
  HIDDEN-GAP), then ≤8 sentences of justification. For LEMMA 2 question (2), either give a concrete
  counterexample (A, f, the dropping component) or state clearly that the per-prime input is genuinely
  load-bearing and why global+avoidance is insufficient. End with a one-line "HIGHEST-RISK" pointing at
  whichever of the two is likeliest to hide an error, or "none found".
</output_contract>

<grounding_rules>
  Standard commutative algebra / Mathlib facts you may assert. Where you INFER vs KNOW, say so. If a claim
  depends on a Mathlib lemma's exact hypotheses that you cannot verify, flag it as "depends on Mathlib
  statement of X". Do not assume char 0 unless I stated it.
</grounding_rules>
