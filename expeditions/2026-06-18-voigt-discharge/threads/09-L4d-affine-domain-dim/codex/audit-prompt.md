<task>
I am an independent FIDELITY reviewer auditing a Lean 4 + Mathlib formalisation. I am NOT
re-proving it (the build is green, zero sorry, axiom-clean). I want a decorrelated mathematical
opinion on whether the headline Lean STATEMENT faithfully captures the informal claim, and whether
any HYPOTHESIS is too strong (spurious) or too weak (missing, so the statement is false/vacuous).

Informal claim being formalised:
"An irreducible affine variety over a field k is EQUIDIMENSIONAL: for the coordinate ring
A = R/I (R = k[x_1..x_n] = MvPolynomial (Fin n) k, I a prime ideal, so A is a domain) and any prime
p of A, we have  height(p) + dim(A/p) = dim(A)  (Krull dimensions, with the arithmetic in WithBot ℕ∞,
honest addition — no truncated subtraction)."

The four Lean headline statements (signatures verbatim):

(1) Headline — affine_domain_height_add_ringKrullDim_quotient_eq
  (k : Type*) [Field k] (n : ℕ) (I : Ideal (MvPolynomial (Fin n) k)) [I.IsPrime]
  (p : Ideal ((MvPolynomial (Fin n) k) ⧸ I)) [p.IsPrime] :
  (p.height : WithBot ℕ∞) + ringKrullDim (((MvPolynomial (Fin n) k) ⧸ I) ⧸ p)
    = ringKrullDim ((MvPolynomial (Fin n) k) ⧸ I)

(2) Supporting brick — height_under_eq_of_isIntegral
  {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [IsDomain R] [IsDomain S]
  [IsIntegrallyClosed R] [IsNoetherianRing R] [Algebra.IsIntegral R S]
  (hinj : Function.Injective (algebraMap R S)) (P : Ideal S) [P.IsPrime] :
  P.height = (P.under R).height
  -- under R = contraction (comap of algebraMap R S). Proof: ≤ via going-up (comap strictly
  -- monotone for integral extensions); ≥ via going-down (Mathlib HasGoingDown instance for
  -- integral extensions of an integrally closed domain, stacks 00H8).

(3) Corollary — height_eq_ringKrullDim_of_isMaximal
  (k) [Field k] (n) (I) [I.IsPrime] (m : Ideal (A)) [m.IsMaximal] :
  (m.height : WithBot ℕ∞) = ringKrullDim A      -- A = (MvPolynomial (Fin n) k) ⧸ I
  -- proof: A/m is a field (dim 0), so headline (1) collapses.

(4) Corollary — ringKrullDim_localizationAtPrime_isMaximal_eq
  (k) [Field k] (n) (I) [I.IsPrime] (m : Ideal A) [m.IsMaximal] :
  ringKrullDim (Localization.AtPrime m) = ringKrullDim A
  -- via IsLocalization.AtPrime.ringKrullDim_eq_height m (Localization.AtPrime m) then (3).

Proof route of (1): Noether-normalize A to an integral injective k-algebra map
g : B = MvPolynomial (Fin s) k ↪ A; contract p to q = p.comap g; brick (2) gives height_A p =
height_B q (B is a polynomial ring over a field, a UFD hence integrally closed Noetherian domain);
the induced quotient map B/q ↪ A/p is integral injective so dim(A/p)=dim(B/q); dim A = dim B = s;
then the (already-proved, reused) polynomial-ring identity height_B q + dim(B/q) = s assembles it.
</task>

<output_contract>
Four short sections, each ≤ 6 lines:
A. FIDELITY of headline (1): does it state "affine domain is equidimensional"? Any way the WithBot ℕ∞
   equality could be vacuously true or mis-typed (e.g. both sides ⊤, or height meaning something other
   than codim of the prime)? Is "I prime / A a domain" genuinely needed for the equality, or is it
   true more generally (and thus the hypothesis arguably too strong)?
B. HYPOTHESES of brick (2): are [IsDomain R],[IsDomain S],[IsIntegrallyClosed R],[IsNoetherianRing R],
   [Algebra.IsIntegral R S], injectivity each necessary? Any one removable (spurious)? Any MISSING
   hypothesis without which P.height = (P.under R).height is FALSE (give a counterexample if so)?
C. CORROLLARIES (3),(4): do the names match content? Is using [m.IsMaximal] (rather than deriving
   maximality from finite-type-over-field via Nullstellensatz) an honest scoping or a hidden gap?
   Is "height m = dim A" actually equidimensionality-at-closed-points, true for ALL maximal m here?
D. VERDICT: one line — does the headline faithfully formalise "affine domains are equidimensional",
   and is any hypothesis too strong or too weak? Flag NAME-vs-CONTENT overclaim if any.
</output_contract>

<grounding_rules>
This is a mathematical-fidelity question; reason from commutative-algebra facts (Noether
normalization, going-up/going-down, catenary/equidimensional theory for affine domains over a field,
Krull dimension in WithBot ℕ∞). Clearly mark any claim that is an INFERENCE about Mathlib's
definitions (e.g. what Ideal.height or ringKrullDim mean) vs a standard mathematical FACT. If you
cannot tell whether a Lean def matches the math meaning, say so rather than assert. A counterexample
beats a vibe.
</grounding_rules>
