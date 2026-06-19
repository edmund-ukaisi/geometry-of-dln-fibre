<task>
I am sizing a Lean 4 / Mathlib formalisation gap. Target: prove, for R = MvPolynomial (Fin n) k
with [Field k] (algebraically closed available if needed), and a prime ideal p ⊆ R, the
height–dimension formula

    Ideal.height p + ringKrullDim (R ⧸ p) = ringKrullDim R    (= n).

Equivalently the geometric form: a smooth k-point of V(I) ⊆ A^n with Zariski tangent dim t has
I.height = n − t. This is the "dimension formula / catenary" content for affine k-algebras.

Mathlib pin: lean4 v4.29.0, Mathlib commit 8a17838 (2026-03-30). Assume current Mathlib.

QUESTION 1 (route): What is the SHORTEST proof route to that formula in current Mathlib?
Compare two classical routes and pick the cheaper one IN LEAN given what Mathlib actually has:
  (a) transcendence degree + Noether normalization: R/p is finite (integral) over a polynomial
      subring A = k[x_1..x_s] with s = trdeg; dim(R/p) = dim A = s; height p = n − s.
  (b) catenary / Cohen–Macaulayness of polynomial rings: every maximal chain of primes has the
      same length; height p + coheight p = dim R for each prime.

QUESTION 2 (inventory): For your chosen route, what is ALREADY in Mathlib vs what must be built?
Be concrete about declaration names / theorems where you can. In particular address:
  - Krull dimension of k[x_1..x_n] (= n)?
  - Noether normalization (existence of the finite/integral polynomial subring)?
  - Does dim equality transfer along integral / finite extensions? (going-up / going-down → equal
    Krull dimension; "dim R = dim S for S integral over R").
  - Going-down for integral extensions of normal/integrally-closed domains?
  - The additivity height p + dim(R/p) = dim R, or any "height of P over p = height p + relative
    height" lemma?
  - Is there any catenary / IsCatenary infrastructure at all?
  - Anything relating ringKrullDim to transcendence degree (trdeg / AlgebraicIndependent)?

QUESTION 3 (size): Give a size verdict — is this a single Lean module (a handful of lemmas resting
on existing bricks), a few modules, or a genuine sub-library that must build transcendence-degree
dimension theory and/or catenary-ness from scratch? Name the 1–2 HARDEST lemmas in the dependency
ladder and roughly estimate effort.
</task>

<output_contract>
Four sections in this order:
  ## Route — which of (a)/(b), and why it is cheaper in Lean
  ## Inventory — present vs absent (concrete decl names where possible), bulleted
  ## Sub-ladder — the lemmas to prove, in dependency order, each one line
  ## Size verdict — module / few-modules / sub-library, + the 1–2 hardest lemmas + effort read
Be terse and concrete. Prefer naming a Mathlib declaration over describing it.
</output_contract>

<grounding_rules>
Distinguish what you KNOW is in Mathlib from what you INFER should be there — mark inferences
explicitly ("inferred, verify"). Do not invent declaration names; if unsure of a name, describe the
result and say the name is uncertain. If a classical theorem is standard but you are unsure of its
Lean status, say so rather than assert.
</grounding_rules>
