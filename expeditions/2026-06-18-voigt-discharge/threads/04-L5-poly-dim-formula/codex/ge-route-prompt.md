<task>
I am formalising in Lean 4 + Mathlib (pinned v4.29.0) the polynomial-ring
dimension formula. Let `k` be a FIELD (NOT necessarily algebraically closed),
`R = MvPolynomial (Fin n) k`, and `p` a prime ideal of `R`. I want:

  HEADLINE (L5.7):  Ideal.height p + ringKrullDim (R ⧸ p) = n
  (equivalently  height p = n − dim(R/p)).

ALREADY PROVED in my file (sorry-free, axiom-clean), call these freely:
- L5.0:  ringKrullDim (MvPolynomial (Fin m) k) = m   [any field k]
- L5.1:  ringKrullDim (R ⧸ p) = (Order.coheight p : WithBot ℕ∞)   [any CommRing, p prime]
- L5.4:  ringKrullDim S = ringKrullDim A   for an integral INJECTIVE ring hom f : A →+* S
         (`ringKrullDim_eq_of_integral_injective`), via going-up chain lift.
- L5.5 (I can prove cheaply via L5.4 + Noether normalization
         `exists_integral_inj_algHom_of_quotient`): ringKrullDim (R ⧸ p) = s,
         where s ≤ n is the Noether-normalization rank: there is an injective
         integral k-algebra map  g : MvPolynomial (Fin s) k →ₐ[k] (R ⧸ p).

MATHLIB BRICKS I HAVE CONFIRMED EXIST at this pin (exact names):
- `Order.krullDim_eq_iSup_height_add_coheight_of_nonempty :
     krullDim α = ↑(⨆ a, height a + coheight a)`   (order level)
- `Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown`  [@stacks 00ON]:
     for `[IsNoetherianRing S] [Algebra.HasGoingDown R S] (p : Ideal R) [p.IsPrime]
     (P : Ideal S) [P.IsPrime] [P.LiesOver p]`,
       `P.height = p.height + (P.map (Quotient.mk (p.map (algebraMap R S)))).height`.
- `Polynomial.height_eq_height_add_one`:  for `[IsNoetherianRing R]`, p prime of R,
     P MAXIMAL of R[X] with P.LiesOver p:  `P.height = p.height + 1`.  (P must be MAXIMAL.)
- Going-down INSTANCE fires:
     `[IsDomain S] [FaithfulSMul A S] [Algebra.IsIntegral A S] [IsIntegrallyClosed A]
       ⊢ Algebra.HasGoingDown A S`.  And `IsIntegrallyClosed (MvPolynomial (Fin s) k)`
     fires (UFM ⇒ integrally closed).
- Noether normalization `exists_integral_inj_algHom_of_quotient` (rank s ≤ n).
- I have the going-up chain lift machinery from L5.4 (lying-over
  `Ideal.exists_ideal_over_prime_of_isIntegral`).

CONFIRMED ABSENT at this pin (grep = 0): `IsCatenary`, `IsEquidimensional`,
`ringKrullDim = trdeg`, any `height p + coheight p = krullDim` for a FIXED prime,
any `MvPolynomial` per-prime height formula. So the headline must be BUILT.

The `≤` direction (height p + coheight p ≤ n) is easy: from
`krullDim_eq_iSup_height_add_coheight_of_nonempty` + `le_iSup` + L5.1, since
krullDim R = n. That gives  height p + dim(R/p) ≤ n.

THE HARD HALF is the `≥` direction (the catenary content):
   height p ≥ n − s,  where s = dim(R/p) = coheight p.
Equivalently I need to exhibit (or prove the existence of) a strictly
ascending chain of primes of length ≥ n − s ending at p (a chain BELOW p),
OR otherwise prove height p ≥ n − s.

My concern: the obvious induction "peel one variable via the one-variable
going-down extension k[x₁..x_{m-1}] ↪ k[x₁..x_m]" — the additivity lemma
`height_eq_height_add_of_liesOver_of_hasGoingDown` applies with base k[x₁..x_{m-1}]
and top k[x₁..x_m] (integral? NO — the polynomial extension is NOT integral, so
HasGoingDown via the integral-extension instance does NOT apply; it applies via
FLAT instead: `Algebra.HasGoingDown.of_flat`, and a polynomial ring IS flat /
free over the subring). And `Polynomial.height_eq_height_add_one` needs P MAXIMAL.

QUESTIONS — give me the cleanest Lean-buildable route for the `≥` direction:

1. What is the cleanest route to `height p ≥ n − dim(R/p)` from THESE bricks?
   Specifically: is the right move to use the FLAT going-down on the polynomial
   tower (k[x₁..x_{m-1}] ↪ k[x₁..x_m] is free hence flat ⇒ HasGoingDown via
   `of_flat`) and the additivity lemma `height_eq_height_add_of_liesOver_of_hasGoingDown`?
   If so, lay out the exact induction (on n) and what `LiesOver` / which primes
   are fed in at each step. Be concrete about which ring is base/top.

2. ALTERNATIVELY: is there a route via the NORMALIZATION extension
   A = k[y₁..y_s] ↪ B = R/p (integral injective, B domain, A integrally closed
   ⇒ HasGoingDown), combined with going-DOWN to build a chain in B from a maximal
   chain in A, then a chain in R below p? Sketch how `height p` (in R) connects
   to chains in R/p or B. (My worry: height p lives in R, B = R/p is a quotient,
   so chains in B are chains ABOVE p, giving coheight not height.)

3. Is there a slicker route I'm missing — e.g. via Krull's height theorem
   (`Ideal.height_le_spanFinrank` gives height ≤ #gens, the WRONG direction) or
   via the localization R_p and a dimension count? Rank routes 1/2/this by
   Lean-buildability with the listed bricks (fewest new sub-lemmas, no new cited
   interface, k a general field).

4. If the `≥` direction genuinely needs a sub-lemma not derivable from the listed
   bricks (e.g. a real catenary induction that itself needs an absent lemma),
   NAME the precise missing lemma and its statement. I would rather report a
   precise gap than force it.
</task>

<output_contract>
1. A ranked verdict on routes 1, 2, 3 (and any 4th you see) by Lean-buildability
   from the listed bricks — most-buildable first.
2. For the TOP route: a concrete step-by-step proof skeleton of the `≥` direction
   (induction variable, base case, the exact additivity/going-down lemma
   invocation, which prime LiesOver which, how the chain length accumulates to
   n − s). Name Mathlib lemmas where you rely on them.
3. An explicit list of any NEW sub-lemmas the top route needs that are NOT in my
   "ALREADY PROVED" / "BRICKS" lists, each with a one-line statement and a flag
   "buildable from bricks" vs "needs absent machinery".
4. If you conclude the `≥` direction is NOT buildable from these bricks without
   new absent machinery, say so plainly and name the single biggest missing lemma.
</output_contract>

<grounding_rules>
- Only claim a Mathlib lemma exists if you are confident at the v4.29 pin; if you
  are inferring a name, FLAG it as "inferred name, verify". I will verify every
  name with grep before building.
- Distinguish "mathematically standard" (the catenary argument is textbook) from
  "the specific Lean bricks close it" — I care about the second.
- Be concrete about base-vs-top ring orientation in every extension you invoke;
  this is where the argument most easily goes wrong.
</grounding_rules>
