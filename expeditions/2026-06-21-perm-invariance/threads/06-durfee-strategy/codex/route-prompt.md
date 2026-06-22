<task>
I need the cleanest Lean 4 / Mathlib (v4.29) PROOF STRATEGY for a single classical q-series
identity. I am NOT asking you to write Lean. I want: (a) which proof METHOD is cleanest to
formalize, (b) the lemma ladder for that method, (c) the single hardest formalization step.

THE IDENTITY (over the formal power series ring ℤ⟦X⟧, X plays the role of q):

    P a * P b  =  ∑_{r=0}^{min(a,b)}  X^{(a−r)(b−r)} · P(a−r) · P r · P(b−r)

where  P n := ∏_{k=1}^{n} (1 − X^k)^{−1}  is the inverse q-Pochhammer (P 0 = 1), realized in
the codebase as  P n = ∏_{k=1}^{n} geomFactor k,  geomFactor k = ∑_{j≥0} X^{jk}  (the explicit
geometric series). This is the N=1 case of a "Durfee square" partition identity.

AVAILABLE PRIMITIVES (already proven in the codebase, against which the proof must be built):
  - P (s+1) = P s * geomFactor (s+1)            [peel the top factor]
  - geomFactor k * (1 − X^k) = 1   for k ≥ 1    [telescoping; geomFactor is the inverse of 1−X^k]
  - P 0 = 1
  - ℤ⟦X⟧ is an integral domain (IsDomain), so 1−X^k (constant coeff 1) is a non-zero-divisor:
    multiplicative cancellation by (1−X^k) is available.
  - Mathlib has: PowerSeries.coeff_mul (antidiagonal convolution), PowerSeries.ext (coeff
    extensionality), Finset.prod / sum / sum_bij / prod_Icc_succ_top, Finset.Nat.antidiagonal.
  - Mathlib does NOT have: Durfee square, Gaussian binomials, q-Pochhammer, q-binomial theorem,
    or any q-series identity. (Mathlib's Nat.Partition.genFun is an INFINITE product over a
    topological coefficient ring — a different object from the finite P n here.)

CANDIDATE METHODS (rank them; pick one):
  (A) PARTITION-COMBINATORIAL. coeff n of both sides counts the same finite set of objects via a
      Durfee-square bijection. Would require BUILDING the bijection and a coeff-counting lemma for
      P n (coeff n (P s) = number of partitions of n into parts ≤ s, or into ≤ s parts) from
      scratch — Mathlib's partition generating-function lemmas are for the infinite product only.
  (B) INDUCTION via the peel/telescope primitives. A double induction reducing (a,b) toward a base
      case using (1−X^k) cancellation. (I have separately observed numerically, exact-integer to
      degree ~40, that BOTH sides satisfy the SAME one-step descent (1−X^b)·SIDE(a,b)=SIDE(a,b−1)
      for every a and every b≥1; the LHS descent is immediate from geomFactor telescoping, the RHS
      descent is a telescoping reindex in r. Base case b=0: both sides = P a.)
  (C) q-binomial / generating-function reduction.

<output_contract>
1. RANKING of (A),(B),(C) by formalization cost in Lean4/Mathlib v4.29, with a one-line reason each.
2. For the method you rank #1: the LEMMA LADDER — each rung a precise statement against the
   primitives above (P, geomFactor, P_succ, geomFactor_mul_one_sub, coeff_mul, sum_bij), in order,
   with the induction variable + invariant if any.
3. The SINGLE hardest Lean step in that ladder, and how to de-risk it.
4. If method (B): is proving the RHS one-step descent (1−X^b)·RHS(a,b)=RHS(a,b−1) likely EASIER
   or HARDER in Lean than proving the identity directly by some other route? Name the specific
   Mathlib reindexing/telescoping lemma the RHS-descent proof would lean on.
5. An honest LoC / sub-lemma-count estimate for method #1.
</output_contract>

<grounding_rules>
- Distinguish what Mathlib v4.29 actually provides (name lemmas only if you are confident they
  exist at that pin) from what must be built. If unsure a lemma exists, say "verify".
- Do not assume any q-series library. The only q-series facts available are the four primitives listed.
- Mark inference vs. fact. Prefer the route with the fewest from-scratch combinatorial bijections.
</grounding_rules>
