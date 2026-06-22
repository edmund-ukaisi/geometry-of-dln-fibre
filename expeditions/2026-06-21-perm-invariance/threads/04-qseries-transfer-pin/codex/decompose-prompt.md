<task>
I have a q-series identity that is EXACT-VERIFIED (checked to high power-series precision over many
parameter choices). I need an INDEPENDENT derivation of it from named elementary q-series primitives —
the cleanest single chain of small classical identities that proves it. Treat the verification as
given; I want the proof structure, with each classical input named precisely.

Notation. For a non-negative integer s, define the inverse q-Pochhammer
    P_s = prod_{k=1}^{s} 1/(1 - q^k)      (P_0 = 1),
a formal power series in q. (Equivalently P_s = sum over partitions with at most s parts of q^{|mu|}.)

THE IDENTITY ("local transfer"). Fix integers b_0,...,b_{N-1} >= 0 and d >= 0. Set b_N := 0. Then

    P_d * prod_{i=0}^{N-1} P_{b_i}
      = sum_{x} q^{Delta_b(x)} * P_{x_N} * prod_{i=0}^{N-1} ( P_{b_i - x_i} * P_{x_i} ),

where the sum is over integer tuples x = (x_0,...,x_{N-1}, x_N) with
    0 <= x_i <= b_i  (for i < N),   x_N >= 0,   sum_{i=0}^{N} x_i = d,
and the exponent is
    Delta_b(x) = sum_{0 <= a < u <= N} (b_a - x_a) x_u.
</task>

<output_contract>
1. State the minimal list of CLASSICAL q-series identities the proof needs, each as its own named
   lemma with its precise statement (Gaussian-binomial / Pochhammer form where relevant). For each,
   say whether it is strictly necessary or avoidable.
2. Give the proof as an explicit chain of small steps: how the named primitives COMPOSE to yield the
   transfer identity. If it is an induction, state the induction variable, the base case, and the
   exact inductive step (what identity closes it).
3. Show the bookkeeping of the exponent Delta_b(x): how Delta decomposes step-by-step to match
   whatever recursion/composition you use. Be explicit and exact.
4. Flag the single step most likely to be subtle or to fail, and how you'd guard it.
Distinguish ESTABLISHED FACT from YOUR INFERENCE throughout.
</output_contract>

<grounding_rules>
Facts about what I have already established (use these; do not re-derive):
- The endpoint identity is verified exactly (integer power-series arithmetic, b up to ~6, d up to ~10,
  N up to ~5, including non-monotone and wide b, zero mismatch). Treat it as TRUE.
- The N=1 case (single block, b = (b_0), so b_1 = 0): the identity reads
      P_d * P_{b_0} = sum_{x_0=0}^{min(d,b_0)} q^{(b_0-x_0)(d-x_0)} P_{d-x_0} P_{x_0} P_{b_0-x_0}.
  I have verified this is the standard "N=1 Durfee" identity P_a P_b = sum_r q^{(a-r)(b-r)} P_{a-r}P_r P_{b-r}
  with a=d, b=b_0, r=x_0. Treat this single-block identity as an available primitive.
- The exponent in "running-residual" form: Delta_b(x) = sum_{u=1}^{N} R_u x_u with
  R_u = sum_{a<u}(b_a - x_a). (Verified.)

Do NOT assume any particular decomposition is the intended one — derive it yourself. In particular do
not assume q-Vandermonde / q-Chu-Vandermonde is required; decide whether it is needed or not as part
of your derivation, and justify. I want your independent read of WHICH primitives are load-bearing.
Be concrete and exact; this is destined for a Lean 4 formalisation, so a minimal primitive set matters.
</grounding_rules>
