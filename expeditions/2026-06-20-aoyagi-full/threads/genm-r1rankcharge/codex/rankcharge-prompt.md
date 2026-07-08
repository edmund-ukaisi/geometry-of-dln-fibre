<task>
Adjudicate a combinatorial identity that gates a resolution-of-singularities descent for deep
linear networks. I need an INDEPENDENT verdict (prove, refute, or "undetermined + why"), not a
rubber stamp. Attack it from scratch.
</task>

<context>
Fix a "width chain" M = (M_0, M_1, ..., M_L), a tuple of natural numbers (L >= 1). Two integer
quantities are defined on chains.

(1) minAdm(M) -- the target codimension. It satisfies the exact layer-peeling recursion
    (this is a THEOREM, take it as given):
      L = 1 (two widths):        minAdm(M_0, M_1) = M_0 * M_1
      L >= 2 (>= 3 widths):      minAdm(M) = min over t in {0,...,min(M_0,M_1)} of
                                     [ (M_0 - t)*(M_1 - t) + minAdm(t, M_2, ..., M_L) ].
    The reduced chain (t, M_2, ..., M_L) has one fewer layer (its leading width is the pivot t).
    Equivalently minAdm(M) = min over an admissible cone of exponent vectors T of a quadratic form
    Mval(M,T); the recursion above is proven equal to that brute-force minimum.

(2) A "rank-corrected charge". At a peel of the leading boundary of a chain N=(N_0,N_1,...,N_k) at
    pivot t (0 <= t <= min(N_0,N_1)), define
        a = N_0 - t,   b = N_1 - t,   n = min(N_2, ..., N_k)  (the tail bottleneck; only for k>=2),
        s = min(b, n).
    The charge for that peel is  a * s   (NOT a * b).
    [Origin, for grounding only: s is the generic rank of the "b non-pivot rows of the tail
     matrix-product A_1 * A_2 * ... * A_{k-1}", whose generic rank is min(N_1,...,N_k); restricted
     to b <= N_1 rows this is min(b, min(N_2,...,N_k)) = min(b,n). The analytic per-peel step can
     only deliver an exponent shift of (a*s)/2, not (a*b)/2, because the map Gamma |-> Gamma * Q_b
     (Gamma an a x b block) has a kernel of dimension a*(b-s) that carries no decay.]

Define the rank-corrected recursion:
      L = 1:      minAdmRank(N_0, N_1) = N_0 * N_1
      L >= 2:     minAdmRank(M) = min over t in {0,...,min(M_0,M_1)} of
                     [ (M_0 - t)*min(M_1 - t, min(M_2,...,M_L)) + minAdmRank(t, M_2,...,M_L) ].
    (Same recursion as minAdm but with the block charge (M_0-t)(M_1-t) replaced by
     (M_0-t)*min(M_1-t, min(M_2,...,M_L)).)
</context>

<question>
Q1. Is minAdmRank(M) = minAdm(M) for ALL chains M? Prove it, or exhibit a chain where they differ.
    Note that trivially minAdmRank(M) <= minAdm(M) since min(M_1-t, n) <= M_1-t termwise; the
    content is whether the smaller per-step charge can ever make the recursive minimum STRICTLY
    smaller.

Q2. Equivalently: is the following per-cut inequality true for every chain M (L>=2) and every legal
    cut t in {0,...,min(M_0,M_1)}?
       (M_0 - t)*min(M_1 - t, min(M_2,...,M_L)) + minAdm(t, M_2,...,M_L)  >=  minAdm(M).
    (The "cap-inactive" cuts, where M_1 - t <= min(M_2,...,M_L), are immediate from the recursion
     for minAdm. The content is the "cap-active" cuts where M_1 - t > min(M_2,...,M_L).)

Q3. Any useful structural facts you can establish and are willing to certify: is minAdm permutation-
    invariant in the widths (M_0,...,M_L)? Is w |-> minAdm(w, W) monotone / Lipschitz in the leading
    width w (for fixed tail W)? These may or may not be the mechanism -- your call.
</question>

<output_contract>
- A verdict on Q1 (TRUE / FALSE / UNDETERMINED) with justification. If FALSE, give the smallest
  explicit counterexample chain M with both values. If TRUE, give the proof (a clean argument, or a
  reduction to a named sub-lemma you can defend).
- A verdict on Q2, and whether the cap-active case needs a genuinely new argument beyond the minAdm
  recursion.
- Whatever you can establish for Q3, marked as PROVED / STRONG-EVIDENCE / CONJECTURE.
- Keep FACT separate from INFERENCE. State any assumption you rely on.
</output_contract>

<grounding_rules>
- These are exact integer objects. No floating point, no approximation. Small cases are decidable by
  direct computation; you may reason by hand on them but state which you actually checked.
- Do not assume the two recursions are equal because they "should be"; that is exactly the question.
- If you find the identity holds only under a scope condition (e.g. weakly-monotone chains), NAME the
  scope precisely.
</grounding_rules>
