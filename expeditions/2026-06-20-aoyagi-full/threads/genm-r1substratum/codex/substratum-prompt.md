<task>
Setting (exact combinatorics, no floats). Fix a chain of nonnegative integer widths
M = (M_0, M_1, ..., M_L), L >= 2. Define, over the integers:

  minAdm(M_0, M_1)            = M_0 * M_1                                              (L = 1 leaf)
  minAdm(M_0, ..., M_L)       = min_{0 <= t <= min(M_0,M_1)} [ (M_0 - t)(M_1 - t)
                                          + minAdm(t, M_2, ..., M_L) ]                 (L >= 2)

This minAdm(M) is a known geometric codimension: it equals codim of the locus
Sigma^0_M = { tuples of matrices A_0,...,A_{L-1} (A_i has shape d_i x d_{i+1} with d = M)
: A_0 A_1 ... A_{L-1} = 0 } inside the tuple space (the "zero-product locus"), taking the
minimum codimension over irreducible components. A cited identity (peeling): for 0 <= r <= min,
  codim { rank(A_0 ... A_{L-1}) <= r }  =  minAdm(M - r)   (subtract r from EVERY width M_i).

The analytic problem behind this. We want to prove an integral over the tuple space is finite for
every c < minAdm(M)/2, by a DESCENT that peels one boundary at a time. Peeling boundary 0 at a
"cut" t (0 <= t <= min(M_0,M_1)) exposes a FREE block Gamma of shape a x b, a = M_0 - t, b = M_1 - t,
and a "tail product" Q_b = the b non-pivot rows of the product A_1 A_2 ... A_{L-1}. Concretely Q_b is
the product of the tail chain (b, M_2, M_3, ..., M_L); its generic rank is s = min(b, n) where
n = min(M_2, ..., M_L). The inner Gamma-integral of
    ( frobSq(A * Qtil) + frobSq(C * Qtil + Gamma * Q_b) )^{-c}
delivers an exponent shift of exactly (a * rank(Q_b)) / 2, because the map Gamma |-> Gamma * Q_b has
rank a * rank(Q_b) (kernel dimension a * (b - rank Q_b), carrying no decay).

On the GENERIC stratum rank(Q_b) = s = min(b,n) it is an established exact fact (checked on tens of
thousands of chains, tight, permutation-invariant) that summing the per-step charge a*s over the
recursion equals minAdm(M) exactly:
    minAdm(M) = min_t [ (M_0 - t) * min(M_1 - t, n) + minAdm(t, M_2, ..., M_L) ].

THE QUESTION. The tail product Q_b can be RANK-DEFICIENT: rank(Q_b) = s' with s' < s = min(b,n).
This is a positive-codimension sub-locus of the tail variables. On that sub-locus the Gamma-integral
only delivers shift a*s'/2 (SMALLER, hence the leftover deeper exponent c - a*s'/2 is LARGER, i.e.
more singular). The descent must still certify finiteness for all c < minAdm(M)/2 near this sub-locus.

Independently determine: what is the CORRECT total codimension "charge" the descent can account on the
sub-generic stratum { rank(Q_b) = s' }, at cut t, combining
  (i) the active-block decay a*s',
  (ii) the codimension of the stratum { rank(Q_b) = s' } within the tail variables, and
  (iii) whatever the deeper recursion contributes,
being careful about whether (ii) and (iii) are ADDITIVE or ENTANGLED (they share the deeper matrices
A_2,...,A_{L-1}). Then decide: is there a chain M, a cut t, and a sub-generic rank s' < min(b,n) at
which this correct charge is STRICTLY LESS THAN minAdm(M)? Either exhibit such (M, t, s') with the
exact shortfall, or give the accounting that shows the charge is >= minAdm(M) for all (t, s') with
equality on the generic stratum. Work it out from the geometry / the peeling identity; do not assume
the answer.
</task>

<output_contract>
1. Your formula for the correct per-stratum charge charge(t, s'), written explicitly in terms of
   minAdm of reduced chains (use the peeling identity codim{rank<=r} = minAdm(chain - r)). State
   clearly whether the stratum-codimension term and the deeper-recursion term are additive or
   entangled, and WHY.
2. Verdict: does min over (t, s') of charge(t, s') equal minAdm(M) and stay >= minAdm(M)?
   YES (closure) or NO (with an explicit (M, t, s') counterexample and the exact shortfall).
3. If NO: which sub-generic stratum, and what does the shortfall mean for a peel-by-boundary
   descent that uses only the rank-corrected active-block charge?
4. If YES: the one-line mechanism (why higher-rank-deficiency strata are never more binding than the
   generic stratum).
Keep it tight. Mark every step as PROVEN / INFERRED / GUESS.
</output_contract>

<grounding_rules>
- Exact integer arithmetic only; no floating point, no Monte-Carlo. If you check examples, use the
  minAdm recursion above verbatim.
- Distinguish the codimension of a FREE matrix rank-drop (b - s')(n - s') from the codimension of a
  PRODUCT rank-drop (which is minAdm(tail - s') by the peeling identity) — these differ; use the
  correct one.
- You may NOT assume the descent closes; you may NOT assume it fails. Derive it.
- Flag any place where the additive-vs-entangled distinction changes the verdict.
</grounding_rules>
