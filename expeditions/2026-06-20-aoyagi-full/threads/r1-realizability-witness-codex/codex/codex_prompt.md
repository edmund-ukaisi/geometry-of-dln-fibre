<task>
I am verifying a proposed equality of two combinatorial functions in a Lean formalisation of a paper on
deep-linear-network multiplication-map fibres (type-A quiver rank patterns). I need an INDEPENDENT
adjudication. Do NOT defer to any prior analysis; derive from the definitions below. Use exact integer
arithmetic; if you write code, make it exact (no floating-point ranks).

SETUP (all over a field k; widths are naturals).
A "dimension vector" is M : indices 0..L (so L+1 widths M_0,...,M_L) and an "exponent vector" T : 0..L-1
(L values T_0,...,T_{L-1}).

The DIAGONAL CASCADE tuple assigns to layer s the rectangular partial-identity block
  A_s = partialId(M_{s+1}, M_s, T_s)  : an (M_{s+1} x M_s) matrix whose entry (a,b) is 1 iff a=b and a<T_s, else 0.
For i <= j the interval sub-product is the LEFT-multiplied product
  submult(i,j) = A_{j-1} * A_{j-2} * ... * A_i      (an M_j x M_i matrix; the empty product at i=j is the identity).
The "rank pattern" of the cascade is  rankFn(i,j) = rank(submult(i,j))  for i<j, = M_i for i=j, = 0 for i>j.

ADMISSIBILITY. Define admBound(0) = min(M_0, M_1), and admBound(s) = M_{s+1} for s>=1.
T is admissible iff:
  (i)  T_s <= admBound(s) for every s;
  (ii) T is weakly decreasing: s <= s' implies T_{s'} <= T_s;
  (iii) T_{L-1} = 0.

CANDIDATE TARGET FUNCTION ("achieverRankPattern"). Define the running-rank vector
  t_0 = M_0,  t_{s+1} = T_s   (so t : indices 0..L).
Define  P(i,j) = t_j  if i<j ;  = M_i if i=j ;  = 0 if i>j.   (NB: for i<j this depends ONLY on the right
endpoint j — it is constant down each column, and is NOT explicitly capped by min(M_i,M_j).)
</task>

<output_contract>
Answer these four questions, each with an explicit verdict and, where a claim is universal or an
existence, an exact certificate (a proof sketch over the integers, or an exact-arithmetic computation):

Q1. Is the equality  rankFn(i,j) = P(i,j)  for the cascade TRUE for all admissible T? If true, prove it
    (give the chain of facts). If false, give an explicit admissible (M,T) and the cell (i,j) where they differ.

Q2. The matrix-side rank of submult(i,j) for the cascade equals  min( w(i,j), min(M_i, M_j) )  where
    w(i,j) = min_{i<=p<j} T_p  is the window-minimum of T over the half-open window. Confirm or refute this
    rank formula (independently — it is the "count-the-1s" claim for a product of partial-identities).
    For i<j, when (if ever) does min(w(i,j), min(M_i,M_j)) differ from the column-constant value t_j? Identify
    the precise hypotheses on (M,T) under which they coincide.

Q3. Which of the three admissibility clauses (i),(ii),(iii) are actually NEEDED for the equality in Q1?
    Determine the minimal subset. In particular: is clause (iii) (last entry zero) needed? Is clause (i)
    alone enough? Is clause (ii) alone enough?

Q4. Is the proposed P "the genuine rank pattern of a generic/optimal admissible representation", or is it
    merely a convenient column-constant formula that happens to agree on admissible T? Concretely: exhibit
    a NON-admissible T where rankFn(cascade) != P, to show the equality has content (is not a definitional
    identity). State at which cell and why P overshoots/undershoots.
</output_contract>

<grounding_rules>
- Treat the definitions above as ground truth; do not import outside conventions.
- partialId is a rectangular diagonal of ones truncated at T_s and at min(rows,cols).
- The product is LEFT-multiplied: submult(i,j) = A_{j-1} ... A_i. Mind the orientation when composing.
- A product of rectangular partial-identities is again a rectangular partial-identity whose rank is the
  window-minimum of the truncation counts, capped by the endpoint dimensions — verify this yourself.
- Distinguish FACT (proved/computed) from INFERENCE (heuristic) explicitly in your answer.
- If you compute, use exact integer/rational arithmetic only.
</grounding_rules>
