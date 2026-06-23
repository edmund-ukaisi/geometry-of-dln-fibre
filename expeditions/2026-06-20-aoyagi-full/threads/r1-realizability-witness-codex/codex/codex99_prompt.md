<task>
I am adjudicating, by exact integer arithmetic, whether a combinatorial decomposition in a Lean
formalisation has a specific class of bug. Derive independently from the definitions; do not import
outside conventions. If you compute, use exact integers (no floating point).

CONTEXT. For a "dimension vector" M = (M_0,...,M_L) (widths, naturals) we study tuples of composable
matrices A_s : (M_{s+1} x M_s). The "rank pattern" of a tuple is r(i,j) = rank(A_{j-1}...A_i) for i<j,
r(i,i)=M_i. A key earlier finding (established): the rank of a product of rectangular partial-identity
blocks with truncation counts T_p over a window [i,j) is
    r(i,j) = min( min_{i<=p<j} T_p ,  min_{i<=s<=j} M_s )   -- window-min of T, capped by ALL widths in [i,j].
A NAIVE "endpoint-only cap" min( window-min T, min(M_i, M_j) ) is WRONG when an intermediate width
M_s (i<s<j) is smaller — the "intermediate-width pinch".

THE CODIM OBJECT. There is a closed-form codimension
    Mval(M,T) = sum_{j=0}^{L-1} (tPrev_j - T_j) * (M_{j+1} - T_j),   tPrev_0 = M_0, tPrev_j = T_{j-1}.
This is the codimension of the admissible stratum with exponent vector T. "Admissible" means:
(i) T_j <= admBound_j  (admBound_0 = min(M_0,M_1), admBound_s = M_{s+1} for s>=1);
(ii) T weakly decreasing; (iii) T_{L-1}=0. minAdm(M) = min over admissible T of Mval(M,T).

THE DECOMPOSITION UNDER TEST. A recursive "dispatcher" classifies a node (root M0, current M) and, when
M is "non-leaf" (minAdm(M) > 0), emits a finite set of CELLS. Each cell c carries a codim c, defined as
codim c := Mval(M0, T_c).toNat for an exponent vector T_c that the dispatcher READS OFF the cell's
rank-drop profile (the running ranks of a representative tuple in that cell's stratum). The codims must:
(C>=) each codim be Mval(M0, T) for SOME admissible T (so each codim >= minAdm); and
(C-exists) at least one cell's codim equal minAdm(M0) (the achiever).
</task>

<output_contract>
Answer with explicit verdicts + exact certificates / counterexamples:

Q1. The codim formula Mval(M,T) — does it contain any matrix-rank or min/cap operation that could carry
    the intermediate-width pinch, or is it a pure polynomial in (M,T)? State which.

Q2. The cell's T_c is read off a running-rank profile. IF that read uses the WRONG endpoint-only cap
    instead of the correct all-widths cap, can it (a) for the ACHIEVER cell, or (b) for a NON-achiever
    cell, produce a T_c that yields a WRONG codim (different from the genuine stratum codim) or a
    NON-admissible T_c? Consider that the achiever T* is itself admissible (monotone), but non-achiever
    cells' profiles need not be. Give an exact (M, T) witness if such a divergence exists, or argue why
    the read is pinch-immune.

Q3. Independently of the read mechanism: is the property "(C>=): codim c = Mval(M0, T_c) for some
    admissible T_c" SELF-CERTIFYING (true by construction once T_c is chosen admissible and codim is
    DEFINED as Mval(M0,T_c)), or does it require a separate rank computation that could pinch? In other
    words, where (if anywhere) does a rank-pattern read with the pinch bug actually change an emitted
    codim, versus where is the codim guaranteed correct by the definition codim:=Mval(M0,T_c)?

Q4. Name the precise condition under which the WHOLE cell/codim decomposition is provably free of the
    intermediate-width-pinch bug-class. (E.g. "if T_c is always chosen admissible-by-construction and
    codim is defined as Mval(M0,T_c), the pinch cannot affect any emitted codim, because ...". Or:
    "the pinch CAN bite at step X if the read is Y".)
</output_contract>

<grounding_rules>
- Mval, admissibility, minAdm exactly as defined above.
- Distinguish FACT (proved/computed exactly) from INFERENCE (heuristic).
- Exact integer arithmetic only if you compute.
- The product is left-multiplied A_{j-1}...A_i; mind orientation.
</grounding_rules>
