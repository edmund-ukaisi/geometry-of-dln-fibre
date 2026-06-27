<task>
Adjudicate a recursion-closing claim (G3.2) for a Lean formalisation roadmap — witness-confirm or find an
obstruction. The math is believed settled (Aoyagi 2013 pp.15-21); I need an independent check that the
RECURSION STEP is exact and threads for general chain length, before committing formalisation lines.

SETUP (exact, real matrices). A "matrix chain" C = (C^(1),…,C^(L)), C^(s) of size M^s × M^{s+1}. Its
product P = C^(1)·…·C^(L) (size M^1 × M^{L+1}). The loss is F = ‖P − B‖²_F (squared Frobenius). For a
rank-r target B, the singular core is B=0; we resolve F at the origin via iterated pivot blow-ups.

THE G3.2 CLAIM (the recursion-closing step): in a pivot chart where the leading 1×1 minor of P is a
UNIT (P[0,0] invertible), there are UNIMODULAR (det=1, polynomial-entry, analytic) row/col changes Q^(s)
(size M^s × M^s) such that the FACTOR-WISE transformed chain
  ∏_s (Q^(s) C^(s) (Q^(s+1))^{-1})   [the inner (Q^(s+1))^{-1} Q^(s+1) cancel in the product]
block-diagonalizes: Q^(0) P (Q^(L))^{-1} = blockdiag[E_1 (regular 1×1), Schur(P)], AND the residual
Schur(P) = ∏_s C'^(s) for a REDUCED chain C'^(s) of sizes (M^s − 1)×(M^{s+1} − 1) — i.e. the Schur
complement of the PRODUCT equals the product of the Schur-reduced FACTORS. Then F splits (after the
parameter change-of-variables, an S1.5 smooth-block fact already proven) as ‖reg‖² + ‖∏C'‖², so
rlctAt(F) = ½·(reg-dim) + rlctAt(‖∏C'‖²), and recurse on C'. Well-founded: ΣM^s strictly drops.

WHAT I VERIFIED (sympy, exact, symbolic generic entries):
- L=2, cases (3,3,3), (3,2,3) [non-square middle], (4,3,2) [decreasing]: the factor-wise construction
  Q^(0)=L0 (clears C^(1) col0 below pivot), Q^(1)=R1 (clears C^(1) row0), threaded R1^{-1} to C^(2), then
  R2 clears the chain's top row. RESULT (all diff=0 EXACTLY): core := (L0·P·R2)[1:,1:] = S1·C2' where
  S1=Schur(C^(1)), C2'=(R1^{-1}C^(2)·R2)[1:,1:], AND core = Schur(P). Reduced dims exactly (M^s−1).
- The reg-count: H¹+H^{L+1}−r regular generators, ½·that = aoyagiLambda's regular shift [−r²+r(H¹+H^{L+1})]/2.
  Matches for (3,3,3) r=1: 5/2.
- The prototype only verified L=1 (single-matrix Schur); I've now verified L=2.
</task>

<output_contract>
1. Is the G3.2 recursion step EXACT and does it thread for general L (not just L=2)? Specifically: does
   "Schur(P) = ∏(Schur-reduced factors)" hold for arbitrary chain length, and is the inner-Q cancellation
   (Q^(s+1))^{-1} Q^(s+1) the right mechanism, or is there an obstruction at L≥3 (e.g. the inner reductions
   conflicting — the Q^(s) that clears C^(s)'s row must equal the Q^(s) that clears C^(s+1)'s col)?
2. The SUBTLE point: at L≥3, the middle factors C^(s) (1<s<L) get reduced on BOTH sides (Q^(s) on left,
   (Q^(s+1))^{-1} on right). Is the two-sided Schur reduction of a middle factor consistent (does clearing
   its row for the (s-1)-pivot conflict with clearing its col for the (s+1)-pivot)? Or does the single
   top-pivot only touch the FIRST row/col of the whole chain (so middle factors are reduced once)?
3. Is the additivity ‖P−B‖² = ‖reg‖² + ‖∏C'‖² correctly scoped as (G3.2: chart+residual) + (S1.5: the
   c-o-v norm split), given Q's are unimodular NOT orthogonal (so it is NOT ‖Q0 P Q2‖²=‖P‖²)? Any gap?
4. Any obstruction to the Lean construction that the L=2 verification masks? Or is this a sound witness
   for the recursion step (construction, not open math)?
</output_contract>

<grounding_rules>
- Exact real-matrix algebra. Distinguish PROVED from CONJECTURE.
- The claim is believed TRUE (Aoyagi); I want independent confirmation it threads for general L + the
  precise mechanism, OR a concrete obstruction. The L=2 cases verified exactly (diff=0).
- Focus on points 1-2 (the general-L threading / inner-Q consistency) — that's where L=2 might mask a gap.

<important>
Do NOT run any shell commands or read any files — this is a PURE REASONING task. All needed facts are in
<task> above (the sympy verifications: L=2 cases (3,3,3),(3,2,3),(4,3,2) all diff=0, and L=3 (3,3,3,3)
diff=0 with the middle factor two-sided-reduced consistently). Reason from these given facts only; do not
attempt to read the Aoyagi PDF or any source. Answer the 4 output_contract points directly.
</important>
