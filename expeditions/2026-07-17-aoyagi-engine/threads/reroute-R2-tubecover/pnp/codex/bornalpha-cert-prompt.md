<task>
Decorrelated adjudication of a per-leaf RESOLUTION-CHART certificate for the (3,3,4)
deep-linear-network RLCT lower bound (rlct >= 1/2 * codim = 4 at the corank-2 stratum).
I want your INDEPENDENT verdict on three kill-conditions, reasoning from the stated
facts only (no Lean, no scripts). Stress-test; do not rubber-stamp.

CONTEXT (all FACT unless marked):

1. The loss K = sum_{i,j} P[i,j]^2, P = A_1 . A_0, widths (3,3,4): A_0 is 3x3, A_1 is 4x3,
   P is 4x3. The RLCT lower bound needs, on every chart c of an up-to-null cover of a nbhd
   of the origin, a "from-below sandwich"
        cst_c * (monomial_c)^2  <=  K o g_c   on dom_c,   cst_c > 0.
   Then rlct >= min_c [ (1/2) * divisorMin_c ], where divisorMin_c = min over the BINDING
   exceptional divisors d (those dividing monomial_c) of (jac_exp_c(d) + 1) / (mono_exp_c(d)),
   and jac_exp = order of that divisor in the chart Jacobian, mono_exp = its order in
   monomial_c (=1 for a squarefree pivot monomial). rlct >= 4 needs divisorMin_c >= 8 on
   every chart AND each chart normal-crossing (a KEPT survivor).

2. The per-chart discharge (single_le_sum) needs the pullback normal form
        K o g_c = (monomial_c)^2 * sum_i resid_i^2
   with a KEPT SURVIVOR: an index i0 with resid_{i0} continuous and resid_{i0}(0) = 1
   (nonzero at the blow-up center). Then K o g_c >= (monomial_c)^2 * resid_{i0}^2.

3. The resolution is Aoyagi's (S,J) self-similar peel. At a coupled block M = Dbar . S
   (Dbar r x r with pivot (0,0)=1, S the r x c residual), the resolution chart uses:
   (i) block-elimination: the Schur complement of the (r-1)x(r-1) sub-block is blown up
       as Delta = E*alpha*Delta_reduced (E = dominant exceptional, alpha = next), and the
       original Dbar[i,j] (i,j>=1) = E*alpha*Delta_reduced[i-1,j-1] + Dbar[i,0]*Dbar[0,j]
       (the block-elim cross-term is KEPT, not dropped);
   (ii) a "born-alpha" recoord shear on the pivot ROW of S:
       S[0,:] := E*(1, t_2, ..., t_c) - sum_{i>=1} Dbar[0,i] * S[i,:]
       (a unipotent |det|=1 shear reading only the residual rows; NOT a coordinate change
       that diagonalizes the loss).
   Rows S[i,:], i>=1, stay free residual.

4. FACT (my exact sympy computation, all 6 block-shapes (r,c) that occur in the (3,3,4)
   peel: (3,3),(2,3),(1,2),(2,2),(3,4),(1,3)): with the born-alpha ON,
      M[0,:] = E*(1, t_2, ..., t_c)  EXACTLY  (the recoord cancels the block-elim cross-term),
      so the PIVOT entry M[0,0] = E EXACTLY, residual = M[0,0]/E = 1 (a CONSTANT).
      Every non-pivot entry M[i>=1, j] = E*(Dbar[i,0]*(1,t..) + alpha*(...)), residual
      vanishing at the center. So the ONLY residual nonzero at the center is index 0 = 1.
   With the born-alpha OFF (recoord dropped): for the genuinely-coupled shapes (r>=2 with
   a residual to recoord) the pivot residual OVER-VANISHES (all residuals 0 at center);
   the terminal 1xc rows (r=1) survive without it (no coupling to recoord).

5. FACT (blow-up Jacobian): a block blow-up along a center of size s contributes exceptional
   exponent (s-1) to the chart Jacobian on the pivot coordinate. In the (3,3,4) canonical
   chart the three blow-ups are: c11-blow-up center size 9 (jac_exp 8), E-blow-up center
   size 8 (jac_exp 7), alpha-blow-up center size 4 (jac_exp 3). The value monomial is
   monomial = c11 * E (the node-1 pivot times the node-2 pivot), squarefree.

6. FACT (permutation invariance of the codimension, established separately): min-adm(3,3,4)=8
   is permutation-invariant; the blow-up center SIZES are permutation-invariant.

<output_contract>
Terse, in these sections. Mark each claim [FACT from brief] / [INFERENCE] / [SPECULATION].

(A) KILL-CONDITION (a): does EVERY singular block-shape expose a SINGLE-ENTRY survivor equal
    to its pivot monomial EXACTLY? Or is there a shape whose only survivor sits in a
    Delta-block position (carrying the extra alpha), which would make its value monomial
    involve alpha? Derive from fact 4's normal form; say if fact 4 suffices or what's missing.

(B) KILL-CONDITION (b): is the sandwich-unit-radius (the radius where the survivor
    resid_{i0} >= 1/2) POSITIVE for every shape? Given fact 4 says resid_{i0} = 1 EXACTLY
    (a constant), what is that radius, and does the sandwich cst*(monomial)^2 <= K o g_c
    hold on the WHOLE chart or only near 0? State cst.

(C) KILL-CONDITION (c): does any shape's Jacobian exponent drop divisorMin below 8?
    Using facts 4-6: which divisors are BINDING (divide the value monomial)? Is alpha
    (jac_exp 3) ever binding? Compute divisorMin for the canonical (binding = {c11 jac 8,
    E jac 7}). Do the DEEPER exceptional divisors (from the r=2, r=1 sub-blocks) become
    binding, and if so with what mono_exp, so that (jac_exp+1)/mono_exp stays >= 8?
    (The claim to test: deeper divisors carry higher mono_exp, so the T-row pivot at the
    top level is the binding one; is that forced or could a deeper divisor bind below 8?)

(D) The single biggest risk you see in reducing the (3,3,4) rlct>=4 lower bound to this
    per-leaf born-alpha certificate across all 6 singular block-shapes. Is there a shape
    or a cover-gap this census would miss?
</output_contract>

<grounding_rules>
You do not have the Lean or the sympy. Reason from the stated facts. Where a conclusion
needs a fact not in the brief, name it. Distinguish the VALUE sandwich (survivor unit)
from the COVER question (measure) — they are different; this brief is about the value
sandwich + the Jacobian/divisorMin, not the cover. Do not invent lemma names.
</grounding_rules>
