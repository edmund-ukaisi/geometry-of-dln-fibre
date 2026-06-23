<task>
Decorrelated second opinion on a per-node geometric reduction step for a deep-linear-network
(DLN) RLCT (real log canonical threshold) calculation. I want you to independently work out the
structure and tell me where my candidate per-step reduction is WRONG or where it holds, not to
rubber-stamp it.
</task>

<setup>
Fix a width vector M = (M_0, M_1, ..., M_L), all M_s >= 1. The loss is
    f(A) = || A^(1) A^(2) ... A^(L) ||_F^2     (squared Frobenius norm)
where A^(s) is a real matrix of size M_{s-1} x M_s, evaluated at the fibre over B = 0
(so the target is the zero matrix; this is the "deepest" / most singular point, all A^(s) = 0).

We want the RLCT of f at the origin A = 0. There is a known closed-form "value side":
define for an exponent vector T = (t_1, ..., t_L), t_0 := M_0,
    Mval(M, T) = sum_{j=1..L} (t_{j-1} - t_j) * (M_{j+1} - t_j)   [indices: M_{j+1} means M[j+1]]
over the admissible cone Adm(M) = { T : t_1 >= t_2 >= ... >= t_L, t_L = 0, t_1 <= min(M_0,M_1),
t_j <= M_{j+1} for j>=2 }. Then minAdm(M) := min_{T in Adm} Mval(M,T), and the claimed RLCT is
    rlct(f, 0) = (1/2) * minAdm(M).

A per-NODE recursion is being formalized. One reduction step ("schurState"):
    S.red = (M_0 - 1, M_1 - 1, M_2, M_3, ..., M_L)   [decrement the first TWO widths by 1]
The step is supposed to satisfy
    rlct(f_M, 0) = nReg/2 + rlct(f_{S.red}, 0),     i.e.   minAdm(M) = nReg + minAdm(S.red),
so nReg := minAdm(M) - minAdm(S.red) is FORCED by the value side.
</setup>

<my_geometric_construction>
The intended geometric mechanism for ONE step: a "hard pivot" blow-up on the (0,0) entry of A^(1).
Write A^(1) = y0 * Ahat with Ahat = [[1, r],[c, D]] (r a 1 x (M_1-1) row, c an (M_0-1) x 1 column,
D an (M_0-1) x (M_1-1) block; y0 the blow-up axis). Then f_M ∘ blowup = y0^2 * core,
core = || Ahat * P ||^2 where P = A^(2)...A^(L) is M_1 x M_L. Splitting P by its first row p_row
(1 x M_L) and the rest P_rest ((M_1-1) x M_L), and setting
    Erow  = p_row + r * P_rest                  (1 x M_L)
    S     = D - c * r                            (the (M_0-1) x (M_1-1) Schur complement)
    SGamma = S * P_rest                          ((M_0-1) x M_L)
one gets the EXACT polynomial identity (I verified this in sympy on several M):
    core = sum_j Erow_j^2 + sum_{i,j} (c_i * Erow_j + SGamma_{i,j})^2
and  || SGamma ||^2 = f_{S.red}(reduced tuple) exactly (the reduced loss).

The intended reading: the M_L entries of Erow are "regular" (Morse / nondegenerate) directions, so
    flatCore  ~  (sum over M_L of Erow^2)  +  || SGamma ||^2
should be a smooth-block split with nReg_geometric = M_L regular squares, and the RLCT splits as
    rlct(flatCore, 0) = M_L / 2 + rlct(||SGamma||^2, 0).
</my_geometric_construction>

<the_facts_that_trouble_me>
The value-side forces nReg = minAdm(M) - minAdm(S.red). I computed this exactly for many M.
It equals M_L for most M, BUT NOT all:
  M = (3,3,3,3): minAdm=6, minAdm(S.red=(2,2,3,3))=4, so nReg=2, but M_L = 3.   MISMATCH.
  M = (4,2,4,2,2): minAdm=3, minAdm(S.red=(3,1,4,2,2))=2, so nReg=1, but M_L = 2. MISMATCH.
Summing M_L over the full schurState recursion to a leaf OVERSHOOTS minAdm(M) badly
(e.g. (4,4,4): sum of M_L per step = 16, but minAdm = 12; (3,3,3,3): 9 vs 6).
</the_facts_that_trouble_me>

<output_contract>
Work this out independently and answer:
1. Is "the M_L entries of Erow are regular directions" actually correct, or are some Erow entries
   NOT genuine regular (nondegenerate-Hessian) directions at the origin? Specifically: Erow =
   p_row + r * P_rest. The r-block (M_1-1 free coords) shears Erow; p_row is the first row of the
   tail product P = A^(2)...A^(L), which itself vanishes to high order at the origin. Under what
   condition on (M_0, M_1, M_L, and the tail) are all M_L Erow-directions genuinely regular, vs.
   only a subset, with the rest folding back into the singular core?
2. What is the correct per-step regular count nReg as a function of M? Is it a LOCAL function of
   (M_0,M_1,M_2,...) at this node, or is it genuinely the global minAdm-difference (i.e. the single
   hard-pivot step is the WRONG granularity and the true resolution needs a different / finer per-step
   structure)?
3. Does the single-hard-pivot (decrement M_0,M_1 by 1) reduction even produce a valid smooth-block
   split at M=(3,3,3,3)? If the M_L=3 Erow squares are not all regular, the squeeze c1*Phi <= flatCore
   <= c2*Phi with Phi = (sum of M_L Erow^2) + ||SGamma||^2 would be FALSE (flatCore would be smaller
   than c1*Phi near 0 in the over-counted directions). Adjudicate: does the squeeze hold or fail at
   (3,3,3,3)?
4. If the single-form M_L presentation is wrong, characterize the scope: for which M does
   nReg = M_L hold (so the simple presentation is valid), and what is the obstruction / correct
   structure for the rest?
</output_contract>

<grounding_rules>
- The Mval/Adm/minAdm definitions above are exact (transcribed from the formalization). Use them.
- This is real-analytic RLCT (Watanabe), origin = the all-zero deepest point.
- Distinguish what you can PROVE from what you conjecture. Give a concrete computation for
  M=(3,3,3,3) if you can (e.g. rank/Hessian count of the Erow block, or the Newton-polytope / monomial
  count of the post-blowup core).
- Do not assume my construction is right; if the per-step granularity is wrong, say so plainly.
</grounding_rules>
