<task>
We are formalising a lower-bound RLCT (real log-canonical threshold) divergence atom for deep
linear networks (DLNs). I need an independent construction/critique of whether a particular
"single-radial-pivot" change-of-variables chart generalises from a worked depth-2 case to
arbitrary depth.

SETUP (exact). For reduced widths M = (M_0, M_1, ..., M_L) (positive integers), the loss is
  F(A) = || A^(0) A^(1) ... A^(L) ||_Frobenius^2 ,
the squared Frobenius norm of a product of L+1 matrices of compatible shapes (A^(s) is
M_s x M_{s+1}, with the last factor M_L x M_{L+1} for an output width; for our "core" we evaluate
at the deepest point and want the box integral near the origin A=0). We want, for c' >= (1/2) minAdm M:
  INT_{[-eps,eps]^N} |F(A)|^{-c'} dA = +infinity  (N = total number of entries = flat dimension),
for every eps>0.  Here minAdm M is the integer
  minAdm M = min over admissible exponent vectors T=(t_1,...,t_L) of
             Mval(M,T) = sum_{j=1}^{L} (t_{j-1} - t_j)(M_{j+1} - t_j),  t_0 := M_0,
  admissibility: 0 <= t_L <= ... <= t_1, t_1 <= min(M_0,M_1), t_j <= M_{j+1}, t_L = 0.
This has a layer-peeling recursion:
  minAdm(M) = min_{t in [0..min(M_0,M_1)]} (M_0 - t)(M_1 - t) + minAdm( (t, M_2, ..., M_L) ).
The minimiser gives a DESCENT PATH of pivots (t_1, t_2, ..., t_{L-1}) plus a final 2-width leaf.

THE WORKED DEPTH-2 CASE (L=2), M=(3,3,4), minAdm=8, threshold 4. A SINGLE change-of-variables
chart phi : R^21 -> R^21 (the 21 flat coords) was constructed and VERIFIED EXACTLY:
  - it is built as: Schur shear (block-triangular, det 1) composed with a coupled "diag(b)=a*beta"
    blow-up of the binding rank-1 pivot u_0;
  - F( phi(u) ) = u_0^2 * U(u)  EXACTLY (polynomial identity), where U is a u_0-free polynomial,
    and U >= a^2 = u_1^2 (bounded below away from 0 on a positive-measure box slice);
  - |det D phi(u)| = |u_0|^7 * |u_1|^2 = |u_0|^{minAdm-1} * |u_1|^2  (the spectator u_1 has loss-base
    exponent 0).
  So the leaf integrand is a PURE-MONOMIAL leaf: (k,h) = (1, minAdm-1) on the single binding axis u_0
  (loss base u_0^2, Jacobian u_0^{minAdm-1}); the box integral diverges at c' >= (h+1)/(2k) = minAdm/2.
The Lean divergence atom accepts an arbitrary product monomial: integrand = (prod_j |u_j|^{h_j}) *
(prod_j |u_j|^{k_j})^{-2c'}, diverging when min over loss-axes (h_j+1)/(2 k_j) <= c'. (PRODUCT/normal-
crossing form, NOT a sum-of-monomials form.)

THE QUESTION. For L >= 3 the descent path has SEVERAL nested pivots (e.g. M=(4,4,2,2) has path
(t_1,t_2)=(4,2) with per-step Schur codims 0,0 and a leaf 2x2 -> minAdm=4; M=(3,3,3,3) has path
(2,1) with codims 1,2 and leaf 1*3=3 -> minAdm=6).  Each pivot is its own Schur blow-up; the
composite chart is a CHAIN of these.

  (1) Does the composite chart still factor as  F( Phi(u) ) = (SINGLE monomial in u)^2 * U,
      U bounded below on a positive-measure box, with |det D Phi| a pure monomial, and the
      resulting leaf threshold EXACTLY minAdm/2 ?   OR does the nested chain produce a genuine
      SUM-of-monomials (e.g. u_0^2 + u_1^2 type, a blow-up of a smooth point) whose box-integral
      threshold is NOT a single pure-monomial axis?
  (2) Concretely for M=(4,4,2,2) and M=(3,3,3,3): construct (or argue the obstruction to) a single
      change-of-variables chart Phi on the flat coordinates with F(Phi(u)) = (monomial)^2 * U,
      U >= c0 > 0 on a positive-measure slice, |det D Phi| a monomial, such that the box integral
      diverges at exactly c' = minAdm/2 and CONVERGES for c' < minAdm/2 (sharp).  Give the explicit
      pivot coordinates and the Jacobian monomial, OR explain why the nested peel forces a sum form
      / a multi-axis leaf where the threshold splits.
  (3) Is the threshold minAdm/2 achievable with a "single binding axis" carrying (1, minAdm-1), the
      way the depth-2 case did, for ALL M?  Or only for a characterised subclass (e.g. L=2, or
      single-pivot descent paths)?  If a subclass, characterise it precisely.

This is for a Lean formalisation: I need EITHER a build-ready general construction OR a precise
characterisation of the M-class where the single-pivot chart works, plus the obstruction outside it.
</task>

<output_contract>
1. A direct answer to (1): single-monomial product form vs sum form for the nested chain. State your
   confidence and whether it is a derivation or a conjecture.
2. For (2): either an explicit chart for (4,4,2,2) and (3,3,3,3) (pivot coords + Jacobian monomial +
   the F = monomial^2 * U factorisation, checked), or the precise obstruction.
3. For (3): the M-class (all M? L=2 only? single-pivot paths only?) for which a single binding axis
   (1, minAdm-1) realises threshold minAdm/2, with the characterisation criterion.
4. Distinguish clearly: derived/proven vs conjectured/heuristic. Flag any step you are unsure of.
</output_contract>

<grounding_rules>
- Exact algebra only for load-bearing claims. If you assert a factorisation F = monomial^2 * U,
  it must be an exact polynomial identity (say so, and ideally give the U).
- The threshold of a PURE monomial product prod x_i^{2 k_i} with Jacobian weight prod x_i^{h_i} is
  min_i (h_i+1)/(2 k_i).  The threshold of a SUM (e.g. x^2 + y^2 with weight x^{a}y^{b}) is the
  Newton-polytope LCT, generally (a+1+b+1)/2 along the diagonal — DIFFERENT.  Keep these separate.
- Do not assume the depth-2 single-radial miracle generalises; test it.
- I am withholding my own tentative conclusion. Reason from the setup.
</grounding_rules>
