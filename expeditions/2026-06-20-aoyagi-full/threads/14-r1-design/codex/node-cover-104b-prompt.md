<task>
Independent check on a resolution-of-singularities RLCT (real log-canonical threshold) computation
for deep linear networks. EXACT pen-and-paper / sympy reasoning; no Lean. I want you to derive,
from scratch, the local RLCT of a specific singularity and tell me whether my proposed "two-strata
cover" reading is correct or has a flaw.

SETUP.
- F(A,B) = ||A . B||_F^2, where A is a generic m x k real matrix and B a generic k x n real matrix,
  both free coordinates; the singular point is the origin A=0, B=0.
- rlct(F, 0) = sup{ c >= 0 : |F|^{-c} is locally integrable near 0 }.
- Under a (possibly non-measure-preserving) resolution map pi, change of variables puts the Jacobian
  into the integrand: integral |F|^{-c} = integral |F o pi|^{-c} |Jac pi|.
- Known target value (Aoyagi): rlct(F,0) = (1/2) min over 0<=t<=min(m,k) of [ (m-t)(k-t) + t n ].
  Define R = (the same min for the (m-1) x (k-1) by (k-1) x n problem) = min over s of
  [ (m-1-s)(k-1-s) + s n ]. (R is the child's 2*rlct.)

FACTS I have (sympy-verified, exact):
- Blow up the (0,0) pivot of A: A = y0 * Ahat, Ahat = [[1, u],[v, W]] (top-left entry exactly 1).
  Then F o phi = y0^2 * core, core = ||Ahat . B||^2, and |Jac phi| = y0^(mk-1).
- Schur-eliminate the unit pivot: with Erow = B[0,:] + u.B[1:,:], S = W - v u, Bred = B[1:,:],
  core = sum_{j=1..n} Erow_j^2 + sum_{i,j} (v_i Erow_j + (S Bred)_{ij})^2, and ||S Bred||^2 is the
  child loss ||A'.B'||^2 (A'=S is (m-1)x(k-1), B'=Bred is (k-1)xn).
- min over 0<=t of [(m-t)(k-t)+tn] = min{ mk , n + R }  (the t=0 term is mk; min over t>=1 is n+R).

MY PROPOSED READING ("two-strata cover", one chart):
  rlct(F,0) = min{ rlct of the y0-factor , rlct of core }
            = min{ (mk-1+1)/2 , rlct(core,0) }
            = min{ mk/2 , (n + R)/2 }
  where (a) the OUTER step uses: F o phi = y0^2 * core is a PRODUCT of |y0|^2 (with Jacobian weight
  y0^(mk-1), in the single variable y0) times core (in the disjoint variables u,v,W,B, weight 1), so
  by Fubini |y0^2 core|^{-c} y0^(mk-1) integrates iff c < mk/2 AND c < rlct(core); hence the OUTER
  combine is a MIN; and (b) rlct(core,0) = n/2 + R/2 because, the pivot of Ahat now being a UNIT (=1),
  core = (n clean smooth Morse squares Erow) + (child ||S Bred||^2) is a SUM in disjoint variables, so
  rlct(core) = n/2 + rlct(child) = n/2 + R/2 (additive), with NO further internal cap.
</task>

<questions>
1. Is the OUTER step sound: for F o phi = y0^2 * core with the extra Jacobian weight y0^(mk-1), is
   rlct = min{ mk/2 , rlct(core) }?  In particular, is "rlct of a product of factors in disjoint
   variable groups (with a monomial weight on one group) = min of the per-group thresholds" correct,
   and does y0 genuinely not appear in core?
2. Is the INNER step sound: is rlct(core, 0) = n/2 + R/2 with NO internal cap, BECAUSE the Schur pivot
   of Ahat is a unit (so core is no longer at a rank-deficient origin and the Erow block is genuinely
   n clean Morse directions)?  Or can core still have its OWN product-type cap (e.g. some Erow_j
   coupling with the child) that lowers rlct(core) below n/2+R/2?  Probe the cross term v_i Erow_j.
3. Does this single chart (the blow-up of {A=0}) plus the Schur/child split actually constitute a
   normal-crossing resolution at the origin, so that the rlct really is read off as the min, valid
   UNIFORMLY in both regimes (mk <= n+R "wide tail" where the y0 divisor binds, and mk >= n+R
   "regular" where the core/child binds)?  Or do the two strata fail to glue (a residual singularity
   the single chart misses)?
4. If there is a flaw (the min is wrong, or core has a hidden cap, or the strata don't glue), give the
   smallest explicit (m,k,n) witness and the correct value.
</questions>

<output_contract>
- Distinguish FACT (computed thresholds, the Fubini argument) from INFERENCE.
- Verify on (m,k,n) = (2,2,2) [expect rlct 3/2, core/child branch binds] and (2,2,4) [expect rlct 2,
  y0 divisor binds, child R=1] and (1,1,2) [expect 1/2].
- State whether the two-strata MIN reading is sound uniformly, or where it breaks.
</output_contract>

<grounding_rules>
- F o phi = y0^2 core and |Jac| = y0^(mk-1) are sympy-verified; do not re-question them.
- rlct of a SUM in disjoint vars is additive (Watanabe); rlct of a PRODUCT in disjoint vars is the min.
- The target (1/2)min{mk,n+R} is the established value; judge whether my cover READS it correctly.
</grounding_rules>
