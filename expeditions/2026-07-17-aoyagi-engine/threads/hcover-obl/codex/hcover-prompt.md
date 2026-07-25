<task>
Adjudicate ONE truth-value with exact algebra: is the following COVER obligation for an
iterated blow-up resolution "detail-at-scale" (standard, decomposable, formalizable as a
clean lemma library) or a "monument" (a single deep new-math obstruction)? Give your own
independent verdict + the ONE thing most likely to break it. Do NOT rubber-stamp.
</task>

<setup>
We resolve the singularity of a homogeneous polynomial loss K(w) = sum_ij (prod_s C^(s))_ij^2
at the origin by Aoyagi's recursive blow-up. The resolution is, in each leaf chart, a
composition along a root->leaf path of tree of "steps". Each STEP is:
      stepMap = (block-center blow-up)  o  (unipotent Schur-clearing shear)
with the block blow-up OUTERMOST. Concretely on coordinates R^D:
  * block-center blow-up  B_{S,p}:  pivot p |-> w_p ; other center coords j in S\{p} |-> w_p*w_j ;
    spectators (j not in S) |-> w_j.  (|det DB| = w_p^{|S|-1}.)
  * Schur-clearing shear  sigma = blockShear(phi):  u |-> u + phi(u), where phi is Aoyagi's
    coordinate displacement realising Q1 . A . Q2 = diag(1, Delta) with Delta = C22 - C21*C12
    (rank<=pivot Schur complement) PLUS the recoord C2' = Q2^{-1} C2 of the downstream factor.
    phi VANISHES on and READS ONLY the "kept" coords (pivot row + pivot col); it WRITES the
    residual block + the recoorded downstream slot (a set DISJOINT from what it reads).
    |det D(blockShear phi)| = 1 exactly (unipotent).

The COVER obligation ("hcover"): for the FULL FAN of leaf charts (at each node, fan over ALL
pivots p in S), the union of the chart images of compact source boxes covers a neighbourhood
of 0 up to a measure-zero set:  ball(0, rho)  subset  Union_c  g_c '' dom_c,  with
dom_c compact.  Equivalently the exceptional escape set has measure 0.

An abstract engine is already PROVEN (sorry-free) that assembles this cover from two per-node
inputs, by structural induction over the tree with an R-dependent box inflation f:
  (A) per-node box-containment:  closedBall 0 r  subset  sigma_p '' closedBall 0 (f r)   for each
      pivot p (the shear inverse maps an r-box into an f(r)-box);
  (B) the block-blow-up argmax atom:  closedBall 0 R  subset  Union_{p in S} B_{S,p} '' closedBall 0 (max R 1)
      (routing x to the pivot p = argmax_{q in S} |x_q|), ALREADY PROVEN for any S.
The engine's node clause requires a SINGLE super-geometric f used at all nodes; over finite
depth the leaf boxes are closedBall 0 (f^[depth] 1) (finite).
</setup>

<facts_established>
By exact sympy computation (no floats), for the FAITHFUL shear (Schur update + Q2^{-1} recoord),
at block sizes 2x2, 3x3, 2x4, 4x4:
  - phi is a valid unipotent shear: phi=0 on kept coords; reads only kept coords; write-set
    disjoint from read-set;
  - phi has polynomial DEGREE EXACTLY 2 in every case (the recoord adds MORE degree-2 products,
    C = block-size-many, but never raises the degree);
  - the naive inverse v |-> v - phi(v) is an EXACT two-sided inverse;
  - hence |phi(v)|_inf <= C*r^2 on |v|_inf<=r  =>  box-bound f(r) = r + C*r^2 per node.
Fan-completeness: the argmax lift reconstructs x for ALL coordinate directions (26/26 on the
3-coord model); a fan PRUNED to a pivot subset (col-pinning) misses a direction (the eps*e_2
escape: forcing pivot=0 with x_0=0 sends every center coord to 0, cannot hit (0,0,eps)); the
FULL fan picks pivot 2 and covers it.  Finite-depth leaf boxes f^[depth] 1 are finite.
</facts_established>

<sub_questions>
1. Is the per-node box-containment (A) for the faithful DEGREE-2 multi-term shear genuinely
   detail-at-scale, or is there a hidden obstruction when the shear has C>1 products per
   coordinate (vs the single-product rank-1 Schur)?
2. Fan-completeness: is "the full fan (argmax over all pivots) covers every direction, up to the
   measure-zero exceptional locus {some pivot coord = 0}" a standard blow-up fact, or does the
   coupling at corank>=2 open a genuinely-omitted direction the argmax routing misses?
3. Is there any place the DEPTH of the composition (deeper-mixed layers) makes the per-node
   picture FAIL -- e.g. a node whose shear is NOT box-bounded, or whose center is not a genuine
   coordinate block, so the argmax atom does not apply?
4. Overall: detail-at-scale (a formaliser can build the general-d hcover as a clean lemma library
   on top of the proven engine + the per-node box lemma) or monument?
</sub_questions>

<output_contract>
- A one-line VERDICT: detail-at-scale | monument | mixed (state which parts).
- For each sub-question 1-4, a short exact-reasoning answer (fact vs inference clearly separated).
- The single thing MOST LIKELY to break the cover if it is wrong.
- Any exact-algebra check you would run that we have not.
</output_contract>

<grounding_rules>
Reason from the setup + facts. Distinguish what you can PROVE from what you INFER. If a claim in
facts_established looks wrong, say so and why. Do not assume our conclusion (none is stated).
</grounding_rules>
