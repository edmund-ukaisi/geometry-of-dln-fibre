<task>
A Lean 4 + Mathlib formalisation has ONE remaining general-M sorry for a divergence atom. I need a
ruthless REACHABILITY / COST read: is the general-M case a bounded, build-ready "det-tactic tide"
(known route, mechanical), does it need genuinely NEW mathematical design, or is it a research-grade
wall? Name the heaviest sub-piece. Do not rubber-stamp; argue from the structure I give.
</task>

<facts>
SETTING. For a width vector M = (M_0,...,M_L) of a deep linear network, routeMCore M is the
squared-Frobenius loss ||A^(0)...A^(L-1)||^2 in flat coordinates (N = sum M_s M_{s+1} dims).
minAdm M is a known integer (the achiever codimension). The atom to discharge:

   for c' >= minAdm/2 and every eps>0:  ∫_{[-eps,eps]^N} |routeMCore M(x)|^{-c'} dx = +infinity.

BANKED, M-AGNOSTIC, PROVEN (sorry-free). A structure `NodeAchieverChart M` with fields:
  - phi : (Fin N -> R) -> (Fin N -> R)   (the achiever chart, flat coords)
  - p : the binding radial pivot axis;  leafH : Fin N -> N  (the Jacobian exponent vector),
    with leafH p = minAdm - 1  (the radial backbone exponent)
  - the EXACT factorization  routeMCore M (phi u) = (u p)^2 * Ufun u
  - Ubound: on each box [0,delta]^N, Ufun <= B for some B>0, and Ufun > 0 a.e.
  - leaf_integrand: (∏_j |u_j|^{leafH j}) |F∘phi|^{-c} = monomialIntegrand(k,leafH,c,u) * (Ufun u)^{-c}
       where k = delta_p (1 on pivot, 0 else)
  - cov: the change-of-variables  ∫_{phi''(V\{u_p=0})} g = ∫_{V\{u_p=0}} ofReal(∏_j|u_j|^{leafH j}) g(phi u)
  - image_subset: a small box [0,delta]^N maps into [-eps,eps]^N.
And a theorem `routeMCore_box_diverges_of_nodeChart : NodeAchieverChart M -> (the atom)`, PROVEN for
arbitrary M. So the atom reduces EXACTLY to: construct a `NodeAchieverChart M` for arbitrary M.

REUSABLE GENERAL-N INFRASTRUCTURE (all banked, general in N, not per-M):
  - cubeBox, coordZero_null (each coordinate hyperplane is Lebesgue-null), monomialThreshold,
    monomialThreshold_le_regularSeq, monomialIntegrand_lintegral_box_eq_top (the sharp ∫u^{-1}=⊤ leaf),
  - paramsEquivFlat (flat<->Params measurable equiv),
  - measurePreserving_paramsPack_of_flatIdxEquiv + continuousLinearMap_abs_det_eq_one_of_measurePreserving
    (an outer coordinate-reshape with |det|=1),
  - pivotBlowupOn (radial blow-up of a coord set) with pivotBlowupOnDeriv_det = (x_p)^{card-1}
    (so |det| = |x_p|^{card-1}), HasFDerivWithinAt for it.

TWO PER-M INSTANCES ARE FULLY BUILT (sorry-free), each ~700-1300 lines of Lean:
  (A) M=(4,4,2,2), minAdm=4. PURE radial blow-up of the deepest 2x2 factor: A2 = u0*[[1,u1],[u2,u3]],
      A0,A1 free.  phi = reshape ∘ (single pivotBlowupOn of 4 coords).  |det Dphi| = |u0|^3 = u^{minAdm-1}.
      ONE weighted axis (u0).  cov drops ONE null-slice {u0=0}.  Ufun>0 a.e. via a nonzero-polynomial
      null-zero-set argument.
  (B) M=(3,3,4), minAdm=8. SINGLE-WEIGHTED radial: a "b = a*beta" Schur substitution + a pivot blow-up
      of 8 coords. |det Dphi| = |u0|^7 * |u1|^2 = u^{minAdm-1} * (one spectator pivot a=u1, exponent 2).
      TWO weighted axes.  cov drops TWO null-slices {u0=0},{u1=0}; phi_injOn off the union of 2 planes.

DECISIVE NEW EVIDENCE (I verified, exact sympy, actual symbolic Jacobian determinants of the verified
hand-frames; not asserted):
  - (4,4,2,2): det(Dphi) = u^3                       (u-exp 3 = minAdm-1)            [genuine diffeo]
  - (3,3,4):   det(Dphi) = -a^2 * u^7                (u-exp 7 = minAdm-1)            [genuine diffeo]
  - (3,3,3,3) minAdm=6 [LDU+chaining frame]: det(Dphi) = a^4 * b^3 * de^2 * (n2) * u^5
                                                    (u-exp 5 = minAdm-1)            [genuine diffeo]
  In ALL THREE: F∘phi has min u-degree exactly 2 (the u^2 rate), V|_{u=0} != 0 (sector witness),
  and the binding leaf exponent at c'=minAdm/2 is exactly -1 (the sharp ∫u^{-1}=⊤).

A UNIFORM closed-form recipe for phi_M exists (a prior thread, "LDU-core compressed-transition +
unit-triangular B/C chaining"), verified EXACTLY on 5 structurally-distinct M including codim-0
boundaries.  General form:  |det Dphi_M| = |u|^{minAdm-1} * ∏_{s,i} |q_{s,i}|^{exponent}, the u-axis
the single binding axis (k=1), every q_{s,i} a k=0 spectator (so the monomialThreshold is exactly
minAdm/2 regardless of the spectator monomial).

KEY OBSERVED SUBTLETY. The number of WEIGHTED axes (axes with nonzero leafH) grows with M:
  (4,4,2,2): 1 weighted axis;  (3,3,4): 2;  (3,3,3,3): 4 (u,a,delta,b).
The `cov` field for k weighted axes needs: phi_injOn off a union of k coordinate hyperplanes, and a
k-fold null-slice drop (add back each {weighted_axis=0} slice as a two-sided null contribution).
Also: the EXACT spectator monomial in det depends on the chaining choices (my free-N chaining gave an
extra n2 factor vs the thread's a^4 de^2 b^3) — so leafH must match the ACTUAL chart's det, derived
per construction.
ALSO OBSERVED: (3,3,3,3)'s chart is built in Lean (matrices + F=u^2*V factorization, sorry-free) but
the determinant + HasFDerivAt + cov + atom were EXPLICITLY DEFERRED to a separate module, with the
note "the two 27-row HasFDerivAt + the 4M-heartbeat composition identity + the heavy dets exceed a
tractable single build."
</facts>

<output_contract>
Answer these, each with a one-line verdict + 2-4 sentences of reasoning:

Q1. Is constructing `NodeAchieverChart M` for ARBITRARY M reachable by a BOUNDED, mechanical
    "det-tactic + radial-blow-up + reshape" route given the two built instances and the closed-form
    recipe — i.e. a build-ready tide — OR does the general case (arbitrary L, arbitrary achiever path)
    require genuinely NEW mathematical design beyond what (3,3,4)+(4,4,2,2)+(3,3,3,3) exercise?

Q2. Name the SINGLE HEAVIEST sub-piece of a general-M `NodeAchieverChart`. Candidates: (i) the
    HasFDerivAt of the N-dim chart (chain rule over a long composition), (ii) the symbolic
    determinant |det Dphi| = ∏|u_j|^{leafH j} at general N (BlockTriangular over fin-cases),
    (iii) the cov with a growing number of null-slice drops, (iv) the F=u^2*V factorization (ring at
    scale), (v) Ufun>0 a.e. (nonzero-polynomial null-set) at general N, (vi) defining a UNIFORM phi_M
    indexed by (L, achiever path) rather than hand-coded per M. Justify the pick.

Q3. Is the right unit of work (a) a single general-M theorem (one phi_M, one det lemma, one cov, all
    indexed by the descent path), or (b) a finite per-node instantiation (build (3,3,3,3) and a few
    more, leave the fully-general L as roadmap)? Which is the honest "bedrock" move?

Q4. Is there a DIFFERENT lower-bound route to the atom that AVOIDS building a full diffeo chart with a
    growing null-slice count — e.g. a curve/wedge restriction (1-parameter or low-dim achiever curve)
    + a direct ∫ along the curve, or a comparison/monotonicity argument |F| <= C*(monomial) on a
    positive-measure region — that would make the lower bound cheaper than the full c-o-v? If so,
    sketch it and say whether it's actually cheaper in Lean than the chart.

Q5. Net cost verdict, pick ONE: BUILD-READY TIDE (commission now) / NEEDS NEW DESIGN (one more
    design pass first) / RESEARCH WALL (roadmap). One paragraph defending the pick, and the single
    thing most likely to make you wrong.
</output_contract>

<grounding_rules>
Reason from the facts above; flag any place you are inferring vs. asserting. Keep separate: the
MATH (does a phi_M exist with the right rate+det — I claim verified) from the LEAN COST (how heavy to
formalise it). The math being settled does NOT make the Lean cheap; address the Lean cost directly.
Do not propose re-deriving the RLCT value (that's a separate banked lane). The single external
citation (monomial_rlct, the ∫u^{-1}=⊤ leaf) is allowed and already wired.
</grounding_rules>
