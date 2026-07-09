You are a decorrelated second-opinion reviewer on a Lean 4 + Mathlib (v4.29) formalisation-scoping question. Give an INDEPENDENT size/risk read. Do not defer to me.

CONTEXT. A deep-linear-network RLCT project needs, as its sole remaining gap, an analytic integrability lemma. On a composable real-matrix chain A_0,A_1,...,A_{N-1} (A_i real, widths M_i), after a Schur/shear reduction the goal reduces to proving, for c' < (1/2)*minAdm(M):

  INTEGRAL over the "deeper" matrices A' of:
      det(Q_b Q_b^T)^{-(M_0 - t)/2}  *  [reduced-chain-loss]^{-(c' - a/2)}   d(A')   <  infinity

where Q_b = (the non-pivot rows of the matrix PRODUCT P = A_1 * A_2 * ... * A_{N-1}), a = (M_0-t)(M_1-t), t a pivot size. The factor det(Q_b Q_b^T)^{-s} blows up on the locus where the matrix PRODUCT drops rank (a proper determinantal subvariety of the deeper matrices). At the binding case (3,3,3,4), t=1, the two exponents saturate their thresholds SIMULTANEOUSLY (zero slack): the coupling exponent = 1 = its own free-matrix integrability threshold (n-p+1)/2, and the residual exponent 3/2 = (1/2)*minAdm(1,3,4). So the two borderline factors share variables and (the claim is) cannot be bounded by Fubini-separating them; they need JOINT principalisation of the product's rank-drop determinantal locus.

The underlying mathematical VALUE is known/true (established by Aoyagi's DLN resolution + independent methods). The question is FORMALISATION SIZE/RISK in Lean 4 + Mathlib v4.29.

MATHLIB v4.29 INVENTORY (verified):
- PRESENT: Matrix.rank API, Matrix/SchurComplement, Matrix/Determinant, LinearAlgebra/ExteriorPower, MeasureTheory integral change-of-variables (Jacobian.lean: integral_image_eq_integral_abs_det_fderiv_smul), RingTheory/Grassmannian (functor-of-points, minimal), basic ideal theory.
- ABSENT: algebraic-geometry blow-up, resolution of singularities, normal-crossing divisors, determinantal ideals (as named objects with codim / primary-decomposition theorems), principalisation / monomialization, toric geometry, Plücker normal form of a product's maximal-minor ideal.

QUESTIONS (be concrete and quantitative):
1. SIZE TIER to formalise the boxed integrability lemma from scratch in Lean 4 + Mathlib v4.29: (a) a few lemmas, (b) one module, (c) a multi-module mini-expedition (weeks/months). Give your best point estimate + a rough "person-week" range.
2. Probability it is TRACTABLE in Lean at v4.29 at all via a MEASURE-THEORETIC route using explicit coordinate change-of-variables charts + monomial integrability (NO AG resolution-of-singularities primitive), vs the probability it forces a large Mathlib-AG detour (building blow-up / principalisation as reusable machinery). 
3. The obstruction claim is that a PRODUCT's rank-drop locus needs a NON-COORDINATE blow-up center (a dense-torus witness [[1,1,2,1],[1,1,2,1]] invisible to coordinate centers). If true, does that kill the "explicit coordinate charts" route? Is there a known way around it (e.g. the product structure lets you blow up one factor at a time on coordinate centers)?
4. WEAKER SUFFICIENT FORM: the project does NOT need the exact RLCT here — only an UPPER bound on the integral's exponent, i.e. finiteness for c' < (1/2)*minAdm, which is a "codim c' < 1/2 * combinatorial bound" one-sided statement. Is there a weaker, coarser sufficient lemma (e.g. a crude determinant lower bound / a domination by a simpler integrable envelope / Holder split with a small margin) that gives finiteness WITHOUT full joint principalisation? Or does the zero-slack borderline provably kill all crude envelopes?
5. Top 3 risks, ranked.

Answer tersely and numerically where you can. This is a scoping decision (build-from-scratch vs cite the classical result), so calibration matters more than optimism.
