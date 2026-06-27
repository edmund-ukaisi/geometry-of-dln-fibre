<task>
Adjudicate a soundness-critical architecture question with exact reasoning. Do NOT run code.

SETTING. Real RLCT of F = ||prod(C) - B||^2_Frobenius at a point, prod(C)=C^(1)...C^(L), C^(s) of size
M^s x M^{s+1}, B of rank r. We are building a Lean recursion for the general-M resolution and must pin
its EXACT shape before committing the Lean contract.

There are TWO candidate descriptions of the recursion STEP, and a formaliser flagged they give different
contracts:
(A) DET-1 / MEASURE-PRESERVING: unimodular (det=1, polynomial, analytic) row/col changes Q^(s) (Gaussian
    elimination, the (u_i, psi_i) adapted basis) — NO blow-up, Jacobian = 1. This would give a CLEAN
    additive recursion: rlctAt(F) = nReg/2 + rlctAt(||prod(C_reduced)||^2 at 0), no monomial weights.
(B) BLOW-UP with nontrivial Jacobian: a coordinate-subspace blow-up of a rank-stratum center (codim
    c = Mval(t)), chart y_i=u, y_j=u*v_j, Jacobian u^{c-1}, F = u^2 * residual. This carries MONOMIAL
    Jacobian weights, headline = inf over leaves of monomialThreshold(d,k,h), NOT a clean nReg/2 chain.

FACTS I established by exact computation:
- The det-1 Schur substitution requires a leading minor of the partial product to be a UNIT (invertible).
  At the ZERO-product core origin (C=0, B=0), the product P=0, so P[0,0]=0 is NOT a unit — the det-1
  chart HYPOTHESIS FAILS at the deepest singular point.
- The det-1 Schur is exactly Aoyagi Theorem 3 / "product_reduction": for a rank-r FIBRE (B != 0), it
  peels the r REGULAR generators cleanly (F = ||reg E_r||^2 + ||prod(C')||^2, C' the reduced chain,
  B'=0), MEASURE-PRESERVING, contributing the regular shift nReg/2 = [-r^2 + r(H^1+H^{L+1})]/2.
- The residual ||prod(C')||^2 at the origin (B'=0) is STILL SINGULAR (e.g. for (2,2,2) the zero-core
  has rlct 3/2 = lambdaCore, NOT the smooth 4/2=2). So the det-1 peel does NOT resolve the core.
- The validated (2,2,2) ladder used a BLOW-UP: step 1 blows up {A1=0} (chart A1 = x*Ahat, Ahat[0,0]=1
  becomes a unit, Jacobian nontrivial x^k, x-exceptional divisor), THEN a unit-Jacobian Lemma-2 Schur
  clear, THEN blow up the residual again (s-exceptional), etc. The 24 leaves are monomial * (unit or
  smooth-block), headline = inf monomialThreshold = 3/2. The monomial weights come from the BLOW-UP
  Jacobians; the Schur clears have UNIT Jacobian.
- aoyagiLambda = [nReg/2 regular shift] + [lambdaCore = (1/2) min_Adm Mval]. The first is the det-1
  product-reduction (Thm 3); the second is the resolution of the zero-core (the blow-up).
</task>

<sub_question>
1. Is the general-M recursion STEP (A) det-1, (B) blow-up, or BOTH-IN-SEQUENCE (a blow-up that exposes
   a unit minor, then a unit-Jacobian det-1 Schur peel within the chart, then recurse on the residual
   zero-core)? Give the explicit Jacobian of the general-M node.
2. The TERMINAL leaf of the resolution recursion: is it a smooth block (rlct nReg/2) or a pure monomial
   (rlct monomialThreshold), or monomial * smooth-block? (Note: the resolution reduces dims keeping L,
   so an all-dims-1 leaf is a monomial c_1...c_L, not a smooth single-matrix block.)
3. Reconcile with the (2,2,2) ladder's blow-up + a planned reusable "g5_pivotNode" / monomialThreshold
   cover (those are blow-up/(B)-flavored): does the general-M recursion feed THEM? I.e. is the headline
   inf monomialThreshold (B-flavored), with the det-1 Schur as the unit-Jacobian chain-reduction WITHIN
   each chart?
4. A certificate I wrote earlier said the recursion "bottoms out at a smooth block leaf" via "unimodular
   det-1 Q" — was that IMPRECISE/INCOMPLETE? Specifically: did it conflate the det-1 product-reduction
   (B != 0 regular peel, the nReg/2 shift, measure-preserving) with the zero-core RESOLUTION (the blow-up,
   monomialThreshold)? Be blunt about whether the "det-1 clean recursion bottoming at a smooth leaf" framing
   is wrong for the ZERO-CORE resolution.
</sub_question>

<output_contract>
- A verdict: (A) / (B) / both-in-sequence, with the explicit general-M node Jacobian.
- The terminal-leaf type (smooth block / monomial / monomial*smooth-block).
- Whether the headline is inf monomialThreshold (and the det-1 Schur's role within it).
- A blunt FACT/INFERENCE assessment of whether the earlier "det-1 clean, smooth-leaf" framing was
  imprecise for the zero-core resolution, and exactly what the correction is.
</output_contract>

<grounding_rules>
- Ground in the facts above + standard resolution-of-singularities / RLCT theory (Aoyagi 2013, Watanabe).
- Reason on paper ONLY; do NOT read files or run code.
- "ratio of a divisor" = (h+1)/(2k) for pullback unit * prod|u_i|^{2k_i}, Jacobian prod|u_i|^{h_i}.
- A det-1 change of variables is measure-preserving (no Jacobian weight); a blow-up has a nontrivial
  monomial Jacobian.
- Preserve FACT vs INFERENCE. Be blunt if the earlier framing was wrong.
</grounding_rules>

<important>
You have NO file, shell, or code access. Do not call any tool. Produce only the reasoned adjudication.
</important>
