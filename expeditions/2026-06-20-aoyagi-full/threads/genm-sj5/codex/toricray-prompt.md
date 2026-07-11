<task>
Independent toric-ray / Newton-polyhedron computation of a real log-canonical threshold (RLCT), to
CERTIFY a no-obstruction claim or find the offending ray. Self-contained; reason in exact algebra.

CONVENTION. For f >= 0 a sum of squares f = sum_i g_i^2 with generators g_i, and a measure
dmu = prod_k |x_k|^{rho_k} dx near 0, the zeta INT f^{-c'} dmu converges  <=>  c' < lambda, where by a
monomializing (toric) resolution pi with exceptional divisors E,
    lambda = min_E  (ord_E(Jac pi) + 1_E) / ord_E(f),   ord_E(f) = 2 * min_i ord_E(g_i),
and for a primitive ray w>=0 the "(Jac+1)" numerator is  <w, rho> + <w, 1>  (the +1 per coordinate).
"CERTIFIED no-obstruction" means lambda >= (1/2)minAdm, i.e. EVERY ray has
    (<w,rho> + <w,1>) / (2 min_i <w, alpha_i>)  >=  (1/2)minAdm,   g_i = x^{alpha_i}(unit).
ANY ray strictly below (1/2)minAdm is a genuine finiteness obstruction (or a setup error).

THE LOCAL MODEL (front peel of a deep-linear chain, rank-one angular chart). The loss on the chart is
    f = R^2 + u^2 ( H1^2 + v^2 H2^2 ),
      H1 = |q1 + s q2|,  H2 = |q2|,   q1,q2 in R^{mL} (mL=4),  R = |P Q_tp| the pivot energy.
Coordinates:
  - u >= 0: the front Gamma-block radial. The Gamma-block is a x b. Blow-up Gamma = u*Matrix(s,t,v),
    giving measure |dGamma| = u^{ab-1} du ds dt dv  (s,t bounded ANGULAR units; v the determinant-normal
    coordinate). So rho_u = ab-1, and v is a genuine coordinate with rho_v = 0.
  - v >= 0: determinant-normal coordinate of the 2x2 (or a x b) Gamma-block. At v=0 the second collapsing
    row loses its q2-direction (H2 drops out of the a x b block's second row).
  - the REDUCED variables governing (R, q1, q2): these are row-blocks of the deeper product of the
    reduced chain redChain = (t, M2, ..., ML). They are NOT free; they degenerate per the reduced chain's
    OWN Aoyagi resolution, whose plain RLCT is (1/2)minAdm(redChain). Treat redChain as an RLCT oracle:
    the reduced sublevel geometry gives, for the PLAIN reduced integrand,
       INT_{reduced} R^{-2 c''} dmu_red < inf  <=>  c'' < (1/2)minAdm(redChain).
    The reduced degeneration is COUPLED: R, q1, q2 all involve the SAME deeper product Z (shared), so
    their vanishing along the reduced exceptional divisors is correlated, not independent.

TWO ANCHORS (compute BOTH):
  (A) M=(3,3,3,4): minAdm=7, front binding cut t=1 -> a=b=2 (ab=4, rho_u=3), redChain=(1,3,4) with
      minAdm(redChain)=3. Target lambda = 7/2. UNIQUE front binding cut.
  (B) M=(4,4,4,4): minAdm=11, TWO front binding cuts: t=2 -> a=b=2 (ab=4, rho_u=3), redChain=(2,4,4)
      minAdm=7; AND t=3 -> a=b=1 (ab=1, rho_u=0), redChain=(3,4,4) minAdm=10. Both give
      peelCharge+minAdm(redChain)=11. The rank-one angular locus {v=0} of the t=2 chart is where the
      t=3 branch also binds. Target lambda = 11/2.

KNOWN INTERMEDIATE (verify, then use): integrating u first,
    INT_0^1 u^{ab-1} (R^2 + u^2 H^2)^{-c'} du  ~  R^{-2c'} (H<=R) ;  R^{2ab-2c'} H^{-2ab} (R<=H), c'>ab/2,
where H^2 = H1^2 + v^2 H2^2. For a=b=2: R^{4-2c'} H^{-4} on R<=H. Then integrating v:
    INT_0^1 (H1^2 + v^2 H2^2)^{-2} dv ~ H1^{-3} H2^{-1}.
So the residual outer integrand on {R<=H} is  R^{4-2c'} H1^{-3} H2^{-1}  against dmu_red.
</task>

<output_contract>
1. VERIFY the two KNOWN INTERMEDIATE asymptotics (u-integral regimes; v-integral) by exact algebra.
2. For anchor (A) (3,3,3,4): enumerate the PRIMITIVE toric rays of the combined resolution (the front
   divisors u, v coupled with the reduced divisors of redChain=(1,3,4)); for EACH give
   (ord_E f, ord_E Jac, ratio = (ord_E Jac + 1)/ord_E f). Report min ratio and whether ANY ray < 7/2.
3. Same for anchor (B) (4,4,4,4), INCLUDING the {v=0} branch and BOTH binding cuts (t=2 and t=3); report
   min ratio and any ray < 11/2.
4. VERDICT per anchor: CERTIFIED no-obstruction (all rays >= (1/2)minAdm) or the OFFENDING ray. State
   explicitly whether the residual decorated integral R^{4-2c'}H1^{-3}H2^{-1} against dmu_red is finite
   for c' < (1/2)minAdm, and what reduced vanishing-order data that requires.
5. End: is there a genuine FINITENESS obstruction, or only a construction/labour gap? The single cheapest
   check that would flip your verdict.
</output_contract>

<grounding_rules>
Do not assume the target lambda=(1/2)minAdm is achieved; test it. Distinguish a FINITENESS obstruction
(a ray strictly below (1/2)minAdm) from a construction gap (all rays >= threshold, theorem unbuilt).
If the reduced coupling data is insufficient to pin a ray, say which datum is missing rather than guessing.
Reason in exact algebra; do not paste code as proof.
</grounding_rules>
