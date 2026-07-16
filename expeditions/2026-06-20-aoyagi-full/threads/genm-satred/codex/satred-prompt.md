<task>
Adjudicate the FINITENESS and the correct reduction MECHANISM of a specific multi-matrix
integral arising in a real-log-canonical-threshold / Watanabe-singular-learning computation
for deep linear networks. I need an INDEPENDENT determination of which mechanism makes it
finite — argue it from scratch; do not assume any particular route is correct.

SETUP (exact). Fix positive integers u, M2, M3, b (widths). Variables, all integrated over the
entrywise box [-1,1]:
  P     : u x u   real matrix (additionally required invertible; the non-invertible set is null)
  z0    : u x M2  real matrix
  B12   : u x b   real matrix
  Acor  : b x M2  real matrix
  z1    : M2 x M3 real matrix
Define the "effective leading layer"  Z := P*z0 + B12*Acor   (a u x M2 matrix), and the integrand
  F(vars) := ||Z * z1||_F^2   (squared Frobenius norm of the u x M3 matrix product Z*z1).
For a real exponent c' > 0 consider
  I(c') := ∫_{boxes} F(vars)^{-c'} d(P,z0,B12,Acor,z1).

Separately define the REDUCED integral over just a (u x M2) matrix W and z1:
  R(c') := ∫_{W in [-T,T]^{uxM2}, z1 in [-1,1]^{M2xM3}} ||W*z1||_F^{-2c'} dW dz1,   T := u+b.
It is known (call it FACT-R) that R(c') < ∞ for all c' < thr, where thr = (1/2)*m, with m a
positive integer depending on (u,M2,M3) [m = the "minimal admissible codimension" of the
3-layer chain (u,M2,M3); e.g. (2,1,1)->m=1, (1,2,2)->m=2, (2,2,2)->m=3].

QUESTIONS.
(Q1) For which c' is I(c') finite? In particular, is I(c') < ∞ for all c' < thr (the SAME
     threshold as R), or is the threshold for I strictly smaller?
(Q2) The natural attempt is the change of variables W = P*z0 + B12*Acor at fixed
     (P,B12,Acor,z1): as a substitution in z0 it is affine with linear part "left-multiply by
     P", Jacobian |det P|^{M2}, so dz0 = |det P|^{-M2} dW. Enlarging the W-image to the full
     [-T,T] box then gives I(c') <= [∫_box |det P|^{-M2} dP] * (bounded) * R(c'). But
     ∫_box |det P|^{-M2} dP DIVERGES for M2>=1 (lct of det is 1). So this bound is vacuous.
     Does this mean I(c') is actually infinite, or is the divergence an ARTIFACT of enlarging
     the W-domain (i.e. the honest integral has no such factor)? Explain precisely.
(Q3) Consider the pushforward density rho(W) of (P,z0,B12,Acor) |-> W = P*z0 + B12*Acor onto
     the u x M2 matrix space. Characterize its singularities: is rho bounded, or does it blow
     up on {rank W < min(u,M2)} (e.g. at W=0, or along {det W=0} when u=M2)? Give the
     singularity order (power / log) as a function of (u, M2, b), as sharply as you can.
     Then: is I(c') = ∫ ||W z1||^{-2c'} rho(W) dW dz1 finite for all c'<thr, given FACT-R and
     your rho-analysis? Does it need c' strictly below thr (headroom), or does it hold up to thr?
(Q4) If instead P is restricted to {|det P| >= delta} (delta>0 fixed), is I finite trivially?
     And is the mass of I coming from {|det P| < delta} -> 0 as delta -> 0, or does the
     near-singular-P region carry non-negligible (but finite) mass?
</task>

<output_contract>
- State, for Q1, the exact finiteness threshold for I(c') (= thr, or strictly less), with reasoning.
- For Q2, a crisp verdict: artifact-of-enlargement vs genuine divergence, with the mechanism.
- For Q3, the singularity order of rho(W) in the regimes u<M2, u=M2, u>M2 (power/log + exponent),
  and whether ∫||Wz1||^{-2c'} rho finite up to thr or only with strict headroom.
- For Q4, whether |det P|>=delta makes it trivial and the delta->0 mass behavior.
- Separate what you PROVE from what you ARGUE heuristically. Give at least a scalar (u=M2=b=M3=1)
  worked check where everything is explicit.
</output_contract>

<grounding_rules>
- Exact algebra. lct/RLCT reasoning, coarea/pushforward-density, Wishart/matrix-product density
  facts are all in scope. Monte-Carlo is only a guide, never a proof.
- Do NOT assume the answer; the point is an independent determination. If a mechanism fails,
  say so and say why.
- Keep the scalar worked example fully explicit (it is checkable by hand).
</grounding_rules>
