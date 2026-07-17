<task>
Independent adjudication of a matrix-integral DOMINATION claim (real-log-canonical-threshold work on
deep linear networks). Argue whichever direction the algebra supports; my own conclusion is WITHHELD.
Distinguish OBSERVED FACT (you derived/verified) from INFERENCE. Exact algebra only; MC guides at most.
</task>

<setup>
Fix a layer-width chain M=(M0,M1,...,M_last), a cut u>=1, a=M0-u, b=M1-u, n=M_last.
- z ranges over a "deep box"; Q_p=Q_p(z) is u x n, full row rank u for generic z. ||Q_p||_F^2=:||R||^2.
- A_cor ranges over [-1,1]^{b x M2}; Z=Z(z) is M2 x n (rank >= a+b); Q_b:=A_cor Z is b x n.
- hsQ:=[Q_p; Q_b] is M1 x n; its singular values = those of the full front product.
- x=(P,B12,C): P is u x u INVERTIBLE (IsUnit), B12 is u x b, C is a x u, all in [-1,1] boxes; Gamma is a x b.
- freedSchurLoss = ||[P|B12] hsQ||_F^2 + ||C Q_p + Gamma' Q_b||_F^2, Gamma'=Gamma+C P^{-1} B12 (unimodular shear).

COORDINATIZATION (I have verified this EXACTLY in sympy over a rational orthonormal frame): let Qhat (u x n)
be an orthonormal basis of row(Q_p), Vhat ((n-u) x n) an orthonormal completion, O=[Qhat;Vhat] orthogonal.
Write Q_p = R Qhat (R u x u invertible, sing. vals = Q_p's), Q_b = X Qhat + Y Vhat with X=Q_b Qhat^T (b x u),
Y=Q_b Vhat^T (b x (n-u)). Set U=[P;C] (M0 x u), W=[B12;Gamma'] (M0 x b). THEN EXACTLY
        freedSchurLoss = ||U R + W X||_F^2 + ||W Y||_F^2.
Also EXACTLY: the transverse Schur complement Q_b(I-Pi_p)Q_b^T = Y Y^T (Pi_p=proj onto row Q_p); and
completing the square in the full W gives constant term ||U Q_p (I-Pi_b)||_F^2 (Pi_b=proj onto row Q_b).

SHELL-j RESTRICTION (1<=j<r, u=t*+j, t* a fixed base rank): A_cor restricted so hsQ has EXACTLY j singular
values < eps and the other min(M1,M2)-j >= eps (a PARTIAL floor). ab/2 < c'.

The banked lemmas available:
(K3) EXACT: integrating Gamma' over R^{ab}: int (w + ||C Q_p + Gamma' Q_b||^2)^{-c'} dGamma'
     = B(ab,c') det(Q_b Q_b^T)^{-a/2} (w + ||C Q_p (I-Pi_b)||^2)^{-(c'-ab/2)}, for c'>ab/2.
(K5) P-radial blow-up of the u x M1 front block [P|B12]=r*What: int_W phi(||W hsQ||^2)
     = int_sphere int_{r>0} r^{u M1 - 1} phi(r^2 ||What hsQ||^2).
(K6) For a rank-rho linear map L, int_cube (||Lx||^2)^{-c''} < inf iff c'' < rho/2.
(K4) A_cor-FREE weight only: int_{A_cor} int_Gamma (w + ||Ccross + Gamma(A_cor Z)||^2)^{-c'} <= Cunif w^{-(c'-ab/2)},
     Cunif free of Z,Ccross,w, PROVIDED a deep floor ZZ^T >= eps^2 U_s U_s^T (m>=a+b orthonormal frame). BUT here
     the weight w = ||[P|B12]hsQ||^2 = ||PR+B12 X||^2+||B12 Y||^2 DEPENDS on A_cor (via X,Y), so K4 does NOT apply directly.

T1 := (1/2) minAdm(M), minAdm(M)=min_r[(M0-r)(M1-r)+minAdm(redChain r M)] (full-chain min over cuts). For L=0,
minAdm(M0,M1,M2)=min_r[(M0-r)(M1-r)+r M2]. At NON-argmin cuts u, T2:=(1/2)(ab+minAdm(redChain u M)) > T1.
</setup>

<the_claim_to_adjudicate>
The estimate (*_T1): for ab/2 < c' < T1, there is C_j < inf (allowed ->inf as c'->T1-) with
   int_z int_{A_cor: shell-j} int_{P unit,B12,C,Gamma'} freedSchurLoss^{-c'}
      <= C_j int_z (commonDivisor(z)^2 ||Q_p(z)||^2)^{-(c'-ab/2)}   [reduced comparator on the SHORTER chain].
This is a genuine DESCENT (RHS = the object on a chain with one fewer layer). The circular route
"shell-domain subset of off-shell domain, so LHS <= off-shell < inf, C_j := LHS/RHS" is KNOWN and UNUSABLE
(off-shell object = the recursion's own goal). A non-circular proof is required.
</the_claim_to_adjudicate>

<questions>
1. CLEANEST NON-CIRCULAR ROUTE. Using the coordinatization + K3/K5/K6 (NOT K4, weight is coupled), what is the
   minimal chain of integrations that yields (*_T1)? In particular: is the natural target the POINTWISE-in-z
   bound  int_{A_cor: shell-j} det(Q_b Q_b^T)^{-a/2} Phi(z,A_cor) dA_cor <= C_j (cd(z)^2 ||Q_p(z)||^2)^{-(c'-ab/2)},
   where Phi = int_{P,B,C}(||PR+B12 X||^2+||B12 Y||^2 + ||C Q_p(I-Pi_b)||^2)^{-(c'-ab/2)} [post-K3]? Or must the
   z-integration be used globally (i.e. is the pointwise-in-z bound FALSE)? Derive the scaling in ||R||=||Q_p|| as
   R->0 and say for which c' the pointwise bound gives exponent exactly 2(c'-ab/2).

2. THE SINGLE NEW SUB-LEMMA beyond K3/K5/K6. State it as sharply as possible. The candidate mechanism is a
   dichotomy on the SVD of Y (tau_1..tau_j small, tau_{j+1}..tau_b floored on shell-j): on Y's b-j strong
   left-directions the W-integral pays (K6 rank integrability); on the j weak directions, smallness of the loss
   forces UR+WX~0 and the U/R-integral pays. Does this dichotomy actually close WITHOUT double-spending W (which
   appears in both ||UR+WX||^2 and ||WY||^2)? Give the exact exponent count.

3. THE BINDING/OBSTRUCTION. The SVD-of-Y measure factor for the j small singular values is
   prod_{i<=j} tau_i^{(n-u)-b} * prod_{i<i'<=j}|tau_i^2-tau_{i'}^2| dtau. And Sigma:=I-X^T(Q_bQ_b^T)^{-1}X has j
   small eigenvalues ~ tau_i^2 (quadratic in the angle) at a corank-j incidence. Does the corank>=2 regime
   (j>=2, b>=2) introduce a divergence that the corank-1 count misses (a prior "light" recursion provably broke
   there)? And when u>t* (so full R->0 is OFF shell-j): where does the T1 threshold get enforced -- by the shell,
   or by the ||R||^{-2(c'-ab/2)} comparator? Is (*_T1) at c'<T1 LABOUR (mechanism clear, long) or a genuine WALL
   (missing math)? Name the missing ingredient if a wall.
</questions>

<grounding_rules>
State which claims you VERIFIED by derivation vs INFERRED. If you find a divergent corner, give the explicit
scaling and exponent count. Do not trust K3-K6 blindly if a derivation contradicts one -- flag it. The threshold
has ZERO slack at argmin cuts (binding corner M=(2,2,3),u=j=1,t*=0 attains c'=T1=2 exactly); a loss in ANY
exponent anywhere is fatal, so keep exponent bookkeeping exact in Q.
</grounding_rules>
