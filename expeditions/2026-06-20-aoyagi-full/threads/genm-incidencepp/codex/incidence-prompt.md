<task>
Independent adjudication of a log-canonical-threshold (RLCT) domination inequality arising in a
formalised proof. Determine, by EXACT algebra (resolution / monomialisation / codim stratification),
the convergence threshold of a constrained matrix integral and whether a stated DOMINATION by a
"reduced comparator" holds with a FINITE per-exponent constant. Argue whichever way the algebra
points; hunt for a divergence or a constant blow-up. Do NOT assume the setup is sound.

=== THE OBJECTS (all real matrices; take the L=0 leaf so the deep factor is the identity) ===
Fix a 3-term chain M = (M0, M1, M2). Choose a "cut" 1 <= u < min(M0,M1); set a = M0-u, b = M1-u.
Variables:
  z         : parameters of a "reduced chain" (u, M2); their product is  Qp := prod(z), a u x M2 matrix.
              (For the leaf, Qp is literally a single u x M2 layer; think of z as ranging over a box,
               Qp full-row-rank u for generic z.)
  A_cor     : a b x M2 matrix (ranges over a box [-1,1]^{b*M2}); set  Qb := A_cor  (b x M2).
  hsQ       : the (u+b) x M2 matrix stacking Qp on top of Qb.
  Front block variables P (u x u), B (u x b), C (a x u): each ranges over a box [-1,1]^{...}.
Derived:
  Pi_b      : orthogonal projection (M2 x M2) onto the row space of Qb.
  I - Pi_b  : projection onto the orthogonal complement of row(Qb).
Exponent:  c'  a real parameter with  ab/2 < c'  (the "freed-corner regime"); set  q := c' - ab/2.

=== THE SHELL REGION (this is load-bearing) ===
Let r = min(M0, M1) (= min(M0,M1) since t*=0 in the binding case). Fix small eps>0 and a level
1 <= j < r.  S_j(z) = { A_cor : the matrix hsQ = (Qp ; Qb) has EXACTLY j singular values < eps
(the other min(M1,M2)-j singular values are >= eps) }.  Note S_j depends on z through Qp: it is the
region where exactly j of hsQ's directions are near-degenerate.  The incidence corner is where a row
direction of Qb aligns with row(Qp): there Qp*(I - Pi_b) -> 0 (the "transverse Schur complement").

=== THE TARGET INEQUALITY (per level j, 1<=j<r) ===
Claim:  for  ab/2 < c' < T1 := (1/2) minAdm(M),  there is a FINITE constant K = K_{j,c'} (allowed to
-> infinity as c' -> T1^-) with

  INT_z  INT_{A_cor in S_j(z)}  det(Qb Qb^T)^{-a/2}  *
        [ INT_{P,B,C} ( || [P|B] . hsQ ||_F^2  +  || C . Qp . (I - Pi_b) ||_F^2 )^{-q}  dP dB dC ]
     <=  K  *  INT_z ( commonDivisor(z)^2 * || Qp(z) ||_F^2 )^{-q}  dz.

Here minAdm(M) = min_{0<=s<=min(M0,M1)} [ (M0-s)(M1-s) + s*M2 ], and [P|B].hsQ = P*Qp + B*Qb
(the u pivot rows of the front-block output).  commonDivisor(z) is a radial monomial from the
comparator's resolution; treat the RHS as the reduced comparator whose RLCT-in-q is
(1/2) minAdm(u,M2) = u*M2/2 (finite iff q < u*M2/2, i.e. c' < (u*M2 + ab)/2 =: T2 >= T1).

Two features the estimate MUST respect (state whether each is forced, and why):
 (i) the moving-subspace incidence: row(Qb) -> row(Qp), where ||Qp(I-Pi_b)||^2 -> 0;
 (ii) det(Qb Qb^T)^{-a/2} and the transverse term stay COUPLED inside the A_cor integral
      (a uniform sup over A_cor pull-out is suspected unsound); the pivot weight
      w ~ ||[P|B].hsQ||^2 stays coupled.

=== THE BINDING CORNER (smallest decisive test) ===
M=(2,2,3), u=1, a=b=1, T1 = (1/2) minAdm(2,2,3) = (1/2)*4 = 2. Take z so Qp = e1 = (1,0,0).
Let A_cor = Qb = (1, t2, t3), and t=(t2,t3) -> 0 (the incidence corner: Qb -> e1 = Qp direction).
Then:
  det(Qb Qb^T) = 1 + |t|^2  (bounded, ~ 1);   ||Qp(I-Pi_b)||^2 = |t|^2/(1+|t|^2) ~ |t|^2 (-> 0).
The front block is scalar: P=p, B=beta, C=gamma. Pivot energy = (p+beta)^2 + beta^2|t|^2;
transverse energy = gamma^2 |t|^2/(1+|t|^2).

=== QUESTIONS ===
Q1. Compute EXACTLY the local RLCT (in c') of the corner integral
    INT_{|t|<delta} (1+|t|^2)^{-1/2} INT_{p,beta,gamma}((p+beta)^2 + beta^2|t|^2 + gamma^2|t|^2/(1+|t|^2))^{-q} dp dbeta dgamma dt,
    q = c' - 1/2.  Give the blow-up (charts, monomial exponents, the radial integral) and the exact
    threshold. Does it equal T1 = 2?  Is convergence strict below T1, with a per-exponent finite value?
Q2. Set up the GENERAL incidence blow-up for arbitrary (u,a,b,j, M): identify the incidence locus
    {row(Qb) meets row(Qp)}, the chart/monomialisation that resolves ||Qp(I-Pi_b)||^2 jointly with
    det(Qb Qb^T)^{-a/2} and the pivot weight, and the resulting joint exponents. Is the det-Gram
    Jacobian discardable (sup pull-out) or must it stay coupled? Give the exact reason.
Q3. THE CRUX — does the DOMINATION hold with FINITE K for every c' < T1?  Specifically: is the map
    z |-> [inner A_cor+front integral] / (commonDivisor(z)^2 ||Qp(z)||^2)^{-q}  BOUNDED over z, uniformly?
    Consider ill-conditioned Qp (||Qp||_F large but sigma_min(Qp) small): does the LHS inner integral
    stay <= K * ||Qp||_F^{-2q}, or does the condition number make K blow up?  Is the correct structure
    a POINTWISE-in-z bound, or must the z-integration genuinely participate (both sides share the
    Qp rank-stratification)?  If pointwise fails, does the integrated bound still hold, and by what
    mechanism (does the shell S_j(z)'s dependence on Qp rescue it)?
Q4. Adjudicate: is the target inequality TRUE (finite per-exponent K) for ab/2 < c' < T1, or is there a
    configuration (a specific z / A_cor region / c' in (ab/2, T1)) where the LHS diverges or K blows up
    while the RHS stays finite?  If TRUE, give the cleanest sufficient argument. If FALSE, give the exact
    witness. Do NOT optimise for agreement.

<output_contract>
- Label every statement [FACT] (exact algebra you can defend) or [INFERENCE].
- Q1: give the corner RLCT as an exact rational with the radial-integral exponent shown (the "INT r^? dr").
- Q2: give the incidence chart(s) and the joint monomial exponents explicitly.
- Q3: state plainly whether a pointwise-in-z bound holds; if not, whether the integrated bound holds and why.
- Q4: state plainly TRUE/FALSE for "finite per-exponent K on ab/2<c'<T1", with the decisive case.
- Prefer a constructive resolution (named charts, Jacobians) over an abstract existence claim.
</output_contract>

<grounding_rules>
- Exact algebra only (rationals / codim counts / monomialised radial integrals). Floats never prove a threshold.
- The RLCT of a loss over a domain is governed by the deepest singular stratum reachable within the domain's closure.
- "Exactly j small singular values of hsQ" caps how degenerate (Qp;Qb) can jointly be within S_j.
- A domination LHS <= K*RHS with both sides sharing an RLCT still needs K finite; K finite is NOT implied by equal RLCTs.
</grounding_rules>
</task>
