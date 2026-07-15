<task>
Real-analysis / algebraic-geometry adjudication for an RLCT (real log canonical threshold)
finiteness question in deep-linear-network fibre geometry. I have WITHHELD my tentative
conclusion; argue whichever way the mathematics points. This gates a Lean formalisation route.

SETUP (a change-of-variables finiteness gate). A layer chain M = (M0, M1, M2, ..., M_last),
arity L. At a BINDING cut u = t*+j (t* = argmin of the layer recursion; strict shell 1<=j<r),
set a = M0-u, b = M1-u. The deep factor Z = product of the deep layers of widths (M2,...,M_last),
an M2 x n matrix (n = M_last); generic rank rho = deepTailMin = min(M2,...,M_last). It is a FACT
(established) that at binding strict shells a+b <= rho-1, so d := rho - b >= a+1 >= 2.

The front-charge integrand (already reduced) is, over the front variables x=(P,B,C) with P in GL_u
and z0 (u x M2), A_cor (b x M2):
    frontChargeIntegrand = det(Q_b Q_b^T)^{-a/2} * (E_top + E_tr)^{-q},   q = c' - a*b/2,
with Q_p = z0*Z (u x n), Q_b = A_cor*Z (b x n), E_top = ||P*Q_p + B*Q_b||_F^2,
E_tr = ||C*(Q_p + P^{-1} B Q_b)(I - Pi_b)||_F^2, Pi_b = projector onto row(Q_b).
The whole thing is integrated over (z_tail building Z, z0, A_cor, x).

TARGET THRESHOLD. Let 2*T1_q := minAdm(M) - a*b, where minAdm(M) = min over cuts of the QIP
recursion (for a 3-chain minAdm(m0,m1,m2) = min_r[(m0-r)(m1-r) + r*m2]; general: minAdm(M) =
min_t[(M0-t)(M1-t) + minAdm(t, M2,...,M_last)]). We need the integral finite for every q < T1_q,
i.e. we need: at EVERY degeneration stratum, the local codimension (the exponent threshold: the
integral converges for 2q < codim) is >= 2*T1_q = minAdm(M) - a*b.

THE STRATA (new content beyond the generic-Z front resolution, which is already known to give the
generic threshold minAdm(M)-a*b). The deep factor Z can drop rank: {rank Z = rho - k}, k=1..rho.
Two established sub-facts:
 (i) parameter-space codimension of {rank(deep product) <= rho-k} in the deep-layer parameters:
     call it kappa_k. It equals the "composite-rank-locus codim" CR((M2,...,M_last), rho-k),
     given by the recursion CR((v0,...,vp),s) = min_{0<=r<=min(v_{p-1},v_p)}
        [(v_{p-1}-r)(v_p-r) + CR((v0,...,v_{p-2},r), s)], base CR((v0,v1),s)=(v0-s)(v1-s)_+;
     and CR(chain, 0) = minAdm(chain). (I have verified this codim recursion numerically.)
 (ii) at a rank-(rho-k) drop, with the k lost singular values scaling like a small parameter t,
      the corank determinant charge behaves as det(Q_b Q_b^T) ~ t^{2*max(0, k-d)}, because Q_b's
      b-dim row space needs b directions and the surviving (rho-k) columns of Z supply only
      min(b, rho-k) of them; when b > rho-k (i.e. k > d) the remaining (k-d) come from the
      t-scaled columns, so (k-d) singular values of Q_b are O(t). (I have verified this exponent
      exactly by log-log slope.) Hence the charge det^{-a/2} ~ t^{-a*max(0,k-d)}.

THE QUESTION. Build the local model at a rank-(rho-k) drop and compute the EXACT local codimension
of frontChargeIntegrand INCLUDING the det charge, then determine whether it can fall below
2*T1_q = minAdm(M) - a*b for some k (which would be a genuine finiteness gap / a wall), or whether
it is always >= 2*T1_q (bounded).

Specifically:
 (Q1) Set up the local RLCT model at the rank-(rho-k) drop: the loss (E_top+E_tr) in adapted
      coordinates, the det charge factor, and the deep-degeneration measure (codim kappa_k). What
      is the exact convergence threshold (codim-with-charge) at each k? Show the polar/monomial
      blow-up arithmetic. In particular treat the FULL COLLAPSE k=rho (Z->0), where the charge is
      maximal (det ~ t^{2b}, charge ~ t^{-ab}) and kappa_rho = CR((M2,...,M_last), 0) =
      minAdm(M2,...,M_last).
 (Q2) Is there any (M, binding cut, k) with codim-with-charge < minAdm(M) - a*b (a genuine gap)?
      In particular, at full collapse the condition reduces to a comparison between two integers
      -- identify which two, and whether the inequality can fail.
 (Q3) Note the SEPARATE fact (established): under a global scaling Z -> r*Z, frontChargeIntegrand
      scales as r^{-(ab+2q)} while a bare comparator (delta^2 ||Q_p||^2)^{-q} scales as r^{-2q}, so
      their RATIO diverges like r^{-ab} at Z->0. Does this ratio-divergence imply the INTEGRAL
      diverges, or only that a bare-comparator domination fails? Distinguish clearly.

<output_contract>
Three sections, terse and decisive:
1. THE CODIM-WITH-CHARGE at a rank-(rho-k) drop: the exact threshold as a function of
   (u, rho, b, a, kappa_k, k), with the blow-up arithmetic. State the full-collapse (k=rho) value.
2. VERDICT: BOUNDED (codim-with-charge >= minAdm-ab at every k) or GENUINE GAP (a witness k where
   it undercuts). If bounded, identify which stratum is the binding one and the clean integer
   inequality that guarantees it. If a gap, give the witness chain/cut/k.
3. The ratio-vs-integral distinction (Q3): does r^{-ab} ratio-blowup kill finiteness or only the
   domination route?
</output_contract>

<grounding_rules>
Flag inference vs. established fact. Do NOT assume the conclusion I want -- I have deliberately
withheld it. If the codim-with-charge depends on a modelling choice (e.g. whether the k lost
singular values are comparable vs hierarchical, or whether the loss coupling is |y|^2 + t^2|W_lost|^2),
state which choice you make and whether it is the worst case. If you find a genuine gap, say so
plainly; if bounded, give the tightest inequality and where it would first fail if widths grew.
</grounding_rules>
</task>
