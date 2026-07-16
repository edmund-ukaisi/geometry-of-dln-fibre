<task>
A deep-linear-network RLCT question. Fix integers u>=1, a>=1, b>=1, and a "deep width chain"
(w_0=M2, w_1, ..., w_L=n) with rho := min(w_0,...,w_L). Let Z be the generic product of the deep
layer matrices (an M2 x n matrix, generic rank rho). Consider the LOCAL integrability, for exponent
q, of a "deep-factor" integrand near a degeneration where rank(Z) drops:

  integrand = det(Q_b Q_b^T)^{-a/2} * frobLoss^{-q},
    Q_b = A_cor . Z   (b x n; A_cor is a free b x M2 matrix, integrated over a box),
    frobLoss = |y|^2 + (residual of a free u x M2 "front" F acting through the LOST singular
               directions of Z), i.e. loss ~ ||F.Z||^2 with F free (u rows).
  measure = Lebesgue on the deep layer matrices, on A_cor, and on F.

A prior analysis handled the COMPARABLE case: all k lost singular values of Z scale like a single
scale t -> 0. It found the per-stratum effective codimension (the radial exponent controlling
finiteness, converges iff 2q < C_k)
    C_k = min( u*rho , u*(rho-k) + kappa_k - gamma_{rho-k} ),
    kappa_k = parameter-space codim of {rank Z <= rho-k}  (composite-rank codim; for a single deep
              matrix = (M2-(rho-k))(n-(rho-k))),
    gamma_s = max_{max(0,b-s)<=h<=min(b,k)} h*(a+b-s-h)   (an A_cor-integral charge exponent),
and concluded C_k >= minAdm(M0,M1,deep) - a*b over a large finite scan, where minAdm is the DLN
codim (min over intermediate ranks: minAdm(x0,x1,rest)=min_t (x0-t)(x1-t)+minAdm(t,rest),
minAdm(x0,x1)=x0*x1), and a=M0-u, b=M1-u for the ambient chain M=(M0,M1,deep).

QUESTION. Consider instead NON-COMPARABLE / HIERARCHICAL degenerations: the k lost singular values
(and, for a MULTI-LAYER deep chain, the different layers) go to zero at DIFFERENT rates -- e.g. one
block ~ t, another ~ t^2, so their singular values are not comparable as t->0. Does there exist such
a hierarchical degeneration whose honest effective codimension (RLCT-codimension = 2 * RLCT) is
STRICTLY LESS than the comparable-case C_k -- and if so, can it drop below minAdm(M) - a*b?
Equivalently: is the single-scale radial model the worst case, or can a multi-scale (toric / Newton
polyhedron) resolution produce a smaller effective codimension?

Please REASON IT OUT (do not just trust the finite scan). In particular:
  (1) For a SINGLE deep matrix Z (so kappa_k is determinantal), set up the honest multi-scale RLCT
      of loss = ||F.Z||^2 (F free u x M2, Z free M2 x n) at a rank drop, using the singular-value
      coordinates of Z with their Vandermonde Jacobian prod_{i<j}|s_i^2-s_j^2| prod s_i^{|M2-n|}.
      Compute the RLCT via the min over rays s_i = tau^{e_i}. Does the hierarchical (unequal e_i)
      resolution lower the codim below the single-scale value? To what value does it bottom out?
  (2) Is there a clean closed form for that honest RLCT-codim of ||F.Z||^2 over 0 (reduced-rank
      regression)? Relate it, if possible, to minAdm of the chain (u, M2, n).
  (3) For a MULTI-LAYER deep chain, consider "layer i degenerates as t^{c_i}" (uniform within each
      layer, different c_i across layers). Compute the effective codim of such a cross-layer ray and
      compare to min_i(layer-dimension) and to minAdm.
  (4) Decide: can any hierarchical degeneration make the deep-factor finiteness FAIL for some
      q < (minAdm(M)-a*b)/2 that the comparable model said was safe? Give the sharpest reason.
</task>

<output_contract>
- State clearly for (1)-(4): FACT (proved/derived) vs INFERENCE vs GUESS.
- Give the honest RLCT-codim of ||F.Z||^2 (single matrix) and its closed form if you find one.
- Concrete numbers for at least one worked case (e.g. u=3, M2=n=4).
- A final one-line verdict: can a hierarchical degeneration undercut minAdm(M)-a*b, YES or NO, and
  the single sharpest reason.
</output_contract>

<grounding_rules>
- This is a decorrelated second opinion; argue it from scratch. Do NOT assume the finite scan is
  right. If you think the single-scale model is an over- or under-estimate, say which and why.
- RLCT here = real log canonical threshold; effective codim = 2*RLCT; convergence of int f^{-q} for
  q < RLCT. Newton-polyhedron RLCT is exact for non-degenerate f but can OVER-estimate the true RLCT
  for degenerate f (e.g. bilinear/product structure) -- keep that distinction sharp.
- minAdm is the deep-linear-network fibre-over-0 codimension; the reduced-rank/Aoyagi result is
  rlct = codim/2.
</grounding_rules>
