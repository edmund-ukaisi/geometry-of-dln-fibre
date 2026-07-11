<task>
An exact finiteness question about an inner integral in a resolution-of-singularities computation for
deep linear networks. Adjudicate exactly and adversarially — I need to know whether a proposed
"integrate the Schur block first" reduction is VALID uniformly, or breaks on a degenerate locus.

SETUP (one pivot chart of a matrix-product loss). Fix integers p >= 1 (= M0 - t), b >= 1 (= M1 - t),
n >= 1 (= M_last). Data:
  - Q_b : b x n  (a fixed matrix, = the "corank rows" of a deeper matrix PRODUCT A1...A_{L-1}; it varies
    with the deeper parameters A'),
  - S : p x n    (a fixed shift matrix, = C * Qtilde_p, built from other chart data x),
  - w >= 0       (the "pivot energy" = ||P * Qtilde_p||^2, P an invertible pivot; fixed given x),
  - Gamma : p x b, integrated over a BOUNDED box (entries in [-1,1], possibly shifted).
The inner integral is
  J(w, S, Q_b) = ∫_{Gamma in box} ( w + || S + Gamma * Q_b ||_F^2 )^{-c'} dGamma.
Then the full object is  ∫_{A'} ∫_{x}  J(w(x), S(x,A'), Q_b(A'))  dx dA'  over bounded boxes, and we want
it finite for c' < (1/2) minAdm(M) (minAdm = the type-A quiver codimension of the chain).

The proposed reduction: change variables so that J becomes  det(Q_b Q_b^T)^{-p/2} * (a Morse residual in
w), reducing the whole thing to  I(a) = ∫ det(Q_b Q_b^T)^{-a/2} d(deeper params)  with a = p.

Answer, exactly:

Q1. Compute J(w,S,Q_b) exactly when Q_b has FULL ROW RANK b (so Q_b Q_b^T is positive definite; requires
    b <= n). Via the SVD of Q_b, show J = det(Q_b Q_b^T)^{-p/2} * R, and identify the residual R (a Morse
    integral over the IMAGE box, shifted by S, regularized by w). Confirm the det(Q_b Q_b^T)^{-p/2} weight.

Q2. THE CRUX. Now let Q_b be RANK-DEFICIENT, rank(Q_b) = r < b (this happens on a locus of the deeper
    params; if b > min(internal widths) it is GENERIC, not null). The map Gamma |-> Gamma*Q_b then has a
    p*(b-r)-dimensional KERNEL. Over the whole space R^{p x b} the integrand is constant along the kernel
    so the whole-space Gamma-integral is +infinity. But the box is BOUNDED. Questions:
      (a) Is J over the BOUNDED box finite when rank(Q_b) = r < b? What is the exact reduced form
          (a bounded kernel-volume factor times det^+(Q_b Q_b^T)^{-p/2} times a residual, where det^+ =
          product of the r NONZERO squared singular values)?
      (b) Does the reduction to the FULL det(Q_b Q_b^T)^{-p/2} weight still make sense (that weight is
          +infinity here), or must one use det^+ / a lower-rank Gram? Is "reduce to I(a)=∫det(Q_bQ_b^T)^{-a/2}"
          well-posed at all when rank Q_b < b generically?
      (c) As a MEASURE statement (integrate over the deeper params A', which pass through the
          rank-deficient locus), is ∫_{A'} J finite for c' < (1/2)minAdm even though the pointwise
          det-weight blows up? What is the correct majorant that is finite uniformly across the bottleneck?

Q3. THE PIVOT. Is the pivot energy w LOAD-BEARING, or can it be dropped? Concretely: does J with w>0 stay
    finite where J with w=0 would diverge (on the rank-deficient / degenerate directions)? A valid majorant
    of the integrand ( w + E )^{-c'} needs a LOWER bound on the base; dropping w (base = E) or dropping E
    (base = w) — do either give a finite majorant of ∫∫ uniformly, or must the full (w+E) be kept? Get the
    correct majorant and say exactly which term rescues the degenerate directions.

Worked instances: (p,b,n) = (2,2,4) full-rank; and a rank-deficient Q_b (e.g. Q_b = Y*A2 with Y 2x1,
A2 1x4, so rank Q_b = 1 < b = 2) — the "narrow internal width" bottleneck.
</task>

<output_contract>
For each Q1-Q3: PROVEN/DERIVED exact statement (mark inference vs fact). J's closed form in both the
full-rank and rank-deficient regimes. A clear YES/NO on whether the "reduce to I(a) = full det-Gram" is
valid uniformly (and if not, the correct det^+ / majorant). A clear YES/NO on whether the pivot w is
load-bearing (droppable or not), with the term that rescues the degenerate directions. If the reduction
breaks on the bottleneck, say so precisely and give the correct replacement.
</output_contract>

<grounding_rules>
Exact algebra (sympy/by-hand). For J, use the SVD of Q_b and integrate the transverse coordinates
explicitly; keep the box BOUNDED (do not extend to R^{p x b} — that is the known over-counting trap). MC
only to guide. Do NOT read my expectation into the answer — I have deliberately not said whether I think
the reduction holds uniformly; hunt for where it breaks.
</grounding_rules>
