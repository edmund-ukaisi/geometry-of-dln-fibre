Self-contained math question. Answer from this prompt ONLY; do NOT read/search files. Be concise
(the reasoning can be brief); prioritise reaching a VERDICT.

Setup: F is u x m (free), Z is m x n (free), loss = ||F Z||_F^2. RLCT lambda = sup{q : int_ball loss^{-q} < inf};
effective codim = 2*lambda. Also a "charge" det(A Z Z^T A^T)^{-a/2} (A free b x m, integrated) multiplies the
integrand. minAdm(chain) = DLN fibre-over-0 codim: minAdm(x0,x1,rest)=min_t (x0-t)(x1-t)+minAdm(t,rest),
minAdm(x0,x1)=x0*x1. Known (Aoyagi): the RLCT-codim of ||F Z||^2 over 0 equals minAdm(u,m,n).

Q1. At a rank-(rho-k) drop of Z (rho=min(m,n)), is the honest RLCT-codim of the loss, resolved via the k lost
singular values at DIFFERENT scales (Vandermonde measure prod|s_i^2-s_j^2| prod s_i^{|m-n|}), SMALLER than the
single-scale radial value u(rho-k)+ (m-(rho-k))(n-(rho-k))? To what value does the min-over-rays bottom out?
Guess: does it bottom out at minAdm(u,m,n)? Give the closed form for a single deep matrix.

Q2. For a deep chain that is a PRODUCT of several layers, a degeneration "layer i ~ t^{c_i}" (uniform within a
layer, different c_i): what is its effective codim, and is it >= min_i(layer-dim) >= minAdm? So do cross-layer
scale differences ever undercut minAdm?

Q3. VERDICT (one line): can any hierarchical/multi-scale degeneration make the honest deep RLCT-codim drop
BELOW minAdm(M0,M1,deep) - a*b, where a=M0-u, b=M1-u? (Hint to check: is minAdm(u,m,...,n) >= minAdm(M0,M1,...,n)
- a*b always? relate to the t=u term of the minAdm recursion.) YES or NO + sharpest reason.
