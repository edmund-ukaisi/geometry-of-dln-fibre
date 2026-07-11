<task>
You are red-teaming a claim in the singularity theory (RLCT / real log canonical threshold)
of deep linear networks (DLN). I need you to HUNT for a counterexample. Withhold agreement;
try hard to BREAK the claim, and if you cannot, tell me the precise mechanism that forbids it.

SETUP (self-contained; standard determinantal / matrix-product geometry over R).
A DLN "chain" is a tuple of layer widths M = (M0, M1, ..., ML), with independent real matrix
layers A_k of shape M_k x M_{k+1}. The "deeper product" of a sub-chain c = (n0, n1, ..., nk) is
P = A_0 A_1 ... A_{k-1}, an n0 x nk matrix; its generic rank is r = min(n0,...,nk) (a narrow
internal width is a BOTTLENECK that caps the rank structurally).

Define minAdm(M) recursively (this is the paper's codimension = the QIP minimum):
  minAdm(M) = min over t in [0, min(M0,M1)] of [ (M0-t)(M1-t) + minAdm(t, M2, ..., ML) ],
  base: minAdm(u,n) = u*n, minAdm(single node) = 0.
Define cCodim(c; rho) = codim { rank(product of chain c) <= rho } in the real factor-parameter
space (Lebesgue). Fact (rank-shift): cCodim(c; rho) = minAdm(c - rho) where each width is
reduced by rho.

THE BOX-INTEGRAL RLCT of a DLN chain equals (1/2) minAdm(M) (this is Aoyagi's theorem, taken as
GROUND TRUTH). We are checking whether a particular RESOLUTION (an iterated corner blow-up / (S,J)
descent) is FAITHFUL, i.e. reproduces (1/2) minAdm without any sub-region undershooting it.

THE RESOLUTION decomposes the loss integral by the corank q of the deeper product P (q smallest
singular values collapse; rho = r - q survive). On the corank-q cell it forms a COUPLED CORNER
whose per-cell RLCT threshold is claimed to be
    (1/2)(D_q + d_q),   with   d_q = M0 * rho   (front charge on surviving directions),
                                D_q = cCodim(P; rho)   (product-rank tube codimension).
The local corner model is  F = u0^2 * U0 + u1^2 * U1  with the "pivot Gram minor"
U0 = sigma_min(P)^2 (smallest singular value squared) vanishing along the rank-drop tube, and the
one-tube reduction gives  lambda = n1/2 + (1/2) min(n0, D/m),  where n0 = the front charge that
flows into the collapsing direction, D = codim (tube dimension) of the rank-drop locus, and
m = order of vanishing of U0 transverse to the tube.  "No collapse" (full value (1/2)(D_q+d_q))
requires the charges to ADD (not take a MIN): i.e. D/m >= n0.

QUESTIONS (hunt hard; exact algebra, not hand-waving):

Q1. Can the pivot Gram minor U0 = sigma_min(P)^2 vanish to order m > 1 (i.e. U0 ~ dist^{2m},
    2m > 2) along the ENTIRE binding rank-drop tube of a DLN product P (possibly with a
    bottleneck), at a GENERIC point of that tube? If yes, exhibit the chain + the tube; that would
    make D/m < D and risk a collapse (the x^2(x^2+y^{2N}) mechanism). If no, give the exact reason.

Q2. Can the coupled corner take a MIN instead of ADD for some anisotropic / higher-corank
    (q >= 3) DLN tube -- i.e. the resolution's per-cell threshold falls BELOW (1/2)(D_q+d_q)?
    Consider bottleneck chains where the deeper product is structurally rank-capped
    (e.g. (M0, 4, 2, 4), (5,2,5), (2,5,2,2,5), (7,2,2,2,7)). Exhibit a collapsing cell or explain
    why the corner always adds.

Q3. Is min over q of (D_q + d_q) always = minAdm(M) with the GEOMETRIC (Lebesgue-pushforward)
    cCodim, or can the geometric tube codimension be STRICTLY SMALLER than the algebraic cCodim
    (a "fat vanishing" a bottleneck could produce), so that D_q < cCodim and a cell undershoots?

Q4. Net: name a concrete DLN chain (widths) + a specific binding rank-drop branch where the
    resolution's per-branch RLCT threshold is STRICTLY LESS than (1/2) minAdm -- OR prove no such
    branch exists and give the single load-bearing geometric reason (the relation between the
    rank-drop tube codimension and the pivot-minor vanishing order for matrix PRODUCTS).
</task>

<output_contract>
Four sections Q1..Q4. For each: a definite YES (with an explicit chain + exact tube + the
undershoot) or NO (with the exact mechanism). End with a one-line verdict:
"COLLAPSE FOUND: <chain>" or "NO COLLAPSE: <one-line reason>". Be adversarial; prefer a concrete
counterexample over agreement. Keep exact algebra (minors, singular-value orders, codims) explicit.
</output_contract>

<grounding_rules>
- Aoyagi's rlct = (1/2) minAdm is GROUND TRUTH; a genuine collapse below it would mean the
  resolution is UNFAITHFUL, so diagnose WHICH object is misread (D, m, or the branch's binding-ness).
- Determinantal ideals over a field are radical (Hochster-Eagon); use this where relevant but
  check it survives the PRODUCT / pushforward structure.
- Distinguish a single 1-D ray U0 -> 0 (NOT decisive) from the full tube DIMENSION/measure.
- Do not trust my framing blindly; if n0, D, m are mis-defined, say so.
</grounding_rules>
