<task>
I am adjudicating a resolution-of-singularities question for a deep-linear-network (DLN) real-log-canonical-threshold computation. I need a DECORRELATED second opinion. Do NOT try to guess "the intended answer"; reason from scratch and give me the exact algebra.

SETUP. Fix a chain of positive integers M = (M0, M1, M2, ..., ML). Define recursively
   minAdm(M) = 0                             if len(M) <= 1
             = M0 * M1                        if len(M) == 2
             = min over t in {0,...,min(M0,M1)} of [ (M0 - t)(M1 - t) + minAdm( (t, M2, ..., ML) ) ].
This is a quadratic-integer-program value (the codimension of a DLN fibre component).

A "peel at level t" pays a source-rank-drop charge (M0 - t)(M1 - t) = codim{ rank(front) <= t } for the M0 x M1
front, then recurses on the reduced chain (t, M2, ..., ML). Set the peel corank (a,b) = (M0 - t, M1 - t) and
d = min(a,b).

THE INTEGRAL. On a pivot chart (a specific t x t minor of the front F is invertible, so F has full row/col rank
t = min(M0,M1)), the relevant local model integrand near a source-rank-drop stratum is, schematically,
   ( w  +  || Delta . C . Z ||_F^2 )^(-c)
where:
   - Delta is a FREE r x k block, r = M0 - t, k = M1 - t  (the "exceptional" corank block);
   - C is a FREE k x M2 block;
   - Z = prod(deep layers) is an M2 x q matrix that is itself a PRODUCT of further free matrices (it can drop rank);
   - w >= 0 is a positive "core" (a pivot energy, bounded below on the sphere after a radial blow-up);
   - || . ||_F is Frobenius norm; c is the exponent, and we integrate over finite boxes.

QUESTIONS (answer each with exact algebra; state PROVEN / heuristic explicitly):

Q1. Integrating out the free block Delta against || Delta . (C Z) ||^2 (with Q := C Z, k x q): what residual
    weight in (C, Z) is left, and on what locus does it blow up? Express the blow-up locus in terms of rank(C Z).

Q2. Fix r = 1 (so Delta is a single row, 1 x k) but allow k >= 2. Show explicitly what || Delta . C . Z ||^2
    equals as a function of (Delta, C, Z), and determine the RANK of the matrix (Delta . C) as a function of r, k.
    Does the k x q product (Delta . C) . Z exhibit a genuine "product-corank" rank-drop variety
    { rank((Delta C) Z) <= rho } with BOTH factors (Delta C) and Z varying, or does it collapse to something
    simpler because of the r = 1 constraint? Be precise about the rank of (Delta C).

Q3. Contrast r = 1, k >= 2 with the case min(r,k) >= 2 (both r,k >= 2). In which of these is the singular locus
    of || Delta . C . Z ||^2 resolvable by a sequence of blow-ups of SINGLE-matrix rank-loci plus a rank-1
    "free-bilinear" leaf ( ||gamma||^2 * ||z^T Z||^2 ), and in which does it genuinely require resolving the
    rank-drop of a PRODUCT of two matrices each of rank >= 2 (the "generic determinantal product" resolution)?
    Give the exact boundary in terms of min(r,k).

Q4. Concretely: take the smallest wide case M0=2, M1=3, and the peel at t = 1 (so r=1, k=2), with M2 = 2 and one
    further free deep layer Z of shape 2 x 2 (chain M = (2,3,2,2)). Write the local model integral over
    (Delta in R^{1x2}, C in R^{2x2}, Z in R^{2x2}) with core w = ||B Z||^2 (B a free 1x2 row), and determine the
    convergence threshold c* (the value c below which the finite-box integral is finite). Compare 2 * c* to
    minAdm-style charge accounting. Is the resolution single-factor (blow-ups of single-matrix loci + free-bilinear)?

<output_contract>
For each of Q1-Q4: a short PROVEN/heuristic verdict line, then the exact algebra. For Q3 give the precise
boundary "single-factor iff min(r,k) <= ___". For Q4 give c* as an exact rational or an explicit inf, and state
whether a single-factor resolution certifies it. Flag any place where my schematic setup is ambiguous or where
the answer depends on a convention I did not pin.
</output_contract>

<grounding_rules>
Use exact algebra (ranks, codimensions, Cauchy-Binet, determinantal-variety codim (m-rho)(n-rho), radial /
projection integrals). Monte-Carlo only as a guide, and say so. If a claim needs a convention I did not fix,
state the convention and answer under it. Do not appeal to "the DLN literature says"; derive it.
</grounding_rules>
