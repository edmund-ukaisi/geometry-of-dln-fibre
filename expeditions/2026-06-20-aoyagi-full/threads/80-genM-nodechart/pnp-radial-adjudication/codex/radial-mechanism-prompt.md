<task>
We are designing a Lean formalisation of a Jacobian-determinant headline for an "achiever chart" of a
deep-linear-network multiplication-fibre RLCT computation. We need an INDEPENDENT analysis of how the
chart's Jacobian determinant factors, specifically how the radial blow-up direction is structured.
Do NOT assume our framing is right; derive the structure yourself from the data below.
</task>

<context>
A width tuple M = (M_0, ..., M_L) gives a flat parameter space R^N, N = flatDim = sum_s M_s * M_{s+1}.
An "achiever chart" phi : R^N -> R^N is built from a structured decoder. Its semantics:
- a scalar "radial pivot" coordinate u (one of the N coords),
- per-layer matrices A_0,...,A_{L-1} built recursively from blocks:
    C_L = u * Rfin           (the deepest "live leaf" block; Rfin a small matrix of free coords),
    C_k = Bmat_k * chainQ(Nblk_k) + u * Rmat_k     (interior boundaries; chainQ(N)=[I | N]),
    A_k = [ C_{k+1} - Nblk_k * Wblk_k ;  Wblk_k ]   (kept rows over lift rows),
  where Bmat_k carries an LDU-coordinatized "K-core", Nblk/Wblk are chaining/lift free coords,
  and Rmat_k / Rfin are the "u-scaled" blocks (the pivot u multiplies these entries).
- The flat chart is the concatenation of all entries of A_0..A_{L-1}.

There is an integer invariant minAdm(M) (a min-codimension from an Aoyagi-style layer-peeling recursion).
Examples computed EXACTLY (sympy, exact rationals):
  M=(2,2,2):   N=8,  minAdm=3,  |det Dphi| = |u|^2 * |b|       (one genuine rank-drop boundary)
  M=(3,3,3,3): N=27, minAdm=6,  |det Dphi| = |u|^5 * (boundary, u-free)
  M=(2,3,2):   N=12, minAdm=4,  |det Dphi| = |u|^3 * |b|^3

In each case the pivot u appears to power exactly minAdm - 1.
</context>

<data>
Define a "pivot blow-up" map pivotBlowupOn(active, p) : R^N -> R^N by
   x_i -> x_p           if i = p
   x_i -> x_p * x_i      if i in active, i != p
   x_i -> x_i            otherwise.
Its Jacobian determinant is exactly x_p^(|active| - 1).

EXACT sympy facts we have established:
1. At M=(3,3,3,3): the set of coordinates k for which the chart output contains a monomial term
   "u * x_k" (the pivot times a single free coord) is exactly {13,14,24,25,26}. These are precisely the
   free entries of the u-scaled blocks Rmat_2 (entries 13,14) and Rfin_3 (entries 24,25,26).
   Taking active = {pivot} ∪ {13,14,24,25,26} (cardinality 6 = minAdm), pivotBlowupOn's det = u^5,
   and  (full chart det) / u^5  is completely u-FREE (= u1^4 * u4^2 * u9^3).
2. At M=(2,2,2): active = {pivot} ∪ {free Rmat entry, free Rfin entry} has cardinality 3 = minAdm,
   pivotBlowupOn det = u^2, and chart det / u^2 is u-free.
3. At M=(2,3,2): active = {pivot} ∪ {2 free Rmat entries, 1 free Rfin entry} = cardinality 4 = minAdm,
   pivotBlowupOn det = u^3, chart det / u^3 is u-free.
</data>

<questions>
Q-A. Given the recursion C_L = u*Rfin and C_k = Bmat_k*chainQ(N_k) + u*Rmat_k, the pivot u enters the
     chart ONLY linearly multiplying entries of the Rmat_k / Rfin blocks. Is it therefore a theorem that
     the full chart Jacobian determinant factors as u^(D) * (a u-free remainder), where D = total number
     of free scalar entries in all the u-scaled blocks (Rmat_k and Rfin)? Derive whether D = (number of
     u-scaled free entries), and whether the "u-free remainder" claim must hold in general or could fail.
     Identify any hypothesis needed (e.g. the K-core / Bmat / Wblk blocks being u-INDEPENDENT).

Q-B. Is the identity  1 + (number of free u-scaled entries) = minAdm(M)  forced, or is it a coincidence
     of these three examples? Reason about what "minAdm" counts (the codimension of the deepest achiever
     stratum / the order of vanishing of the squared loss) and whether the u-scaled DOF count must equal
     it. If you think it can fail for some M, give the M and the mechanism.

Q-C. Could there be an M where the pivot u multiplies a PRODUCT of two free coords (u*x_j*x_k) or appears
     QUADRATICALLY (u^2 * ...) in some chart entry, which would break the single-pivot-blow-up radial
     model (forcing the u-handling into a per-boundary block rather than one clean radial layer)? Reason
     from the recursion structure (C_k = Bmat*chainQ + u*Rmat, and the kept/lift split) about whether
     u can ever appear non-linearly or multiply two free coords in a chart output.
</questions>

<output_contract>
For each of Q-A, Q-B, Q-C: a direct verdict (forced / can-fail / needs-hypothesis), the mechanism/derivation,
and — if can-fail — the explicit M and where it bites. Mark clearly what is a proof vs a heuristic.
</output_contract>

<grounding_rules>
Reason from the recursion structure given. The sympy facts above are exact (not floats). Do not rubber-stamp;
if the general claim is weaker than the 3 examples suggest, say so and bound it.
</grounding_rules>
