<task>
Adjudicate a singularity-resolution / RLCT question about "zero-product" integrals of deep-linear
networks. This is exact real-analysis / algebraic-geometry-of-singularities, not code.

SETUP. A "3-width chain" is a triple (x,s,z) of positive integers. Two real matrices A0 (shape x×s)
and A1 (shape s×z). The "loss" is L(A0,A1) = ‖A0·A1‖_F^2 (squared Frobenius norm of the product,
which is an x×z matrix). We integrate over a fixed cube box (say [-1,1]^{xs} × [-1,1]^{sz}):

    I(c) = ∫_box  L(A0,A1)^{-c}  dA0 dA1.

DEFINE minAdm(x,s,z) = min over integers t in [0, min(x,s)] of [ (x-t)(s-t) + t·z ].
It is a THEOREM (Aoyagi; take as given) that the real-log-canonical threshold equals ½·minAdm(x,s,z),
i.e. I(c) < ∞ for c < ½·minAdm(x,s,z) and I(c) = ∞ for c > ½·minAdm(x,s,z). We only care about the
FINITENESS direction: prove I(c) < ∞ for every c < ½·minAdm(x,s,z).

A "WAIST" is a chain with s < min(x,z) (a strict interior minimum). Minimal example (2,1,2)
[minAdm=2, threshold 1]. Others: (3,1,3) [minAdm=3], (3,2,3) [minAdm=5, threshold 5/2],
(4,2,4) [minAdm=8].

THE CANDIDATE PROOF ROUTE ("head-split / front-peel"), and WHY IT FAILS ON WAISTS.
The generic finiteness proof peels the FRONT layer A0. Pick the binding t=t★ (the minimizing cut).
Write A0 in a block chart with a t×t invertible pivot block P; the top t "pivot rows" of the product
A0·A1 are [P | B12]·A1, an t×z matrix (B12 is the t×(s-t) off-diagonal front block). The proof needs
the FRONT integral ∫ over (P,B12) of ‖[P|B12]·A1‖^{-2c''} to be finite up to c'' < ½·minAdm(t,z) =
½·(t·z) (the "reduced comparator" charge). BUT the linear map (P,B12) ↦ [P|B12]·A1 has rank
= t·rank(A1) = t·min(s,z) = t·s (on a waist s<z, A1 has full row rank s). So this front integral only
converges for c'' < t·s/2 < t·z/2. This is a genuine gap of t·(z-s): the front variables (only t·s of
them mapping into the t×z target) CANNOT deliver codimension t·z; they factor through rank(A1)=s and
lose the extra z-s columns. Numerically confirmed: on (3,2,3) at t★=1, front charge = t·s = 2 but the
comparator needs t·z = 3.

THE PROPOSED FIX ("route A", direct rank-stratification of the deep layer + Morse codim-rescue).
Instead of routing everything through the small front pivot, STRATIFY by rank(A1) = k (k = 0..s),
cover the box by shells {rank(A1) ≈ k}, and bound each shell separately, then sum. The intent:
- On shell k, the zero-product locus stratum {A0·A1=0, rank(A1)=k} has codimension
  (s-k)(z-k) + x·k, and min over k of this = minAdm(x,s,z) (reversal-equivalent to the min over t).
- The x·k part ("A0 vanishes on the k-dim colspace of A1") is x·k CLEAN linear equations on A0
  (a genuine full-rank Morse integral, no rank-collapse) — apparently NO front-pivot gap.
- The (s-k)(z-k) part is the determinantal codimension of {rank(A1)=k}, handled by a Morse/AM-GM
  "corner" codim-rescue: the small singular values of A1 give squared-norm blocks whose Morse
  integrals converge when their codimension is large enough.
There is a BANKED lemma (call it qPeel) that proves finiteness of a "corner slice" of the form
    ∫_{u∈[0,1]^q} (Σ_i u_i²·‖X_i‖²)^{-c'} · Π_i |u_i|^{h_i}   integrated over deep blocks X_i∈ℝ^{m_i+1},
finite for c' < ½·Σ_i(h_i+1) PROVIDED the per-block "codim gate" h_i ≤ m_i holds for every i (weighted
AM-GM at weights w_i=(h_i+1)/Σ, then Tonelli factors into u-marginals + per-block Morse integrals).
The gate h_i ≤ m_i is the analog of "the pivot does not wall": a Jacobian power h_i must be backed by a
deep block of dimension ≥ h_i+1.

WHAT I NEED YOU TO ADJUDICATE (either direction — do NOT assume the fix works).
1. Is the loss ‖A0·A1‖^{-2c}, restricted to a neighborhood of the BINDING rank-drop shell
   {rank(A1)=k★} (k★ the minimizing k) on a waist, resolvable into a convergent qPeel-style
   corner slice at threshold ½·(shell codim) = ½·minAdm, with ALL per-block codim gates h_i ≤ m_i
   satisfied? Or does the COUPLING between "A0 vanishes on the moving colspace of A1" and "A1 near
   rank k★" obstruct the decoupling — i.e. does a codim gate fail (the front-pivot wall recurring in
   a new guise), or does some Jacobian power exceed its block's available codim?
2. Concretely work (3,2,3) (binding k★=1, x=z=3, s=2, minAdm=5, threshold 5/2) and (2,1,2)
   (rank-1, minAdm=2, threshold 1) and if possible a longer waist (3,1,3) or (4,2,4): set up the local
   resolution near the binding stratum, identify the radial (u_i) directions, the deep Morse blocks
   (X_i) and their dimensions m_i, the Jacobian powers h_i, check Σ(h_i+1) = minAdm and each h_i ≤ m_i.
3. Is there a genuinely-NEW obstruction that neither the front-peel NOR this direct rank-stratified
   route resolves with elementary (weighted-AM-GM + Morse + Tonelli + determinantal-shell) machinery?
   In particular: does the coupling force a NON-normal-crossings singularity that needs a genuine
   (iterated / toric) resolution rather than a single corner slice? For a waist with s≥2 (so A1 near
   rank k★ is a genuine determinantal singularity, not a smooth point), is the "(s-k)(z-k) determinantal
   codim" deliverable by a single Morse/AM-GM corner, or does IT need its own recursive resolution
   (a nested peel), and if so does that nested peel itself hit a waist / a gate failure?

VERDICT REQUIRED: CLOSES (the waist is dischargeable by direct rank-stratification + banked
Morse/corner machinery + finite summation of shells; give the shell design, the per-shell block
dims/Jacobian powers, and confirm the gates) OR WALL (the direct route hits a specific obstruction no
elementary re-expression routes around; name the exact obstruction and why it is not the front-pivot
wall in disguise).
</task>

<output_contract>
Respond in this order, terse and exact:
A. Verdict token on line 1: exactly "CLOSES" or "WALL" (or "CLOSES-WITH-CAVEAT: <one line>").
B. The (3,2,3) binding-shell resolution worked explicitly: local coordinates near {rank(A1)=1,
   A0·A1=0}; the radial directions; the deep Morse blocks with their dimensions m_i and Jacobian
   powers h_i; the arithmetic Σ(h_i+1) =? 5 and the gate checks h_i ≤? m_i. If a gate fails, say which
   and by how much.
C. (2,1,2) and one longer waist ((3,1,3) or (4,2,4)) checked the same way, briefly.
D. The general (x,s,z) waist statement: does the shell-sum reconstruct minAdm with all gates satisfied
   for every waist, or is there a family where a gate fails? Give the general gate inequality.
E. The determinantal sub-question (item 3): is {rank(A1)=k} codim (s-k)(z-k) deliverable by a single
   corner, or does it need a nested resolution — and does that nesting terminate without a new wall?
F. If CLOSES: the one lemma most likely to be the genuinely-new (non-banked) analytic content.
   If WALL: the single sharpest obstruction, and whether reversal / permutation symmetry evades it.
</output_contract>

<grounding_rules>
- Exact rational / integer arithmetic for all codimensions, thresholds, ranks, Jacobian powers.
  Distinguish a proven inequality from a plausibility argument; flag every inference.
- The RLCT value ½·minAdm is GIVEN (Aoyagi). Do NOT re-derive it; the question is purely whether the
  FINITENESS half is reachable by the direct rank-stratified Morse/corner route on WAISTS.
- Treat "does a codim gate fail" as the crux — the front-peel already fails by exactly t·(z-s); the
  question is whether the direct route's gates (h_i ≤ m_i) hold where the front-peel's did not.
- Do not defer to authority or to me; if you think the direct route also walls, say WALL and prove it.
</grounding_rules>
