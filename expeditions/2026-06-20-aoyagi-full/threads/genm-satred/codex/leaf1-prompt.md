<constraints>Do NOT run shell commands or read files. Answer from mathematical reasoning ALONE
(read-only exec, no approval). The problem is fully specified below.</constraints>

<task>
Adjudicate a soundness/route question in a resolution-of-singularities RLCT reduction. Argue whichever way;
I have NOT told you my expected answer.

SETUP. Real matrices. A "deep" matrix Zdeep (M2×n) with rank ρ = its number of singular values ≥ some
threshold. A reduced-param box: z ranges over a box, giving a pivot block Qp = z0·Zdeep (u×n, z0 the u×M2
leading layer from z) and a corank block Qb = A_cor·Zdeep (b×n, A_cor a b×M2 box variable). Stack
G = [Qp; Qb] (M1×n, M1=u+b). Front outer blocks P (u×u), B12 (u×b) over boxes.

The front integral to bound (per fixed (z, A_cor)):
   I(z,A_cor) := ∫_{P,B12 boxes} frobSq([P|B12]·G)^{-c''}   (joint-linear front; [P|B12] is u×M1)
A banked lemma (D-B): for a LINEAR map L of rank r, ∫_{cube} frobSq(L·x)^{-c'} dx < ∞ iff c' < r/2, but
the VALUE is finite, NOT uniformly bounded in L (it blows up as L degenerates). The map (P,B12)↦[P|B12]·G
has rank u·rank(G) = uρ when G is full-rank-ρ.

The DIFFICULTY. A "shell" restricts the OUTER data so that prod = A'0·Zdeep (M1×n) has exactly j singular
values < ε (j≥1). hsQ = [z0;A_cor]·Zdeep is a ROW-PERMUTATION of prod, so shares its singular values — j of
them < ε. A proposed domain "pivotShell(ε) = {A_cor | hsQ·hsQ^T ⪰ ε²·1}" (ALL M1 singular values ≥ ε) is
therefore DISJOINT from the shell (j≥1). BUT the shell IS provably inside a FRAME good-set
G_frame(ε') = {weakEigCount_{ε'}(Zdeep) ≤ M2−m}, m = min(M1,Mlast)−j, at a RESCALED ε' ≤ ε/√(M1·M2)
(Ky-Fan: the shell's small singular values of A'0·Zdeep force ≤ M2−m small singular values of Zdeep, i.e.
Zdeep's top-m frame has singular values ≥ ε'). A frame selector gives Zf with Zf·Zf^T ⪰ ε'²·(m-frame
projection) UNCONDITIONALLY, and Zf = Zdeep on G_frame.

QUESTIONS.
Q1. Is the reduction "shell-integrand ≤ front-integral over (matBox ∩ pivotShell(ε))" SOUND, or FALSE for
    j≥1? If false, is the fix (a) drop pivotShell → integrate over the FULL matBox (moving all conditioning
    to the frame floor Zf·Zf^T ⪰ ε'²·m-frame), (b) a Ky-Fan reduction to a pivot-SUB-block (u×n, the top-u
    directions) floor rather than the full M1×M1 hsQ floor, or (c) pivotShell at the rescaled ε' (does the
    shell sit in {hsQ·hsQ^T ⪰ ε'²·1}?)? Rank the fixes.
Q2. Over the FULL matBox (fix a), does I(z,A_cor) admit a UNIFORM finite bound (a bare constant, uniform in
    z and A_cor), given ONLY the m-frame floor Zf·Zf^T ⪰ ε'²·(m-frame proj)? Note G = [Qp;Qb] can still
    degenerate (rank < ρ) as (z0, A_cor) → 0 even with the m-frame floored, since Qp=z0·Zf, Qb=A_cor·Zf.
    If NOT uniform, must the reduction carry a (z,A_cor)-dependent factor (e.g. det(G G^T)^{-·}) to a
    downstream induction, rather than a bare constant?
Q3. Net: is the "bare-constant front bound" (route α) RECOVERABLE for the shell (j≥1) by any conditioning
    domain the shell actually sits in, or does the shell-j (j≥1) mass INTRINSICALLY require the front bound
    to be a non-uniform factor carried to the induction (making a bare-constant route unsound for j≥1)?
</task>

<output_contract>
Q1: VERDICT (sound / false-for-j≥1) + rank the 3 fixes (best first, 1 line each). Q2: VERDICT (uniform /
not) + why, with the degeneration locus named. Q3: VERDICT (bare-constant recoverable / intrinsically
non-uniform for j≥1) + the single cheapest exact check. Be decisive; flag inference vs proven.
</output_contract>

<grounding_rules>
Distinguish PROVEN from INFERENCE. Do not assume my expected answer. Name any extra hypothesis a fix needs.
</grounding_rules>
