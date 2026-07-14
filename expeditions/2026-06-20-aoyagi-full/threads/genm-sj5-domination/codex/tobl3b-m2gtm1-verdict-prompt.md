<task>
Give a PROSE verdict (do NOT run any code — reason from the facts). Adjudicate three sub-questions about a generality gap in a recursive finiteness proof. I am WITHHOLDING my conclusion. Tag each step FACT vs INFERENCE.
</task>

<setup>
A recursion proves "box integral I(M,c') < ∞ for c' < ½·minAdm(M)" for every layer-width chain M=(M0,...,ML), by strong induction on chain arity, peeling the FRONT two widths (M0,M1) at a binding cut t★. The peel's "off-sector mountain" is the sum over shells of rank u=t★+j (j≥1) of the front block, with coranks a=M0−u, b=M1−u.

On each off-sector shell the current bound reduces the contribution to a "corank weight"
  W = ∫ det((A_cor·Z_deep)(A_cor·Z_deep)^T)^{−a/2} dA_cor  (A_cor is b×M2; Z_deep = A2·...·A_{L-1}, the deep-tail product M2×ML).
STANDARD FACT: W < ∞ iff rank(Z_deep) ≥ a+b.

The current proof sources the floor on rank(Z_deep) from a SHELL on the FULL product Z_full = A0·Z_deep (an M1×ML matrix). Ky-Fan/Weyl then certifies only m = min(M1,ML)−j strong directions of Z_deep. NUMERICS: for wide chains (M2>M1, L≥1) this m < a+b (e.g. M=(4,3,5,5), t★=1, off-sector u=2: a=2,b=1, m=min(3,5)−1=2 < 3). So the corank-weight BOUND diverges there. (Cited RLCT facts: rlct = ½·minAdm and Watanabe rlct ≤ ½·codim ⟹ the TRUE total integral I(M,c') is finite for c'<½·minAdm.)

A BANKED combinatorial theorem is available: at a nondegenerate binding cut t★ (a★=M0−t★≥1, b★=M1−t★≥1), EVERY front-peel co-minimizing "deep rank" ρ of the reduced chain (t★,M2,...,ML) — the rank of Z_deep on the top-dimensional component of the reduced zero-locus — satisfies ρ ≥ a★+b★−1. Since an off-sector sits at u=t★+j with a=a★−j, b=b★−j, we get a★+b★−1 = a+b+(2j−1) ≥ a+b+1 for j≥1. (Numeric check, 713 shells: the co-minimizer ρ ≥ a+b on ALL shells where the Ky-Fan floor m < a+b — zero exceptions.)
</setup>

<questions>
Q1 REACHABILITY: The inductive step is universally quantified over EVERY ≥3-width chain M. Is the divergent (M2>M1) regime therefore genuinely reachable (a wide chain like (4,3,5,5) is a legitimate step input), or does the binding-cut structure forbid the (a,b,j) combination from ever arising? Verdict + reason.

Q2 PERMUTATION-INVARIANCE: minAdm is permutation-invariant, so sorting a wide chain gives a narrow one where the mountain converges. But permuting interior widths changes the parameter-space dimension (Σ Mi·Mi+1 differs) and the product shape. Can the finiteness of the box integral be transferred from a sorted chain to a wide one by a measure-preserving change of variables — i.e. is integral-finiteness permutation-invariance available WITHOUT going through the codim/RLCT (which would be circular with what the recursion proves)? Verdict: valid cover, or circular/unavailable?

Q3 BOUND-ARTIFACT vs WALL, and the FIX: Given the true integral is finite and the off-sector is a nonnegative sub-piece of it, must the divergence be a BOUND ARTIFACT (the Ky-Fan Z_full-shell floor m under-counts the true deep rank)? And does the banked co-minimizer bound (ρ ≥ a★+b★−1 > a+b at off-sectors) mean the CORRECT fix is simply to SOURCE the deep rank from the co-minimizer / a shell on Z_deep DIRECTLY (rather than the Ky-Fan floor from Z_full) — making this a re-plumbing of banked pieces rather than fresh analytic content? Or is there a genuine obstruction (e.g. the co-minimizer's ρ is the rank on ONE component, not the a.e. rank the shell integral needs)? Sketch the residual precisely.
</questions>

<output_contract>
- Q1, Q2, Q3: direct verdict + load-bearing reason, FACT/INFERENCE tagged.
- For Q3, state carefully whether "ρ = deep rank on the top-dim reduced component" is the same quantity that controls W's convergence a.e. over the shell, or whether a residual (low-ρ sub-loci) remains — and if so whether it is bounded/recursion-closable or a wall.
- End with the single most likely way this analysis is wrong.
</output_contract>

<grounding_rules>
- Reason from the setup + standard singular-value / matrix-integral (Wishart) / RLCT-additivity theory. Name mechanisms.
- Distinguish "true integral finite" from "this bound shows it".
- Do NOT run code. Prose only.
</grounding_rules>
