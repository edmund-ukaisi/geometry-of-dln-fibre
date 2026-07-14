<task>
Adjudicate a GENERALITY-SCOPE question for a recursive proof that a certain box integral is finite for ALL layer-width vectors ("chains") M. Answer three sub-questions in either direction, WITH exact reasoning. Do NOT assume my conclusion — I am withholding it. Flag every step FACT vs INFERENCE.
</task>

<setup>
Fix a chain M = (M0, M1, M2, ..., ML) of positive integers (widths of a deep linear network). The DLN loss at target 0 is loss_M(A) = ‖A0·A1·...·A_{L-1}‖_F^2 where A_i is an M_i × M_{i+1} real matrix (so the product is M0 × ML). The "box integral" is I(M, c') = ∫_{box} loss_M(A)^{-c'} dA over the cube of all matrix entries in [-1,1]. The target ("(□)") is: I(M, c') < ∞ for every c' < ½·minAdm(M), where minAdm(M) is a combinatorial codimension.

TWO CITED FACTS (established, not to re-derive):
  (F1) Watanabe universal bound: the real log-canonical threshold rlct(loss_M) ≤ ½·codim = ½·minAdm(M).
  (F2) Aoyagi exact DLN computation: rlct(loss_M) = ½·minAdm(M).
  Consequence: I(M,c') < ∞ for all c' < ½·minAdm(M) is TRUE (the theorem). The project is trying to RE-PROVE this directly via a recursion (NOT by citing F2), to replace the opaque cited step.

COMBINATORIAL FACT (landed): minAdm is permutation-invariant in the widths: minAdm(M∘σ) = minAdm(M) for any permutation σ. It is defined by the layer-peeling recursion
  minAdm(M0,...,ML) = min_{0≤t≤min(M0,M1)} [ (M0−t)(M1−t) + minAdm(t, M2, ..., ML) ].

THE RECURSION being formalised: strong induction on chain arity. To prove I(M,·)<∞ for every (L+1)-width chain M, assume it for every L-width chain, then a single "peel" of the FRONT two widths (M0,M1) at a binding cut u★ (the t achieving the min above) reduces to the (one-shorter) reduced chain redChain(u★,M) = (u★, M2, ..., ML). The peel splits the front matrix A0 (M0×M1) by its rank; the MAIN sector is rank = u★, and the "off-sector mountain" is the sum over shells where rank(A0-block) = u = u★+j, j≥1, with row/col coranks a = M0−u, b = M1−u.

THE OFF-SECTOR MOUNTAIN BOUND (the piece under scrutiny): on shell j the current proof bounds the shell's contribution by a "corank weight"
  W = ∫_{A_cor ∈ box(b×M2)} det( (A_cor·Z_deep)(A_cor·Z_deep)^T )^{−a/2} dA_cor,
where Z_deep = A1·A2·...·A_{L-1} is the M2×ML "deep tail product" and A_cor is a b×M2 block of A0. Standard matrix-integral fact (please verify): W < ∞ iff rank(Z_deep) > a+b−1, i.e. rank(Z_deep) ≥ a+b.

THE SHELL only CERTIFIES a floor on rank(Z_deep): because the shell condition lives on the M1-row product Z_full = A0·Z_deep (M1×ML), Ky-Fan/Weyl gives that the shell forces at most m = min(M1, ML) − j strong directions of Z_deep. So the bound W converges iff m ≥ a+b.

NUMERIC FINDING (exhaustive over M ∈ [2..5]^{4,5}, all binding cuts, a,b≥1): for L≥1, m = min(M1,ML)−j ≥ a+b holds for ALL chains with M2 ≤ M1 (57/57), and FAILS for exactly the M2 > M1 wide chains (7/64), e.g. M=(4,3,4,4): binding u★=1, off-sector u=2 gives a=2, b=1, m = min(3,4)−1 = 2 < a+b = 3. At L=0 (deep tail is a single width, Z_deep = identity, full rank) it always converges.
</setup>

<questions>
Q1 (REACHABILITY). In this FRONT-peeling arity recursion, is the M2 > M1 regime genuinely reachable at the point where the off-sector mountain is invoked? The inductive STEP is universally quantified over every (L+1)-width chain M. Does that mean a wide chain like M=(4,3,4,4) is a legitimate input whose off-sector mountain must be discharged — or is there a structural reason the divergent (a,b,j,M2>M1) combination never actually arises at a binding cut? Reason from the recursion + binding-cut structure.

Q2 (PERMUTATION-INVARIANCE COVER). minAdm is permutation-invariant, and a wide chain M=(4,3,4,4) sorts to a chain like (4,4,4,3) where M2 ≤ M1 (mountain converges). Can the permutation-invariance of the CODIM be leveraged to transfer the FINITENESS of the box integral I(M,c') from a sorted chain to the wide chain — i.e. is there a measure-preserving change of variables (or base-change symmetry) making I(M,·)<∞ ⟺ I(M∘σ,·)<∞ directly? Note: permuting interior widths changes the parameter-space DIMENSION (Σ M_i M_{i+1} differs), and changes the product's shape. Is integral-finiteness perm-invariance obtainable WITHOUT going through the codim/RLCT (which would be circular with what (□) is proving)? Adjudicate: is Q2 a valid cover, or circular/unavailable?

Q3 (BOUND ARTIFACT vs WALL). Given F1+F2, the TRUE total integral I(M,c') is finite; and the off-sector shell contribution is a NON-NEGATIVE sub-piece of that finite total, hence itself finite. So is the "divergence" on M2>M1 shells necessarily a BOUND ARTIFACT (the corank-weight bound W is too lossy because the shell-certified floor m = min(M1,ML)−j undercounts the TRUE rank(Z_deep), which is generically min(M2,ML) ≥ a+b on the wide family)? If so, would a FINER stratification — stratifying Z_deep DIRECTLY by its own rank ρ (rather than the shell floor from Z_full), and recursing on the low-ρ sub-loci which carry positive codimension — recover a convergent bound? Or is there a genuine obstruction making even the true shell integral divergent (a WALL)? Sketch what the finer stratification would need.
</questions>

<output_contract>
- For each of Q1, Q2, Q3: a direct verdict + the load-bearing reason, FACT vs INFERENCE tagged.
- Verify (or correct) the matrix-integral fact "W < ∞ iff rank(Z_deep) ≥ a+b" and the Ky-Fan floor m = min(M1,ML)−j.
- For Q3, state whether the divergence must be a bound artifact given F1+F2 + nonnegativity, and what a finer Z_deep-rank stratification concretely requires.
- End with the single most likely way your own analysis is wrong.
</output_contract>

<grounding_rules>
- Ground in the setup facts + standard singular-value / matrix-integral / RLCT theory. Do not invent project-specific lemmas.
- If a claim is standard, name the mechanism (Ky-Fan/Weyl, Wishart/matrix-argument-gamma convergence, resolution of singularities / RLCT additivity).
- Distinguish "the true integral is finite" from "this particular bound shows it".
</grounding_rules>
