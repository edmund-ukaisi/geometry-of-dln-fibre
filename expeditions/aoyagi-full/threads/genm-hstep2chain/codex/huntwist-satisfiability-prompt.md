<task>
Red-team a Lean-formalisation claim: a specific "germ" that a banked reduction reduces a goal to is
FALSE (unsatisfiable), even though the reduction itself is a valid implication. I need an independent
check of the underlying non-commutative matrix algebra.

SETTING (deep linear network RLCT formalisation). At a rank-r "deepest point" the loss RLCT reduces to
comparing two functions via `rlctAtOn`. There is a per-layer 2x2 block structure over `Fin r ⊕ (core)`.
For each layer s the "reindexed decode layer" is a block matrix
    Chat_s = fromBlocks (A_s) (Y_s) (Z_s) (T_s)
with (1,1)-block A_s = deepBlkA_s + X_s, where deepBlkA_s is a FIXED invertible r×r "deepest constant"
(NOT the identity; discriminator has deepBlkA=3), and X_s,Y_s,Z_s,T_s-part are small "gauge reads"
(→ 0 at the basepoint). The honest product P = Chat_0 · Chat_1 · … · Chat_{L-1} equals the reindexed
network product, and the target "Score" is
    Score(x) = ‖ blockSchur(P) ‖²_F,  where blockSchur(M) = M22 − M21·(M11)^{-1}·M12.

There is a BANKED, machine-verified general recursion (call it schur_product_ldu_rec):
    blockSchur(P) = coreProd,   coreProd = S^conj_0 ·(1−K̂_1)· S^conj_1 ·…·(1−K̂_{L-1})· S^conj_{L-1}
with the HONEST per-layer Schur cores  S^conj_s = blockSchur(Chat_s) = T_s − Z_s·A_s^{-1}·Y_s
(pivot A_s = deepBlkA_s + X_s), K̂_s = Kcoup of the honest chain, K̂_0 = 0. This is TRUE.

THE GERM ("huntwist"). A banked bridge reduces the RLCT goal to (a ∀-eventually-near-basepoint pointwise
matrix/energy identity):
    frobSq( prod_s ( (1 − K_s) · S^naive_s ) ) = Score(x)
where the cores are the NAIVE ones produced by the actually-wired "coreAbsorb":
    S^naive_s = t_s − Z_s·(1 + X_s)^{-1}·Y_s          (pivot 1 + X_s, i.e. deepBlkA_s replaced by 1)
(t_s is the raw core-slot decode = T_s at boundary layers). The map Ψ that produces (1−K_s)·S^naive_s is a
per-layer LEFT multiplication S ↦ (1−K_s)·S, and K must satisfy K_s(basepoint)=0 and be continuous/smooth.

MY CLAIM (to be red-teamed): huntwist is FALSE for every admissible coupling K, because a per-layer LEFT
shear cannot convert the naive cores S^naive (pivot 1+X) into the honest cores S^conj (pivot deepBlkA+X),
and S^naive_s and S^conj_s differ at FIRST ORDER in the reads (their difference
Z_s·A_s^{-1}·Y_s − Z_s·(1+X_s)^{-1}·Y_s ≈ (deepBlkZ_s·deepBlkA_s^{-1} − Z_s)·Y_s is O(read), since
deepBlk constants are O(1)). Hence near the basepoint frobSq(prod((1−K)S^naive)) and Score have different
leading (2nd-order) quadratic parts, so the identity fails in every neighborhood.

NUMERICAL EVIDENCE (L=2, r=1, all core-blocks 1×1, random rational reads, deepBlkA_0=3, deepBlkA_1=2):
    Score = blockSchur(P)                       = 0.0651
    prod((1−K̂)·S^naive), K̂ = honest Kcoup      = 0.1816   (≠ Score)
    blockSchur(naive product ∏ fromBlocks(1+X,Y,Z,t)) = 0.2119   (≠ Score)
The repo's own prior L2 work also states (docstring): "bare Ψ + conjugate absorb ≠ Score" — the L2 proof
therefore used TWO steps: Step Θ (an RLCT bridge between a CONJUGATE core-absorb, pivot deepBlkA+X, and the
NAIVE one) ∘ Step Ψ_conj (a CONJUGATE per-layer shear on the conjugate cores). The general banked bridge
provides only ONE step with the NAIVE core-absorb.

<output_contract>
Answer in <=6 short sections, in this order:
1. VERDICT: Is huntwist (as stated, naive cores, single per-layer left-shear, K(basepoint)=0, continuous)
   satisfiable by ANY admissible K? YES / NO / UNSURE, one line.
2. The single cleanest reason (the algebraic obstruction, or if you disagree, the mechanism that rescues it).
3. Is there ANY continuous K with K(basepoint)=0 s.t. frobSq(prod((1−K)S^naive)) = frobSq(blockSchur(P))
   holds in a NEIGHBORHOOD of the basepoint? Give the decisive first/second-order argument (treat reads &
   core coords as small; deepBlk constants O(1)).
4. Do you agree the correct fix is: (a) use the CONJUGATE core-absorb S^conj in the Ψ step, plus (b) a
   separate Step-Θ RLCT bridge naive↔conjugate — i.e. the general bridge must mirror the L2 two-step,
   and the single-naive-Ψ bridge is structurally insufficient? AGREE / DISAGREE + one line.
5. Any way I'm wrong (e.g. frobSq/energy being weaker than matrix equality could be exploited; or the
   ∀-eventually could hold despite pointwise mismatch)? Flag the strongest counter to my claim.
6. Confidence (0-1) that huntwist is unprovable as stated.
</output_contract>

<grounding_rules>
This is pure non-commutative matrix algebra + a germ/Taylor argument; reason from the given structure.
Mark any step that assumes commutativity or scalar-only (my numerics are scalar; the real problem is
matrix/non-commutative — state if your argument is scalar-only vs general). Distinguish "I derived this"
from "plausible". Do NOT trust my numbers blindly; if a step needs a matrix (non-scalar) check to be
decisive, say so.
</grounding_rules>
