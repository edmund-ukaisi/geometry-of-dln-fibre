<constraints>Do NOT run shell commands or read files. Answer from mathematical reasoning ALONE
(read-only exec, no approval). Fully specified below.</constraints>

<task>
Red-team the GEOMETRIC PREMISE of a joint-rank-sector RLCT descent. Argue whichever way; I have NOT told
you my expected answer. Real matrices; frobSq = sum of squared entries.

A "hard cell" has an energy `frobSq(F · G)` where F is a FRONT factor integrated over a box and G encodes
reduced-chain leading data. Two front shapes:
 (W) WIDE F = [P | B12] (u×M1, P u×u invertible, B12 u×b), with G = [Qp; Qb] = [z0; A_cor]·Zdeep (M1×n),
     and the identity frobSq(P·(Qp + P⁻¹B12·Qb)) = frobSq([P|B12]·[Qp;Qb]) (VERIFIED exact numerically).
 (T) TALL F = [P; C] (M0×M1, P u×u, C a×u, u=M1), with frobSq(P·Qp)+frobSq(C·Qp) = frobSq([P;C]·Qp)
     (VERIFIED exact). The corank block is empty here (b=0).

THE DESCENT (premise to red-team):
 (P1) Reorganize the energy as `frobSq(F·G)`, LINEAR in the joint front F (no affine drop).
 (P2) Stratify a rank r of G (or of the corank block A_cor·Zdeep); each stratum reduces to a SHORTER chain
      redChain(u'_r), carrying a Gram determinant to an induction. Two Gram integrals arise, and the CLAIM
      is they are DIFFERENT objects:
      (a) CORANK Gram: ∫_{A_cor box} det((A_cor·Zdeep)(A_cor·Zdeep)ᵀ)^{−a/2} dA_cor — a "strong-block"
          integral over the corank variable A_cor; finite iff a < ρ−b+1 (ρ=rank Zdeep). FAILS at the "edge"
          a+b=ρ+1 (a=ρ−b+1 exactly, giving a<a false — a boundary logarithm).
      (b) PIVOT Gram: det(Q̃ₚ Q̃ₚᵀ)^{−a/2} (Q̃ₚ the u×n pivot block) integrated over the REDUCED-CHAIN
          parameters z (NOT over A_cor) — CLAIMED to be absorbed by the reduced chain's own recursion (the
          induction hypothesis), because det(Q̃ₚQ̃ₚᵀ) is the reduced chain's leading-layer Gram singularity.
 (P3) min over strata of [charge_r + minAdm(redChain u'_r)] = minAdm(M) (the minAdm recursion).

QUESTIONS.
Q1. Is (P1) sound and rank-preserving — does reorganizing to the joint linear front F change the RLCT vs
    the original coupled energy? Any hidden Jacobian/measure factor from the P⁻¹ (wide) or the stacking (tall)?
Q2. Is the (a)-vs-(b) distinction REAL and correctly stated — i.e. is the corank Gram (over A_cor,
    condition a<ρ−b+1, failing at the edge) genuinely a DIFFERENT integral from the pivot Gram (over the
    reduced z, absorbed by the IH)? Is "carry the pivot Gram to the IH, do NOT do a separate corank
    strong-block for the hard/edge cells" the correct reading of the trap — or is there a case where the
    pivot Gram ALSO needs a separate convergence condition (not absorbed by the IH)?
Q3. Biggest soundness risk in (P1)-(P3) for a formaliser about to build it? Name the single cheapest exact
    check that would most reduce the risk.
</task>

<output_contract>
Q1: VERDICT (sound / hidden factor) + the exact Jacobian if any. Q2: VERDICT (distinction real / conflated)
+ when the pivot Gram is/ isn't IH-absorbed. Q3: the one biggest risk + cheapest check. Decisive; flag
inference vs proven.
</output_contract>

<grounding_rules>Distinguish PROVEN from INFERENCE. Do not assume my expected answer. Name extra hypotheses.</grounding_rules>
