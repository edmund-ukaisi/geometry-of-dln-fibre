<task>
I am fidelity-reviewing a Lean 4 formalisation of a block-matrix Schur-complement identity.
Verify it faithfully encodes the intended math. Answer from first principles; do NOT trust my framing.

DEFINITIONS (a chain of 2x2-blocked matrices over a commutative ring; layer s has an r-by-r pivot block
in the (1,1) position and a core block; width family m: ℕ → Type):
  C : (s:ℕ) → Matrix (r ⊕ m s) (r ⊕ m (s+1))
  partProd C 0 = 1 (identity),  partProd C (k+1) = partProd C k * C k
     [so partProd C k = C_0 * C_1 * ... * C_{k-1}, the product of the FIRST k layers, EXCLUSIVE]
  blockSchur P = P.toBlocks₂₂ - P.toBlocks₂₁ * inverse(P.toBlocks₁₁) * P.toBlocks₁₂
     [(1,1)-block Schur complement; inverse is a TOTAL ring inverse = the honest inverse when pivot invertible]
  Kcoup C k = (C k).toBlocks₂₁ * inverse((partProd C (k+1)).toBlocks₁₁) * (partProd C k).toBlocks₁₂
  coreProd C 0 = 1,  coreProd C (k+1) = coreProd C k * (1 - Kcoup C k) * blockSchur (C k)

THEOREM (claimed, under: every layer pivot (C k)₁₁ invertible for k<L, every partial-product pivot
(partProd C k)₁₁ invertible for k≤L):
  blockSchur (partProd C L) = coreProd C L

INTENDED INFORMAL IDENTITY (a "cert", with INCLUSIVE partial products P_k = C_0*...*C_k):
  Sch(C_0·C_1·…·C_{L−1}) = S_0·(1−K_1)·S_1·(1−K_2)·S_2·…·(1−K_{L−1})·S_{L−1}
  where S_s = Sch(C_s) is the per-layer (1,1)-block Schur complement,
  and K_k = (C_k)₂₁ · (P_k)₁₁⁻¹ · (P_{k−1})₁₂  with inclusive P_k = C_0·…·C_k.

QUESTIONS:
1. Index bridge: is the Lean "Kcoup C k" (using EXCLUSIVE partProd) equal to the cert's "K_k" (using
   INCLUSIVE P_k)? Check for an off-by-one. (Note cert P_k = partProd C (k+1), cert P_{k-1} = partProd C k.)
2. Leading term: does Kcoup C 0 = 0, and does the unrolled coreProd C L therefore recover the cert product
   that LEADS with a bare S_0 (no (1-K_0) factor)? Unroll coreProd C 3 explicitly and compare term-by-term
   with the cert's S_0(1-K_1)S_1(1-K_2)S_2.
3. Hypotheses: are "every layer pivot k<L" and "every partial-product pivot k≤L" the correct, minimal
   invertibility hypotheses this recursion needs (given it is proved by folding the two-factor step
   Sch(G0·G1) = Sch(G0)·(1-K)·Sch(G1), K = (G1)₂₁·(G0·G1)₁₁⁻¹·(G0)₁₂, which itself needs G0₁₁, G1₁₁, (G0·G1)₁₁
   all invertible)? Are they over-strong (forcing vacuity) or too weak (making the claim false)?
4. Any other fidelity gap between the Lean theorem and the intended identity.
</task>

<output_contract>
For each of the 4 questions: a one-word verdict (FAITHFUL / OFF-BY-ONE / TOO-STRONG / TOO-WEAK / GAP)
followed by <=3 sentences of justification. Then a final one-line overall verdict: FAITHFUL or the list
of issues. Be terse.
</output_contract>

<grounding_rules>
Distinguish what you PROVE algebraically (state it as derived) from what you INFER about intent.
If a claim needs a computation, do the computation (e.g. unroll coreProd C 3). Do not assume my
index bridge is correct — re-derive it. Flag any step you cannot verify.
</grounding_rules>
