<task>
Adjudicate whether a divisibility-with-continuous-quotient identity can hold. Exact algebra; flag
FACT vs INFERENCE. Do NOT rubber-stamp; verify the necessary-condition argument independently.
</task>

<context>
Polynomial ring ℝ[u] in the flat coordinates of a deep-linear-network resolution. At a specific node,
three objects (all exact polynomials / a monomial):
 - F_i (i=0..3): the four entries of  coreGen ∘ foldG_child  (coreGen = entries of the matrix product
   A2·A1·A0; foldG = the composed FULL block blow-ups along the branch).
 - resid_j (j=0..3): the four foldResid_child slots (the fold's residual).
 - b := foldB_child = u_000 · u_011   (a squarefree monomial in two COORDINATES).

The claimed invariant (StepInv), for SOME functions q_ij CONTINUOUS on a region V that INCLUDES the
locus b=0 (the exceptional divisor — the RLCT lives there):
    F_i(u) = Σ_j q_ij(u) · ( b(u) · resid_j(u) )   for all u ∈ V, all i.

COMPUTED FACTS (exact, on witness d=(2,2,2,2); identical on (2,3,2,2)):
 - b = u_000 · u_011.
 - Polynomial ideal membership F_i ∈ ⟨ b·resid_j : j ⟩ : slots 1,3 TRUE; slots 0,2 FALSE.
 - Divisibility of F_i by b (i.e. F_i|_{u_000=0}=0 AND F_i|_{u_011=0}=0): slots 1,3 TRUE; slots 0,2 FALSE
   (slots 0,2 are NOT divisible by b).
 - The "pointwise" q_ij = δ_ij (i.e. F_i = b·resid_i) is FALSE for all i.
 - Whole-product Σ_i F_i² ∈ ⟨ b·resid_j ⟩ : FALSE.
</context>

<questions>
1. Can the StepInv identity hold for slot i=0 (F_0 NOT divisible by b) with q_0j CONTINUOUS on V∋{b=0}?
   Argument to check: RHS = b·(Σ_j q_0j·resid_j); let Q := Σ_j q_0j·resid_j (continuous on V). Then
   F_0 = b·Q on V, so where b≠0, Q = F_0/b. For Q continuous across b=0 (b = u_000·u_011 a product of
   two coordinate hyperplanes), must F_0 be divisible by u_000 and by u_011? Is "continuous divisibility
   by a coordinate = polynomial divisibility" correct here (bounded near the hyperplane ⟹ the coordinate
   divides)? Conclude whether q continuous can exist when b ∤ F_0.
2. Does allowing q CONTINUOUS (not polynomial) create ANY escape that the polynomial ideal-membership
   check misses, GIVEN b is a coordinate monomial? Or is the polynomial check both necessary and
   sufficient here?
3. Could restricting V to avoid {b=0} rescue it — and is that legitimate for an RLCT statement whose
   content is precisely the behavior along the exceptional divisor b=0?
4. Bottom line (one sentence): does the raw StepInv ∃(continuous)q HOLD or FAIL at this node?
</questions>

<output_contract>
- Verdict on Q1 with the necessary-condition argument checked (or corrected). Q2 necessary+sufficient
  ruling. Q3 the V-restriction legitimacy. Q4 one-sentence bottom line. FACT vs INFERENCE flagged.
</output_contract>

<grounding_rules>
Exact algebra. The RLCT (real log-canonical threshold) is a local invariant at/near the singular locus;
a statement whose region excludes the exceptional divisor would not compute it. Justify any divisibility
or continuity claim.
</grounding_rules>
