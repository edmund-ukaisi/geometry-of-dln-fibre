<task>
Adjudicate the STRUCTURE of an "integrate-the-front-first" majorant step in a matrix-integral
finiteness proof. Answer 4 sharp sub-questions. Reason from exact algebra; give me your independent
verdict, not a rubber stamp. I withhold my own conclusion deliberately.
</task>

<setup>
Fix real 3x4 matrix P with singular values s1 >= s2 >= s3 >= 0 (Gram G = P Pᵀ is 3x3 PSD, eigenvalues
s1²,s2²,s3²). Fix c' > 0 (think c' just below 7/2). Define the FRONT integral over the free 3x3 box
A0 ∈ [-1,1]^{3×3}:

    g(P) := ∫_{A0 box} frobSq(A0 · P)^{-c'} dA0,   frobSq(M) = sum of squares of entries = ‖M‖_F².

Note frobSq(A0 P) = Σ_{j=1}^3 s_j² ‖(A0 Q)_{·j}‖²  after diagonalising G = Q diag(s²) Qᵀ and rotating
A0 ↦ A0 Q (measure-preserving on the box up to enclosing in a ball). Here (A0 Q)_{·j} ∈ ℝ³ (m0 = 3
rows). So g is a function of (s1,s2,s3).

CONTEXT (facts I have established; treat as given inputs, not to re-derive):
- A downstream banked Lean lemma ("LAYER 2") proves ∫_{tail box} σ_min(P)^{-a} dP < ∞ for every
  0 ≤ a < 1, where σ_min(P) = s3 (smallest singular value), and the tail box is the 2-factor product
  box P = A1·A2 (A1 3x3, A2 3x4). It does this via σ_min^{-a} ≤ C·det(G)^{-a/2} and a per-factor
  determinant integral. It ONLY handles the weight σ_min^{-a} with a<1.
- The intended "step (a)" is a pointwise-in-P bound of the form
      g(P) ≤ C · σ_min(P)^{-α'}   with  α' = 2c' - m0·(r-1) = 2c' - 6  (r=3, m0=3),
  which for c' < 7/2 gives α' < 1, so LAYER 2 would then integrate it.
- A separate exact analysis (Beta-reduction, Monte-Carlo confirmed) found: near the codim-1 rank locus
  {s3→0, s2≥κ}, g(P) ≍ s3^{-α}, α = max(0, 2c'-m0(q-1)) with q the corank. And the full composed
  integral ∫_{tail box} g(P) dP converges iff c' < ½·minAdm = 7/2, where the rank-(≤q-1) product tube
  has codim D_prod(q) and the "linchpin" minAdm = min_q [ D_prod(q) + m0(q-1) ] holds; for this tail
  D_prod = (8,4,1) at q=(1,2,3) and m0(q-1) = (0,3,6), so D_prod(q)+m0(q-1) = (8,7,7).
</setup>

<questions>
Q1 (global validity of the step-(a) bound). Does g(P) ≤ C·σ_min(P)^{-α'} with α' = 2c'-6 (< 1) hold
   for ALL P in the box, or only on a sector {s2 ≥ κ}? Compute the scaling of g(P) near the deeper
   rank locus where BOTH s2,s3 → 0 (say s2 = s3 = σ, s1 = O(1)). Give g ≍ σ^{-β2}; find β2. Is the
   bound g ≤ C·σ_min^{-α'} true or false there?

Q2 (is the deep stratum binding?). For each stratum "k smallest singular values ≍ σ" (k=1,2,3),
   give g ≍ σ^{-β_k} and the convergence condition of ∫_{stratum-k tube} g against tube codim D_k
   (use D_k for k=1,2,3 = D_prod at q=3,2,1 = 1,4,8). At which k does the integral first diverge as
   c' ↑? Are strata k=1 AND k=2 both binding at the same threshold, or only k=1?

Q3 (single global majorant?). Is there ANY weight W(P) that (i) dominates g(P) pointwise on the whole
   box AND (ii) is of a form LAYER 2 can integrate, i.e. σ_min(P)^{-a} or det(G)^{-a/2} with a<1?
   For each of those two forms, on the codim-2 stratum, what exponent 'a' would be forced, and is it
   < 1? Conclude whether a single global majorant of that restricted form exists.

Q4 (measurability, cheapest route). The sector {s2(P) ≥ κ} = {2nd-smallest singular value ≥ κ} =
   {at least two eigenvalues of G = PPᵀ are ≥ κ²}. In a proof assistant whose library has the
   char-poly / elementary-symmetric functions of G (continuous in P) and the operator norm (continuous)
   but LACKS continuity of individually-sorted eigenvalues, what is the cheapest way to show this set is
   Borel-measurable? Evaluate these candidate routes and pick the cheapest, or propose a better one:
     (a) ‖∧²G‖_op ≥ κ²·‖G‖_op  (exterior square / 2nd compound; ‖·‖_op = largest eigenvalue for PSD);
     (b) a sign-condition on the characteristic polynomial q(t)=det(tI−G) and q'(t) at t=κ² that counts
         "≥2 roots ≥ κ²";
     (c) something else.
</questions>

<output_contract>
For each Q1–Q4: a direct answer with the exact exponent/algebra, then one line "FACT" vs "INFERENCE".
End with: does the step-(a) majorant NEED a rank-stratum dichotomy (sector + complement), and if so is
the complement a genuinely separate integrability obligation or absorbed by the σ_min^{-a} weight?
</output_contract>

<grounding_rules>
Exact algebra only for the exponents (Beta-function / radial-measure scaling). Do NOT trust a float rank.
Keep "the integral of the bound diverges" separate from "the true integral diverges". If you find my
setup exponents wrong, say so and give the correction.
</grounding_rules>
