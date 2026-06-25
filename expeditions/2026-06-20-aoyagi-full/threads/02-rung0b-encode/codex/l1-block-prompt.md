<task>
Lean 4 + Mathlib v4.29 proof strategy (diagnosis, not code) for the matrix block-normal-form lemma.

FROZEN STATEMENT (prove exactly):
  theorem block_elimination (H : Fin (L + 1) → ℕ) (r : ℕ)
      (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r) :
      ∃ (P : Matrix (Fin (H 0)) (Fin (H 0)) ℝ)
        (Q : Matrix (Fin (H (Fin.last L))) (Fin (H (Fin.last L))) ℝ),
        IsUnit P ∧ IsUnit Q ∧
          P * B * Q = Matrix.of (fun i j => if (i:ℕ) = (j:ℕ) ∧ (i:ℕ) < r then (1:ℝ) else 0)

i.e. over ℝ, a rank-r matrix is equivalent (via invertible P, Q) to the block-normal form diag(E_r, 0).
This is "matrix equivalence ⟺ equal rank" over a field. I searched: Mathlib v4.29 does NOT seem to
package this directly (no Matrix.exists_mul_mul_eq_blockDiagonal, no SNF over a field as matrices).

What I found that EXISTS: Matrix.rank, rank_reindex, mulVecLin, LinearMap.toMatrix, rank-nullity
(finrank_range + finrank_ker = domain), Basis.toMatrix / basis change-of-basis, LinearMap.toMatrix'.
</task>

<output_contract>
1. The cleanest route. Candidates I'm weighing — rank them:
   (A) Linear-map picture: realize B as toMatrix of mulVecLin; pick a domain basis whose last (b−r)
       vectors span ker and first r map to an image basis, extend image basis to codomain basis; then
       P,Q are the change-of-basis matrices and P·B·Q = toMatrix in the good bases = block-normal.
       Which exact Mathlib lemmas glue "toMatrix in basis e,f" to "P_basis · B · Q_basis"? (the
       basis-change conjugation: LinearMap.toMatrix_..., basisToMatrix_mul / Basis.toMatrix_mul_...)
   (B) Is there a Mathlib lemma giving the existence of such bases directly from rank = r
       (e.g. a basis adapted to a subspace / quotient: Submodule.exists_..., Basis.ofSplit, the
       exact-sequence splitting)? Name it if it exists.
   (C) Pure matrix Gaussian elimination (build P,Q as products of elementary matrices). Likely worst.
2. The exact statement-matching hassle: my RHS is `Matrix.of (fun i j => if i=j ∧ i<r then 1 else 0)`.
   The natural normal form from route (A) is "1 iff f.symm i = e (something) and index < r" — what's
   the cleanest way to land EXACTLY this `if (i:ℕ)=(j:ℕ) ∧ (i:ℕ)<r` shape? (reindex along an equiv that
   sorts the r image-basis vectors first.)
3. Honest size estimate (helper-lemma count). If route (A) is ~150 lines, say so and give the staging.
4. Any v4.29 API name you cite that you are NOT certain of — flag it; I will rg-verify.
</output_contract>

<grounding_rules>
Separate KNOWN Mathlib API from INFERENCE. Do not invent lemma names. If the honest answer is "Mathlib
lacks a one-shot lemma; this is a genuine construction", say so and give the minimal decomposition.
</grounding_rules>
