<task>
Lean 4 + Mathlib v4.29. Finishing A3 (LDU-core Jacobian det). I have LANDED these (sorry-free):
- `lowerTri_det (f : M→ₗM)(g : N→ₗN)(h : M→ₗN) : det (lowerTri f g h) = f.det * g.det` where
  `lowerTri f g h : M×N→ₗM×N`, (m,n)↦(f m, g n + h m). [the 2-block lower-tri det]
- A1: `det_mulLeft_matrixSpace K : det (X↦K*X on Matrix(Fin t)(Fin c)) = K.det^c`;
      `det_mulRight_matrixSpace K : det (X↦X*K on Matrix(Fin r)(Fin t)) = K.det^r`.
- `matrixSplit : Matrix(Fin t)(Fin t) ℝ ≃ₗ LDUParam t` where
  `LDUParam t := (LowIdx t → ℝ) × (Fin t → ℝ) × (UpIdx t → ℝ)`,
  `LowIdx t := {p:Fin t×Fin t // p.2<p.1}`, `UpIdx t := {p // p.1<p.2}`.
  `matrixSplit M = (lower entries, diagonal, upper entries)`; `matrixSplit.symm w = lowMat w.1 +
  diagonal w.2.1 + upMat w.2.2`.
- The multiplicity count `∏_{p:LowIdx t} q p.1.2 = ∏ j, q j ^ (t-1-j)` (via Fin.card_Ioi + card_bij),
  and the scalar-scaling det `det (pi fun i => mulRight ℝ (w i) ∘ proj i) = ∏ w` (via det_pi).

GOAL. Define `lduCoreDeriv l q u : LDUParam t →ₗ LDUParam t` = `matrixSplit ∘ₗ lduCoreDerivMatrix l q u`
where `lduCoreDerivMatrix l q u (dl,dq,du) = lowMat dl * diag q * (1+upMat u) + (1+lowMat l) * diag dq
* (1+upMat u) + (1+lowMat l) * diag q * upMat du`, and prove
  `lduCoreDeriv_det : LinearMap.det (lduCoreDeriv l q u) = ∏ i, q i ^ (2*(t-1-i))`
(then `|det| = ∏ |q i|^(2(t-1-i))` by abs_prod/abs_pow). Independent of l,u (unit factors det 1).

THE SPECIFIC QUESTION: the cleanest Lean route for the DET COMPUTATION, given the above. My plan:
1. `det lduCoreDeriv = det (matrixSplit ∘ₗ lduCoreDerivMatrix)`. To compute, move to the matrix space:
   conjugate by the unit factors. Let `L' = 1+lowMat l` (unit-lower-tri, det 1), `U' = 1+upMat u`
   (unit-upper-tri, det 1). The map `mulLeft (L')⁻¹` and `mulRight (U')⁻¹` are det-1 (A1, since
   det L'⁻¹ = 1). After conjugating `lduCoreDerivMatrix` by them, the matrix map becomes
   `(dl,dq,du) ↦ (L')⁻¹·lowMat dl·diag q + diag dq + diag q·upMat du·(U')⁻¹`, where the first term is
   strictly-LOWER, second diagonal, third strictly-UPPER — so under `matrixSplit` it is BLOCK-DIAGONAL
   over (LowIdx, Fin t, UpIdx): lower-out←dl only, diag-out←dq only, upper-out←du only.
2. Then `det = det(lower block)·det(diag block: identity, det 1)·det(upper block)`. The lower block is
   `dl ↦ matrixSplit_lower((L')⁻¹·lowMat dl·diag q)`; since (L')⁻¹ is unit-lower, the strict-lower part
   of (L')⁻¹·lowMat dl equals lowMat dl's strict-lower part (the unit diag adds nothing NEW on the strict
   lower triangle? NO — (L')⁻¹·lowMat dl can fill lower entries from products). Hmm — is the lower block
   actually triangular-with-the-right-det, or do I need the strict-lower part to be exactly `dl scaled by
   q`? Worried the (L')⁻¹ mixing breaks the clean `∏ q` scaling.

QUESTIONS:
1. Is my plan-step-2 worry real? After conjugating by (L')⁻¹/(U')⁻¹, is the LOWER-output-block (as a map
   `dl ↦ lower-coords`) actually equal to a TRIANGULAR map (w.r.t. some order on LowIdx) with diagonal
   `q`-scaling = ∏ q_j^(t-1-j)? Or does the unit-factor mixing only make it block-triangular (so I still
   need a Leibniz/triangular-det argument on LowIdx, not just a product)? Give the precise reason.
2. If the lower-block is only block-triangular (not diagonal) over LowIdx, what is the cleanest Lean route
   to its det = ∏ q_j^(t-1-j)? (A `Matrix.det_of_lowerTriangular` over a linear order on LowIdx? Then I
   need an explicit matrix for the lower-block and its triangularity — back to index arithmetic.)
3. ALTERNATIVELY: is it cleaner to NOT conjugate, and instead evaluate at l=0,u=0 (L=U=1) where the map
   is manifestly diagonal-scaling, then prove det is independent of l,u separately (det lduCoreDeriv is a
   POLYNOMIAL in l,u that... no, det could depend on l,u a priori)? Is "det independent of l,u" easy
   (e.g. the l,u-dependence is a det-1 unipotent change of the SAME endomorphism up to conjugation)?
4. Your single cleanest recommended route for `lduCoreDeriv_det` in Lean v4.29, with the lemma chain.
   I want to MINIMIZE explicit-matrix index arithmetic. Be decisive and concrete.
</task>

<output_contract>
1. Answer Q1 (is the worry real) — yes/no + the precise reason, 2-3 sentences.
2. Answer Q2 or Q3 (whichever your route needs) concretely.
3. RECOMMENDATION: the single cleanest route + lemma chain (named v4.29 lemmas), ≤6 steps.
4. The single biggest remaining risk + how to pre-empt.
Terse. Name only lemmas you're confident exist in v4.29; flag others VERIFY.
</output_contract>

<grounding_rules>
Distinguish "exists" (fact) from "should work" (inference). Flag uncertain lemma names VERIFY.
Do not invent signatures.
</grounding_rules>
