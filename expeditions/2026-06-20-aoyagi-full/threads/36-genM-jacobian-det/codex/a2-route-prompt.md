<task>
Lean 4 + Mathlib v4.29.0. I am building a parametric "Schur-frame Jacobian determinant" theorem.

SETUP. Fix naturals t, r, c. Consider the map (this is the differential DS, already linear in increments)
on the product of four real matrix spaces
  E := Matrix (Fin t) (Fin t) ℝ            -- dK block
     × Matrix (Fin t) (Fin c) ℝ            -- dN block
     × Matrix (Fin r) (Fin t) ℝ            -- dX block
     × Matrix (Fin r) (Fin c) ℝ            -- dE block
given fixed matrices X : Matrix (Fin r) (Fin t) ℝ, K : Matrix (Fin t) (Fin t) ℝ, N : Matrix (Fin t) (Fin c) ℝ.
The linear endomorphism D : E →ₗ[ℝ] E sends (dK, dN, dX, dE) to
  ( dK,
    K * dN + dK * N,
    dX * K + X * dK,
    dE + X*dK*N + X*K*dN + dX*K*N ).
(Block-LOWER-triangular: output i reads only earlier inputs plus its own diagonal action.)

GOAL theorem:  |LinearMap.det D| = |K.det| ^ (r + c).
The diagonal block actions are: dK↦dK (det 1), dN↦K*dN (det = K.det^c), dX↦dX*K (det = K.det^r),
dE↦dE (det 1). The off-diagonal couplings are strictly lower-triangular so don't affect det.

ALREADY PROVEN (clean, elaborates): A1 — for the standalone maps
  mulLeftMat K : Matrix (Fin t) (Fin c) ℝ →ₗ Matrix (Fin t) (Fin c) ℝ, X ↦ K*X, has det = K.det^c,
  mulRightMat K : Matrix (Fin r) (Fin t) ℝ →ₗ Matrix (Fin r) (Fin t) ℝ, X ↦ X*K, has det = K.det^r,
via colEquiv (column equiv to Fin c → Fin t → ℝ) + LinearMap.det_conj + LinearMap.det_pi + LinearMap.det_toLin'.

KEY MATHLIB I FOUND:
- LinearMap.det_prodMap (f : Module.End R M) (f' : Module.End R M') : (prodMap f f').det = f.det * f'.det.
- Matrix.det_fromBlocks_zero₂₁ (A : m×m) (B : m×n) (D : n×n) : det (fromBlocks A B 0 D) = det A * det D.
- Matrix.det_fromBlocks_zero₁₂ similarly for upper-right-zero.
- Matrix.BlockTriangular.det (over a LinearOrder grading) : det = ∏ over image, det (toSquareBlock ...).
- LinearMap.toMatrix_prodMap, LinearMap.det_toMatrix, Module.Free.chooseBasis.

QUESTION. What is the CLEANEST, most robust route to prove |det D| = |K.det|^(r+c) in Lean, given A1?
Two candidate architectures:
 (a) ABSTRACT product-endomorphism: keep D as an endo of the 4-fold product E; peel off the unipotent
     (strictly-lower-triangular) part as det 1, then det D = det(diagonal prodMap) = 1 * K.det^c * K.det^r * 1.
     Is there a Mathlib lemma "det of (id + strictly-lower-block-nilpotent) = 1", or a clean way to get
     "det D = product of diagonal block dets" for a block-lower-triangular endo of a PRODUCT of modules
     WITHOUT going through an explicit fromBlocks matrix? The differential is NOT a prodMap (it has the
     off-diagonal couplings), so det_prodMap doesn't apply directly. I need the triangular generalization.
 (b) FLATTENED matrix: realize D as a matrix over (Fin(t+r))×(Fin(t+c)) (the (t+r)×(t+c) matrix space,
     blocks TL=dK,TR=dN,BL=dX,BR=dE), prove BlockTriangular over a Fin-4 grading g(TL)<g(TR),g(BL)<g(BR),
     apply BlockTriangular.det. This is what an existing hand-built (3,3,3,3) instance does over Fin 27.
     The cost: extracting the differential's entries as an explicit Matrix, and identifying the diagonal
     blocks with mulLeft/mulRight (A1).

Specifically:
1. Does Mathlib v4.29 have a lemma giving det of a block-triangular ENDOMORPHISM of a binary/finite PRODUCT
   of modules = product of diagonal block dets (the abstract analog of det_fromBlocks_zero₂₁)? If yes, name it.
   If no, what is the shortest way to manufacture it from det_prodMap + a "unipotent has det 1" step?
2. Is "det (id + n) = 1 for n strictly-lower-triangular-nilpotent" available, or must I build it
   (e.g. via Matrix.det_one_add_... or characteristic-poly, or just realize id+n is block-unitriangular
   in fromBlocks form and use det_fromBlocks_zero₂₁ with the diagonal = id)?
3. RECOMMENDATION: pick (a) or (b) and give the precise lemma chain (names + the 2-3 key rewrite steps).
   I want the route with the fewest fragile entrywise/cast steps. Block-2x2-nested fromBlocks is acceptable.
</task>

<output_contract>
1. Answer Q1 (named lemma or "no, build it") in 2-3 sentences.
2. Answer Q2 (named lemma or the construction) in 2-3 sentences.
3. RECOMMENDATION: (a) or (b), with the precise Lean lemma chain — every lemma named, the ≤5 key steps.
   If (a) abstract: how to get the triangular det without an explicit matrix.
   If (b): the grading and how to identify diagonal blocks with A1's mulLeft/mulRight.
4. One paragraph: the single most likely failure point in your recommended route and how to pre-empt it.
Be concrete and terse. Name only lemmas you are confident exist in Mathlib v4.29.
</output_contract>

<grounding_rules>
Flag any lemma name you are NOT sure exists in v4.29 as "VERIFY". Distinguish "this lemma exists" (fact)
from "this should work" (inference). Do not invent lemma signatures.
</grounding_rules>
