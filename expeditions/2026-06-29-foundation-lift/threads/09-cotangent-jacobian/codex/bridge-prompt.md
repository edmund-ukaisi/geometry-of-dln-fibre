<task>
I am re-homing an already-green Lean 4 / Mathlib module that proves the Zariski-cotangent =
Jacobian-kernel formula at a rational point of an affine variety (no smoothness assumed). I want a
decorrelated red-team of the INDEX / TRANSPOSE bookkeeping on the cokernel–kernel bridge — the one
place a subtle transpose error would hide and still typecheck/compile. The Lean compiles green and is
axiom-clean; that does NOT rule out a statement that is faithfully proved but mis-stated. Check the
MATH, not the Lean syntax.

SETUP (Lean defs, transcribed):
- R = MvPolynomial σ k, σ a Fintype, k a field. g : ι → R a finite generating family (ι Fintype),
  a : σ → k a k-rational point with eval a (g i) = 0 for all i. A = R ⧸ span(range g), m_A the
  maximal ideal = ker of the augmentation ε : A → k induced by eval a.
- jacobianMatrix g a : Matrix ι σ k,  entry (i, x) = eval a (pderiv x (g i)).
  So ROWS are indexed by generators ι, COLUMNS by variables σ. (i = which generator, x = which var.)
- jacobian g a : (σ → k) →ₗ[k] (ι → k) := (jacobianMatrix g a).mulVecLin.   [J : domain σ→k, codomain ι→k]
- jacobianTranspose g a : (ι → k) →ₗ[k] (σ → k) := (jacobianMatrix g a)ᵀ.mulVecLin. [Jᵀ : domain ι→k, codomain σ→k]
- In Mathlib, for a Matrix M : Matrix m n k, `M.mulVecLin : (n → k) →ₗ[k] (m → k)` is v ↦ M.mulVec v
  with (M.mulVec v) i = ∑ j, M i j * v j. So jacobian g a has domain (σ→k), codomain (ι→k). Good.
  And (jacobianMatrix g a)ᵀ : Matrix σ ι k, so jacobianTranspose has domain (ι→k), codomain (σ→k). Good.

THE BRIDGE (two claims):

(B1) finrank_ker_jacobian_eq_finrank_coker:
     finrank k (ker (jacobian g a)) = finrank k ((σ → k) ⧸ range (jacobianTranspose g a)).
  Proof: rank-nullity on J gives rank(range J) + finrank(ker J) = card σ (card of the DOMAIN σ→k).
         rank-nullity on the quotient gives finrank(coker Jᵀ) + rank(range Jᵀ) = card σ
         (card of (σ→k), the CODOMAIN of Jᵀ). finrank(range J) = finrank(range Jᵀ) because
         rank M = rank Mᵀ (Matrix.rank_transpose). omega closes it.

(B2) finrank_tensor_kaehler_eq_coker (the geometric half):
     finrank k (k ⊗_A Ω[A⁄k]) = finrank k ((σ → k) ⧸ range (jacobianTranspose g a)).
  Route: conormal sequence of R ↠ A base-changed to k: k ⊗_A Ω[A⁄k] ≅ (k ⊗_A (A ⊗_R Ω[R⁄k])) ⧸ K',
  where K' = range of the base-changed inclusion of K := ker(mapBaseChange k R A), and K =
  span_R{ 1 ⊗ D(g i) : i }. A coordinate iso Ψ : k ⊗_A (A ⊗_R Ω[R⁄k]) ≃ₗ[k] (σ → k) sends the
  base-changed conormal generator (1 ⊗ (1 ⊗ D(g i))) to the vector  x ↦ ε(pderiv x (g i)) = the
  i-th GRADIENT ROW of g evaluated at a, i.e. the vector (eval a (pderiv x (g i)))_{x∈σ} ∈ (σ→k).
  That vector equals jacobianTranspose g a (Pi.single i 1): indeed
  jacobianTranspose g a (e_i) x = ∑ i', (eval a (pderiv x (g i'))) * (e_i) i' = eval a (pderiv x (g i)).
  So Ψ maps span{conormal generators} onto range(jacobianTranspose), hence
  k ⊗_A Ω[A⁄k] ≅ (σ→k) ⧸ range(jacobianTranspose). finrank equal.

Then the headline chains: finrank(CotangentSpace(localization at m_A)) = finrank(m_A.Cotangent)
[flat localization] = finrank(k ⊗_A Ω[A/k]) [split augmentation, kerCotangentToTensor bijective]
= finrank(coker Jᵀ) [B2] = finrank(ker J) [B1].

WHAT TO CHECK (be adversarial):
1. The transpose direction in B2. The conormal/gradient vectors are the ROWS of the Jacobian
   (one per generator i, a vector indexed by variables x∈σ). I claim these gradient row-vectors are
   exactly the COLUMNS of Jᵀ = the image vectors jacobianTranspose(e_i) ∈ (σ→k). So the cokernel of
   Jᵀ : (ι→k)→(σ→k) is (σ→k)/span{gradient rows}. Is "range(jacobianTranspose) = span{gradient rows}"
   the correct object whose cokernel is the cotangent space? Or have I confused J and Jᵀ — should the
   cotangent space be coker(J) instead, which lives in (ι→k) and has the WRONG dimension?
2. The card bookkeeping in B1: both rank-nullity instances use card σ (= dim of (σ→k)). ker J lives in
   the domain (σ→k) ✓. coker Jᵀ = (σ→k)/range Jᵀ lives in the codomain of Jᵀ which is (σ→k) ✓. Both
   card σ. Is the use of Matrix.rank_transpose (rank M = rank Mᵀ) the only thing tying them, and is
   that step legitimate over a field? Any way the equality finrank(ker J)=finrank(coker Jᵀ) could be
   an artifact of both sides accidentally being card σ minus the SAME rank when they should differ?
3. Sanity: is the FINAL headline finrank(ker J) (J's kernel, in (σ→k), dim = #vars − rank) the right
   notion of Zariski tangent dimension? The Zariski tangent space at a is {v ∈ (σ→k) : every
   generator's gradient · v = 0} = ker(J) since (J v)_i = gradient(g_i)·v. So tangent dim = dim ker J.
   Cotangent dim = tangent dim (finite-dim duality over a field). Does the chain deliver THAT, i.e. is
   "finrank(CotangentSpace) = finrank(ker J)" the geometrically correct statement (cotangent dim =
   tangent dim = #vars − rank(Jacobian)), with NO off-by-transpose giving #generators − rank instead?

Give a CONCRETE 2-variable / 2-generator worked example (e.g. σ={x,y}, one or two explicit polys at a
point) to confirm the dimensions come out right under my conventions, and flag any step where the
transpose could be silently wrong.
</task>

<output_contract>
1. VERDICT on each of the three checks: SOUND / SUSPECT / WRONG, one line each.
2. The worked 2x2 example with explicit numbers (Jacobian matrix, ker J dim, coker Jᵀ dim, the
   geometric tangent dim) confirming or refuting.
3. The single most likely place a transpose/index error would hide and survive compilation, if any.
4. Bottom line: is the headline `finrank(CotangentSpace at a) = finrank(ker (jacobian))` the
   geometrically correct (#vars − rank) statement, yes/no.
Keep it under ~400 words plus the example. Mark every claim as DERIVED (you computed it) vs ASSUMED
(taking my transcription on trust).
</output_contract>

<grounding_rules>
You only have my transcription of the Lean, not the source — treat the def signatures as given but
challenge the MATHEMATICAL claims. Distinguish what you verified by computation from what you took on
trust. If a claim cannot be checked from what I gave, say so rather than guessing.
</grounding_rules>
