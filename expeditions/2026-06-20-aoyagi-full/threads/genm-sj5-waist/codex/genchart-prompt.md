<task>
Lean 4 + Mathlib v4.29. I am generalizing a WORKING sorry-free change-of-variables lemma from a fixed
(3,2,3) case to variable width, and need the cleanest proof structure for the Jacobian determinant at
variable width.

CONTEXT. This is the "max-pivot Schur chart" for a deep-layer matrix in a DLN RLCT finiteness proof.
Fix nats s, z. Consider the matrix A : Fin (s+1) → Fin (z+1) → ℝ. Parametrize the "max-pivot sector"
{A[0][0] ≠ 0} by (p, t, ℓ, w) with p : ℝ, t : Fin z → ℝ, ℓ : Fin s → ℝ, w : Fin s → Fin z → ℝ, via
the chart Φ:
  A[0][0]     = p
  A[0][j+1]   = p * t[j]
  A[i+1][0]   = ℓ[i] * p
  A[i+1][j+1] = w[i][j] + ℓ[i] * p * t[j]
The parameter-space dimension is 1 + z + s + s*z = (s+1)*(z+1), matching A. On {p ≠ 0}, Φ is a
polynomial bijection onto its image with inverse t[j]=A[0][j+1]/p, ℓ[i]=A[i+1][0]/p,
w[i][j]=A[i+1][j+1] - A[i+1][0]*A[0][j+1]/p. The Jacobian determinant is |det DΦ| = |p|^{s+z}.

The FIXED (3,2,3) case (s=1, z=2) is already proved sorry-free via the standard recipe:
- HasFDerivAt Φ (explicit ContinuousLinearMap.pi of component derivatives) v   [via hasFDerivAt_pi, .mul, .add]
- the derivative's toMatrix' is an explicit lower-triangular 6x6 matrix; det = p^3 via
  Matrix.det_of_lowerTriangular + fin_cases on the 6x6 indices
- Set.InjOn Φ {v | v 0 ≠ 0} by pivot cancellation
- MeasureTheory.lintegral_image_eq_lintegral_abs_det_fderiv_mul volume ... fed |det| = |p|^3
The fin_cases blow-up in the determinant step does NOT generalize to variable (s,z).

I have BANKED, sorry-free, at v4.29:
- blockSplitD t a b : ((Fin t ⊕ Fin a) → (Fin t ⊕ Fin b) → ℝ) ≃ᵐ ((P,B₁₂,C)) × (Fin a → Fin b → ℝ),
  measure-preserving (measurePreserving_blockSplitD), reads the 4 blocks of a fromBlocks matrix.
- the shear D ↦ Γ = D − C·P⁻¹·B₁₂ as a measure-preserving translation at fixed (P,B₁₂,C)
  (via measurePreserving_add_right); frees the Schur complement block.
These are for a t×t pivot; my chart is a 1×1 pivot (t=1, a=s, b=z), and the Schur complement Γ = w
is EXACTLY my w-block.

TWO CANDIDATE ROUTES for the general lemma
  schurChartGen_cov : ∫⁻ y in Φ '' {p≠0}, g y = ∫⁻ v in {p≠0}, ofReal(|p|^{s+z}) * g (Φ v)
(g : ambient → ℝ≥0∞ arbitrary):

ROUTE A (explicit Jacobian, generalize the prototype). Prove HasFDerivAt + det = p^{s+z} + InjOn at
variable width, feed lintegral_image_eq_lintegral_abs_det_fderiv_mul. Determinant needs a variable-width
lower-triangular det over a composite index type (Unit ⊕ Fin z ⊕ Fin s ⊕ (Fin s × Fin z) with lex order,
or Fin((s+1)(z+1))). Concern: proving off-triangle entries vanish structurally, and getting the diagonal
product = p^{s+z}, without fin_cases.

ROUTE B (compose measure-CoV theorems, avoid the big determinant). Decompose Φ = Assemble ∘ Shear_w ∘ Scale:
(1) Scale: (t,ℓ) ↦ (p·t, p·ℓ) at fixed p — a DIAGONAL linear map on ℝ^z × ℝ^s = ℝ^{s+z}, det = p^{s+z}
    (clean: product of z+s one-d scalings x ↦ p·x, no triangular matrix);
(2) Shear_w: w ↦ w + ℓ p t — measure-preserving translation (banked idea);
(3) Assemble: place entries into the matrix — a measure-preserving reindex.
The p appears as an integration variable, so Scale is a p-DEPENDENT inner scaling; needs Tonelli to pull
p out, per-p scaling CoV with p-dependent det |p|^{s+z}, then recombine. Concern: the Tonelli +
p-dependent-det bookkeeping, and which exact Mathlib lemma gives ∫⁻ over ℝ^n of f(p • x) = |p|^{-n}·∫⁻ f
(or the forward direction) for a scalar smul on a pi type ℝ^n.
</task>

<output_contract>
1. VERDICT: which route (A or B) is the cheaper/cleaner Lean-v4.29 build for the VARIABLE-width lemma?
   One paragraph why.
2. If Route A: the exact clean way to compute the variable-width determinant det = p^{s+z} WITHOUT
   fin_cases — name the Mathlib lemma(s) (Matrix.det_of_lowerTriangular / BlockTriangular / det_fromBlocks
   / a composition det_comp) and the index type + order to use, and how to discharge the off-diagonal
   vanishing structurally. Flag any lemma you are NOT sure exists at v4.29.
3. If Route B: name the EXACT Mathlib v4.29 lemma for the scalar-smul lintegral CoV on ℝ^n (Real.rpow /
   addHaar / Measure.map (r • ·)), state its exact direction/signature as best you know, and give the
   Tonelli skeleton (which variable is pulled out, how the p-dependent det is handled). Flag existence
   uncertainty.
4. A THIRD option if you see one cleaner than both (e.g. induction on s peeling one row/column, or a
   det-via-comp of the two banked pieces + one scaling).
5. Rank the top-3 riskiest Lean friction points for the winning route.
</output_contract>

<grounding_rules>
Distinguish [FACT] (you are confident the lemma exists at Mathlib v4.29 with that signature) from
[INFERENCE] (plausible but unverified — I will grep/verify locally before building). For any Mathlib
lemma name you cite, mark it [FACT] only if you are confident of the exact name at v4.29; otherwise
[INFERENCE] and describe the shape so I can search. Do not invent lemma names silently.
</grounding_rules>
