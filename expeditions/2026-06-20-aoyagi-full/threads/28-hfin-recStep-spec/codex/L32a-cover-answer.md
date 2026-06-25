1. **COVER: CORRECT.**  
   **Proven from finite-dimensional max:** every nonzero entry vector `d ∈ R^{r^2}` has at least one max-modulus entry. If pivot `p` is chosen with `|d_k| ≤ |d_p|`, then the ratios `d_k / d_p` all lie in `[-1,1]`. So the bounded-ratio source misses no part of the argmax cell.  
   **Needs-care:** ties are covered multiple times, but tie loci are codimension-1 null hypersurfaces. The omitted set `{Δ = 0} × S` has codimension `r^2` and is null.

2. **C-O-V VALIDITY: CORRECT, with boundary bookkeeping.**  
   On `{a ≠ 0}`, the map
   `a, u_k ↦ d_p = a, d_k = a u_k`
   is injective with inverse `a = d_p`, `u_k = d_k/d_p`, and is polynomial/C¹. The Jacobian is `|a|^{r^2-1}`.  
   **Needs-care:** the source with `|u_k| ≤ 1` is not open, and `a=0` collapses all ratios to `{Δ=0}`. Formally, apply COV on open pieces such as `a>0`, `a<0`, `|u_k|<1`, then add boundaries by null-set arguments; or use an area/change-of-variables theorem for measurable a.e.-injective C¹ maps. Dropping `{a=0}` is legitimate because it is null in source and its image is null in target.

3. **RANK STRATIFICATION: NEEDS-CARE.**  
   You cannot merely drop rank-drop loci as null. Null sets can still control divergence through neighborhoods: `|x|^{-α}` diverges near `{x=0}` even though `{x=0}` is null.  
   For `r=2,p=4`, the rank-1 locus `{det R=0}` is codimension 1 in `R`-space. The exact locus may be ignored as a set, but neighborhoods of it must be resolved. The Schur split near rank 1 gives, after coordinates,
   `‖RS‖² ≃ ‖P‖² + ‖B Q‖²`,
   with `P ∈ R^4`, scalar `B`, and `Q ∈ R^4`. That lower `B Q` core is exactly what must be handled recursively.

4. **THRESHOLD COMBINATION: CORRECT.**  
   After the radial blow-up,
   `G ∘ φ = a² ‖RS‖²`, and the density contributes `|a|^{r^2-1}`. Locally this factors as
   `|a|^{r^2-1-2c'} · ‖RS‖^{-2c'}`.  
   Therefore the chart is finite only if both the `a`-integral and the inner `(R,S)` integral are finite, so the combination is a **minimum**:
   `min(r²/2, inner threshold)`.  
   Inside the Schur chart, the split is a disjoint **sum**
   `‖P‖² + ‖B Q‖²`, so the RLCTs **add**:
   `jp/2 + λ_{r-j,p}`.  
   **Inference:** no hidden coupling between `a` and `(R,S)` remains, except harmless box-bound dependence; local product comparison is enough.

5. **DEPTH / TERMINATION: CORRECT.**  
   The well-founded measure is the determinantal size/corank `r`. Since the blown-up angular matrix has pivot entry `1`, its rank is at least `1`. On a rank-`j` Schur chart, the lower core has size `r-j`, strictly smaller than `r`. So recursion cannot revisit the same size.

6. **ANY HOLE: NO fatal measure-theoretic hole in the cover, but one fragile step.**  
   The atlas-cover plus recursive Schur resolution is sound for the stated upper-bound strategy. I do not see a smallest `(r,p)` counterexample where a stratum diverges below your recursive `λ_{r,p}`.

   The most fragile formalisation step is not the radial cover; it is making the “rank-`j` Schur split” into an actual local finite measurable cover with uniform comparison
   `‖RS‖² ≃ ‖P‖² + ‖B Q‖²`.
   Do not treat exact rank strata as integration domains. Use neighborhoods where a chosen `j×j` minor is invertible, prove the coordinate change/Jacobian/comparability there, and let the lower Schur complement `B` carry the recursive singularity.