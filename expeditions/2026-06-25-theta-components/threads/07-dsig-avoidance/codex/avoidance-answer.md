1. **VERDICT:** [proof] **TRUE under the stated component-structure hypotheses; in fact true for every component whose realizer has product rank exactly `r`, not only top-dimensional ones.**

2. **STRUCTURAL REASON:** [proof] Let `C = V(p)` be such a component, with realizer `M` and `rank P(M)=r`. Choose endpoint base changes `g_N in GL(d_N)`, `g_0 in GL(d_0)` such that  
   `g_N P(M) g_0^{-1} = diag(I_r,0)`.  
   Taking all interior `g_i = I`, this is an allowed quiver base change, so the transformed tuple `M'` lies in the same orbit, hence in `C`. At `M'`, the fixed top-left `r x r` minor is `1`. Therefore `detDelta` does not vanish identically on `C`, so `detDelta notin p`.

3. **GLOBAL VS PER-COMPONENT PIVOT:** [proof] **Global.** The same polynomial `detDelta` works for all components. The base change may depend on the component, but the open set `D(detDelta)` is fixed and intersects every component. What is not required is that `detDelta(M) != 0` at the originally chosen realizer.

4. **RANK-`< r` TOP-COMPONENT WORRY:** [proof] Under your stated structure, no top component, and indeed no component in that indexing, is contained in product-rank `< r`, because each component contains a realizer with product rank exactly `r`. [standard fact] Non-equidimensionality is separate: in `(2,2,3), r=1`, the lower-dimensional component is still generically product-rank `1`; it is lower-dimensional because of extra rank-pattern constraints, not because it lies in `Sigma^0`.

5. **CHEAPEST SHARP COMPUTATION:** [conjecture/inference] Test `(2,2,3,2), r=1`. It is still small, but unlike `(2,2,2,2)` it should include a top component coming from the middle rectangular pair via `det(A_3 A_2)`, not just individual square-map determinants. Check that the top-dimensional part of `sigmaIdeal : detDelta^infty` equals the top-dimensional part of `sigmaIdeal`. This directly tests the single-global-pivot claim.