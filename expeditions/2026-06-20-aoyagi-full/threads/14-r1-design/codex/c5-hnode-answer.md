**Q1.**  
[FACT] In a Schur chart with a hard unit pivot on the rank-1 complement, the block identity gives exactly  
`flatCore = Σ E_j² + Σ_i,j (b_i E_j + SΓ_i,j)²`.  
[FACT] Frobenius orthogonality of block columns prevents survivor/complement cross terms.  
[INFERENCE] The survivor pass-through does not create a second core: the full-rank downstream segment is a unit gauge, so it only conjugates/identifies `SΓ` with the survivor’s later reduced-chain product.  
[FACT] In the adapted Schur coordinates the pivot-column tail is zero at the deepest point, hence `b -> 0`.

**Q2.**  
[FACT] Under the stated hard-pivot hypothesis, the survivor/complement split is a basis split inside one product `D C`, not a Fubini product of independent losses.  
[INFERENCE] The reduced state is one chain: the complement pivot supplies the regular `E` block, while the survivor block is carried forward as `SΓ`.  
[FACT] A genuine two-core obstruction would require `||D_S U||² + ||D_K Z||²` with both `D_S` and `D_K` singular and sharing downstream variables. That is not the stated C5 chart, because the complement side has a hard unit pivot.

**Q3.**  
[FACT] The non-vanishing survivor entries need not lie in the pivot column tail `b`; they lie in the surviving block/gauge.  
[FACT] If the pivot column is normalized to `(1,0,...)` at the deepest point, then `Σ_i b_i² -> 0`.  
[INFERENCE] A chart where survivor unit entries appear inside `b` is a bad basis choice, not an algebraic obstruction to G2.

**Q4.**  
[INFERENCE] For rank-1 complement C5 nodes, the single Schur `hnode` mechanism should produce the required normal form.  
[INFERENCE] For larger partial drops, the same argument should iterate one complement pivot at a time or use the block-pivot analogue; the remaining work is chart bookkeeping and determinant/unit verification, not a new multi-core geometry.

VERDICT: WITNESS (hnode uniform at C5, same mechanism)