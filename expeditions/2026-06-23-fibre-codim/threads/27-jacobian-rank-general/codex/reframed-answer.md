**1. Is Step 2 Circular?**

Yes, unless you have an independent Jacobian-minor proof.

The endpoint orbit gives `δ` image directions everywhere. The hard part is the extra `C` directions. At a generic smooth reduced point of a fibre component, `rank(d mult_A) = card - dim F_α`, so

`rank(d mult_A) ≥ C + δ`

is exactly the desired component dimension bound in Jacobian language. Without an independent structural proof producing those extra `C` directions, Step 2 is not a proof of the hard direction; it is the hard direction.

Also, generic smoothness of `(F)_red` alone is not enough. The reduced tangent sits inside `ker d mult_A`; equality needs generic reducedness of the scheme fibre along the component. So route B carries both a circularity risk and a scheme-theoretic reducedness burden.

**2. Fibration Route Soundness**

(i) `G` connected preserves irreducible components: yes, standard and clean. A connected algebraic group acts on the finite discrete set of irreducible components; the image is connected, hence constant. Since the identity fixes each component, all of `G` fixes each component.

(ii) For `Z_j -> Mat^{=r}`: sound. The endpoint group `H = GL_{d_N} x GL_{d_0}` is transitive on `Mat^{=r}`. Since `Z_j` is `G`-stable, hence `H`-stable, if `Z_j` has one point over one rank-`r` matrix, it has points over every rank-`r` matrix. Fibres over different rank-`r` matrices are literally translates.

(iii) Codimension: sound, but only after using the exact-rank locus correctly. The homogeneous argument applies to

`Σ^r = mult^{-1}(Mat^{=r})`,

not directly to `Σbar^r = mult^{-1}(Mat^{≤r})`. Then use LR Cor. 4.4 / Lemma 4.5: `Σbar^r = closure(Σ^r)`, so `dim Σ^r = dim Σbar^r`, hence the codimension is `C`.

**3. The Orbit-Dimension Recast**

Yes: the homogeneous base lets you avoid a general fibre-dimension theorem, but you still need a special homogeneous-sweep dimension lemma.

Let

`X = Rep(d)`,  
`H = GL_{d_N} x GL_{d_0}`,  
`K = Stab_H(E)`,  
`F = mult^{-1}(E)`,  
`Z = mult^{-1}(Mat^{=r})`.

Then `Z = H · F` by endpoint equivariance. Consider

`H x F -> Z`,  
`(h, A) ↦ h · A`.

For any image point represented by `(h0, A0)`, the fibre is exactly

`{(h0 k, k^{-1} · A0) : k ∈ K}`.

So the only redundant directions are `K`. Therefore

`dim Z = dim H + dim F - dim K`.

But `dim H - dim K = dim(H · E) = dim Mat^{=r} = δ`, already matching the endpoint orbit-dimension machinery. Thus the formaliser-facing identity is:

`varietyDim(productRankLocusEQ d r) = deformationδ d r + varietyDim(fibreOverE d r)`.

Then combine with

`varietyDim(productRankLocusEQ d r) = varietyDim(productRankLocusLE d r) = card - cCodim(d,r)`,

to get

`varietyDim F = card - C - δ`.

This is the clean route.

**4. Route Ranking**

1. **(c) Equivariant fibration as orbit-dimension count**: best. Reuses baseChange, mult-equivariance, endpoint orbit dimension, `deformationδ`, and avoids scheme fibres, Jacobians, generic smoothness, and component classification. Needs one special homogeneous-sweep lemma.

2. **(b) General equivariant fibration / fibre-dimension theorem**: mathematically clean, but bad for the current engine if general fibre-dimension machinery is missing.

3. **(a) Jacobian + generic smoothness**: worst. Step 2 is the hard theorem in disguise unless independently proved, and generic reducedness is an extra burden. The examples already show uniform rank bounds are false.

**5. Likely Error + Cheapest Test**

Most likely error: writing the sweep identity for `Σbar^r` instead of `Σ^r`. The endpoint orbit of `E` only reaches exact rank `r`, not lower ranks.

Cheapest test: in `(3,3,3), r=1`, the zero-product point lies in `Σbar^1` but cannot lie in `H · F`, because endpoint `GL x GL` translation preserves product rank exactly. So prove the orbit identity for exact rank first, then use density/closure to transfer dimension to `Σbar^r`.