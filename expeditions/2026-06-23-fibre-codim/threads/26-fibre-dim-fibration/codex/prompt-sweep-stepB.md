# Codex consult — cleanest Lean realization of the homogeneous-sweep dim identity (route c, Step B)

## Context (Lean 4 / Mathlib v4.29, affine-AG engine, NO schemes)

Deep linear networks. `Rep_d` = matrix tuples `(A_1,…,A_N)`; `mult(A) = A_N⋯A_1 : Mat_{d_N×d_0}`.
`F = mult⁻¹(E)`, `E = diag(I_r,0)` rank `r`. `Σ^r = {A : rank(mult A) = r} = mult⁻¹(Mat^{=r})`
(exact rank). `H = GL_{d_N}×GL_{d_0}` acts on the END factors of `Rep_d`; `mult` is H-equivariant:
`mult(h·A) = h_N · mult(A) · h_0⁻¹` (LANDED `mult_smul`). `Mat^{=r} = H·E` is one H-orbit (any two
rank-r matrices are GL×GL-equivalent, LANDED `exists_baseChange_of_rank_eq`). So `Σ^r = H·F`.

Engine is purely affine: dimension = `varietyDim Z = (ringKrullDim (MvPolynomial σ k ⧸ vanishingIdeal
Z)).unbotD 0`; the engine computes orbit dims via `ringKrullDim = trdeg` (`AffineNoetherRank`) and an
orbit-PULLBACK construction (`OrbitPullbackDim`: `varietyDim(orbitRankLocus M) = ringKrullDim(range of
the orbit-pullback algebra map)` — but that is for a SINGLE G_d-orbit-closure of a POINT M, not for H
acting on a whole subvariety F).

## The target (route c, Step B — the one genuinely new rung)

> **`varietyDim Σ^r = δ + varietyDim F`**,  `δ = r(d_N+d_0−r) = dim Mat^{=r} = dim(H·E)`.

The pen-and-paper argument (CERTIFIED, exact on 9 cases): the action map `α : H × F → Σ^r`,
`(h,A)↦h·A`, is surjective with every fibre `≅ Stab_H(E)` (a coset), so `dim Σ^r = dim H + dim F −
dim Stab_H(E) = (dim H − dim Stab) + dim F = δ + dim F`. Equivalently `mult|_{Σ^r} : Σ^r → Mat^{=r}`
has all fibres = H-translates of F (homogeneous base ⟹ all fibres isomorphic), so no general
fibre-dimension theorem is needed — only that `Mat^{=r}` is one H-orbit of dim δ.

**LANDED engine handles:** `mult_smul` (H-equivariance), `exists_baseChange_of_rank_eq` (Mat^{=r} = one
H-orbit), `DeterminantalStratumDim` (`dim Mat^{≤r} = δ`), `SigmaCodim` (`dim Σ̄^r = card − C`),
`ringKrullDim = trdeg` (`AffineNoetherRank.ringKrullDim_quotient_unbotD_eq_trdeg_toNat`,
`trdeg_eq_of_integral_injective`), `trdeg_add_eq` (Mathlib tower additivity), `OrbitPullbackDim`,
`AffineDomainDimension` (equidim `height p + dim(A/p) = dim A`).

## QUESTIONS — the cleanest Lean realization at v4.29, NO schemes, NO general fibre-dim theorem

1. **Two candidate realizations of Step B — which is cleaner in this affine/trdeg engine?**
   - **(B-trdeg)** Coordinate rings: `O(Mat^{=r}) ↪ O(Σ^r)` (the comorphism of `mult|_{Σ^r}`, injective
     since `mult|_{Σ^r}` dominant). `trdeg_k O(Σ^r) = trdeg_k O(Mat^{=r}) + trdeg_{Frac O(Mat^{=r})}
     O(Σ^r)` (`trdeg_add_eq`). `trdeg_k O(Mat^{=r}) = δ`. The relative trdeg = dim of the GENERIC
     fibre; **homogeneity (Mat^{=r} = one H-orbit) ⟹ the generic fibre dim = dim F** (all fibres are
     H-translates of F). Is "homogeneous base ⟹ relative trdeg = dim of the specific fibre F" cleanly
     provable in Mathlib v4.29? What is the precise lemma chain (does it need `Frac`/localization at the
     generic point, or can H-translation give it directly)? This is the no-jump, supplied by
     homogeneity rather than flatness — is that realizable without a flatness/generic-flatness theorem?
   - **(B-orbit)** Mimic the engine's `OrbitPullbackDim` but for the H-action on F: build the
     "H-sweep pullback" algebra map and compute `dim Σ^r` as `dim H − dim Stab + dim F` via a
     trdeg/Krull count on the sweep. Is this a from-scratch construction or does `OrbitPullbackDim`'s
     machinery (which handles a single orbit of a point) generalize to an orbit of a subVARIETY F?

2. **The hardest sub-point in (B-trdeg): "relative trdeg = dim F" via homogeneity.** Concretely: the
   generic fibre of `mult|_{Σ^r}` is `Spec(O(Σ^r) ⊗_{O(Mat^{=r})} Frac(O(Mat^{=r})))` — its dim =
   relative trdeg. We want this = `dim F` (the fibre over the CLOSED point E). For a general dominant
   map these differ (fibre dim can jump). Homogeneity: every fibre is `h·F ≅ F`, so they're all
   `dim F`. **In Mathlib v4.29, how do I convert "all closed fibres isomorphic (H-translates)" into
   "generic fibre dim = dim F" WITHOUT a constructibility/Chevalley theorem?** Is there an
   H-equivariant trick: e.g. the projection `H × F → Σ^r` is surjective and `dim(H×F) = dim H + dim F`
   (product dim — is `ringKrullDim`/`trdeg` of a PRODUCT of affine varieties additive in Mathlib
   v4.29? `trdeg` of a tensor product over k?), and the generic fibre of `α` has dim = dim Stab
   (a subgroup, computable), giving `dim Σ^r = dim H + dim F − dim Stab` — does THIS avoid the
   generic-fibre-of-mult issue by using the product + the group fibres (which ARE all isomorphic to
   Stab, a fixed group)?

3. **Is `trdeg`/`ringKrullDim` of a PRODUCT additive at v4.29?** (`trdeg_k (A ⊗_k B) = trdeg_k A +
   trdeg_k B` for f.g. domains? `Algebra.TensorProduct` + `trdeg`?) This would let the (B-orbit) route
   compute `dim(H × F) = dim H + dim F` cleanly, reducing Step B to the fibre-dim of the GROUP action
   map (fibres = a fixed group Stab) — which is more uniform than `mult`'s fibres.

4. **Step C (`dim Σ^r = dim Σ̄^r`).** `Σ̄^r = closure(Σ^r)`, `varietyDim` IS closure-dimension
   (`ringKrullDim` of `MvPolynomial ⧸ vanishingIdeal`, and `vanishingIdeal(Σ^r) = vanishingIdeal(Σ̄^r)`
   since `Σ̄^r = closure Σ^r`). So is `varietyDim Σ^r = varietyDim Σ̄^r` essentially DEFINITIONAL in
   this engine (both read the vanishing ideal of the same closure)? Or is there a subtlety
   (`productRankLocus` exact vs `productRankLocusLE`)? Confirm this is cheap.

5. **Overall: is route c (the sweep) genuinely more reachable at v4.29 than the dead routes** (the
   determinantal-presentation/flatness wall of threads 09/14/20, and the circular Jacobian route)? Or
   does Step B hide an equivalent wall (a product-dim or homogeneous-fibre-dim theorem Mathlib lacks)?
   Give the module/sub-lemma decomposition with the HARD rung named, and the exact Mathlib v4.29 lemma
   names to verify exist (trdeg of tensor product, trdeg_add_eq hypotheses, any orbit/quotient-dim).

Be concrete and skeptical. Flag any step that secretly needs a constructibility/Chevalley/flatness
theorem absent from Mathlib v4.29.
