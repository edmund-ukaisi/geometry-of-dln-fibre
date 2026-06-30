# BdetMonomial assembly — remaining plan (after leafH_diagAxis closed)

## State
- leafH_diagAxis: CLOSED (decode thrash cracked; diagAxis frameSplitEquiv canonicalized to k.isLt form).
- diagAxis_ne_leafPivot, frameSplitEquiv_proof_irrel, diagAxis_injective, u_diagAxis, lhs_collapse,
  BchartLeaf_abs_det_free (hreg-cond), BchartLeaf_kLDU_abs_det_split, readK_kLDU_pbo: all sorry-free.
- eihd_hreg (genm-castdet @2b199058, RouteMHregPerm) + RouteMTwoSidedReg: brought onto branch.

## Remaining lemma 1: mem_image_diagAxis_of_leafH_ne_zero
Statement: `interiorLive_leafH ha h0r h0c j ≠ 0 → j ∈ Finset.image (diagAxis ha) Finset.univ`.
(Note: drop the `j ≠ pivot` hyp — at pivot, leafH = minAdm-1 which CAN be ≠0, so the pivot must be
EXCLUDED separately in the assembly via the `if j=pivot` split, NOT here. Restate: the assembly splits
the pivot off first (if_pos→1), then on `univ \ {pivot}`, the nonzero-leafH j are exactly image diagAxis.)
Cleaner: `j ≠ pivot → interiorLive_leafH j ≠ 0 → ∃ i, diagAxis i = j`. Proof: leafH j (j≠pivot) =
liveLeafHOnIdx (chartIdxEquiv j); nonzero ⟹ chartIdxEquiv j = ⟨k, Sum.inl s⟩ with frameSplitEquiv s =
Sum.inl(inl(inl qK)) and (finProd.symm qK).1 = .2 (diagonal). At L=2 k∈{0,1}; k=1 K-block is Fin(Text 3)
= Fin 0 (Text_Lsucc_eq_zero) so vacuous ⟹ k=0; then j = chartIdxEquiv.symm ⟨0, Sum.inl (fse.symm
(inl inl inl (finProd (i,i))))⟩ = diagAxis i with i = (finProd.symm qK).1. Use the explicit match-decode
idiom (match hc : chartIdxEquiv j / match heqf : frameSplitEquiv …) as in kLDU_injStep2.

## Remaining lemma 2: interiorLive_BdetMonomial_of_hreg (the assembly)
Target: `|det D(BchartLeaf∘kLDU)(pbo u)| = ∏ j, if j=pivot then 1 else |u j|^{leafH j}` (hreg hyp).
Chain:
  LHS = BchartLeaf_kLDU_abs_det_split (pbo u)
      = |det D(BchartLeaf)(kLDU(pbo u))| · |det D(kLDU)(pbo u)|
  factor1 = BchartLeaf_abs_det_free (kLDU(pbo u)) hreg = |det(readK (kLDU(pbo u)) ⟨0⟩)|^{r+c}
          = (readK_kLDU_pbo) |det(kLens(readK u ⟨0⟩))|^{r+c} = (kLens_det) |∏_i (readK u ⟨0⟩) i i|^{r+c}
          = |∏_i u(diagAxis i)|^{r+c}                          [u_diagAxis: (readK u ⟨0⟩) i i = u(diagAxis i)]
  factor2 = kLDU_ambient_abs_det (pbo u) = ∏_{k:Fin 2} ∏_{i:Fin(Text(k+2))} |q_{k,i}(pbo u)|^{2(...)}
          k=1: Fin(Text 3)=Fin 0 vacuous (=1). k=0: ∏_i |q_{0,i}(pbo u)|^{2(Text2-1-i)}
          q_{0,i}(pbo u) = (matrixSplit(readK (pbo u) ⟨0⟩)).2.1 i = (readK (pbo u) ⟨0⟩) i i
                         = (readK_pbo_all: K-diag pbo-fixed) u(diagAxis i)
  factor1·factor2 = lhs_collapse (τ=Text2, q i := u(diagAxis i)) = ∏_i |u(diagAxis i)|^{(r+c)+2(Text2-1-i)}
                  = ∏_i |u(diagAxis i)|^{leafH(diagAxis i)}     [leafH_diagAxis]
  RHS reindex: ∏ j (if j=pivot then 1 else |u j|^{leafH j})
             = (prod split off pivot: if_pos→1, one_mul) ∏_{j∈univ\{pivot}} |u j|^{leafH j}
             = (Finset.prod_subset image⊆univ\{pivot}, off-image leafH=0 ⟹ |u j|^0=1)
               ∏_{j∈image diagAxis} |u j|^{leafH j}
             = (Finset.prod_image, diagAxis_injective) ∏_i |u(diagAxis i)|^{leafH(diagAxis i)}
  ⟹ LHS = RHS. ∎
Key Mathlib: Finset.prod_subset, Finset.prod_image, Finset.prod_eq_mul_prod_diff_singleton_of_mem,
Fin.prod_univ_two (factor2 k-split), the Text 3 = 0 vacuity (Fintype.card Fin 0).

## Then (step 2 fill + step 5)
interiorLive_BdetMonomial := interiorLive_BdetMonomial_of_hreg ha h0r h0c u (eihd_hreg ha)
→ interiorLive_abs_det sorry-free → fire step 5 (apply routeMCore_box_diverges_achiever_spine in
RouteMLayerCoverGE, lead-authorized) → R1-LOWER leg sorry-free.
