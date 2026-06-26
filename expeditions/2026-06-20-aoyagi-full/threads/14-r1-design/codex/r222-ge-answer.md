**Verdict:** with the listed gated tools, use the full cover. A direct box estimate is not the shortest sound Lean route. The only plausible shortcut is to stop at the δ-chart and prove a new weighted monomial × smooth-4-block integrability/product lemma; existing `smoothBlockND_rlct` / `product_min_rlct_of_ne` are unweighted `rlctAtOn`, so they do not account for the Jacobian weight.

**Shortest Sound Route**

SURE project names:

`rlctAtOn_ge_of_integral_lt`
`g5_pivotNode`
`cover_integral_lt_top_iff`
`argmaxCellOn_cover`
`pivotBlowupOnDeriv_det`
`monomialIntegrand_integrable_of_lt`
`integrableOn_monomial_mul_unit_iff`
`case222_unit_leaf_threshold`
`case222_block_leaf_threshold`
`tailLift_lemma2Inv_lintegral_image` / `setLIntegral_image_of_mp`

Do the ≥ proof by finite cover composition:

1. Pick a bounded open box `U0 := Set.univ.pi fun _ => Set.Ioo (-1) 1`.
2. Prove finiteness of `∫⁻ x in U0, ofReal (|myF222 x| ^ (-(c' : ℝ)))`.
3. Apply `rlctAtOn_ge_of_integral_lt myF222 hFm U0 hU0 h0 (3/2) ...`.

Do **not** apply `g5_pivotNode` with this bounded `U0` as its `U`. That cover hypothesis is false: `U0` is not a.e. equal to the global union of argmax cells; the RHS also contains points outside `U0`.

Instead use the cutoff form:

`∫⁻ x in U0, f x = ∫⁻ x, U0.indicator f x`

then apply `g5_pivotNode active Set.univ hUnivCov` to the cutoff integrand. For the top node,

`Set.univ =ᵐ[volume] ⋃ p∈active, argmaxCellOn active p`

follows from `argmaxCellOn_cover` plus nullity of the active-zero subspace `{x | ∀ j∈active, x j = 0}`. It is **not** just `{0}` null; for step 1 it is the `A = 0` coordinate plane.

Recursion: after step 1, each summand is again recursed by rewriting the set integral over `chartDomOn active p \ pivotZeroOn p` as a full-space integral with an indicator, then applying the next `g5_pivotNode` to the new accumulated integrand. Lemma-2 is only a measure-preserving splice, not a pivot node.

Leaf facts: analytically only **two** finiteness lemmas are needed: unit leaves `(d,k,h)=(2,![1,1],![3,2])` and block leaves `(3,![1,1,1],![3,2,3])`. Lean still needs 24 chart wrappers or a symmetry/indexing layer.

Assessment: mechanical composition, not a new analytic pole, if the cutoff recursion is used. Budget: about 1-2 focused days; more if you insist on flattening a global bounded 24-image cover directly.