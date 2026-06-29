**1. KILL-TEST**

Route b is structurally sound **if** the layer grade is assigned so that each Frame output at layer `k` depends only on variables in layers `j ≥ k`. From your summary, that follows from the recursion: `A_k` reads `C(k+1)`, and `C(k+1)` reads only later boundaries. Thus `∂A_k/∂x_j = 0` for `j < k`, giving exactly one-sided block triangularity with rows graded by output layer and columns by input layer.

So the `C(k+1)` coupling is off-diagonal, det-irrelevant, provided the grading direction matches Mathlib’s convention:

`b j < b i → M i j = 0`.

With `b = layer index`, nonzero entries occur only for `column layer ≥ row layer`, so this is upper block-triangular. No two-sided coupling follows from your summary.

ASSUMPTION: no Frame output coordinate assigned to layer `k` also includes a normalization, constraint, or reshuffle depending on earlier layers.

**2. The Diagonal Blocks**

The diagonal block for layer `k` is the derivative of the local layer assembly with later accumulators frozen:

`variables at layer k ↦ A_k`, with `C(k+1)` treated as constant.

The later-boundary coupling contributes only to `∂A_k/∂x_j` for `j > k`, so it should not enter the diagonal block. The diagonal block therefore must contain the local Schur/K frame map for that boundary, the local radial coordinates, and whatever local identity/linear reshaping is part of Frame.

This is good only if the K-coupling is local to a single boundary/layer. Then its determinant is the expected Schur-frame factor, e.g. morally `|det K_k|^(r+c)`, while the LDU pivot monomial remains banked in `Kparam`, not in Frame. The radial determinant is also diagonal-block-local.

Verify: the variables defining one `K_k` are all assigned the same layer grade, and the output coordinates whose determinant gives `|det K_k|^(r+c)` are in the same block. If `K_k` is split across adjacent boundaries, Route b’s per-layer product breaks.

**3. Lean Route**

For opaque widths, the less brittle path is **(a)**: one global grading `b : Fin N → ℕ`, apply `Matrix.BlockTriangular.det`, then build a general equivalence

`Fin blockSize ≃ {i // b i = k}`

from `Finset.card`/subtype machinery.

That matches the actual fused Frame and directly proves that the bad cross-boundary terms are off-diagonal. It also avoids resurrecting F1 in disguise.

Route **(b)**, a chain of per-layer insertion CLMs plus `listProd_clm_abs_det`, is attractive because the telescope is already banked, but it is dangerous unless each insertion CLM is allowed to depend on later parameters and you prove its product equals the fused Frame derivative. Otherwise it risks smuggling back the false “disjoint factors reproduce the chain” claim.

Yes, the `pivotBlowupOnDeriv_det` pattern using `Equiv.swap` and `Finset.card_equiv` sounds transferable: use cardinal/equivalence builders, not literal index lists.

**4. Biggest Risk**

The kill-condition is: a diagonal block is not actually local. Concretely, if `∂ output(layer k) / ∂ input(layer k)` contains terms whose determinant depends on later-layer variables through `C(k+1)` in a way not accounted for by the certified per-layer factor, then Route b fails.

Cheapest discriminating check before the cold build: for the general Frame definitions, prove or inspect the dependency lemma

`layer(input) < layer(output) → derivative entry = 0`

and separately inspect the diagonal restriction `layer(input)=layer(output)=k` to confirm it is exactly the frozen-accumulator local Schur/radial block. If that diagonal restriction still contains later variables in determinant-relevant positions, stop.