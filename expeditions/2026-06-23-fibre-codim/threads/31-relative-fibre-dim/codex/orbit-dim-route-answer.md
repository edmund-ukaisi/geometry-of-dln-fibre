**VERDICT:** ORBIT-DIM ROUTE ALSO WALLED: it needs Mathlib-absent theorem X = a reducible affine fibre-dimension/image-dimension theorem, e.g. `varietyDim_image_eq_of_surjective_uniform_fibre_dim`; it does not literally need the chart route’s determinantal ideal theorem, but proving X in Lean would require the same kind of missing product/component/fibre-dimension infrastructure.

**Q1. Action Pullback**
FACT: For the action map `α : H × F → Σ^r`, set-surjectivity should give
`O(Σ^r) ≃ (α*).range`, by identifying `ker α*` with `vanishingIdeal Σ^r`.

But the landed orbit method then breaks. In the orbit-closure case, `(μ_M*).range` is a subalgebra of the domain `O(G_d)`, hence a domain, so the engine can use:
`ringKrullDim = trdeg`
via the finite-type domain machinery, e.g. local lemmas like `ringKrullDim_quotient_unbotD_eq_trdeg_toNat`, `trdeg_eq_of_integral_injective`, and Mathlib’s `trdeg_add_eq`.

Here `(α*).range ≃ O(Σ^r)`. If `Σ^r` is reducible, this ring has zero divisors. Reducibility of `F` alone does not logically force reducibility of the sweep, but your worked anchor and intended generality do force the route to handle reducible `Σ^r`. So: `varietyDim Σ^r = trdeg ((α*).range)` is not available from landed machinery, and `(α*).range` is not a domain in the cases that matter.

**Q2/Q3. The Hidden Missing Theorem**
The tight missing theorem is:

```text
For a surjective finite-type morphism f : X → Y of affine k-varieties,
with X,Y possibly reducible, if all fibres have dimension e
(or are all isomorphic to a fixed fibre S), then

  varietyDim X = varietyDim Y + e.
```

Applied to `α`:

```text
varietyDim (H × F)
  = varietyDim Σ^r + varietyDim Stab_H(E),
```

with `varietyDim Stab_H(E) = dim H - δ`, and also

```text
varietyDim (H × F) = dim H + varietyDim F.
```

FACT from your v4.29 inventory: Mathlib lacks the needed general product theorem
`ringKrullDim (A ⊗[k] B) = ringKrullDim A + ringKrullDim B`, and the reducible relative dimension/additivity theorem is still a `proof_wanted`-level gap around `MvPolynomial.fin_ringKrullDim_eq_add_of_isNoetherianRing`.

So the orbit route is not a landed-domain argument. The uniform-fibre step is not a domain statement; reducibility leaks through `H × F`, through `O(F)`, and through taking max over components. Homogeneity tells you the fibre dimensions. It does not give Lean the theorem turning that into `dim image = dim source - dim fibre`.

This is not exactly the chart route’s determinantal ideal-generation theorem. But it is not cheaper: it replaces explicit chart algebra with a broad Chevalley/fibre-dimension/product/component sublibrary.

**Q4. Top Component Trick**
Taking one top-dimensional irreducible component `F₀` helps only superficially.

INFERENCE: If you had a clean component theory, `H × F₀` would be irreducible and the image closure `Z₀ = closure(H·F₀)` would be irreducible. Then `O(Z₀)` is a domain, so the domain-style pullback philosophy becomes plausible.

But the residual missing theorem is still not the single-point orbit formula
`dim(G·x) = dim G - dim Stab(x)`. The set `H·F₀` is a family sweep, not one orbit. The needed statement is:

```text
For α₀ : H × F₀ → closure(H·F₀),
with generic/uniform fibre Stab_H(E),

  dim closure(H·F₀)
    = dim(H × F₀) - dim Stab_H(E)
    = δ + dim F₀.
```

That is the irreducible fibre-dimension theorem / constructible-image dimension theorem. Mathlib v4.29 does not have this as an algebraic-geometry package.

Also, to conclude `varietyDim Σ^r = varietyDim closure(H·F₀)`, you need finite irreducible-component decomposition, minimal-prime/component correspondence, and `dim finite union = max dim components`. Those are exactly part of the reducible wall.

**Cost**
A targeted abstract `X` sublibrary: roughly **12-20 modules**.

A chart-local replacement using pivot trivializations: roughly **7-12 modules**, but then you are back to product dimension, finite-cover gluing, and determinantal/localized ideal control.

So the orbit-dim route is genuinely walled. It avoids the chart theorem only by assuming a larger absent theorem.