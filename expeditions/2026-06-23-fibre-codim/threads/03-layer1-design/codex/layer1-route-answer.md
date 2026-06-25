I checked this against the pinned local `mathlib` rev in [lean/lake-manifest.json](/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/lake-manifest.json:4).

**Verdict:** the cleanest route is **not** the full bundle theorem. It is a narrowed version of **(i)**:

> flatness + known `dim total` + known `dim base` + affine-domain equidimensionality  
> ⟹ fixed closed fibre has the forced dimension.

Mathlib v4.29 has the useful pieces: flat algebras give going-down, `exists_ltSeries_of_hasGoingDown` exists, and `Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown` is already listed in the height theorem API. Chevalley is constructibility/open-map, not fibre dimension; StandardSmooth has relative-dimension predicates, but no Krull-dimension fibre theorem attached. ([leanprover-community.github.io](https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/Ideal/GoingDown.html))

**1. Cleanest Route**

Use route **(i′)**:

```lean
A := coordinate ring of a rank-r affine chart of the base
B := coordinate ring of the corresponding total chart/component
m : Ideal A := maximal ideal of the chosen matrix B₀

[Module.Flat A B]
ringKrullDim A = a
ringKrullDim B = a + d
m.height = a
m.map (algebraMap A B) ≠ ⊤
⊢ ringKrullDim (B ⧸ m.map (algebraMap A B)) = d
```

This is much cheaper than proving general fibre-dimension additivity.

Why the others lose:

- **(ii) local trivialisation + product + glue:** geometrically natural, Lean-expensive. You need affine open-cover infrastructure, dimension of principal opens, product/tensor-product dimension, and gluing for your closed-subset `varietyDim`.
- **(iii) three vanishing ideals:** not enough. Your catenary bridge controls a single affine-domain or ambient polynomial quotient. It does not by itself relate base/total/fibre ideals under a morphism.
- **(iv) group-orbit total route:** total dimension is already known. Recomputing it by orbit-image machinery does not produce fibre dimension unless you also build the quotient/fibre theorem. A direct orbit computation of the fixed fibre might be viable, but that is a different, highly project-specific route.

**2. The Two Inequalities**

For the full theorem, yes: going-down gives the **lower** bound cleanly. In fact use the stronger existing theorem

```lean
Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown
```

rather than only chain lifting.

For the **narrow fixed-fibre theorem**, the same height formula plus your landed affine-domain formula in [AffineDomainDimension.lean](/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/AffineDomainDimension.lean:113) gives both sides:

- Upper: for every prime `P ⊇ mB`, `P.height ≥ m.height = dim A`; catenarity/equidimensionality of `B` gives `dim B/P ≤ dim B - dim A`.
- Lower: choose `P` minimal over `mB`; its vertical fibre height is `0`, so `P.height = m.height`, hence `dim B/P = dim B - dim A`.

For the **general** flat finite-type theorem, the upper bound is still the real wall: it is the no-jumping/equidimensionality/dimension-formula half.

**3. Hardest Missing Piece**

For a general theorem, the missing piece is **(a)**, more precisely the finite-type morphism dimension formula / altitude theorem:

```lean
flat finite type + constant fibre dimension
⊢ ringKrullDim B = ringKrullDim A + d
```

Upper semicontinuity is one classical way to build it, but the Lean API theorem you would want is the ringKrullDim equality or its upper-bound half. Mathlib’s Chevalley file gives constructibility of images and an open-map result under going-down/finite presentation, not dimension arithmetic. ([leanprover-community.github.io](https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/Spectrum/Prime/Chevalley.html))

**4. Narrower Target**

Yes, the fact that `dim total` and `dim base` are already pinned changes the route substantially. You should target the fixed-fibre height squeeze, not a general bundle theorem.

The hard requirements become:

- identify the fibre coordinate ring as `B ⧸ mB`;
- prove flatness after restricting to a rank-`r` chart;
- handle localization/open-chart dimension;
- handle components if the total is reducible.

This avoids product dimension `dim(U × F)` and avoids upper semicontinuity.

**5. Module Budget + Risk**

For the narrowed route: **~5-8 focused modules** if the domain/component story is clean; **~8-10** if reducible component assembly is painful.

Likely modules:

1. fixed-fibre flat height squeeze;
2. rank-`r` principal charts and “nonempty principal open has same dimension”;
3. coordinate-ring and fibre-quotient identification;
4. local trivialisation implies flatness;
5. component/top-dimensional assembly;
6. final `varietyDim`/codim bridge.

Residual risk is **not** Mathlib’s going-down/height API. The risk is the project geometry: algebraising the local trivialisation, proving the right localized map is flat, and making reducible components line up with the already-known `cCodim` value. The full bundle theorem should be roadmapped; the narrowed height-squeeze is the buildable route.