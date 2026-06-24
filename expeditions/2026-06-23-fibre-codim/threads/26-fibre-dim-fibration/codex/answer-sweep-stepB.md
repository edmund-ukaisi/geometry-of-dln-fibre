Checked against the local v4.29 worktree. My skeptical verdict: **Step B is the hard rung; neither proposed route is currently “clean” in this affine engine.** The sweep is mathematically right, but formalizing it without schemes or a fibre-dimension theorem still requires a substantial replacement theorem.

**1. B-trdeg vs B-orbit**

`B-trdeg` is conceptually closest to the statement, but it is not clean in Mathlib v4.29. `Algebra.trdeg_add_eq` exists and is already used locally in `AffineNoetherRank.trdeg_eq_of_integral_injective`, but it only gives tower additivity. It does **not** identify the relative trdeg with the dimension of the closed fibre over `E`.

The missing bridge is exactly:

```lean
generic fibre dimension = dimension of the homogeneous closed fibre F
```

Homogeneity gives isomorphic closed fibres, but Mathlib does not provide “all closed fibres isomorphic ⇒ generic fibre has same dimension”. Proving that without constructibility/flatness means building an explicit generic-fibre isomorphism over `FractionRing O(Mat^{=r})`, then proving base-change invariance of `varietyDim` for `F`. That is not a short lemma chain.

`B-orbit` is also not a small generalization of `OrbitPullbackDim`. The existing theorem

```lean
varietyDim_eq_ringKrullDim_range_orbitPullback
```

is for the image of one point orbit map `G_d → Rep_d`. For a sweep `H × F → Rep_d`, you would need a new coordinate ring for `H × F`, a pullback algebra map, product dimension, and then an image/fibre quotient computation. The current `OrbitPullbackDim` machinery does not compute `dim(domain) - dim(stabilizer)`.

**2. Homogeneous fibres vs generic fibre**

There is an H-equivariant idea, but it still has hard algebra:

1. Let `K = FractionRing O(Mat^{=r})`.
2. Show the generic rank-`r` matrix over `K` is `H(K)`-equivalent to `E`.
3. Use `mult_smul` to identify the generic fibre with `F_K`.
4. Prove `dim_K F_K = dim_k F`.

Step 4 is the wall. It needs base-change dimension invariance, likely via tensor products/localization/minimal primes. That is not currently packaged.

**3. Product dimension**

No ready-made v4.29 theorem found for:

```lean
Algebra.trdeg k (A ⊗[k] B) =
  Algebra.trdeg k A + Algebra.trdeg k B
```

nor for `ringKrullDim` of tensor products/products of affine varieties.

What exists:

```lean
Algebra.trdeg_add_eq
Algebra.trdeg_add_le
MvPolynomial.trdeg_of_isDomain
AlgEquiv.trdeg_eq
Module.Flat.of_linearEquiv
Module.flat_of_localized_span
RingHom.Flat.propertyIsLocal
IsLocalization.flat
Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown
```

So tensor/product dimension would be a new project. For reducible `F`, it is worse: `varietyDim` is max-over-components via minimal primes, not just domain trdeg.

**4. Step C**

Cheap, but not definitional unless the exact-rank closure lemma is already in hand.

Since

```lean
varietyDim Z =
  (ringKrullDim (MvPolynomial σ k ⧸ vanishingIdeal k Z)).unbotD 0
```

this is immediate from:

```lean
vanishingIdeal k (canonicalCoord d '' productRankLocus d r)
  =
vanishingIdeal k (canonicalCoord d '' productRankLocusLE d r)
```

or from a `repClosure` equality. But if `Σ̄^r` is represented as `productRankLocusLE d r`, you still need the density/closure statement for exact rank. Once that lemma exists, Step C is just `rw [varietyDim, hvanishing]`.

**5. Recommended decomposition**

I would isolate the hard theorem honestly:

```lean
-- HARD RUNG
theorem varietyDim_exactRank_eq_delta_add_varietyDim_fibre
  ...
```

Then split supporting modules:

```lean
Core.ExactRankClosure
  productRankLocusLE_eq_repClosure_productRankLocus
  vanishingIdeal_productRankLocus_eq_productRankLocusLE
  varietyDim_productRankLocus_eq_productRankLocusLE

Core.EndBaseChangeSweep
  sweep_surjective_onto_exactRank
  fibre_translate_eq
  all_rank_r_fibres_isomorphic
  -- uses mult_smul, exists_baseChange_of_rank_eq,
  -- image_smul_fibre, codimRepCanonical_fibre_eq_of_rank_eq

Core.HomogeneousSweepDim  -- HARD
  varietyDim_homogeneous_sweep_eq_base_add_fibre
```

The hard module cannot currently be discharged by existing Mathlib alone. It must choose one of:

- explicit exact-rank chart trivialization and flatness/local freeness;
- generic-fibre plus base-change dimension theorem;
- product/quotient dimension theorem for `H × F → Σ^r`.

All three are substantial. So route c is a good **organizing interface**, but Step B hides a wall comparable to the earlier flatness/product-dimension wall. The local probes in `FibreDimFibration`, `FlatTrivialProductProbe`, and `ChartFlatnessProbe` are already pointing at the same obstruction.