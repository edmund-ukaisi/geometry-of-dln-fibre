**1. DIRECT FIBRE-CODIM**

Blocked for `B ≠ 0`.

- **KNOWN:** item 2 computes `codimRepCanonical (orbitRankLocus M)` for single full `GL_d` orbit closures.
- **KNOWN:** `fibre d 0 = productRankLocusLE d 0`, so r=0 works because the zero fibre is a finite union of those orbit closures.
- **KNOWN/INFER:** for `B ≠ 0`, `fibre d B` is not `GL_d`-stable: `mult(P • A) = P_N mult(A) P_0⁻¹`, so the full action moves it to another fibre.
- **MISSING:** any theorem turning “intersection with an outer-orbit slice” or “transverse fibre of `mult`” into a codimension formula.
- **Conclusion:** item-2 Voigt machinery does not apply directly. `B ≠ 0` breaks exactly the orbit-closure structure used for `B=0`.

No provable module count here, unless one builds a new slice/fibre-dimension theorem. Hardest missing theorem: `codim(fibre over a point of a smooth homogeneous base) = codim(total rank locus) + dim(base)`.

**2. HOMOGENEOUS-FIBRATION**

Mathematically right, but not cheap in Lean v4.29.

- **KNOWN:** rank-exact matrices form one `GL_{d_N} × GL_{d_0}` orbit.
- **KNOWN:** fibres over rank-`r` matrices are isomorphic by the outer action.
- **INFER:** the orbit dimension `r(d_0+d_N-r)` can be proved by explicit pivot charts, but Mathlib does not provide it as a ready determinantal-rank-stratum theorem.
- **MISSING:** algebraic group quotient/orbit dimension theorem, `dim G/H`, or `dim orbit = dim G - dim stabilizer`.
- **MISSING:** `dim(total space of a Zariski locally trivial bundle) = dim(base) + dim(fibre)`.
- **MISSING:** a ready AG theorem that an equivariant map over a single orbit with local sections has additive dimension.

Homogeneity alone does not avoid the wall. The moment you pass from “all fibres are isomorphic” to “dimension of the union is fibre + base”, you need the same missing fibre-dimension/local-triviality theorem.

No cheap provable route. If forced from scratch, this is roughly 7-10 modules: rank-stratum charts, local sections, algebraic trivializations, dimension of finite open covers, dimension of products/localizations, and the final codim bridge. Hardest sub-lemma: `codimRepCanonical`/`varietyDim` additivity for a finite Zariski-locally trivial affine bundle.

**3. ROUTE-C-STYLE DODGE**

Also blocked as a cheap route.

- **KNOWN:** Core has much of the route-c AG stack: height/codim via vanishing ideals, Krull/trdeg bridges, Kähler/Jacobian machinery, smooth-point regularity, and the orbit-pullback image pipeline.
- **KNOWN:** the fibre differential at `A` is
  ```text
  d(mult)_A(ΔA) = Σ_i A_N ... A_{i+1} · ΔA_i · A_{i-1} ... A_1.
  ```
- **INFER:** one can formalise this differential and compute its rank at carefully chosen smooth-looking points.
- **MISSING:** a parametrisation/image theorem for `fibre d B` analogous to `orbitPullback M` for orbit closures.
- **MISSING:** a theorem that the height of the level-set ideal of `mult - B` is controlled globally by that Jacobian rank.
- **MISSING:** the lower bound for every component of `fibre d B`, namely `dim fibre ≤ dim Σ^r - r(d_0+d_N-r)`. This is the bundle/fibre-dimension statement in disguise.

The derivative alone is not enough. At some points it gives the ambient level-set tangent rank; identifying the correct top-component dimension still needs either local triviality over the rank stratum or an equivalent global equidimensionality/lower-bound theorem.

No cheap provable module count. A from-scratch direct Jacobian route is likely 10+ modules and still has as hardest sub-lemma the global height lower bound for `Ideal.span {entries(mult-B)}`.

**4. CITE**

Yes, this is the honest move.

Use a small cited interface, separate from Aoyagi’s RLCT interface, named by content:

```lean
structure BundleShiftInterface
    (d : Fin (N + 1) → ℕ)
    (K : Type v) [Field K] [IsAlgClosed K] [CharZero K]
    (ι : ℝ →+* K) where
  cited_bundle_shift_lemma46 :
    ∀ (B : Matrix (Fin (d (Fin.last N))) (Fin (d 0)) ℝ) (r : ℕ),
      B.rank = r →
      (∀ i, r ≤ d i) →
      codimRepCanonical (fibre (k := K) d (B.map ι))
        =
      codimRepCanonical (productRankLocusLE (k := K) d r)
        + (r * (d 0 + d (Fin.last N) - r) : ℕ∞)
```

Then the consumer proves, using the landed `codim Σ̄^r = cCodim d r` bridge and existing `RlctInterface.cited_aoyagi_dln`:

```lean
I.rlct (lossDLN d B)
  = (((cCodim d r hr).toNat : ℝ)
      + (r * (d 0 + d (Fin.last N) - r) : ℝ)) / 2
```

Implementation size: 1 small DLN module, roughly 80-150 LoC if the aggregate `codim Σ̄^r = cCodim` theorem is already exposed. Hardest sub-lemma: not mathematical; it is the `ℕ∞.toNat` arithmetic/finite-codim transport after rewriting by the cited shift and the landed `cCodim` theorem.

**Slicker Proof?**

No global slick product isomorphism appears. For canonical `B_0`, one can write local block-Gaussian charts after choosing rank-`r` pivots through the layers, but those choices vary and amount to Grassmannian/flag data. That gives a local-trivialization proof, not a global affine product
`mult⁻¹(B) ≅ mult⁻¹(0 for d-r) × affine`.

So the constructive version still needs finite chart dimension, product dimension, localization/open-cover invariance, and gluing back to `codimRepCanonical`. That is not cheaper than citing Lemma 4.6.

Verdict: **CITE-lemma-4.6.**