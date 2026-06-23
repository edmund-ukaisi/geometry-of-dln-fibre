Short answer: the clean general statement is not realistically reachable in Mathlib v4.29 without building substantial dimension theory for morphisms. The group/homogeneous-base story is not the main blocker; the blocker is turning “finite type family with constant fibre” into a `ringKrullDim` equality.

**1. What The Bundle Proof Needs**

To prove

```lean
varietyDim X = varietyDim Y + varietyDim (fibre f y)
```

for a locally trivial affine-variety bundle, you would need roughly:

| Needed lemma/theorem | Status in Mathlib v4.29 terms |
|---|---|
| Polynomial map induces a coordinate-ring map `k[Y] →ₐ[k] k[X]` | Mostly local/project-specific for your closed-subset model. Mathlib has the algebra pieces, not your variety wrapper. |
| Dominance iff coordinate-ring map is injective | Close cousins in scheme/algebraic geometry, but for your `vanishingIdeal` affine-subset setup this is a Nullstellensatz bridge you likely must prove. |
| Fibre coordinate ring identification: `k[fibre f y] ≃ k[X] ⊗_{k[Y]} k` or quotient by pulled-back maximal ideal | Algebra pieces exist: quotients, tensor products, ideals. The geometric fibre/vanishing-ideal equality is missing for your model. |
| Equivariance + transitive `G`-action gives all fibres isomorphic | Group-action API exists, but algebraic group actions/orbit varieties/local triviality are not packaged at this level. Likely project-specific. |
| Zariski local triviality as first-class data: open cover `Uᵢ` with `f ⁻¹ Uᵢ ≃ Uᵢ × F` | Essentially absent for affine varieties. Scheme local-property infrastructure exists, but not a ready affine-variety bundle API. |
| Dimension is local on a nonempty open cover | Missing for your `varietyDim`. There are Krull/topological dimension APIs, but not this affine-variety theorem. |
| Nonempty open subset of irreducible affine variety has same dimension | Missing in your wrapper. Ring-localization height tools are close cousins. |
| Product dimension: `dim (U × F) = dim U + dim F` | Major missing piece. For `F = A^r`, this reduces to polynomial-ring dimension, but for general affine `F` it needs tensor-product/finitely-generated-algebra dimension theory. |
| Convert dimension equality to codimension equality | You already have the irreducible catenary complement using `height_add_ringKrullDim_quotient_eq`; this part is available once irreducibility/primality hypotheses are in place. |

Mathlib does have the basic `ringKrullDim` and `Ideal.height` infrastructure, and the smooth/standard-smooth APIs exist on both the ring and scheme sides. Current generated docs expose `AlgebraicGeometry.Smooth`, `SmoothOfRelativeDimension`, and standard-smooth relative-dimension predicates such as `RingHom.IsStandardSmoothOfRelativeDimension` / `Algebra.IsStandardSmoothOfRelativeDimension`; they also expose the basic Krull-dimension and ideal-height namespaces. citeturn10view0turn12view0turn16view1turn18view1

**2. Shorter Routes**

The shortest viable route is not “formalize locally trivial bundles”; it is a commutative-algebra theorem of the following shape:

```lean
-- schematic statement
φ : A →ₐ[k] B
A, B finitely generated k-algebras
A irreducible/equidimensional/catenary
B flat over A
all fibres have ringKrullDim d
⊢ ringKrullDim B = ringKrullDim A + d
```

Then your homogeneous/equivariant input only has to show flatness or local triviality, and that all closed fibres are isomorphic, hence have the same `varietyDim`.

Mathlib has `Flat`, smooth/étale APIs, standard-smooth relative-dimension structure, base-change style infrastructure, and polynomial-ring Krull-dimension lemmas such as the `MvPolynomial.ringKrullDim_of_isNoetherianRing` theorem you mention. But it does not appear to have the needed theorem:

```lean
flat finite type morphism + constant fibre dimension
  ⇒ dim total = dim base + fibre dimension
```

nor the weaker generic fibre theorem:

```lean
dominant finite type morphism of irreducible affine varieties
  ⇒ dim X = dim Y + dim generic fibre
```

A global trivialisation helps only in special cases. If you can prove

```lean
k[X] ≃ₐ[k] k[Y][t₁, ..., tᵣ]
```

then `MvPolynomial.ringKrullDim_of_isNoetherianRing` basically gives the result. If instead

```lean
k[X] ≃ₐ[k] k[Y] ⊗[k] k[F]
```

for a general affine fibre `F`, you still need the missing tensor-product/product dimension theorem.

The smooth route is also too narrow. If `f` is smooth of relative dimension `d`, Mathlib has close API support for expressing that, but you would still need the theorem connecting `SmoothOfRelativeDimension d` to `ringKrullDim` of total spaces and fibres. And your bundle fibre need not be smooth.

**3. Hardest Missing Piece**

The real missing theorem is a dimension theorem for finite-type morphisms, preferably in ring form:

```lean
-- one useful target
theorem ringKrullDim_eq_base_add_fibreDim_of_flat_finiteType
  (φ : A →+* B)
  [IsNoetherianRing A] [Algebra.FiniteType A B]
  [Flat A B]
  (constant_fibre_dim : ∀ p, ringKrullDim (B ⊗[A] κ(p)) = d) :
  ringKrullDim B = ringKrullDim A + d
```

A more classical variant would be the generic fibre dimension theorem plus upper semicontinuity/equidimensionality for flat finite-type maps.

At this Mathlib pin, I would budget this as a substantial development, not a lemma or two: roughly 8-15 focused modules if you stay affine/ring-theoretic, more if you route through schemes. The build would include coordinate-ring/fibre-ring identification, localization and open-subset dimension lemmas, product/tensor-product dimension over algebraically closed fields, generic fibre dimension, flat/equidimensional fibre dimension, and bridges back to your `varietyDim`/`height` definitions.

So: for the paper formalisation, the pragmatic route is to avoid proving the general homogeneous-bundle theorem unless it becomes central. Use explicit parametrisation/Jacobian-rank/trdeg computations where possible, or prove a narrowly tailored global-trivialisation/polynomial-extension statement for the specific fibre.
