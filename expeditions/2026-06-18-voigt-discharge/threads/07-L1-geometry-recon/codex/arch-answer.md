1. **A avoids the new scheme-to-`ringKrullDim` dimension bridge.**

S new bridge needed? **YES:** `Scheme` dimension/topological dimension of the orbit closure -> underlying space -> `topologicalKrullDim` -> affine identification with `PrimeSpectrum (R ⧸ I)` -> `PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim` / `IsHomeomorph.topologicalKrullDim_eq` -> your `varietyDim`.

A new bridge needed? **NO scheme-dimension bridge:** it stays at `A := R ⧸ I`, localizes at the maximal ideal of `M`, uses local regularity + cotangent dimension. But do not hide the extra ring bridge: `ringKrullDim A = ringKrullDim Aₚ` at the closed orbit point, or equivalently “local dimension at `M` equals global dimension of the irreducible variety.”

2. **Mathlib surface.**

S provides, by your audit: `smooth_of_grpObj_of_isAlgClosed`, `Scheme.Hom.dense_smoothLocus_of_perfectField`, `PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim`, `IsHomeomorph.topologicalKrullDim_eq`, `Ideal.Quotient.isDomain_iff_prime`, `PrimeSpectrum.irreducibleSpace`.

S forces you to build: GL as schemes, product group scheme, action morphism, orbit map, scheme/rank-locus comparison, dominance/image-closure statements, smooth target-point extraction, tangent/differential comparison, and final scheme-dimension transport.

A provides: `MvPolynomial.vanishingIdeal`, `MvPolynomial.pderiv`, `IsLocalRing.CotangentSpace`, `IsRegularLocalRing.iff_finrank_cotangentSpace`, `Algebra.smoothLocus`, `isOpen_smoothLocus`.

A forces you to build: maximal ideal/residue field of `M`, cotangent/Jacobian computation, cotangent dimension = `finrank (range delta)`, regularity at `M`, G-invariance of regular/smooth locus, orbit-open/dense-in-rank-locus, and local/global dimension equality at the closed point.

3. **Crux: generic smoothness.**

Generic smoothness is not cleanly point-set at this pin if the only density theorem is `Scheme.Hom.dense_smoothLocus_of_perfectField`. `Algebra.smoothLocus` plus openness is not by itself a dense/nonempty smooth-locus theorem.

But this does **not** force full S. It only forces a small affine-Spec detour for `Spec(A) -> Spec(k)` unless you prove a ring-side generic smoothness theorem yourself. Do not model `G`, orbit maps, or orbit closures as schemes just to access generic smoothness.

4. **Smooth point -> regular local ring.**

Harder than it looks. Standard math: smooth finite-type algebra over a field has regular local rings. Mathlib path, if available, would be:

`p ∈ Algebra.smoothLocus k A`
-> localized algebra is smooth over `k`
-> smooth over regular base field implies regular local ring
-> `IsRegularLocalRing (Localization.AtPrime p)`.

You report no direct bridge, so expect to build a commutative-algebra lemma. The cotangent computation is the cleaner load-bearing lemma:

`finrank k (IsLocalRing.CotangentSpace (Localization.AtPrime p)) = finrank k (LinearMap.range delta)`,

after identifying the residue field with `k`. Cleaner, but it does not replace regularity or local/global dimension.

5. **Third routes.**

Orbit-map fibre dimension / `dim O = dim G - dim Stab`: elegant on paper, bad in Lean here. It needs fibre-dimension or quotient/orbit scheme infrastructure, plus stabilizer scheme smoothness. Cost: worse than A, close to S.

Direct rational parametrization/local slice: possible for type A if you already have normal forms and rank charts. It avoids generic smoothness, but requires bespoke coordinate chart algebra and a dense-open chart proof. Cheaper only if that infrastructure is already mostly formalized.

Direct determinantal/rank-locus dimension: likely worst. You would rebuild height/dimension theory for quiver determinantal ideals.

6. **Net.**

Use **A**, with a minimal affine-scheme import only to obtain dense smooth locus if necessary. Do not choose S unless you actually need reusable scheme-orbit infrastructure later.

RECOMMENDATION = A, HARDEST = prove the closed orbit point `M` has a regular local ring of the correct global dimension, KILL = if you cannot get a smooth/regular closed point in the open orbit without developing substantial Nullstellensatz/local-global dimension infrastructure.