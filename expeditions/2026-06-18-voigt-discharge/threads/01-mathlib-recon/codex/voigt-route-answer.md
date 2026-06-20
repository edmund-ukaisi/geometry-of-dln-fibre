**A. Route Verdict**
The tangent+smoothness route is the right mathematical route and probably the best reusable Lean route, but it is not “close” in Mathlib. Mathlib has generic smoothness and regular-local cotangent foundations, but the missing bridge is large: concrete affine tangent spaces, smooth point to regular local ring, orbit locally closed/open in its closure, and height = ambient dimension minus local/scheme dimension.

Orbit-dimension and fibre-dimension routes are not cleaner in Lean: they need stabilizer group schemes, quotient/orbit dimension, and fibre-dimension theorems. The rank-locus/determinantal route may be cleaner for equioriented type A on paper, but Mathlib appears to have no determinantal-ideal height/rank-locus geometry, so it becomes a separate large sublibrary.

**B. Pillar Coverage**
**P1. Krull Dimension / Height**

PRESENT, verified in v4.29 source:
- `ringKrullDim`
- `Ring.KrullDimLE`
- `FiniteRingKrullDim`
- `ringKrullDim_le_of_surjective`
- `ringKrullDim_quotient_le`
- `ringKrullDim_eq_of_ringEquiv`
- `ringKrullDim_eq_zero_of_field`
- `Ideal.primeHeight`
- `Ideal.height`
- `Ideal.height_eq_primeHeight`
- `Ideal.primeHeight_le_ringKrullDim`
- `Ideal.height_le_ringKrullDim_of_ne_top`
- `IsLocalization.AtPrime.ringKrullDim_eq_height`
- `IsLocalRing.maximalIdeal_height_eq_ringKrullDim`
- `Polynomial.ringKrullDim_of_isNoetherianRing`
- `MvPolynomial.ringKrullDim_of_isNoetherianRing`
- `PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim`
- Krull height theorem inequalities such as `Ideal.height_le_spanFinrank`, `height_le_ringKrullDim_quotient_add_spanFinrank`, `ringKrullDim_le_ringKrullDim_quotient_add_spanFinrank`.

ABSENT / inferred absent:
- No catenary / universally catenary API found.
- No ready theorem `height p + ringKrullDim (R ⧸ p) = ringKrullDim R`.
- No ready theorem `height I = n - dim V(I)` for `MvPolynomial (Fin n) k`.
- No ideal-level `coheight` dimension formula found; only generic `Order.coheight`.

**P2. Tangent / Cotangent / Regularity**

PRESENT:
- `KaehlerDifferential`, notation `Ω[A⁄R]`, `KaehlerDifferential.D`.
- `Ideal.Cotangent`, `Ideal.cotangentToQuotientSquare`, `Ideal.cotangentEquivIdeal`.
- Local-ring cotangent space: `CotangentSpace R := (maximalIdeal R).Cotangent`.
- `IsRegularLocalRing`.
- `isRegularLocalRing_iff`.
- `IsRegularLocalRing.iff_finrank_cotangentSpace`, giving regular local ring iff `Module.finrank (ResidueField R) (CotangentSpace R) = ringKrullDim R`.

ABSENT / inferred absent:
- No packaged `ZariskiTangentSpace` for affine varieties.
- No ready bridge “linearized equations = tangent space”.
- No found theorem `Smooth/IsSmoothAt ⇒ IsRegularLocalRing`.
- No ready theorem identifying tangent dimension of a `k`-point with `finrank` of local cotangent space.

**P3. Smoothness / Generic Smoothness**

PRESENT:
- `Algebra.FormallySmooth`.
- `Algebra.Smooth`.
- `Algebra.smooth_iff`.
- `RingHom.FormallySmooth`.
- `RingHom.Smooth`.
- `RingHom.smooth_def`.
- `RingHom.Smooth.propertyIsLocal`.
- `Algebra.IsSmoothAt`.
- `Algebra.smoothLocus`.
- `Algebra.isOpen_smoothLocus`.
- `Algebra.smoothLocus_eq_univ_iff`.
- `Algebra.IsSmoothAt.exists_notMem_smooth`.
- `Algebra.IsSmoothAt.exists_notMem_isStandardSmooth`.
- Scheme smoothness: `AlgebraicGeometry.Smooth`.
- `Scheme.Hom.smoothLocus`.
- `Scheme.Hom.mem_smoothLocus`.
- `Scheme.Hom.isOpen_smoothLocus`.
- `Scheme.Hom.smoothLocus_eq_top_iff`.
- Generic smoothness over perfect fields:
  `Scheme.Hom.genericPoint_mem_smoothLocus_of_perfectField`,
  `Scheme.Hom.dense_smoothLocus_of_perfectField`.
- Group-scheme smoothness over alg. closed fields:
  `AlgebraicGeometry.smooth_of_grpObj_of_isAlgClosed`.

ABSENT / inferred absent:
- No regular locus API found.
- No orbit/stabilizer smoothness or orbit-dimension API.
- Generic smoothness exists, but applying it to your concrete orbit closure still needs the affine/scheme bridge.

**P4. Irreducibility / Variety Side**

PRESENT:
- Concrete Nullstellensatz API:
  `MvPolynomial.zeroLocus`,
  `MvPolynomial.vanishingIdeal`,
  `MvPolynomial.vanishingIdeal_zeroLocus_eq_radical`,
  `MvPolynomial.IsPrime.vanishingIdeal_zeroLocus`,
  `MvPolynomial.isMaximal_iff_eq_vanishingIdeal_singleton`.
- Spectrum closed-set API:
  `PrimeSpectrum.zeroLocus`,
  `PrimeSpectrum.vanishingIdeal`,
  `PrimeSpectrum.isClosed_iff_zeroLocus`,
  `PrimeSpectrum.isClosed_iff_zeroLocus_ideal`,
  `PrimeSpectrum.isClosed_iff_zeroLocus_radical_ideal`,
  `PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure`,
  `PrimeSpectrum.vanishingIdeal_closure`,
  `PrimeSpectrum.isIrreducible_zeroLocus_iff`,
  `PrimeSpectrum.isIrreducible_iff_vanishingIdeal_isPrime`,
  `PrimeSpectrum.irreducibleSpace`.
- General topology:
  `IsIrreducible.image`,
  `IsPreirreducible.image`,
  `isIrreducible_iff_closure`.
- Affine schemes/spaces:
  `AlgebraicGeometry.AffineSpace`,
  `AlgebraicGeometry.AffineSpace.SpecIso`,
  `AlgebraicGeometry.AffineSpace.homOfVector`,
  `AlgebraicGeometry.AffineSpace.homOverEquiv`.

ABSENT / inferred absent:
- No packaged affine algebraic variety category over `k`.
- No GL_n as an algebraic variety/scheme found. `Matrix.GeneralLinearGroup` exists as a type/group, not as a ready scheme object.
- No ready product-of-GL irreducibility theorem.
- No ready orbit map/orbit closure/algebraic group action API.
- No determinantal rank-locus ideal-height API found.

**C. Field Hypotheses**
Cleanest Lean hypothesis: `[Field k] [IsAlgClosed k]`.

Why:
- Nullstellensatz / closed k-point dictionary uses `[IsAlgClosed k]`.
- Generic smoothness in Mathlib needs `[PerfectField k]`; `[IsAlgClosed k]` supplies this via the instance `perfectField [IsAlgClosed k]`.
- No characteristic zero hypothesis is needed if you assume algebraically closed.
- Smooth ⇒ regular should not mathematically need algebraic closedness, but the theorem is not found as a ready Mathlib bridge.
- If you weaken to merely perfect, generic smoothness survives, but your concrete `MvPolynomial.zeroLocus`/`vanishingIdeal` closure story becomes harder.

**D. Build Ladder**
1. **Affine coordinate wrappers** — one PR/tide.
   Package `Rep_d` as `MvPolynomial` variables, coordinate evaluation, polynomial maps, vanishing ideals, closure as radical/prime ideal where possible.

2. **GL and orbit map geometry** — module to sizeable module.
   Model each `GL_n` as the principal open `D(det)` in affine matrix space; product as a principal open/localization. Prove irreducible/reduced/finite presentation. Define the orbit morphism and prove its image closure is irreducible.

3. **Concrete tangent spaces** — sizeable module.
   Define affine Zariski tangent at a `k`-point, prove tangent to zero locus is the kernel of linearized equations, prove tangent functoriality for polynomial maps, and identify the orbit-map differential with your `δ⁰`.

4. **Smooth point on the orbit** — module to sizeable module.
   Use `Scheme.Hom.dense_smoothLocus_of_perfectField`; prove smooth locus is stable under the group action; prove the orbit is locally closed/open in its closure; translate a smooth orbit point to `M`.

5. **Height/dimension bridge** — sizeable sub-library.
   Prove the needed affine dimension formula, preferably the tailored form:
   for prime `I ≤ k[x₁,…,xₙ]`, if a closed point of `V(I)` is smooth with tangent dimension `t`, then `I.height = n - t`. This is the largest missing piece.

6. **Final Voigt assembly** — one PR/tide.
   Combine `height = n - tangentDim`, `tangentDim = dim im δ⁰`, and your existing linear algebra `dim C¹ - dim im δ⁰ = dim Ext¹`.

Biggest must-build pieces:
- Height/dimension formula for polynomial rings or a tailored smooth-point height theorem.
- Affine Zariski tangent API and linearization lemmas.
- Smooth/regular local bridge.
- GL/orbit closure geometry.
- Orbit locally closed/open-in-closure theorem.

**E. Biggest Risk**
The main risk is not generic smoothness; Mathlib has that. The risk is the height bridge. Since your codimension is literally `Ideal.height`, every non-determinantal route must eventually prove a serious dimension formula connecting height, local dimension, and tangent dimension. That is the part most likely to turn this from a theorem into a commutative-algebra sublibrary.
