**Q1**

Use **(a)**: the generic rank should be the `FractionRing B`-rank of the span of the differentials in `Ω[FractionRing B ⁄ k]`. This is the cleanest common target because A4.2 is field-theoretic and A4.3 can still compute it by localizing the cotangent/tangent calculation from `B`. I would not make the public rank a `B`-rank: even though `Ω[B/k]` is accessible because `B` is a localization, you then owe torsion/localization rank bookkeeping before comparing to trdeg. Also, do not rely on `K = FractionRing B` being algebraic over `E = k(f_selected)`; that is false unless the orbit map is generically finite. The honest A4.2 statement should be a finite-family char-zero differential-independence lemma inside the field `FractionRing B`.

- Recommended definition:
  ```lean
  noncomputable def genericDifferentialRank
      (k B ι : Type*) [Field k] [CommRing B] [IsDomain B]
      [Algebra k B] [Fintype ι] (f : ι → B) : ℕ :=
    Module.finrank (FractionRing B)
      (Submodule.span (FractionRing B)
        (Set.range fun i : ι =>
          KaehlerDifferential.D k (FractionRing B)
            (algebraMap B (FractionRing B) (f i))))
  ```
  If inference is brittle, add explicit `[Algebra k (FractionRing B)] [IsScalarTower k B (FractionRing B)]`.

- Known v4.29 APIs to use:
  - `KaehlerDifferential.D`
  - `KaehlerDifferential.map_D`
  - `KaehlerDifferential.mvPolynomialBasis`
  - `KaehlerDifferential.mvPolynomialBasis_repr_apply`
  - `KaehlerDifferential.isLocalizedModule_map`
  - `KaehlerDifferential.isLocalizedModule_of_isLocalizedModule`
  - `Fintype.range_linearCombination`

**Q2**

For a genuinely algebraic separable tower `k → E → K`, use **formal étaleness**, not formal unramifiedness. The exact triple is `(R,S,T) = (k,E,K)`, and the map is `KaehlerDifferential.mapBaseChange k E K : K ⊗[E] Ω[E⁄k] →ₗ[K] Ω[K⁄k]`. Mathlib already packages the injectivity as part of a linear equivalence:
`KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale k E K`. The subtlety is important: `FormallyUnramified.of_isSeparable` only gives `Subsingleton Ω[K⁄E]`; injectivity also needs the preceding `H1Cotangent E K` term killed, which is exactly what `FormallyEtale` supplies.

- Known v4.29 names:
  - `Algebra.FormallyEtale.of_isSeparable`
  - `KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale`
  - `Algebra.H1Cotangent.exact_δ_mapBaseChange`
  - `KaehlerDifferential.exact_mapBaseChange_map`
  - `LinearMap.exact_zero_iff_injective`

- Manual JZ route, if needed:
  ```lean
  Algebra.H1Cotangent.exact_δ_mapBaseChange k E K
  ```
  with `(R,S,T) = (k,E,K)`, then use `[Algebra.FormallyEtale E K]` to make `H1Cotangent E K` subsingleton.

- Char-zero algebraic route:
  - `PerfectField.ofCharZero`
  - `Algebra.IsAlgebraic.isSeparable_of_perfectField`
  - then `Algebra.FormallyEtale.of_isSeparable`

**Q3**

Yes, avoid a Jacobian matrix in the main formulation. Define the cotangent map as the finite linear-combination map whose range is exactly the differential span; then prove A4.3 by identifying this cotangent map with the dual of the localized infinitesimal orbit map, up to explicit `K`-linear equivalences coming from multiplication by the generic invertible matrices. The clean identity is not “pderiv entries equal δ”; it is a rank-preserving factorization of the generic tangent map through `(deformationδ M M)` after base change to `K = FractionRing B`. Then use dual-rank equality to pass between cotangent span rank and tangent image rank. The constant-rank-under-`G` step is not needed as a pointwise theorem; it is replaced by the single generic linear-equivalence calculation.

- Define:
  ```lean
  noncomputable def cotangentFamilyMap
      (k K ι : Type*) [Field k] [Field K] [Algebra k K]
      [Fintype ι] (F : ι → K) :
      (ι → K) →ₗ[K] Ω[K⁄k] :=
    Fintype.linearCombination K
      (fun i => KaehlerDifferential.D k K (F i))
  ```

- Rank bridge:
  - `Fintype.range_linearCombination`
  - `LinearMap.finrank_range_dualMap_eq_finrank_range`
  - `LinearEquiv.finrank_eq`
  - `LinearEquiv.finrank_map_eq`

- Kähler/derivation APIs:
  - `KaehlerDifferential.linearMapEquivDerivation`
  - `Derivation.liftKaehlerDifferential_comp_D`
  - `KaehlerDifferential.map_D`
  - `KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale`
  - `KaehlerDifferential.isLocalizedModule_map`

**Q4**

I would not leave separable algebraic base-change injectivity as the open obligation; Mathlib v4.29 already makes it almost immediate through formal étaleness. The scoped lemma that should carry A4.2 is the finite-family theorem below, because it hides the actual hard work: selecting a maximal algebraically independent subfamily and proving its differentials remain independent in `Ω[FractionRing B⁄k]` in characteristic zero. Then A4.4 can depend only on this lemma plus your A4.3 theorem. If you still want a small helper for the formally étale part, use the second signature and prove it immediately.

- Main scoped A4.2 lemma:
  ```lean
  theorem trdeg_adjoin_le_genericDifferentialRank
      (k B ι : Type*) [Field k] [CharZero k]
      [CommRing B] [IsDomain B] [Algebra k B] [Fintype ι]
      (f : ι → B) :
      (Algebra.trdeg k (Algebra.adjoin k (Set.range f))).toNat ≤
        genericDifferentialRank k B ι f := by
    -- open obligation: char-zero algebraic independence gives
    -- K-linear independence of the differentials in Ω[FractionRing B⁄k]
  ```

- Wrapper for your image algebra:
  ```lean
  theorem trdeg_subalgebra_le_genericDifferentialRank
      (A : Subalgebra k B) (hA : A = Algebra.adjoin k (Set.range f)) :
      (Algebra.trdeg k A).toNat ≤ genericDifferentialRank k B ι f := by
    simpa [hA] using trdeg_adjoin_le_genericDifferentialRank k B ι f
  ```

- Small formally étale helper:
  ```lean
  theorem kaehler_mapBaseChange_injective_of_isSeparable
      (k E K : Type*) [Field k] [Field E] [Field K]
      [Algebra k E] [Algebra E K] [Algebra k K] [IsScalarTower k E K]
      [Algebra.IsSeparable E K] :
      Function.Injective (KaehlerDifferential.mapBaseChange k E K) := by
    haveI : Algebra.FormallyEtale E K :=
      Algebra.FormallyEtale.of_isSeparable E K
    exact (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale k E K).injective
  ```

BIGGEST RISK: proving “algebraically independent finite family in a char-zero field has linearly independent Kähler differentials after embedding into `FractionRing B`”; cheapest fallback is to state exactly `trdeg_adjoin_le_genericDifferentialRank` as the one scoped A4.2 obligation.