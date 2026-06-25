**Q1**

- `Algebra.IsAlgebraic D (FractionRing D)`: not an instance, and no `IsFractionRing.isAlgebraic` declaration at v4.29. Use theorem `IsFractionRing.comap_isAlgebraic_iff`.

```lean
haveI : Algebra.IsAlgebraic D (FractionRing D) :=
  (IsFractionRing.comap_isAlgebraic_iff
    (A := D) (K := FractionRing D) (C := FractionRing D)).mpr
    (inferInstance : Algebra.IsAlgebraic (FractionRing D) (FractionRing D))
```

Related names:
`IsFractionRing.isAlgebraic_iff` is elementwise.
`IsFractionRing.comap_isAlgebraic_iff` is the whole-algebra version.
`Algebra.IsAlgebraic.of_finite` is the instance backing the self-algebraic `inferInstance`.

- `Algebra (Localization.Away g) (FractionRing D)` and tower `D → D[1/g] → Frac D`: use theorem/abbrev `IsLocalization.localizationAlgebraOfSubmonoidLe` plus theorem `IsLocalization.localization_isScalarTower_of_submonoid_le`.

```lean
let hM : Submonoid.powers g ≤ nonZeroDivisors D :=
  powers_le_nonZeroDivisors_of_noZeroDivisors hg

letI : Algebra (Localization.Away g) (FractionRing D) :=
  IsLocalization.localizationAlgebraOfSubmonoidLe
    (Localization.Away g) (FractionRing D)
    (Submonoid.powers g) (nonZeroDivisors D) hM

letI : IsScalarTower D (Localization.Away g) (FractionRing D) :=
  IsLocalization.localization_isScalarTower_of_submonoid_le
    (Localization.Away g) (FractionRing D)
    (Submonoid.powers g) (nonZeroDivisors D) hM
```

- `IsFractionRing (Localization.Away g) (FractionRing D)`: theorem, not automatic for `Away`.

```lean
letI : IsFractionRing (Localization.Away g) (FractionRing D) :=
  IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
    (Submonoid.powers g) (Localization.Away g) (FractionRing D)
```

Exact signature source shape:

```lean
IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
  [IsDomain R] (M : Submonoid R) (S T : Type*) [CommRing S] [CommRing T]
  [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
  [IsLocalization M S] [IsFractionRing R T] :
  IsFractionRing S T
```

- `trdeg_add_eq`: exact name is root `trdeg_add_eq`, theorem.

```lean
trdeg_add_eq
  [Nontrivial R] {A : Type v} [CommRing A] [NoZeroDivisors A]
  [Algebra R A] [Algebra S A]
  [FaithfulSMul R S] [FaithfulSMul S A] [IsScalarTower R S A] :
  Algebra.trdeg R S + Algebra.trdeg S A = Algebra.trdeg R A
```

Global variables also include `[CommRing R] [CommRing S] [Algebra R S]`.

- Faithfulness names:
  - `faithfulSMul_iff_algebraMap_injective`: theorem.
  - `FaithfulSMul.algebraMap_injective`: theorem.
  - `RingHom.injective`: theorem, for maps out of a simple ring into a nontrivial semiring.
  - `IsFractionRing.injective`: theorem.
  - `IsFractionRing.instFaithfulSMul`: instance, generated from anonymous source instance, for `[IsFractionRing R K]`.
  - `FractionRing.instFaithfulSMul`: instance, generated from anonymous source instance.

Useful local incantations:

```lean
haveI : FaithfulSMul k D :=
  (faithfulSMul_iff_algebraMap_injective k D).mpr
    (RingHom.injective (algebraMap k D))

haveI : FaithfulSMul (Localization.Away g) (FractionRing D) :=
  (faithfulSMul_iff_algebraMap_injective
    (Localization.Away g) (FractionRing D)).mpr
    (IsFractionRing.injective (Localization.Away g) (FractionRing D))
```

Gap to flag: for applying `trdeg_add_eq k (Localization.Away g) (FractionRing D)`, you also need `FaithfulSMul k (Localization.Away g)`. Use `IsLocalization.injective` plus composition.

```lean
haveI : FaithfulSMul k (Localization.Away g) :=
  (faithfulSMul_iff_algebraMap_injective k (Localization.Away g)).mpr <| by
    rw [IsScalarTower.algebraMap_eq k D (Localization.Away g)]
    exact (IsLocalization.injective (Localization.Away g) hM).comp
      (RingHom.injective (algebraMap k D))
```

- Direct trdeg-localization lemma: I found no `Algebra.trdeg_localization`, `IsLocalization.trdeg`, `trdeg_Away`, or `trdeg_FractionRing` in v4.29. Nearest alternatives: `trdeg_add_eq`, `trdeg_add_le`, `trdeg_eq_zero`, `trdeg_eq_zero_iff`, `AlgEquiv.trdeg_eq`.

**Q2**

- `[IsDomain (Localization.Away g)]`: not automatic from `[IsDomain D]` alone. Use theorem `IsLocalization.isDomain_localization` or `IsLocalization.isDomain_of_le_nonZeroDivisors`.

```lean
let hM : Submonoid.powers g ≤ nonZeroDivisors D :=
  powers_le_nonZeroDivisors_of_noZeroDivisors hg

letI : IsDomain (Localization.Away g) :=
  IsLocalization.isDomain_localization
    (M := Submonoid.powers g) hM
```

Related automatic instance: `Localization.instNoZeroDivisors`, but that only gives `NoZeroDivisors`, not `Nontrivial`.

- `[Algebra D (Localization.Away g)]` and `[Algebra k (Localization.Away g)]`: automatic via instance `OreLocalization.instAlgebra`.

- `[IsLocalization.Away g (Localization.Away g)]`: automatic because `IsLocalization.Away` is an abbrev and instance `Localization.isLocalization` applies.

- `[IsScalarTower k D (Localization.Away g)]`: source-inferable in v4.29, but no separate named localization instance found. Robust explicit fallback:

```lean
letI : IsScalarTower k D (Localization.Away g) :=
  IsScalarTower.of_algebraMap_eq (fun x => rfl)
```

- `[Algebra.FiniteType k (Localization.Away g)]`: automatic instance `instFiniteTypeAway` from `Mathlib.RingTheory.Localization.Away.AdjoinRoot`.

It is exactly the instance:

```lean
instance {S : Type*} [CommRing S] [Algebra R S] [Algebra.FiniteType R S] (f : S) :
    Algebra.FiniteType R (Localization.Away f)
```

It composes using theorem `Algebra.FiniteType.trans`. The finite-presentation analogue is instance `instFinitePresentationAway`; helper theorem `Algebra.FinitePresentation.of_isLocalizationAway`.