**A**

Projection compatibility is reachable at modest cost only as a **local algebra factorization**, not as a full scheme-pullback theorem unless the target rank-chart presentation is already banked.

Sharp target:

```lean
(schurToDsigAt I).comp (targetSchurComap I)
  = localizedMultComapAt I
```

where, inferentially,

```lean
targetSchurComap I :
  TargetMatrixPivotLoc I →ₐ[k] SchurLoc I

localizedMultComapAt I :
  TargetMatrixPivotLoc I →ₐ[k] Localization.Away (chartDsigAt I)
```

is induced by `multComap d` plus the lemma that the target pivot determinant maps to `chartDsigAt I`.

If you already have an equivalence

```lean
targetSchurChartEquiv I :
  TargetRankChartLoc I ≃ₐ[k] SchurLoc I
```

then the stronger equality is honest:

```lean
schurToDsigAt I =
  localizedMultComapAt I |>.comp (targetSchurChartEquiv I).symm.toAlgHom
```

Key proof shape: localization extensionality, then `MvPolynomial.algHom_ext` on target matrix coordinate variables. The key obstruction is not tensor algebra; it is proving the pivot determinant and Schur reconstruction formulas really match `multComap` after quotient/localization. Mathlib API names are inference, but expect `IsLocalization.Away.mapₐ`, an `IsLocalization` ext lemma, and `MvPolynomial.algHom_ext`.

**B**

A genuine target-side overlap is not an AlgEquiv

```lean
SchurLoc I ⊗[k] F ≃ₐ[k] SchurLoc J ⊗[k] F
```

on the unlocalized products. The correct object is double-localized.

Name it:

```lean
targetProductOverlapTransition I J
```

with shape:

```lean
Localization.Away uIJ (SchurLoc I ⊗[k] F)
  ≃ₐ[k]
Localization.Away uJI (SchurLoc J ⊗[k] F)
```

where

```lean
uIJ := triv I (algebraMap _ (Localization.Away (chartDsigAt I)) (chartDsigAt J))
```

up to your actual names.

Definition should be by conjugating the existing source/base overlap through the two localized product trivializations:

```lean
(localizedTriv I J).symm ≪≫ chartOverlapTransition I J ≪≫ localizedTriv J I
```

Reachable laws: inverse/round-trip, restriction to the canonical double-overlap map, and compatibility with the localized trivializations. Full bundled triple cocycle is a separate packaging problem because the domains are dependent double/triple localizations with chart-dependent `SchurLoc`s. `transitionFactors` is useful for explicit formulas/base-algebraicity, but it does not by itself supply the target-side cocycle object.

**C**

1. Projection factorization: very high value / medium cost. Build first; it turns the existing `schurToDsigAt` flatness into geometry of `mult`.

2. Chartwise flatness headline over named base map: high value / low cost. Package what is already proved, ideally after A so the base map is visibly geometric.

3. `targetProductOverlapTransition` pairwise on double-localized tensor products: high value / medium-high cost. Build as pairwise transition data, not a global bundle.

4. Global `Flat π`: highest mathematical value / high cost. Roadmap ceiling, not the next increment; it needs projection compatibility, target rank-chart identifications, triple-overlap coherence, and local-to-global flatness packaging.

**D**

Trap: proving more theorems over `schurToDsigAt` while never mentioning `multComap`.

Detection: if the theorem statement has no `multComap`, no target Schur chart comorphism, and no equality/factorization of AlgHoms, it is only flatness over an artificial chart base map. It does not prove compatibility with the geometric projection `mult`.