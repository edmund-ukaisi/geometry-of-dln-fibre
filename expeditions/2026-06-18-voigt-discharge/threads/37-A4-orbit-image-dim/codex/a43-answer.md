**Q1**

Use the **hybrid Kähler/Jacobian-factorization route**, not explicit `pderiv(det⁻¹)` expansion.

Lean-cost ranking:

1. **Best:** define a generic tangent map `orbitJacobianK M : C0K →ₗ[K] C1K`, prove the Kähler span rank equals the row-rank/range-rank of this map, then prove
   ```lean
   orbitJacobianK M =
     targetGenericIsoK d ∘ₗ deformationδK M ∘ₗ domainGenericIsoK d
   ```
   up to exact order conventions. This avoids expanding adjugates.

2. **Worse:** compute all `pderiv` entries of `genericOrbitCoord`. It is possible, because Mathlib has localization/Kähler tools, but the inverse matrix contributes quotient-rule bookkeeping everywhere.

3. **Worst in Lean:** pure `AlgEquiv`-on-Ω homogeneity. Mathlib has `KaehlerDifferential.map`, but I did not find a ready `KaehlerDifferential.mapEquiv`; also the induced map from a field automorphism is naturally semilinear, not immediately a plain `K`-linear rank-preserving map.

For a localization element `b : B`, the workable formula is not “differentiate localization by hand” but:
```lean
KaehlerDifferential.map_D
-- map k k B K (D k B b) = D k K (algebraMap B K b)
```
plus `KaehlerDifferential.isLocalizedModule_map`. For `genericOrbitCoord`, differentiate the identity
```lean
genericUnit v * genericUnitInv v = 1
```
to get `d(P⁻¹) = -P⁻¹ dP P⁻¹`, rather than expanding `det⁻¹ • adjugate`.

Verified present locally: `KaehlerDifferential.map_D`, `mapBaseChange_tmul`, `isLocalizedModule_map`, `isLocalizedModule_of_isLocalizedModule`, `mvPolynomialBasis_repr_apply`.

**Q2**

Do not try to express constant rank primarily as an automorphism of `Ω[K⁄k]`. Mathlib has enough to build such maps from `KaehlerDifferential.map`, but it is not the cheapest surface.

Instead express homogeneity as a **K-linear factorization of the generic tangent map**:
```lean
Jη = ρ(Pgen) ∘ δK ∘ τ(Pgen)
```
where:

- `δK` is the base change of `deformationδ M M` to `K`,
- `ρ(Pgen)` is the target action `A_i ↦ Pgen_{i+1} A_i Pgen_i⁻¹`,
- `τ(Pgen)` is the domain left/right trivialization converting coordinate tangent vectors at `Pgen` into Lie algebra elements.

Then use finite-dimensional duality to identify the Kähler differential span with the range of `Jη.dualMap`.

Useful verified names:

```lean
KaehlerDifferential.linearMapEquivDerivation
Derivation.liftKaehlerDifferential_comp_D
LinearMap.finrank_range_dualMap_eq_finrank_range
Submodule.dualLift
Subspace.dual_finrank_eq
```

Names to define locally: `orbitJacobianK`, `targetGenericIsoK`, `domainGenericIsoK`, `cotangentDualEquivK`.

**Q3**

Definite answer: the headline bound needs only
```lean
genericDifferentialRank k (groupRing d) (genericOrbitCoord M)
  ≤ finrank k (LinearMap.range (deformationδ M M))
```
not equality.

Your chain is:
```text
varietyDim = trdeg ≤ genericDifferentialRank ≤ finrank(range δ⁰)
```
So equality A4.3 is stronger than necessary.

I would change the assembly hypothesis from equality to the upper bound:
```lean
(hA43_le :
  genericDifferentialRank k (groupRing (k := k) d) (genericOrbitCoord M)
    ≤ finrank k (LinearMap.range (deformationδ M M)))
```
and finish by `hA42.trans hA43_le`.

Best scoped residual:
```lean
theorem genericDifferentialRank_genericOrbitCoord_le_finrank_range_deformationδ
    {d : Fin (N + 1) → ℕ} [Fintype (RepCoord d)]
    (M : Tuple (k := k) d) :
    genericDifferentialRank k (groupRing (k := k) d) (genericOrbitCoord M)
      ≤ finrank k (LinearMap.range (deformationδ M M))
```

If you want a more structural residual, leave:
```lean
theorem orbitJacobianK_factorization ... :
  orbitJacobianK M =
    (targetGenericIsoK d).toLinearMap.comp
      ((deformationδK M).comp (domainGenericIsoK d).toLinearMap)
```
All rank inequalities then become finite-dimensional linear algebra.

**Q4**

A clean surjection exists, but canonically it is from the **dual of the tangent image**, not directly from `K ⊗ C⁰`.

Let:
```lean
B := groupRing (k := k) d
K := FractionRing B
ΩK := Ω[K⁄k]
S := Submodule.span K
  (Set.range fun x : RepCoord d =>
    KaehlerDifferential.D k K
      (algebraMap B K (genericOrbitCoord M x)))
```

Define or prove:

```lean
J : C0K →ₗ[K] C1K := orbitJacobianK M

W : Submodule K C1K :=
  (LinearMap.range (deformationδK M)).map (targetGenericIsoK d).toLinearMap

hJ : LinearMap.range J ≤ W
```

Then codrestrict:
```lean
JW : C0K →ₗ[K] W := J.codRestrict W ...
```

With the coordinate cotangent equivalence:
```lean
Ψ : ΩK ≃ₗ[K] Module.Dual K C0K
```
the surjection is:
```lean
Module.Dual K W
  -- JW.dualMap
→ Module.Dual K C0K
  -- Ψ.symm
→ ΩK
  -- rangeRestrict, after identifying the range with S
→ S
```

In Lean shape:
```lean
def spanSurj : Module.Dual K W →ₗ[K] S := ...
```

Why this bounds the rank:
```lean
finrank K S
  ≤ finrank K (Module.Dual K W)
  = finrank K W
  ≤ finrank K (K ⊗[k] LinearMap.range (deformationδ M M))
  = finrank k (LinearMap.range (deformationδ M M))
```

Use `Subspace.dual_finrank_eq` and `Module.finrank_baseChange`. Exact syntax for the base-changed `δK` via `TensorProduct.lTensor` / `LinearMap.lTensor` should be verified; the lemma name shape is not the hard part.

**VERDICT:** PROVABLE via Kähler row-space + generic tangent factorization, about 6-8 lemmas. For fastest discharge, SCOPE the residual to the upper-bound theorem, not the full equality.