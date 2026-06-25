**Q1.** Go forward: prove each `X ab - C (forcedB22 ab) ∈ Iad.map Ψ`, because `minor ∈ sigmaIdeal` pushes by `Ideal.mem_map_of_mem` (confident-v4.29) into `Iad` and then into `Ψ(Iad)`; the `Ψ.symm` route forces denominator computations through `IsLocalization.algEquivOfAlgEquiv_symm` (confident-v4.29).

**Q2.** Use `(*)` as the spine, but prove it by the bordered determinant identity, not determinant expansion. The clean lemma is:

```lean
blockAlgEquiv ... minorPoly_ab
  = C detSchurS * X ab - C ((forcedNum ... ) ab.1 ab.2)
```

Proof spine: `det_submatrix_multPoly_mem_sigmaIdeal` (local/confident), `IsLocalization.algEquivOfAlgEquiv_eq` (confident-v4.29), `AlgEquiv.map_det` (confident-v4.29), `det_fromBlocks_scalar_eq` (local/confident), plus the coordinate lemmas `blockAlgEquiv_X_pivot`, `blockAlgEquiv_X_b12`, `blockAlgEquiv_X_b21`, `blockAlgEquiv_X_b22` (local/confident). For the `Fin r ⊕ Unit` vs `Fin (r+1)` mismatch, use the existing local pattern with `Matrix.det_submatrix_equiv_self` and `Matrix.submatrix_submatrix` (confident-v4.29). Applying `det_fromBlocks_scalar_eq` only in the localized target is not lower friction; it still needs the same “this determinant is the image of the minor” proof, with more localization coercions.

**Q3.** The exact membership lemmas are:

```lean
Ideal.unit_mul_mem_iff_mem   -- left unit multiple
Ideal.mul_unit_mem_iff_mem   -- right unit multiple
```

both confident-v4.29. For the unit in `T := MvPolynomial B22block Sd`:

```lean
have hunitSd : IsUnit (algebraMap R Sd detSchurS) :=
  IsLocalization.map_units (M := Submonoid.powers detSchurS) Sd
    (⟨detSchurS, Submonoid.mem_powers _⟩ : Submonoid.powers detSchurS)

have hunitT : IsUnit (C (algebraMap R Sd detSchurS) : T) :=
  RingHom.isUnit_map (C : Sd →+* T) hunitSd
```

`IsLocalization.map_units`, `Submonoid.mem_powers`, `RingHom.isUnit_map` are confident-v4.29. Specialized alternative: `IsLocalization.Away.algebraMap_isUnit` (confident-v4.29). For the forced denominator equation use `IsLocalization.mk'_spec'` (confident-v4.29); explicit inverse route via `IsLocalization.Away.invSelf` / `IsLocalization.Away.mul_invSelf` also exists but is less clean.

Then:

```lean
exact (Ideal.unit_mul_mem_iff_mem K hunitT).mp hcleared
```

where `hcleared : C (algebraMap R Sd detSchurS) * (X ab - C (forcedB22 ab)) ∈ K`.

**Q4.** Let `K := Iad.map (Ψ : A_loc →+* T)` and `J := graphIdeal forcedB22`.

Height transport:

```lean
have hKheight : K.height = Iad.height :=
  height_map_algEquiv Ψ Iad
```

`height_map_algEquiv` is local/confident; underlying Mathlib lemma is `RingEquiv.height_map` (confident-v4.29). Prime transport: `Ideal.map_isPrime_of_equiv Ψ` (confident-v4.29). For `J`: `graphIdeal_isPrime` and `height_graphIdeal_forcedB22_eq` (local/confident). Squeeze with `Ideal.height_strict_mono_of_is_prime` (confident-v4.29); if Lean needs the finite-height instance for `J`, build it from `Ideal.finiteHeight_iff_lt` (confident-v4.29) and `height_graphIdeal_forcedB22_eq`.

Quotient iso chain, cleanest after `hKJ : K = J`:

```lean
let e₁ : A_loc ⧸ Iad ≃ₐ[k] T ⧸ J :=
  Ideal.quotientEquivAlg Iad J Ψ hKJ.symm

let e₂ : T ⧸ J ≃ₐ[k] Sd :=
  (graphIdealQuotientEquiv forcedB22).restrictScalars k

exact e₁.trans e₂
```

Names: `Ideal.quotientEquivAlg`, `Ideal.quotientEquivAlg_mk` (confident-v4.29), `graphIdealQuotientEquiv` (local/confident), `AlgEquiv.restrictScalars` (confident-v4.29). If you keep the intermediate quotient by `K`, use `Ideal.quotientEquivAlg Iad K Ψ rfl`, then `Ideal.quotientEquivAlgOfEq k hKJ` / `Ideal.quotientEquivAlgOfEq_mk` (confident-v4.29), then `graphIdealQuotientEquiv`. No `ringKrullDim Sd` route needed.