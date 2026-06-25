**1. ROUTE VERDICT**

Use plan **(a)+(b)**. The clean public API should hide the rename in one wrapper:

```lean
φ := deepBaseComap (k := k) d :
  MvPolynomial (RepCoord (dStratum (d 0) (d (Fin.last N)))) k →ₐ[k]
  MvPolynomial (RepCoord d) k
```

implemented as `multComap d ∘ MvPolynomial.renameEquiv ...`.

Recommended composite:

```lean
SchurLoc (d 0) (d (Fin.last N)) r
  -- (basePresentationEquiv ...).symm.toAlgHom
→ₐ[k]
Localization.Away detPivotPoly ⧸ Iad
  -- Ideal.quotientMapₐ IadDeep φloc hIad
→ₐ[k]
Localization.Away ΔPdeep ⧸ IadDeep
```

where

```lean
φloc :=
  IsLocalization.Away.mapₐ
    (Localization.Away detPivotPoly)
    (Localization.Away ΔPdeep)
    φ
    detPivotPoly
```

after installing `IsLocalization.Away (φ detPivotPoly) (Localization.Away ΔPdeep)` by rewriting with `φ detPivotPoly = ΔPdeep`.

No cleaner route skips the rename unless you rebuild/transport the whole N=1 base presentation to `MvPolynomial (Fin p × Fin q) k`. That is more churn than a `deepBaseComap` wrapper.

**2. THE `detPivotPoly ↦ ΔPdeep` TRANSPORT**

Pin this statement:

```lean
theorem deepBaseComap_detPivot
    (d : Fin (N + 1) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last N)) (hq : r ≤ d 0) :
    deepBaseComap (k := k) d
      (detPivotPoly (k := k) (d 0) (d (Fin.last N)) r hp hq)
      =
    ΔPdeep (k := k) d r hp hq := by
  -- rw [detPivotPoly, ΔPdeep, AlgHom.map_det]
  -- ext i j
  -- use multPoly_stratum_apply / N=1 variable lemma
```

For `Away.mapₐ`, the exact local instance is:

```lean
have hdet := deepBaseComap_detPivot (k := k) d r hp hq
haveI :
    IsLocalization.Away
      (deepBaseComap (k := k) d
        (detPivotPoly (k := k) (d 0) (d (Fin.last N)) r hp hq))
      (Localization.Away (ΔPdeep (k := k) d r hp hq)) := by
  rw [hdet]
  infer_instance
```

Use `AlgHom.map_det` for the determinant. Verified locally: `AlgHom.map_det`, `RingHom.map_det`, `AlgEquiv.map_det`.

The indices line up as:

```lean
Fin.castLE hp : Fin r → Fin (d (Fin.last N)) -- rows
Fin.castLE hq : Fin r → Fin (d 0)            -- columns
```

and for `dStratum q p`, the source variable is the single matrix entry `⟨0, row, col⟩`, with `row : Fin p`, `col : Fin q`.

**3. THE `sigmaIdeal → sigmaIdeal` DIRECTION**

Yes, this is provable without circularity. Pin:

```lean
theorem deepBaseComap_sigmaIdeal_le
    (d : Fin (N + 1) → ℕ) (r : ℕ) :
    (sigmaIdeal (k := k) (dStratum (d 0) (d (Fin.last N))) r).map
        (deepBaseComap (k := k) d).toRingHom
      ≤ sigmaIdeal (k := k) d r := by
  -- rw [Ideal.map_le_iff_le_comap]
  -- intro f hf
  -- rw [sigmaIdeal, MvPolynomial.mem_vanishingIdeal_iff] at hf ⊢
  -- intro x hx
```

Mechanism: if `A ∈ productRankLocusLE d r`, then the one-matrix tuple with matrix `mult d A` lies in `productRankLocusLE (dStratum (d 0) (d last)) r`. Then

```lean
aeval (canonicalCoord d A) (deepBaseComap d f)
=
aeval (canonicalCoord (dStratum _ _) (singleMatrixTuple (mult d A))) f
```

by `MvPolynomial.algHom_ext` on generators and `eval_multPoly`.

Important correction: this is not “a base point lifts to a total point.” The needed direction is: a **deep total point** in `Σ̄^r_d` maps by `mult` to a **base matrix point** in `Σ̄^r_(q,p)`.

Then lift to localizations:

```lean
Iad ≤ IadDeep.comap φloc
```

using `Ideal.map_le_iff_le_comap`, `IsLocalization.Away.mapₐ_apply`, `IsLocalization.map_eq`, and `Ideal.mem_map_of_mem` all verified locally. This should not be deferred to R2-3b-4.

**4. THE `IsScalarTower` / INSTANCE LADDER**

Define the map first:

```lean
noncomputable def schurToSred :
    SchurLoc (k := k) (d 0) (d (Fin.last N)) r →ₐ[k]
      Sred (k := k) d r hp hq :=
  (Ideal.quotientMapₐ (IadDeep (k := k) d r hp hq) φloc hIad).comp
    (basePresentationEquiv (k := k) (d 0) (d (Fin.last N)) r hp hq).symm.toAlgHom
```

Then use the ring map to define the `SchurLoc`-algebra:

```lean
noncomputable instance :
    Algebra (SchurLoc (k := k) (d 0) (d (Fin.last N)) r)
      (Sred (k := k) d r hp hq) :=
  (schurToSred (k := k) d r hp hq).toRingHom.toAlgebra
```

Pin the tower:

```lean
instance :
    IsScalarTower k
      (SchurLoc (k := k) (d 0) (d (Fin.last N)) r)
      (Sred (k := k) d r hp hq) := by
  refine IsScalarTower.of_algebraMap_eq (fun x ↦ ?_)
  simp [RingHom.algebraMap_toAlgebra, AlgHom.commutes]
```

Use `RingHom.toAlgebra` here. `Algebra.compHom` exists, but `toAlgebra` is the direct construction and does not conflict with the existing `Algebra k Sred`.

Also pin `Nontrivial (SchurLoc ...)`, usually via the existing domain argument for `SchurLoc`.

**5. R2-3b-3 PRE-STAGE**

Use this arbitrary-coefficient-ring contract, not `baseChangeAlgEquiv`:

```lean
example {R : Type u} [CommRing R] {N : ℕ}
    (d : Fin (N + 1) → ℕ)
    (toSub fromSub :
      RepCoord d → MvPolynomial (RepCoord d) R)
    (h_to_from :
      ∀ x, MvPolynomial.aeval toSub (fromSub x)
        = (MvPolynomial.X x : MvPolynomial (RepCoord d) R))
    (h_from_to :
      ∀ x, MvPolynomial.aeval fromSub (toSub x)
        = (MvPolynomial.X x : MvPolynomial (RepCoord d) R)) :
    MvPolynomial (RepCoord d) R ≃ₐ[R]
      MvPolynomial (RepCoord d) R :=
  AlgEquiv.ofAlgHom
    (MvPolynomial.aeval toSub)
    (MvPolynomial.aeval fromSub)
    (by
      apply MvPolynomial.algHom_ext
      intro x
      change MvPolynomial.aeval toSub
          (MvPolynomial.aeval fromSub (MvPolynomial.X x)) = _
      rw [MvPolynomial.aeval_X]
      exact h_to_from x)
    (by
      apply MvPolynomial.algHom_ext
      intro x
      change MvPolynomial.aeval fromSub
          (MvPolynomial.aeval toSub (MvPolynomial.X x)) = _
      rw [MvPolynomial.aeval_X]
      exact h_from_to x)
```

Verified local names here: `AlgEquiv.ofAlgHom`, `MvPolynomial.aeval`, `MvPolynomial.aeval_X`, `MvPolynomial.algHom_ext`.