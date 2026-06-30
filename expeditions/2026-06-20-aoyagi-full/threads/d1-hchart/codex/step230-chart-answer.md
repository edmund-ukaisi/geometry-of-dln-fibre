**1. Define `Φ`**
Best option: use an indicator sum, not unique extraction.

```lean
def p (c : Fin N) : Prop := c ∈ Set.range ec

def gsel (k : Fin nReg) (w : Fin N → ℝ) : ℝ :=
  lossEntry (er k) w - lossEntry (er k) 0

noncomputable def Φ (w : Fin N → ℝ) : Fin N → ℝ :=
  fun c =>
    if hp : p c then
      ∑ k : Fin nReg, if ec k = c then gsel k w else 0
    else
      w c
```

Ranked options:

1. **Indicator sum as above.** Cleanest. No dependent inverse. Key local lemmas:
   ```lean
   lemma Φ_ec (k) : Φ w (ec k) = gsel k w := by
     simp [Φ, p, Function.Injective.eq_iff hinj_ec]

   lemma Φ_not_mem {c} (hc : ¬ p c) : Φ w c = w c := by
     simp [Φ, p, hc]
   ```
   `Function.Injective.eq_iff` should exist, but verify exact simp behavior.

2. **Build `(Fin nReg → ℝ) × ({c // ¬ p c} → ℝ)` and reindex to `Fin N → ℝ`.** Mathematically clean, but you pay upfront for an equivalence
   `Fin N ≃ Fin nReg ⊕ {c // ¬ p c}`. Good if later chart code wants an explicit product split.

3. **Define `selectedEquiv : Fin nReg ≃ {c // p c}` and use `.symm`.** Better than raw `Classical.choose`, but still exposes the unique-index machinery in the definition.

I would use option 1 and isolate all `ec` injectivity simplification in `Φ_ec`.

**2. Fderiv Route**
Define the derivative componentwise.

```lean
def dG (k : Fin nReg) : (Fin N → ℝ) →L[ℝ] ℝ :=
  prodAuxEntryDeriv ... 2 (er k).1 (er k).2

noncomputable def dΦcoord (c : Fin N) : (Fin N → ℝ) →L[ℝ] ℝ :=
  if hp : p c then
    ∑ k : Fin nReg, if ec k = c then dG k else 0
  else
    ContinuousLinearMap.proj c

noncomputable def dΦ : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ) :=
  ContinuousLinearMap.pi dΦcoord
```

Then prove per coordinate and assemble with the verified Mathlib v4.29 theorem:

```lean
have hcoord : ∀ c, HasFDerivAt (fun w => Φ w c) (dΦcoord c) 0 := by
  intro c
  by_cases hp : p c
  · -- selected branch
    simp [Φ, dΦcoord, hp]
    exact HasFDerivAt.fun_sum (u := Finset.univ) (fun k hk => by
      by_cases hkc : ec k = c
      · simpa [hkc, gsel] using
          (hasStrictFDerivAt_lossEntry ...).hasFDerivAt.sub
            (hasFDerivAt_const _ _)
      · simpa [hkc] using hasFDerivAt_const (0 : ℝ) (0 : Fin N → ℝ))
  · -- complement branch
    simpa [Φ, dΦcoord, hp] using
      (ContinuousLinearMap.proj c : (Fin N → ℝ) →L[ℝ] ℝ).hasFDerivAt
```

Assemble:

```lean
have hΦ : HasFDerivAt Φ dΦ 0 := by
  simpa [Φ, dΦ] using (hasFDerivAt_pi.2 hcoord)
```

Verified names: `hasFDerivAt_pi`, `hasFDerivAt_pi'`, `hasFDerivAt_pi''`, `ContinuousLinearMap.pi`, `ContinuousLinearMap.pi_apply`, `ContinuousLinearMap.proj`, `ContinuousLinearMap.proj_apply`, `ContinuousLinearMap.hasFDerivAt`, `HasFDerivAt.fun_sum`, `HasFDerivAt.sub`, `hasFDerivAt_const`.

For `ContDiff ℝ 2 Φ`, use the same component split:

```lean
exact contDiff_pi'.2 hcoordSmooth
-- or:
exact contDiff_pi.2 hcoordSmooth
```

Verified names: `contDiff_pi`, `contDiff_pi'`, `ContDiff.sum`, `ContDiff.sub`, `contDiff_const`, `contDiff_apply`, `ContDiff.of_le`.

**3. Det Nonzero**
Let

```lean
def D : Matrix (Fin N) (Fin N) ℝ :=
  LinearMap.toMatrix' (dΦ : (Fin N → ℝ) →ₗ[ℝ] (Fin N → ℝ))
```

Entry convention, verified:

```lean
LinearMap.toMatrix'_apply :
  LinearMap.toMatrix' f i j = f (Pi.single j 1) i
```

Block determinant:

```lean
have hzero :
    ∀ i, ¬ p i → ∀ j, p j → D i j = 0 := by
  intro i hi j hj
  have hij : i ≠ j := fun h => hi (h ▸ hj)
  simp [D, dΦ, dΦcoord, hi, ContinuousLinearMap.pi_apply,
        ContinuousLinearMap.proj_apply, Pi.single_apply, hij]

have hblock :=
  D.twoBlockTriangular_det p hzero
```

Verified theorem shape:

```lean
Matrix.twoBlockTriangular_det
  (M : Matrix m m R) (p : m → Prop) [DecidablePred p]
  (h : ∀ i, ¬ p i → ∀ j, p j → M i j = 0) :
  M.det =
    (toSquareBlockProp M p).det *
    (toSquareBlockProp M fun i => ¬ p i).det
```

Now define the selected-coordinate equivalence:

```lean
noncomputable def ecRangeEquiv :
    Fin nReg ≃ {c : Fin N // p c}
```

from `hinj_ec`. Then prove two local determinant lemmas:

```lean
lemma selected_block_det :
    (Matrix.toSquareBlockProp D p).det =
      (jacFlatL2.submatrix er ec).det := by
  rw [← Matrix.det_submatrix_equiv_self ecRangeEquiv]
  ext a b
  simp [D, dΦ, dΦcoord, Φ_ec,
        LinearMap.toMatrix'_apply,
        jacFlatL2_apply_eq_lossEntryDeriv]

lemma complement_block_det :
    (Matrix.toSquareBlockProp D (fun c => ¬ p c)).det = 1 := by
  have hI : Matrix.toSquareBlockProp D (fun c => ¬ p c) = 1 := by
    ext i j
    simp [D, dΦ, dΦcoord, i.property,
          LinearMap.toMatrix'_apply,
          ContinuousLinearMap.proj_apply, Pi.single_apply]
  simpa [hI]
```

Then:

```lean
have hDdet : D.det ≠ 0 := by
  rw [D.twoBlockTriangular_det p hzero, selected_block_det,
      complement_block_det, mul_one]
  exact hminor
```

Bridge to CLM determinant:

```lean
have hdΦdet : dΦ.det ≠ 0 := by
  change LinearMap.det (dΦ : (Fin N → ℝ) →ₗ[ℝ] (Fin N → ℝ)) ≠ 0
  simpa [D] using hDdet
```

Verified determinant bridge names: `ContinuousLinearMap.det` is an abbrev for linear determinant; `LinearMap.det_toMatrix'`; `LinearMap.det_toLin'`; `LinearMap.det_toContinuousLinearMap`; `ContinuousLinearMap.toContinuousLinearEquivOfDetNeZero`; `ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero`.

Finally:

```lean
noncomputable def f' : (Fin N → ℝ) ≃L[ℝ] (Fin N → ℝ) :=
  dΦ.toContinuousLinearEquivOfDetNeZero hdΦdet

have hΦ' : HasFDerivAt Φ (f' : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ)) 0 := by
  simpa [f'] using hΦ
```

Because `gsel k 0 = 0`, `Φ 0 = 0` should be just a selected-branch finite sum of zeros plus complement zero.

**4. Biggest Risk**
Put the 3-attempt watch on these, in order:

1. `ecRangeEquiv : Fin nReg ≃ {c // p c}` and its simp lemmas. If this gets noisy, stop and make explicit lemmas `ecRangeEquiv_apply` and `ecRangeEquiv_surj`.

2. `selected_block_det`. This is the alignment point between `D (ec a) (ec b)` and `jacFlatL2 (er a) (ec b)`, via `LinearMap.toMatrix'_apply` and `jacFlatL2_apply_eq_lossEntryDeriv`.

3. The `ContinuousLinearMap.det` bridge. Avoid proving anything abstract: `change LinearMap.det (...) ≠ 0`, then `simpa [D]` using `LinearMap.det_toMatrix'`.