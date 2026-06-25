1. Use `Measure.pi` first, then convert to `volume`.

```lean
theorem finAppend_mp_pi (n m : ℕ) :
    MeasurePreserving (finAppend n m)
      ((Measure.pi (fun _ : Fin n => (volume : Measure ℝ))).prod
        (Measure.pi (fun _ : Fin m => (volume : Measure ℝ))))
      (Measure.pi (fun _ : Fin (n + m) => (volume : Measure ℝ))) := by
  unfold finAppend
  exact
    (measurePreserving_sumPiEquivProdPi_symm
      (fun _ : Fin n ⊕ Fin m => (volume : Measure ℝ))).trans
      (measurePreserving_arrowCongr'
        (fun _ : Fin n ⊕ Fin m => (volume : Measure ℝ))
        (fun _ : Fin (n + m) => (volume : Measure ℝ))
        finSumFinEquiv (MeasurableEquiv.refl ℝ)
        (fun _ => MeasurePreserving.id (volume : Measure ℝ)))

theorem finAppend_mp_volume (n m : ℕ) :
    MeasurePreserving (finAppend n m)
      (((volume : Measure (Fin n → ℝ))).prod ((volume : Measure (Fin m → ℝ))))
      (volume : Measure (Fin (n + m) → ℝ)) := by
  simpa [volume_pi] using finAppend_mp_pi n m
```

Confidence: verified locally. Names confident-v4.29.

2. **ABANDON** for final `e222`, though Q1 is fixable. Decisive reason: `piCurry + explicit reindex` stays entirely in `Measure.pi`, so your existing `measurePreserving_piCurry` plus `measurePreserving_arrowCongr'` proof is reused verbatim and no product-measure joins appear. If `myEq : Fin 8 ≃ FlatIdx H222`, use `myEq.symm` in `arrowCongr'`.

3. Clean construction:

```lean
def H222 : Fin 3 → ℕ := fun _ => 2

def fin8EquivFlatIdx222 : Fin 8 ≃ FlatIdx H222 :=
  (((finProdFinEquiv : Fin 2 × Fin 2 ≃ Fin (2 * 2)).prodCongr
      (Equiv.refl (Fin 2))).trans
      (finProdFinEquiv : Fin (2 * 2) × Fin 2 ≃ Fin ((2 * 2) * 2))).symm.trans
    ((Equiv.sigmaEquivProd (Σ _ : Fin 2, Fin 2) (Fin 2)).trans
      ((Equiv.sigmaEquivProd (Fin 2) (Fin 2)).prodCongr
        (Equiv.refl (Fin 2)))).symm
```

This is row-major: `k = j + 2*i + 4*s`, so `0 ↦ (0,0,0)`, ..., `7 ↦ (1,1,1)`. No inverse proof needed with this chain. If hand-writing by cases, yes, left/right inverses are decidable: use `fin_cases ... <;> rfl` or `native_decide` for concrete coordinate facts. Names confident-v4.29.