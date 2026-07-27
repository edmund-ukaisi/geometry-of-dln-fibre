## Section 1: ROUTE VERDICT

Choose A, but orient `Equiv.ofBijective` carefully. Define the computable map `w : tupIdx dvec → Fin 21`, prove `Function.Bijective w` by kernel `decide`, and use `Equiv.ofBijective w ...` in the forward flatten. Then the inverse flatten—the direction equal to `eWrap`—reads coordinates through the transparent forward map `w`; the opaque generated inverse is never reduced.

This avoids route B’s manually derived canonical permutation and records the scattered layout only once. The complete skeleton below typechecks on this v4.29 workspace. There is no more direct arbitrary-nested-pi theorem: the slick raw-pi idiom is precisely two `piCurry`s followed by `arrowCongr'`, with `volume_preserving_arrowCongr'`.

## Section 2: SKELETON

```lean
open MeasureTheory
open DLNFibre.Core
open DLNFibre.DLN.RLCT (measurePreserving_piCurry)

namespace DLNFibre.DLN.Aoyagi.Corank2CoreGenWrap

/-- `(layer,row,col) ↦` the coordinate read by `eWrap`. -/
def eWrapIdx (t : tupIdx dvec) : Fin 21 :=
  ⟨if t.1.1.val = 0 then
      if t.1.2.val = 0 then
        if t.2.val = 0 then 20 else if t.2.val = 1 then 2 else 3
      else if t.1.2.val = 1 then
        if t.2.val = 0 then 0 else if t.2.val = 1 then 4 else 6
      else
        if t.2.val = 0 then 1 else if t.2.val = 1 then 5 else 7
    else
      8 + 4 * t.2.val + t.1.2.val,
    by
      rcases t with ⟨⟨i, r⟩, c⟩
      have hr := r.isLt
      have hc := c.isLt
      fin_cases i <;>
        simp_all [dvec] <;>
        split_ifs <;>
        omega⟩

private theorem eWrapIdx_bijective :
    Function.Bijective eWrapIdx := by
  decide

/-
Important orientation: `toFun = eWrapIdx` is transparent.
Only this direction will occur when `eWrapFlat.symm` is evaluated.
-/
noncomputable def eWrapIdxEquiv : tupIdx dvec ≃ Fin 21 :=
  Equiv.ofBijective eWrapIdx eWrapIdx_bijective

/-- Custom flatten whose inverse has exactly the `eWrap` layout. -/
noncomputable def eWrapFlat :
    Tuple (k := ℝ) dvec ≃ᵐ (Fin 21 → ℝ) :=
  (MeasurableEquiv.piCurry
      (fun (i : Fin 2) (_ : Fin (dvec i.succ)) =>
        Fin (dvec i.castSucc) → ℝ)).symm.trans
    ((MeasurableEquiv.piCurry
        (fun (q : Σ i : Fin 2, Fin (dvec i.succ))
          (_ : Fin (dvec q.1.castSucc)) => ℝ)).symm.trans
      (MeasurableEquiv.arrowCongr'
        eWrapIdxEquiv (MeasurableEquiv.refl ℝ)))

theorem measurePreserving_eWrapFlat :
    MeasurePreserving eWrapFlat
      (volume : Measure (Tuple (k := ℝ) dvec))
      (volume : Measure (Fin 21 → ℝ)) := by
  unfold eWrapFlat

  have h₁ := measurePreserving_piCurry
    (fun (i : Fin 2) (_ : Fin (dvec i.succ)) =>
      Fin (dvec i.castSucc) → ℝ)
    (fun i _ => (volume : Measure (Fin (dvec i.castSucc) → ℝ)))

  have h₂ := measurePreserving_piCurry
    (fun (q : Σ i : Fin 2, Fin (dvec i.succ))
      (_ : Fin (dvec q.1.castSucc)) => ℝ)
    (fun _ _ => (volume : Measure ℝ))

  have hr := volume_preserving_arrowCongr'
    eWrapIdxEquiv
    (MeasurableEquiv.refl ℝ)
    (MeasurePreserving.id (volume : Measure ℝ))

  exact (h₁.symm _).trans ((h₂.symm _).trans hr)

/-- The fiddly coordinate match. -/
theorem eWrapFlat_symm_coe :
    (eWrapFlat.symm :
      (Fin 21 → ℝ) → Tuple (k := ℝ) dvec) = eWrap := by
  funext u i
  fin_cases i <;>
    (funext r c
     fin_cases r <;>
     fin_cases c <;>
     rfl)

theorem measurePreserving_eWrap :
    MeasurePreserving eWrap
      (volume : Measure (Fin 21 → ℝ))
      (volume : Measure (Tuple (k := ℝ) dvec)) := by
  have h := (measurePreserving_eWrapFlat).symm eWrapFlat
  rwa [eWrapFlat_symm_coe] at h

end DLNFibre.DLN.Aoyagi.Corank2CoreGenWrap
```

## Section 3: FAILURE MODES

- `Equiv.ofBijective` has an opaque generated inverse. Do not try to compute `eWrapFlat (eWrap u)`. Orient it as above and compare `eWrapFlat.symm` with `eWrap`, so reduction uses `eWrapIdx`.

- The dependent `< 21` proof will not close before splitting the layer. Use exactly:
  ```lean
  rcases t with ⟨⟨i,r⟩,c⟩
  have hr := r.isLt
  have hc := c.isLt
  fin_cases i <;> simp_all [dvec] <;> split_ifs <;> omega
  ```

- Function-level `rfl` will not split the dependent widths. Use:
  ```lean
  funext u i
  fin_cases i <;>
    (funext r c; fin_cases r <;> fin_cases c <;> rfl)
  ```

- Avoid unfolding/simplifying the opaque inverse of `Equiv.ofBijective`; that recreates the cast wall.

- `by decide` is safe here and was checked at this pin. Use kernel `decide`, not `native_decide`.