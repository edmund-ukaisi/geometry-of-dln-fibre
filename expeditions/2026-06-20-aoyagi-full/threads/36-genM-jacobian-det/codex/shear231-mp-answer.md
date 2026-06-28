**Recommendation: Option B.** Use one split and the banked `measurePreserving_coreShear_measurable` with `a = 1`, `b = 2`, `c = 6`.

The split order I would use is:

```lean
(split231 u).1 0       = u 0
(split231 u).2.1 0     = u 6
(split231 u).2.1 1     = u 7
(split231 u).2.2 0     = u 1
(split231 u).2.2 1     = u 2
(split231 u).2.2 2     = u 3
(split231 u).2.2 3     = u 4
(split231 u).2.2 4     = u 5
(split231 u).2.2 5     = u 8
```

The `piFinSuccAbove` peels are precisely:

```lean
Fin 9: peel 0  -- original coord 0
Fin 8: peel 5  -- original coord 6
Fin 7: peel 5  -- original coord 7
```

Concrete skeleton:

```lean
/-- After coord `0` has been peeled, peel original coords `6,7` as the `Fin 2` core. -/
noncomputable def coreSpec231 :
    (Fin 8 → ℝ) ≃ᵐ (Fin 2 → ℝ) × (Fin 6 → ℝ) :=
  (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 8 => ℝ) 5).trans
    ((MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ)
      ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin 7 => ℝ) 5).trans
        (MeasurableEquiv.prodCongr
          (MeasurableEquiv.funUnique (Fin 1) ℝ).symm
          (MeasurableEquiv.refl (Fin 6 → ℝ))))).trans
    (((MeasurableEquiv.prodAssoc :
        (ℝ × (Fin 1 → ℝ)) × (Fin 6 → ℝ) ≃ᵐ
          ℝ × ((Fin 1 → ℝ) × (Fin 6 → ℝ))).symm).trans
      (MeasurableEquiv.prodCongr
        (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 2 => ℝ) 0).symm
        (MeasurableEquiv.refl (Fin 6 → ℝ)))))

noncomputable def split231 :
    (Fin 9 → ℝ) ≃ᵐ (Fin 1 → ℝ) × ((Fin 2 → ℝ) × (Fin 6 → ℝ)) :=
  (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 9 => ℝ) 0).trans
    (MeasurableEquiv.prodCongr
      (MeasurableEquiv.funUnique (Fin 1) ℝ).symm
      coreSpec231)
```

Measure-preserving split:

```lean
theorem measurePreserving_coreSpec231 :
    MeasurePreserving (coreSpec231 : (Fin 8 → ℝ) → _) volume volume := by
  unfold coreSpec231
  refine (volume_preserving_piFinSuccAbove (fun _ : Fin 8 => ℝ) 5).trans ?_
  refine (MeasurePreserving.prod (MeasurePreserving.id _) ?_).trans ?_
  · refine (volume_preserving_piFinSuccAbove (fun _ : Fin 7 => ℝ) 5).trans ?_
    exact MeasurePreserving.prod
      (volume_preserving_funUnique (Fin 1) ℝ).symm
      (MeasurePreserving.id _)
  · refine ?_.trans ?_
    · rw [show (volume : Measure (ℝ × ((Fin 1 → ℝ) × (Fin 6 → ℝ))))
            = (volume : Measure ℝ).prod ((volume : Measure (Fin 1 → ℝ)).prod volume) by
            rw [Measure.volume_eq_prod _ _, Measure.volume_eq_prod _ _],
          show (volume : Measure ((ℝ × (Fin 1 → ℝ)) × (Fin 6 → ℝ)))
            = ((volume : Measure ℝ).prod (volume : Measure (Fin 1 → ℝ))).prod volume by
            rw [Measure.volume_eq_prod _ _, Measure.volume_eq_prod _ _]]
      exact MeasurePreserving.symm MeasurableEquiv.prodAssoc
        (measurePreserving_prodAssoc
          (volume : Measure ℝ) (volume : Measure (Fin 1 → ℝ)) volume)
    · rw [show (volume : Measure ((ℝ × (Fin 1 → ℝ)) × (Fin 6 → ℝ)))
            = (volume : Measure (ℝ × (Fin 1 → ℝ))).prod volume by
            rw [Measure.volume_eq_prod _ _],
          show (volume : Measure ((Fin 2 → ℝ) × (Fin 6 → ℝ)))
            = (volume : Measure (Fin 2 → ℝ)).prod volume by
            rw [Measure.volume_eq_prod _ _]]
      exact MeasurePreserving.prod
        (volume_preserving_piFinSuccAbove (fun _ : Fin 2 => ℝ) 0).symm
        (MeasurePreserving.id _)

theorem measurePreserving_split231 :
    MeasurePreserving (split231 : (Fin 9 → ℝ) → _) volume volume := by
  unfold split231
  refine (volume_preserving_piFinSuccAbove (fun _ : Fin 9 => ℝ) 0).trans ?_
  exact MeasurePreserving.prod
    (volume_preserving_funUnique (Fin 1) ℝ).symm
    measurePreserving_coreSpec231
```

Define the core shift as a function of the split base:

```lean
noncomputable def base231 (q : (Fin 1 → ℝ) × (Fin 6 → ℝ)) : Fin 9 → ℝ :=
  ![q.1 0, q.2 0, q.2 1, q.2 2, q.2 3, q.2 4, 0, 0, q.2 5]

noncomputable def shift231 :
    (Fin 1 → ℝ) × (Fin 6 → ℝ) → (Fin 2 → ℝ) :=
  fun q i => - lam231 (base231 q) i * q.2 5

theorem base231_measurable : Measurable base231 := by
  apply measurable_pi_iff.2
  intro i
  fin_cases i <;> simp [base231] <;> fun_prop

theorem shift231_measurable : Measurable shift231 := by
  apply measurable_pi_iff.2
  intro i
  unfold shift231
  exact ((lam231_measurable i).comp base231_measurable).neg.mul
    ((measurable_pi_apply 5).comp measurable_snd)
```

Then the conjugation and MP proof:

```lean
set_option maxHeartbeats 1000000 in
theorem split231_shear231 (u : Fin 9 → ℝ) :
    split231 (shear231 u)
      = (fun q : (Fin 1 → ℝ) × ((Fin 2 → ℝ) × (Fin 6 → ℝ)) =>
          (q.1, (q.2.1 + shift231 (q.1, q.2.2), q.2.2))) (split231 u) := by
  apply Prod.ext
  · funext k
    fin_cases k
    simp [split231, coreSpec231, shear231, MeasurableEquiv.piFinSuccAbove,
      MeasurableEquiv.funUnique, MeasurableEquiv.prodCongr, MeasurableEquiv.prodAssoc,
      Fin.insertNthEquiv, Fin.removeNth, Fin.succAbove]
  apply Prod.ext
  · funext k
    fin_cases k <;>
      simp [split231, coreSpec231, shear231, shift231, base231, lam231,
        MeasurableEquiv.piFinSuccAbove, MeasurableEquiv.funUnique,
        MeasurableEquiv.prodCongr, MeasurableEquiv.prodAssoc,
        Fin.insertNthEquiv, Fin.removeNth, Fin.succAbove] <;>
      ring
  · funext k
    fin_cases k <;>
      simp [split231, coreSpec231, shear231, MeasurableEquiv.piFinSuccAbove,
        MeasurableEquiv.funUnique, MeasurableEquiv.prodCongr, MeasurableEquiv.prodAssoc,
        Fin.insertNthEquiv, Fin.removeNth, Fin.succAbove]

theorem shear231_eq_conj (u : Fin 9 → ℝ) :
    shear231 u = split231.symm
      ((fun q : (Fin 1 → ℝ) × ((Fin 2 → ℝ) × (Fin 6 → ℝ)) =>
          (q.1, (q.2.1 + shift231 (q.1, q.2.2), q.2.2))) (split231 u)) := by
  rw [← split231_shear231, MeasurableEquiv.symm_apply_apply]

theorem measurePreserving_shear231 :
    MeasurePreserving shear231 (volume : Measure (Fin 9 → ℝ)) volume := by
  have hcore :=
    measurePreserving_coreShear_measurable 1 2 6 shift231 shift231_measurable
  have hconj : MeasurePreserving
      (split231.symm ∘
        (fun q : (Fin 1 → ℝ) × ((Fin 2 → ℝ) × (Fin 6 → ℝ)) =>
          (q.1, (q.2.1 + shift231 (q.1, q.2.2), q.2.2))) ∘
        split231)
      volume volume :=
    (measurePreserving_split231.symm split231).comp
      (hcore.comp measurePreserving_split231)
  refine hconj.congr shear231_measurable ?_
  filter_upwards with u
  exact (shear231_eq_conj u).symm
```

There is no need for Option A. Option C is essentially the `skew_product` lemma you already banked; Mathlib does not give a ready-made nonlinear triangular-coordinate shear lemma at this specificity.