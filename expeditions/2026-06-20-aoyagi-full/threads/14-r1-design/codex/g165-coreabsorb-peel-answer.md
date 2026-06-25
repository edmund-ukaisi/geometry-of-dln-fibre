**WINNER:** Route A (MP). It is much lower friction: only needs `Measurable shift` (continuity suffices) and avoids building `Dπ`, proving `HasFDerivAt`, and matrix/CLM determinant bookkeeping.

Mathlib v4.29 does **not** seem to have a named specialized additive lemma exactly for `(x,y) ↦ (x, y + f x)`. It does have the right Fubini atom:

```lean
MeasurePreserving.skew_product
measurePreserving_add_right
Measure.volume_eq_prod
MeasurePreserving.prod
Measure.measurePreserving_swap
measurePreserving_prodAssoc
```

So hand-build a thin additive-skew wrapper.

Proof skeleton:

```lean
-- A = Reg × Spec, B = Core
have hskew : MeasurePreserving
    (fun p : (Reg × Spec) × Core => (p.1, p.2 + shift p.1)) volume volume := by
  rw [show (volume : Measure ((Reg × Spec) × Core))
        = (volume : Measure (Reg × Spec)).prod (volume : Measure Core) from
        Measure.volume_eq_prod _ _]
  exact MeasurePreserving.skew_product
    (μa := (volume : Measure (Reg × Spec)))
    (μb := (volume : Measure (Reg × Spec)))
    (μc := (volume : Measure Core))
    (μd := (volume : Measure Core))
    (f := id)
    (g := fun a c => c + shift a)
    (MeasurePreserving.id _)
    (by fun_prop) -- or `measurable_snd.add (hshift.measurable.comp measurable_fst)`
    (ae_of_all _ fun a =>
      (measurePreserving_add_right (volume : Measure Core) (shift a)).map_eq)

let reassoc : Reg × (Core × Spec) ≃ₜ (Reg × Spec) × Core :=
  (Homeomorph.prodCongr (Homeomorph.refl Reg) (Homeomorph.prodComm Core Spec)).trans
    (Homeomorph.prodAssoc Reg Spec Core).symm

have hreassoc : MeasurePreserving reassoc volume volume := by
  -- `Measure.volume_eq_prod`, `MeasurePreserving.prod`,
  -- `Measure.measurePreserving_swap`, `measurePreserving_prodAssoc`
  -- same pattern as existing `chartN_mp`.
  exact by
    -- routine product-volume reassociation proof
    sorry

have hmp : MeasurePreserving coreAbsorb volume volume := by
  -- `coreAbsorb = reassoc.symm ∘ skew ∘ reassoc`
  exact hreassoc.symm.comp (hskew.comp hreassoc) |> by
    simpa [coreAbsorb, reassoc]

have hkey :=
  rlctAtOn_comp_homeomorph coreAbsorb hmp coreAbsorb.measurableEmbedding G 0
simpa [coreAbsorb_basepoint] using hkey
```

Gotchas:

- The middle-slot shear is handled cleanly by regrouping
  `Reg × (Core × Spec) ≃ₜ (Reg × Spec) × Core`; no deeper Fubini issue.
- For Route B, expect high friction: no convenient “block-unipotent CLM det = 1” lemma. You would likely unfold via `ContinuousLinearMap.det`, matrices, and `Matrix.det_of_lowerTriangular`.
- `volume` on `Fin n → ℝ` and nested products needs explicit `Measure.volume_eq_prod` rewrites.