**Q1.** Use route (a). There is no Mathlib v4.29 “Fin-indexed shear preserves volume” lemma that avoids the same product split. The clean chain is:

```lean
-- local helper, not Mathlib:
measurePreserving_coreShear_measurable
  (a b c : ℕ)
  (shift : (Fin a → ℝ) × (Fin c → ℝ) → (Fin b → ℝ))
  (hshift : Measurable shift)
```

For `121`, define a split whose forward map is:
```lean
split121 u = (![u 0], (![u 2], ![u 1, u 3]))
```

Build it from certain v4.29 names:
```lean
MeasurableEquiv.piFinSuccAbove (fun _ : Fin 4 => ℝ) 0
MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 1
MeasurableEquiv.funUnique (Fin 1) ℝ
MeasurableEquiv.prodCongr
```

The MP proof uses:
```lean
volume_preserving_piFinSuccAbove
volume_preserving_funUnique
MeasurePreserving.prod
Measure.volume_eq_prod
```

Then set:
```lean
shift121 : (Fin 1 → ℝ) × (Fin 2 → ℝ) → (Fin 1 → ℝ)
shift121 q := fun _ => - ((q.2 0) / (q.1 0)) * q.2 1
```

and prove:
```lean
shear121 =
  split121.symm ∘ coreShear121 ∘ split121
```

Then:
```lean
have hshear : MeasurePreserving shear121 volume volume :=
  (measurePreserving_split121.symm split121).comp
    ((measurePreserving_coreShear_measurable 1 1 2 shift121 hshift121).comp
      measurePreserving_split121)
```

Finally compose:
```lean
have hQ121 : MeasurePreserving Q121 volume volume :=
  (measurePreserving_paramsEquivFlat M121).comp measurePreserving_pack121

have hphi : MeasurePreserving phi121sm volume volume := by
  rw [phi121sm_eq_Q121_shear121]
  exact hQ121.comp hshear
```

Reindex friction: `funUnique` has the wrong orientation for splitting, so use `.symm`; product `volume` often needs `rw [Measure.volume_eq_prod _ _]`; and `piFinSuccAbove` after removing coord `0` uses index `1 : Fin 3` to pick original coord `2`.

**Q2.** Yes: `MeasurePreserving.skew_product` only needs measurability. Exact v4.29 hypothesis:

```lean
theorem MeasurePreserving.skew_product
    [SFinite μa] [SFinite μc]
    {f : α → β} (hf : MeasurePreserving f μa μb)
    {g : α → γ → δ}
    (hgm : Measurable (uncurry g))
    (hg : ∀ᵐ a ∂μa, Measure.map (g a) μc = μd) :
    MeasurePreserving
      (fun p : α × γ => (f p.1, g p.1 p.2))
      (μa.prod μc) (μb.prod μd)
```

In `coreShear`, use:
```lean
(measurable_snd.add (hshift.comp measurable_fst))
```
and:
```lean
ae_of_all _ fun rs =>
  (measurePreserving_add_right (volume : Measure (Fin b → ℝ)) (shift rs)).map_eq
```

**Q3.** Yes. With Lean’s totalized division, `shear121` is a global measurable bijection and globally measure-preserving.

Use inverse:
```lean
shear121Inv v = ![v 0, v 1, v 2 + (v 1 / v 0) * v 3, v 3]
```

Both compositions are identity by cancellation; no `v 0 ≠ 0` hypothesis is needed. At `a = 0`, Lean has `b / 0 = 0`, so the fiber translation is just identity in `z`. The map and inverse are measurable because coordinate projections, multiplication, negation/subtraction, and real division are measurable.

Package as:
```lean
noncomputable def shear121ME : (Fin 4 → ℝ) ≃ᵐ (Fin 4 → ℝ) := ...
```

Then:
```lean
shear121ME.measurableEmbedding
```

No pole split is needed for `cov`. The pole may still matter for the rate identity, but not for change of variables.

**Q4.** Yes. Once you have:

```lean
hmp  : MeasurePreserving phi121sm volume volume
hemb : MeasurableEmbedding phi121sm
```

the cov proof is just:

```lean
set S := V \ {x : Fin 4 → ℝ | x 2 = 0} with hS
have hSmeas : MeasurableSet S :=
  hV.diff (measurableSet_eq_fun (measurable_pi_apply 2) measurable_const)

change
  ∫⁻ x in phi121sm '' S, g x
    = ∫⁻ u in S,
        ENNReal.ofReal (∏ j, |u j| ^ (0 : ℕ)) * g (phi121sm u)

calc
  ∫⁻ x in phi121sm '' S, g x
      = ∫⁻ u in S, g (phi121sm u) := by
          exact (hmp.setLIntegral_comp_emb hemb g S).symm
  _ = ∫⁻ u in S,
        ENNReal.ofReal (∏ j, |u j| ^ (0 : ℕ)) * g (phi121sm u) := by
          refine setLIntegral_congr_fun hSmeas (fun u hu => ?_)
          simp only [pow_zero, Finset.prod_const_one,
            ENNReal.ofReal_one, one_mul]
```

If the goal has `leafH121`, use:
```lean
simp only [leafH121, pow_zero, Finset.prod_const_one,
  ENNReal.ofReal_one, one_mul]
```

RECOMMEND: prove `measurePreserving_coreShear_measurable`, define/package `shear121ME`, prove `MeasurePreserving shear121` by conjugating through `split121`, compose with `Q121`, then apply `setLIntegral_comp_emb`. No pole split is needed for `cov`. Uncertain/nonexisting names: `split121`, `shear121ME`, `measurePreserving_coreShear_measurable`, and `phi121sm_eq_Q121_shear121` are local helpers you would add; the Mathlib v4.29 names above are verified.