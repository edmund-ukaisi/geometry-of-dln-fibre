  -- `Equiv.preimage_piEquivPiSubtypeProd_symm_pi`

-- 3) transport the set integral
have hsplit :
  ∫⁻ u in boxε, F u =
  ∫⁻ z in s×ˢt, F (e.symm z) := by
  -- `MeasurePreserving.setLIntegral_comp_preimage_emb` + `hpre`

-- 4) factor on product space + Tonelli
-- show: F (e.symm (x,y)) = f0 x * f1 y
have hfactor :
  ∫⁻ z in s×ˢt, F (e.symm z)
    = (∫⁻ x in Icc (0:ℝ) ε, f0 x) * (∫⁻ y in restBox, f1 y) := by
  -- `setLIntegral_prod` + `lintegral_lintegral_mul`

-- 5) the binding axis integral is ⊤
have hnot : ¬ IntegrableOn (fun x => |x| ^ s) (Ioo (0:ℝ) ε) := by
  -- your `abs_rpow_integrableOn_Ioo_iff` + hexp
have htop_Ioo :
  ∫⁻ x in Ioo (0:ℝ) ε, ENNReal.ofReal (|x| ^ s) = ⊤ := by
  -- contrapose `lintegral_ofReal_ne_top_iff_integrable`
have htop_Icc :
  ∫⁻ x in Icc (0:ℝ) ε, ENNReal.ofReal (|x| ^ s) = ⊤ := by
  -- `lintegral_mono_set` (Ioo ⊆ Icc), `top_le_iff`

-- 6) rest factor ≠ 0
have hpos_rest :
  0 < ∫⁻ y in restBox, f1 y := by
  -- `setLIntegral_pos_iff` + support contains `pi univ (fun _ => Ioo 0 ε)`
  -- use `volume_pi_Ioo` and `measure_Ioo_pos`
have hne_rest : (∫⁻ y in restBox, f1 y) ≠ 0 := ne_of_gt hpos_rest

-- 7) conclude
simp [hfactor, htop_Icc, ENNReal.mul_top hne_rest]
```

That avoids any `Finset.prod_eq_top` lemma and keeps everything 2D.

---

**Q3 (boundary `c' ≥ threshold`)**  
`≥` is correct and clean. For your monomial, integrability is **strict** `s > -1` on each axis; so at `s = -1` it already diverges. Hence `c' = threshold` should diverge (no need for strict `>`). The `0^neg` convention doesn’t rescue integrability because it only changes a measure‑zero set.

The only subtlety is the **existence** of a binding axis from the infimum: since the index set is `Fin d`, you can use `Finset.inf_le_iff` after rewriting `⨅` as `Finset.univ.inf`. That gives an actual `j0` with `axisRatio ≤ c'`, hence `k j0 ≠ 0` and the exponent bound.

---

If you want, I can help you turn the above skeleton into a full Lean proof with your actual names (`monomialIntegrand`, `unitBox`, `axisRatio` lemmas) and the measurability boilerplate.
tokens used
53,168
**Q1 (⊤ vs ¬IntegrableOn)**  
Yes — the clean bridge is `ENNReal.lintegral_ofReal_ne_top_iff_integrable` on the restricted measure. For a.e.-measurable nonnegative `f`, on `μ := volume.restrict s` you get:
```
∫⁻ x in s, ENNReal.ofReal (f x) ≠ ∞ ↔ IntegrableOn f s
```
So your divergence goal is:
```
by_contra hfinite
have hInt : IntegrableOn f s :=
  (ENNReal.lintegral_ofReal_ne_top_iff_integrable (μ:=volume.restrict s) hfm hnonneg).1 hfinite
-- contradiction with your 1D criterion
```
This is usually simpler than working directly with `lintegral_prod`. The `0^neg` issue is null-set only; you can always reduce to `Ioo` and then use `lintegral_mono_set` to lift to `Icc`.

---

**Q2 (factor + one binding axis)**  
There is no single “pi-product” lemma for `Fin d`, but the clean route in v4.29 is **split one axis and use Tonelli**.

**Key lemmas (all in Mathlib v4.29):**
- `MeasureTheory.setLIntegral_prod` (Tonelli on `s ×ˢ t`)
- `MeasureTheory.lintegral_lintegral_mul` (separable product)
- `MeasurePreserving.setLIntegral_comp_preimage_emb`
- `volume_preserving_piEquivPiSubtypeProd`
- `Equiv.preimage_piEquivPiSubtypeProd_symm_pi`
- `ENNReal.mul_top` / `ENNReal.top_mul`

**Skeleton (lean-ish, omitting measurability boilerplate):**
```
classical
-- 1) pick binding axis j0 from the inf
have hInf :
  (Finset.univ.inf (fun j => axisRatio (h j) (k j))) ≤ ENNReal.ofReal c' := by
    -- use S2 + Finset.inf_eq_iInf
    -- simp [Finset.inf_eq_iInf] at ...
have hc'lt : (ENNReal.ofReal c') < ⊤ := by simp
obtain ⟨j0, -, hratio⟩ :=
  (Finset.inf_le_iff (s:=Finset.univ) (f:=fun j => axisRatio (h j) (k j)) hc'lt).1 hInf
have hk0 : k j0 ≠ 0 := by
  -- axisRatio = ⊤ iff k=0, so hratio forbids k=0
have hexp : (h j0 : ℝ) - (2 * (k j0 : ℝ)) * c' ≤ -1 := by
  -- convert hratio using `ENNReal.toReal_le_toReal` or `ofReal_le_ofReal_iff`

-- 2) split the box by j0
set p : Fin d → Prop := fun j => j = j0
let e := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin d => ℝ) p
have hmp : MeasurePreserving e volume volume :=
  volume_preserving_piEquivPiSubtypeProd (α:=fun _ => ℝ) p
have hpre :
  e ⁻¹' (pi univ (fun _ : Subtype p => Icc (0:ℝ) ε) ×ˢ
         pi univ (fun _ : Subtype (¬p) => Icc (0:ℝ) ε))
    = (pi univ (fun _ : Fin d => Icc (0:ℝ) ε)) := by
  -- `Equiv.preimage_piEquivPiSubtypeProd_symm_pi`

-- 3) transport the set integral
have hsplit :
  ∫⁻ u in boxε, F u =
  ∫⁻ z in s×ˢt, F (e.symm z) := by
  -- `MeasurePreserving.setLIntegral_comp_preimage_emb` + `hpre`

-- 4) factor on product space + Tonelli
-- show: F (e.symm (x,y)) = f0 x * f1 y
have hfactor :
  ∫⁻ z in s×ˢt, F (e.symm z)
    = (∫⁻ x in Icc (0:ℝ) ε, f0 x) * (∫⁻ y in restBox, f1 y) := by
  -- `setLIntegral_prod` + `lintegral_lintegral_mul`

-- 5) the binding axis integral is ⊤
have hnot : ¬ IntegrableOn (fun x => |x| ^ s) (Ioo (0:ℝ) ε) := by
  -- your `abs_rpow_integrableOn_Ioo_iff` + hexp
have htop_Ioo :
  ∫⁻ x in Ioo (0:ℝ) ε, ENNReal.ofReal (|x| ^ s) = ⊤ := by
  -- contrapose `lintegral_ofReal_ne_top_iff_integrable`
have htop_Icc :
  ∫⁻ x in Icc (0:ℝ) ε, ENNReal.ofReal (|x| ^ s) = ⊤ := by
  -- `lintegral_mono_set` (Ioo ⊆ Icc), `top_le_iff`

-- 6) rest factor ≠ 0
have hpos_rest :
  0 < ∫⁻ y in restBox, f1 y := by
  -- `setLIntegral_pos_iff` + support contains `pi univ (fun _ => Ioo 0 ε)`
  -- use `volume_pi_Ioo` and `measure_Ioo_pos`
have hne_rest : (∫⁻ y in restBox, f1 y) ≠ 0 := ne_of_gt hpos_rest

-- 7) conclude
simp [hfactor, htop_Icc, ENNReal.mul_top hne_rest]
```

That avoids any `Finset.prod_eq_top` lemma and keeps everything 2D.

---

**Q3 (boundary `c' ≥ threshold`)**  
`≥` is correct and clean. For your monomial, integrability is **strict** `s > -1` on each axis; so at `s = -1` it already diverges. Hence `c' = threshold` should diverge (no need for strict `>`). The `0^neg` convention doesn’t rescue integrability because it only changes a measure‑zero set.

The only subtlety is the **existence** of a binding axis from the infimum: since the index set is `Fin d`, you can use `Finset.inf_le_iff` after rewriting `⨅` as `Finset.univ.inf`. That gives an actual `j0` with `axisRatio ≤ c'`, hence `k j0 ≠ 0` and the exponent bound.

---

If you want, I can help you turn the above skeleton into a full Lean proof with your actual names (`monomialIntegrand`, `unitBox`, `axisRatio` lemmas) and the measurability boilerplate.
