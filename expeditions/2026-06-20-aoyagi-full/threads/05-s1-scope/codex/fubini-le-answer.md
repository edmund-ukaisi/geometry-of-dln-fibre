**Short answer:** the obstruction is real only if you try to make `V := V₀ ∩ {H ≤ R²}` itself the RLCT witness. The clean bridge is option **(b)**: choose an open finite-measure `V₀ ∋ y0`, split it into low/high `H`, use `core_int_of_joint_int` on the low part, and prove the high part is integrable because `|H|^{-(c-1/2)}` is bounded there.

No continuity or local boundedness of `H` is needed.

**Clean Lean Route**
From a joint admissible witness, shrink the open joint neighborhood to a product:
```lean
A ×ˢ Vbase ⊆ Ω_joint,   0 ∈ A,   y0 ∈ Vbase
```
using `mem_nhds_prod_iff'`. Pick `R > 0` with `Icc (-R) R ⊆ A`. Then choose a bounded open ball
```lean
V₀ := Metric.ball y0 δ
```
with `V₀ ⊆ Vbase ∩ U_hHne`, so `H ≠ 0` a.e. on `V₀`, and `volume V₀ < ∞`.

Now split:
```lean
Vlo := V₀ ∩ {y | H y ≤ R ^ 2}
Vhi := V₀ ∩ {y | R ^ 2 < H y}
```

On `Vlo`, apply your lemma:
```lean
core_int_of_joint_int (c' : ℝ) R ... Vlo ...
```
because `H ≤ R²` holds pointwise on `Vlo`.

On `Vhi`, prove directly:
```lean
IntegrableOn (fun y => |H y| ^ (-((c' : ℝ) - 1 / 2))) Vhi volume
```
by `IntegrableOn.of_bound`. Since `R² < H y` and `b := (c' : ℝ) - 1/2 ≥ 0`,
```lean
|H y| ^ (-b) ≤ (R ^ 2) ^ (-b)
```
by `Real.rpow_le_rpow_of_nonpos`. The set has finite measure because `Vhi ⊆ Metric.ball y0 δ`.

Then combine:
```lean
have hVsplit : V₀ = Vlo ∪ Vhi := by
  ext y
  by_cases h : H y ≤ R ^ 2
  · simp [Vlo, Vhi, h]
  · simp [Vlo, Vhi, h, not_le.mp h]

have hcoreV₀ : IntegrableOn core V₀ volume := by
  rw [hVsplit]
  exact hcore_lo.union hcore_hi
```

This gives an **open** core witness `V₀`, so `(c' - 1/2)` is admissible for `rlctAtOn H y0`.

**Arithmetic Finish**
Let
```lean
bNN : NNReal := ⟨(c' : ℝ) - 1 / 2, by linarith⟩
```
Then from the open witness:
```lean
(bNN : ℝ≥0∞) ≤ rlctAtOn H y0
```
by `le_sSup`.

Finally:
```lean
(c' : ℝ≥0∞)
  = (1 / 2 : ℝ≥0∞) + (bNN : ℝ≥0∞)
  ≤ (1 / 2 : ℝ≥0∞) + rlctAtOn H y0
```
using `NNReal.coe_sub`, `tsub_add_cancel_of_le`, and monotonicity of addition. If `(c' : ℝ) ≤ 1/2`, use `le_trans hc (le_self_add)` or the corresponding `ENNReal` addition monotonicity.

**Answers To Your Options**
- **(a)** No. For merely measurable `H`, you cannot use the y-slice directly and choose a bound. There may be no open sub-neighborhood where `H ≤ R²`, even a.e.
- **(b)** Yes. This is the minimal-friction route. The high part is harmless because the **core** integrand is bounded there, and `V₀` has finite measure.
- **(c)** Do not change the cusp lemma. Keep `core_int_of_joint_int` rectangular and bounded. Add a wrapper lemma that outputs open-neighborhood core integrability by doing the split.

**Important Fidelity Point**
`H y0 > 0` does **not** imply `rlctAtOn H y0 = ⊤` for merely measurable `H`. That implication needs something like continuity or an a.e. lower bound on an open neighborhood. Point values do not control this `sSup` definition.

**Lemma Names**
CONFIDENT:
- `mem_nhds_prod_iff'`
- `IsOpen.mem_nhds`
- `Metric.mem_nhds_iff`
- `Metric.ball_mem_nhds`
- `Metric.isOpen_ball`
- `Metric.isBounded_ball.measure_lt_top`
- `MeasurableSet.inter`, `MeasurableSet.union`, `MeasurableSet.diff`
- `measurableSet_le`, `measurableSet_lt`
- `ae_restrict_of_ae_restrict_of_subset`
- `ae_restrict_mem`
- `IntegrableOn.mono_set`
- `IntegrableOn.union`
- `IntegrableOn.of_bound`
- `Real.rpow_le_rpow_of_nonpos`
- `Real.rpow_nonneg`
- `le_sSup`, `sSup_le`
- `ENNReal.ofReal_coe_nnreal`
- `NNReal.coe_sub`
- `tsub_add_cancel_of_le`

NAME-UNCERTAIN:
- Direct named measurability lemma for `fun y => |H y| ^ (-b)`. In this repo, use:
```lean
(by fun_prop : Measurable (fun y => |H y| ^ (-b))).aestronglyMeasurable
```
which matches the existing `S1Fubini.lean` style.