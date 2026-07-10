**Verdict**
Do not start by defining global `α/K/Y` recursion as ordinary Lean functions. Prove `normalSlice_transfer` from an abstract finite chart datum first; then the only hard residue is constructing that datum.

**1. Lemma DAG**
1. `abbrev redTail (M) (q) := fun i : Fin (L+1+1) => M i.succ - q`  
   [REACHABLE]

2. `frontStratumIntegral` definition, if not already landed.  
   [REACHABLE]

3. `shiftedThreshold`:
```lean
(c' : ℝ) < (minAdm M : ℝ)/2 →
q ≤ tailMin M →
(c' : ℝ) - (M 0 * q : ℝ)/2 < (minAdm (redTail M q) : ℝ)/2
```
[BANKED-reuse / follows from `frontCharge_ge_minAdm`]

4. `morse_reduced_box_lt_top`:
```lean
theorem morse_reduced_box_lt_top
  (R : Fin (L+1+1) → ℕ) (d : ℕ) (c' : NNReal)
  (hIH : RouteMBoxThresholdFinite R)
  (hc : (c' : ℝ) < ((d + minAdm R : ℕ) : ℝ)/2) :
  ∫⁻ Y in paramsBoxM R 1,
    ∫⁻ X in morseBox d 1,
      ENNReal.ofReal (((∑ i, X i ^ 2) + frobSq (prod R Y)) ^ (-(c' : ℝ))) < ⊤
```
[REACHABLE, but include `d=0` and `c'=d/2` branches]

5. `NormalSliceChartData M q χ` record:
fields should include finite chart set, measure-preserving coordinate map, spectator finite-volume bound, reduced `Y : Params (redTail M q)`, Morse block `R : Fin (M 0*q) → ℝ`, and a pointwise loss domination/equality.
[REACHABLE-def]

6. `normalSlice_chart_lt_top`:
```lean
theorem normalSlice_chart_lt_top
  (χ : NormalSliceChartData M q)
  (hcRed : (c' : ℝ) - (M 0*q : ℝ)/2 < (minAdm (redTail M q) : ℝ)/2)
  (hIH : RouteMBoxThresholdFinite (redTail M q)) :
  χ.chartIntegral c' < ⊤
```
[REACHABLE]

7. `frontStratumIntegral_le_chart_sum`:
```lean
frontStratumIntegral M q c'
  ≤ ∑ χ : ChartIndex M q, chartIntegral M q χ c'
```
Finite cover + `lintegral_iUnion_le`/`tsum_fintype`.
[REACHABLE once cover field exists; cover construction is HARD]

8. `tailThread_rank_eq`:
```lean
(prod (tailChain M) A').rank
  = q + (prod (redTail M q) (χ.Y A')).rank
```
on chart `χ`.
[HARD-opaque-width]

9. `tailThread_rank_eq_q_iff`:
```lean
(prod (tailChain M) A').rank = q ↔ prod (redTail M q) (χ.Y A') = 0
```
uses `Matrix.rank_eq_zero_iff` after (8).
[REACHABLE after (8)]

10. `tailThread_jacobian_one`:
chart coordinate map is measure-preserving / abs-Jacobian `1`.
[HARD-opaque-width]

11. `frontLoss_normalSlice_split`:
```lean
frobSq (rmatMul A0 (prod (tailChain M) A'))
  ≃ (∑ i, R_i^2) + frobSq (prod (redTail M q) Y)
```
Prefer a `≤ C * ...` domination, not exact equality, unless exact is already natural.
[HARD-opaque-width; uses banked Schur block split]

12. `normalSlice_transfer`: combine finite chart sum, each chart finite, `shiftedThreshold`.
[REACHABLE after walls]

**2. Entry Point**
First prove `morse_reduced_box_lt_top`.

Reason: it is independent of the threaded dependent-width algebra, tests the exponent shift against `hIH`, and exposes the missing borderline case `c' = M0*q/2`. If this lemma is clean, the rest can be reduced to chart data.

**3. Walls**
Real walls:

- Threaded tail normal form over widths `M i.succ - q`.  
  Pattern: keep everything in `Matrix (Fin q ⊕ Fin (M i - q)) ...`; use `blockSplitEquiv`/`finSplit`, not entrywise casts.

- Product telescoping/reassociation.  
  Pattern: `set X := ...; set Y := ...; exact mul_three_reassoc A X Y`. Do not rely on `rw [Matrix.mul_assoc]`.

- Entrywise block identities under opaque widths.  
  Pattern: prove per-entry `have`s at explicit indices like `⟨k, by omega⟩`; after `fin_cases`, close with `exact h`. Avoid hoping `simp` sees dependent `Fin` defeqs.

- `⅟` vs `⁻¹` under integrals.  
  Pattern: if a pointwise chart gives `IsUnit A.det`, use `letI := A.invertibleOfIsUnitDet hA`, then `rw [invOf_eq_nonsing_inv]`; prefer final integrand lemmas stated with `A⁻¹`.

- Rank transport through unit factors.  
  Confirmed Mathlib v4.29: `Matrix.rank_mul_eq_left_of_isUnit_det`, `Matrix.rank_mul_eq_right_of_isUnit_det`. Local repo has block rank: `Matrix.rank_fromBlocks_zero_offdiag`, `Matrix.rank_eq_zero_iff`.

**4. Simplifications**
Best: define `NormalSliceChartData` as an interface and prove `normalSlice_transfer` from it. Then construct the data separately. This gives the cleanest Lean decomposition.

Second best: define α/K/Y only inside a chart-construction namespace, exposing only `Y`, rank equation, loss domination, and MP fields.

Weak: an existence-only
```lean
∃ U V Y, IsUnit U.det ∧ IsUnit V.det ∧ U * P * V = blockUpper ...
```
helps rank algebra, but does not give a measurable coordinate change, Jacobian, or domain control. Not enough for the integral.

Bad shortcut: pointwise rank-normal-form existence. Nonconstructive, not measurable, no CoV.

**5. Restatement Flags**
- Add a lemma for the equality case `c' = M0*q/2`; the certificate only says regimes `≷`. Lean will hit equality.
- `hIH` is for `paramsBoxM _ 1`; chart images may be translated/enlarged. Either prove bounded-domain stability of `RouteMBoxThresholdFinite`, or include domain domination in `NormalSliceChartData`.
- “α⁻¹ only as units” is not a Lean analytic statement. State the actual measurable equivalence and Jacobian/domination lemma.
- Use banked pieces directly: `pivotLocus_eq_iUnion`, `pivotChartCover_matBox_le_sum`, `frobSq_schur_block_split`, `measurePreserving_shearSub`, `radial_morse_residual_power_le`, `sumSqND_box_lt_top`.