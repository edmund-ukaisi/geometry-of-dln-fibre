import DLNFibre.DLN.RLCT.Validate.Case222Block

/-!
# `DLNFibre.DLN.RLCT.Validate.Case222CoverGE` — the `(2,2,2)` ≥-direction headline

The `≥` half of the `(2,2,2)` resolution value: `rlctAtOn myF222 0 ≥ 3/2`. Together with the gated
`≤`-half (`rlctAtOn_myF222_le`, `Case222Resolution`) this pins `rlctAtOn myF222 0 = 3/2 = ⨅`.

## The reduction (gated `rlctAtOn_ge_of_integral_lt`) — on a BOUNDED open box

`rlctAtOn_ge_of_integral_lt` reduces `3/2 ≤ rlctAtOn myF222 0` to the threshold-integral finiteness
over an open `U ∋ 0`. The witness MUST be a **bounded** open box `openBox = (−1,1)^8`, NOT `univ`:
`∫⁻_univ |myF222|^{−c'} = ⊤` (the integrand stays bounded below by a positive constant on the
infinite-measure region away from the zero locus, so it diverges at infinity — RLCT is a *local*
quantity at `0`, witnessed by any bounded neighbourhood). So `hfin` is stated over `openBox`
(Codex 2026-06-21 soundness catch — the `univ` form is FALSE).

## The cover (route R, gated `g5_pivotNode` / `recStep`)

`hfin` over `openBox` is discharged by the 3-deep `g5_pivotNode` recursion (the `Case222Block`
driver): `∫⁻_{openBox} f = ∫⁻_univ openBox.indicator f` (`recStep`/`setLIntegral_indicator`), then
`g5_pivotNode` on `univ` (`univ_ae_cover`, always-true cover) splits into the leaf sum — each leaf
finite below its `monomialThreshold = 3/2` (`monomialIntegrand_integrable_of_lt` + the unit-factor
bridge `integrableOn_monomial_mul_unit_iff`). The 4 step-1 A-pivots collapse to one chain by the
A-block coordinate symmetry of `myF222`.

SPECIFY stage: `rlctAtOn_myF222_ge` headline verified (reduces to `hfin` over `openBox`); `hfin`
body `sorry` pending the recursion assembly.
-/

open MeasureTheory Set
open scoped ENNReal BigOperators
namespace DLNFibre.DLN.RLCT

/-- The bounded open box `(−1, 1)^8` — a bounded open neighbourhood of `0`, the LOCAL witness for the
`≥`-direction threshold integral (the `univ` integral diverges at infinity). -/
def openBox : Set (Fin 8 → ℝ) := Set.univ.pi (fun _ => Set.Ioo (-1 : ℝ) 1)

/-- `openBox` is open. -/
theorem isOpen_openBox : IsOpen openBox :=
  isOpen_set_pi Set.finite_univ (fun _ _ => isOpen_Ioo)

/-- `0 ∈ openBox`. -/
theorem mem_openBox_zero : (0 : Fin 8 → ℝ) ∈ openBox := by
  intro i _; exact ⟨by norm_num, by norm_num⟩

/-- The step-1 A-block active set `{a00,a01,a10,a11} = {0,1,2,3}`. -/
def Aact : Finset (Fin 8) := {0, 1, 2, 3}

/-! ## Per-leaf monomial finiteness below `3/2` (the leaf-integrability the cover consumes)

Each cover leaf's integrand is a `monomialIntegrand` on `Fin 8` with two (unit) or three (block)
binding axes and the rest spectators (`k = 0`). For the `≥` lower bound every leaf must be finite
below its threshold `3/2`. The threshold-VALUE is `⨅ⱼ axisRatio (hⱼ) (kⱼ) = 3/2`: the binding axes
realise `2` and `3/2`, and the spectator axes (`k = 0`) give `axisRatio _ 0 = ⊤` — so they do NOT
lower the `⨅`. (The gated `monomialThreshold_ge_of_mult` does NOT apply — it needs `kⱼ ≥ 1` on every
axis, which the spectators violate; the spectator/binding split below is the route-R-shaped proof.) -/

/-- **Spectator axis ratio is `⊤`.** `axisRatio h 0 = (h+1)/(2·0) = ⊤` — a `k = 0` (spectator) axis
imposes no threshold bound (it does not lower the `⨅`). -/
theorem axisRatio_spectator (h : ℕ) : axisRatio h 0 = ⊤ := by
  unfold axisRatio; simp [ENNReal.div_zero]

/-- **The unit-leaf `Fin 8` monomial threshold is `≥ 3/2`** (the `≥`-half; the gated
`unitMonomialThreshold_le` is the `≤`-half, so `= 3/2`). Per-axis: binding axes (`k = 1`) via
`axisRatio_ge_of_mult` (`m = 3`, `3·1 ≤ hⱼ+1`); spectator axes (`k = 0`) via `axisRatio_spectator`
(`⊤`). This is the per-leaf finiteness input the `≥`-cover needs (the `≤`-work only had `≤`). -/
theorem unitMonomialThreshold_ge : (3 : ℝ≥0∞) / 2 ≤ monomialThreshold 8 unitK8 unitH8 := by
  rw [(monomial_rlct 8 unitK8 unitH8).1]
  refine le_iInf (fun j => ?_)
  rcases Nat.eq_zero_or_pos (unitK8 j) with h0 | hpos
  · rw [h0, axisRatio_spectator]; exact le_top
  · have hm : 3 * unitK8 j ≤ unitH8 j + 1 := by fin_cases j <;> simp_all [unitK8, unitH8]
    have := axisRatio_ge_of_mult (unitH8 j) (unitK8 j) 3 hpos hm
    rwa [show ((3 : ℕ) : ℝ≥0∞) / 2 = 3 / 2 by norm_num] at this

/-- **Unit-leaf integrability below `3/2`.** For `0 < c' < 3/2`, the unit-leaf monomial integrand is
integrable on the unit box (`monomialIntegrand_integrable_of_lt`, `c' < 3/2 = monomialThreshold`). The
unit-leaf finiteness the `≥`-cover consumes. -/
theorem unit_leaf_integrable (c' : NNReal) (hc0 : 0 < c') (hc' : (c' : ℝ≥0∞) < 3 / 2) :
    IntegrableOn (monomialIntegrand 8 unitK8 unitH8 (c' : ℝ)) (unitBox 8) volume :=
  monomialIntegrand_integrable_of_lt 8 unitK8 unitH8 c' hc0
    (lt_of_lt_of_le hc' unitMonomialThreshold_ge)

/-- The block-leaf `Fin 8` binding-monomial exponents (loss base `∏|uⱼ|^{2kⱼ}`): `k = 1` on the THREE
block-leaf exceptional axes (step-1, step-2-δ, step-3 pivots), `0` on the five spectators. -/
def blockK8 : Fin 8 → ℕ := ![1, 1, 1, 0, 0, 0, 0, 0]

/-- The block-leaf `Fin 8` Jacobian exponents (`∏|uⱼ|^{hⱼ}`): `h = 3, 2, 3` on the three exceptional
axes (`|det| = u₀³·u₂²·u_blk³`), `0` on the five spectators. -/
def blockH8 : Fin 8 → ℕ := ![3, 2, 3, 0, 0, 0, 0, 0]

/-- **The block-leaf `Fin 8` monomial threshold is `≥ 3/2`.** Same spectator/binding split as the unit
leaf: the three binding axes (`(k,h) = (1,3),(1,2),(1,3)`) realise `2, 3/2, 2 ≥ 3/2` via
`axisRatio_ge_of_mult` (`m = 3`); the five spectators give `⊤`. -/
theorem blockMonomialThreshold_ge : (3 : ℝ≥0∞) / 2 ≤ monomialThreshold 8 blockK8 blockH8 := by
  rw [(monomial_rlct 8 blockK8 blockH8).1]
  refine le_iInf (fun j => ?_)
  rcases Nat.eq_zero_or_pos (blockK8 j) with h0 | hpos
  · rw [h0, axisRatio_spectator]; exact le_top
  · have hm : 3 * blockK8 j ≤ blockH8 j + 1 := by fin_cases j <;> simp_all [blockK8, blockH8]
    have := axisRatio_ge_of_mult (blockH8 j) (blockK8 j) 3 hpos hm
    rwa [show ((3 : ℕ) : ℝ≥0∞) / 2 = 3 / 2 by norm_num] at this

/-- **Block-leaf integrability below `3/2`.** For `0 < c' < 3/2`, the block-leaf monomial integrand is
integrable on the unit box. The block-leaf finiteness the `≥`-cover consumes. -/
theorem block_leaf_integrable (c' : NNReal) (hc0 : 0 < c') (hc' : (c' : ℝ≥0∞) < 3 / 2) :
    IntegrableOn (monomialIntegrand 8 blockK8 blockH8 (c' : ℝ)) (unitBox 8) volume :=
  monomialIntegrand_integrable_of_lt 8 blockK8 blockH8 c' hc0
    (lt_of_lt_of_le hc' blockMonomialThreshold_ge)

/-! ## Effective-support containment (the leaf integrals are over a bounded box)

The step-1 chart domain `chartDomOn Aact 0` bounds only the *non-pivot active* coordinates
(`|x₁|, |x₂|, |x₃| ≤ 1`); the pivot `x₀` and the spectators `x₄..x₇` are FREE there. What bounds them
is the `openBox` cutoff carried through the chart: on `{step1A x ∈ openBox}` the pivot
(`step1A x` slot 0 `= x₀`) and the spectators (slots 4..7 `= x₄..x₇`) are each in `(−1, 1)`. So the
EFFECTIVE support of the `p = 0` summand sits inside the symmetric cube `[−1, 1]^8` — the integral is
over a bounded box, which is what the per-leaf `monomialThreshold` integrability (unit-box-shaped)
needs. (Codex 2026-06-21 Q3 mitigation: the support→bounded-box step.) -/

/-- **`p = 0` effective-support containment.** On the step-1 chart domain `chartDomOn Aact 0`, the
`openBox` cutoff `step1A x ∈ openBox` forces `x ∈ [−1, 1]^8`: the pivot `x₀` and spectators `x₄..x₇`
are bounded by `openBox` (via `step1A` slots `0, 4..7`), the active `x₁, x₂, x₃` by `chartDomOn`. -/
theorem p0_support_subset_cube (x : Fin 8 → ℝ)
    (hcd : x ∈ chartDomOn Aact 0) (hob : step1A x ∈ openBox) :
    x ∈ Set.univ.pi (fun _ : Fin 8 => Set.Icc (-1 : ℝ) 1) := by
  intro i _
  simp only [openBox, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Ioo] at hob
  fin_cases i
  · have := hob 0; simp only [step1A, Matrix.cons_val_zero] at this; exact ⟨this.1.le, this.2.le⟩
  · have := hcd 1 (by decide) (by decide); rw [abs_le] at this; exact this
  · have := hcd 2 (by decide) (by decide); rw [abs_le] at this; exact this
  · have := hcd 3 (by decide) (by decide); rw [abs_le] at this; exact this
  · have := hob 4; simp only [step1A, Matrix.cons_val] at this; exact ⟨this.1.le, this.2.le⟩
  · have := hob 5; simp only [step1A, Matrix.cons_val] at this; exact ⟨this.1.le, this.2.le⟩
  · have := hob 6; simp only [step1A, Matrix.cons_val] at this; exact ⟨this.1.le, this.2.le⟩
  · have := hob 7; simp only [step1A, Matrix.cons_val] at this; exact ⟨this.1.le, this.2.le⟩

/-- The symmetric unit cube `[−1, 1]^8` — the bounded box the `p = 0` leaf support sits inside
(`p0_support_subset_cube`); the box on which the per-leaf monomial integrability is transported. -/
noncomputable def cube8 : Set (Fin 8 → ℝ) := Set.univ.pi (fun _ => Set.Icc (-1 : ℝ) 1)

/-- `cube8` is measurable. -/
theorem cube8_meas : MeasurableSet cube8 := MeasurableSet.univ_pi (fun _ => measurableSet_Icc)

/-- The `p = 0` step-1 leaf-summand integrand: `|det φ₁| · (openBox.indicator |myF222|^{−c'}) ∘ φ₁`. -/
noncomputable def p0integrand (c' : NNReal) (x : Fin 8 → ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal |(pivotBlowupOnDeriv Aact 0 x).det|
    * openBox.indicator (fun y => ENNReal.ofReal (|myF222 y| ^ (-(c' : ℝ)))) (pivotBlowupOn Aact 0 x)

/-- The `p = 0` integrand vanishes off `{step1A x ∈ openBox}` (the `openBox.indicator` factor). -/
theorem p0integrand_support (c' : NNReal) (x : Fin 8 → ℝ) (hx : p0integrand c' x ≠ 0) :
    step1A x ∈ openBox := by
  unfold p0integrand at hx
  by_contra hni
  rw [show pivotBlowupOn Aact 0 x = step1A x from (step1A_eq_pivotBlowupOn x).symm,
    Set.indicator_of_notMem hni, mul_zero] at hx
  exact hx rfl

/-- **`p = 0` cube-bound reduction.** The step-1 `p = 0` summand is bounded by the integral over the
bounded cube `cube8`: the integrand vanishes off `{step1A x ∈ openBox}`, and there (on the chart
domain) `x ∈ cube8` (`p0_support_subset_cube`); so the chart-domain indicator is dominated by the
`cube8` indicator (`lintegral_indicator` + `lintegral_mono`). Reduces the unbounded chart-domain
integral to a bounded box, where the per-leaf monomial integrability applies. -/
theorem p0_summand_le_cube (c' : NNReal) :
    ∫⁻ x in chartDomOn Aact 0 \ pivotZeroOn 0, p0integrand c' x
      ≤ ∫⁻ x in cube8, p0integrand c' x := by
  rw [← lintegral_indicator (chartDomOn_diff_measurableSet Aact 0) (p0integrand c'),
    ← lintegral_indicator cube8_meas (p0integrand c')]
  apply lintegral_mono
  intro x
  by_cases hmem : x ∈ chartDomOn Aact 0 \ pivotZeroOn 0
  · rw [Set.indicator_of_mem hmem]
    by_cases hf : p0integrand c' x = 0
    · rw [hf]; exact zero_le _
    · rw [Set.indicator_of_mem (show x ∈ cube8 from
        p0_support_subset_cube x hmem.1 (p0integrand_support c' x hf))]
  · rw [Set.indicator_of_notMem hmem]; exact zero_le _

/-- **A step-1 A-pivot leaf-summand is finite (below `3/2`).** For each A-pivot `p ∈ {0,1,2,3}` and
`c' < 3/2`, the `p`-cell of the step-1 `g5_pivotNode` split — the chart-domain integral of
`|det φ₁ₚ| · (openBox.indicator |myF222|^{−c'}) ∘ φ₁ₚ` — is finite. This is the per-A-pivot recursion
chain (Lemma-2 splice → step-2 `{1,2,3}` → step-3 block → per-leaf `monomialThreshold = 3/2`
finiteness). The four pivots' chains are structurally analogous (each factors `myF222 ∘ φ₁ₚ =
yₚ²·Qₚ` by `ring`, the residual `Qₚ` a resolved form with the same leaf thresholds). -/
theorem aPivotSummand_lt_top (c' : NNReal) (hc' : (c' : ℝ≥0∞) < 3 / 2) (p : Fin 8) (hp : p ∈ Aact) :
    ∫⁻ x in chartDomOn Aact p \ pivotZeroOn p,
        ENNReal.ofReal |(pivotBlowupOnDeriv Aact p x).det|
          * openBox.indicator (fun y => ENNReal.ofReal (|myF222 y| ^ (-(c' : ℝ))))
              (pivotBlowupOn Aact p x) < ⊤ := by
  sorry

/-- **The `(2,2,2)` ≥-direction threshold finiteness (over the bounded box).** For every `c' < 3/2`,
the threshold integral of `myF222` over the bounded open box `(−1,1)^8` is finite — the LOCAL input
the `≥` lower bound needs. The step-1 `g5_pivotNode` (`recStep` on the box) splits it into the four
A-pivot summands (`aPivotSummand_lt_top`), each finite; `ENNReal.sum_lt_top` closes. NOTE the `univ`
form is FALSE (diverges at infinity); the bound is genuinely local. -/
theorem myF222_threshold_lintegral_lt_top (c' : NNReal) (hc' : (c' : ℝ≥0∞) < 3 / 2) :
    ∫⁻ x in openBox, ENNReal.ofReal (|myF222 x| ^ (-(c' : ℝ))) < ⊤ := by
  rw [recStep Aact 0 (by decide) openBox isOpen_openBox.measurableSet
    (fun y => ENNReal.ofReal (|myF222 y| ^ (-(c' : ℝ))))]
  exact ENNReal.sum_lt_top.2 (fun p hp => aPivotSummand_lt_top c' hc' p hp)

/-- **The `(2,2,2)` ≥-direction headline.** `rlctAtOn myF222 0 ≥ 3/2` — the lower bound matching the
gated `≤`-half (`rlctAtOn_myF222_le`). Via `rlctAtOn_ge_of_integral_lt` on the bounded open box
`openBox ∋ 0` (`myF222_threshold_lintegral_lt_top` supplies the local threshold finiteness for every
`c' < 3/2`). -/
theorem rlctAtOn_myF222_ge : (3 : ℝ≥0∞) / 2 ≤ rlctAtOn myF222 0 := by
  apply rlctAtOn_ge_of_integral_lt myF222 ?_ openBox isOpen_openBox mem_openBox_zero (3 / 2)
    myF222_threshold_lintegral_lt_top
  unfold myF222; fun_prop

end DLNFibre.DLN.RLCT
