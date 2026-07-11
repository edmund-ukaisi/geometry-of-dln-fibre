import DLNFibre.DLN.RLCT.Validate.RouteMSJSlice334
import DLNFibre.DLN.RLCT.Validate.RouteMSJLedger

/-!
# `DLNFibre.DLN.RLCT.Validate.RouteMSJCorner334` — the `(3,3,3,4)` `t=1` decorated corner-slice

**Thread `genm-corner334`, T4 first-settling slice.** Assembles the banked additive-corner endpoint
(`RouteMSJSlice334.sjSlice_corner_two_block_lt_top`) into the `(3,3,3,4)`, binding-cut `t=1`
**decorated corner-slice** finiteness, and — the genuinely-new content here — makes the corner
endpoint's abstract *units-positive* hypothesis CONCRETE by tying it to the rank of the deep data
`A₂`, and maps the boundary: EXACTLY ONE vanishing unit (the other positive) forces divergence below
the threshold, while the both-zero locus is finite (loss ≡ 0, by the rpow-zero convention). So the
units are not merely sufficient — a one-sided rank-drop of `A₂` genuinely diverges on the fixed slice
(the boundary is mapped by the two directional lemmas, NOT a clean `⟺`; see §3).

This is the smallest settling piece that validates the **min→sum mechanism IN LEAN** before the
general decorated recursion glue (pen-and-paper certificate
`expeditions/2026-06-20-aoyagi-full/threads/genm-vsastruct/t4-merge-derisk.md`, §1–§3). What it adds
over the banked `RouteMSJSlice334`:

1. **The min→sum distinction at the carrier level** (`sjLoss_indicator_two_block`). Recording the
   block-additive support via the banked `prependColumn` with the **indicator** columns
   `a_k(i)=𝟙[block(i)=k]` produces the **ADDITIVE** two-block loss `u₀²·U₀ + u₁²·U₁` (each block owns
   its own fresh divisor; the two divisors are NOT shared). Contrast `radialAttach`
   (`= prependColumn (fun _ => 1)`, the banked `sjLoss_prependColumn_one`): there EVERY generator
   shares the fresh divisor, giving the MULTIPLICATIVE `u₀²·(everything)`, whose repetition across
   blocks lands the `3/2` undershoot (`RouteMSJSlice334.sjSlice334_symmetric_undershoot`). The
   indicator/`radialAttach` choice is the min→sum crux.

2. **The concrete units from the deep data `A₂`** (`cornerUnit0`, `cornerUnit1`, `cornerUnits_pos`).
   In the corner endpoint `U₀,U₁` are analytic *units* — NOT the vanishing monomial residual of the
   pure `sjLoss` ledger. Faithful to the cert, `U₀ = ‖w₁ᵥ*A₂‖² + δ²‖w₂ᵥ*A₂‖²` and
   `U₁ = a_piv²·‖v̄ᵥ*A₂‖²` (sums of squares of the deep matrix-vector products). They are strictly
   positive **when `A₂` has full row rank** (`Function.Injective A₂.vecMul`, the rows independent) and
   the test directions `w₁, v̄` are nonzero — the *sufficient* condition `cornerUnits_pos` proves. (The
   converse is FALSE: a rank-deficient `A₂` that does not annihilate the test vectors also gives
   positive units; so this is a one-directional link, not an `iff`.)

3. **The sector slice + the sharp boundary** (`sjCorner334_sector_slice_lt_top`,
   `cornerSlice334_eq_top_of_unit0_zero`, `cornerSlice334_eq_top_of_unit1_zero`). On the generic-minor
   **sector** `{A₂ : full row rank}` (+ nonzero test directions) the units are positive, so the slice
   is finite at `7/2 = ½·minAdm(3,3,3,4)` (the good branch, closed by the banked additive-corner
   endpoint). The hypothesis is SHARP on the fixed slice: if a unit VANISHES (e.g. `A₂` rank-drop
   annihilating `v̄`, so `U₁ = 0`) the slice integral is `⊤` for `c'` at/above the corresponding
   boundary (`c' ≥ 2` when `U₁ = 0 < U₀`; `c' ≥ 3/2` when `U₀ = 0 < U₁`) — a vanishing unit genuinely
   diverges BELOW `7/2`. Consequently the `A₂`-rank-drop complement is **not finite fixed-slice by
   fixed-slice**: its finiteness is a **joint obligation** (integrated over the deep data `A₂`,
   Tonelli, at the deeper stratum's threshold), deferred to the general-recursion follow-on — NOT a
   fixed-slice hypothesis, and NOT an a.e.-drop (the weight is unbounded near the rank-drop locus).
   (An earlier fixed-slice "cover" hypothesis was DROPPED as false-premise: on the fixed slice the
   complement's conclusion `< ⊤` is itself false for `c' ∈ [2, 7/2)`, per the divergence lemmas.)

**The soundness point (min→sum, not a scalar-split min).** The corner endpoint's proof is the
weighted AM-GM at the min-cut weights where the two codimensions **ADD** (`4+3 = 7 → 7/2`); an
independent scalar split of the two divisors would take the **MIN** (`→ 3/2`, the `z²(x²+y²)`
collapse). The units-positive hypothesis is exactly what pins the coupled (additive) branch.

S2-FREE: no `monomial_rlct`, no `cited_aoyagi_dln`. This proves box-finiteness at the branch
threshold `7/2 = ½·minAdm(3,3,3,4)` only; the `rlct = ½·codim` reading stays Cited.
-/

namespace DLNFibre.DLN.RLCT

open MeasureTheory Set Real
open scoped ENNReal BigOperators Matrix

/-! ## 1. The min→sum crux at the carrier level — indicator `prependColumn` is ADDITIVE -/

variable {d : ℕ}

/-- **Indicator `prependColumn` produces the block-ADDITIVE loss (the min→sum crux).** Prepending
two fresh exceptional divisors `u₀, u₁` with the **indicator** support columns `a₀ = 𝟙[block 0]`,
`a₁ = 𝟙[block 1]` factors the terminal loss as the **sum of two block terms**, each block owning its
own fresh divisor and the two divisors NOT shared. Shown here on the concrete `3`-generator, `2`-block
witness — block `0 = {gen 0, gen 1}` (column `a₀ = ![1,1,0]`), block `1 = {gen 2}` (column
`a₁ = ![0,0,1]`):

    sjLoss (prependColumn ![1,1,0] (prependColumn ![0,0,1] ebase)) (u₀ ::: u₁ ::: rest)
        = u₀²·(b₀² + b₁²) + u₁²·(b₂²)  =  u₀²·U₀(rest) + u₁²·U₁(rest).

This is the additive shape the corner endpoint consumes. Contrast `sjLoss_prependColumn_one` (the
`radialAttach` all-ones column) where EVERY generator shares the fresh divisor and the loss is the
MULTIPLICATIVE `u₀²·(reduced)`; its repetition across blocks lands the `3/2` undershoot
(`sjSlice334_symmetric_undershoot`). The indicator (block-additive) vs all-ones (shared/multiplicative)
choice is exactly the min (`3/2`) → sum (`7/2`) distinction (t4-merge-derisk §1). -/
theorem sjLoss_indicator_two_block (ebase : SJSupport (Fin 3) d)
    (u₀ u₁ : ℝ) (rest : Fin d → ℝ) :
    sjLoss (prependColumn ![1, 1, 0] (prependColumn ![0, 0, 1] ebase))
        (Fin.cons u₀ (Fin.cons u₁ rest))
      = u₀ ^ 2 * (genMonomial ebase 0 rest ^ 2 + genMonomial ebase 1 rest ^ 2)
        + u₁ ^ 2 * genMonomial ebase 2 rest ^ 2 := by
  unfold sjLoss
  rw [Fin.sum_univ_three]
  simp only [genMonomial_prependColumn, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [show (![1, 1, 0] : Fin 3 → ℕ) 2 = 0 from by decide,
      show (![0, 0, 1] : Fin 3 → ℕ) 2 = 1 from by decide]
  simp only [pow_zero, pow_one, one_mul, mul_pow, sq_abs]
  ring

/-! ## 2. The concrete deep-data units and their positivity from full row rank -/

variable {q : ℕ}

/-- **The corner unit `U₀ = ‖w₁ᵥ*A₂‖² + δ²·‖w₂ᵥ*A₂‖²`** (t4-merge-derisk §2), as an explicit sum of
squares of the deep matrix-vector products `w ᵥ* A₂`. Strictly positive when `A₂` has full row rank
and `w₁ ≠ 0` (`cornerUnits_pos`); the converse fails (positivity does not force full rank). -/
def cornerUnit0 (A₂ : Matrix (Fin 2) (Fin q) ℝ) (w₁ w₂ : Fin 2 → ℝ) (δ : ℝ) : ℝ :=
  (∑ j, (w₁ ᵥ* A₂) j ^ 2) + δ ^ 2 * (∑ j, (w₂ ᵥ* A₂) j ^ 2)

/-- **The corner unit `U₁ = a_piv²·‖v̄ᵥ*A₂‖²`** (t4-merge-derisk §2). -/
def cornerUnit1 (A₂ : Matrix (Fin 2) (Fin q) ℝ) (vbar : Fin 2 → ℝ) (apiv : ℝ) : ℝ :=
  apiv ^ 2 * (∑ j, (vbar ᵥ* A₂) j ^ 2)

/-- **A sum of squares of a nonzero vector is strictly positive.** -/
theorem sum_sq_pos_of_ne_zero {v : Fin q → ℝ} (hv : v ≠ 0) : 0 < ∑ j, v j ^ 2 := by
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hv
  have hj0 : v j ≠ 0 := by simpa using hj
  refine Finset.sum_pos' (fun i _ => sq_nonneg _) ⟨j, Finset.mem_univ j, ?_⟩
  exact lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hj0))

/-- **Full row rank ⟹ the deep matrix-vector product of a nonzero direction is nonzero.**
`Function.Injective A₂.vecMul` is exactly "the rows of `A₂` are linearly independent" = full row
rank; then a nonzero direction `w` maps to a nonzero `w ᵥ* A₂` (`vecMul 0 = 0` + injectivity). -/
theorem vecMul_ne_zero_of_injective {A₂ : Matrix (Fin 2) (Fin q) ℝ}
    (hinj : Function.Injective A₂.vecMul) {w : Fin 2 → ℝ} (hw : w ≠ 0) : w ᵥ* A₂ ≠ 0 := by
  intro hcontra
  apply hw
  apply hinj
  show w ᵥ* A₂ = (0 : Fin 2 → ℝ) ᵥ* A₂
  rw [hcontra, Matrix.zero_vecMul]

/-- **Full row rank + nonzero test directions ⟹ the corner units are strictly positive.** With `A₂`
full row rank (`Function.Injective A₂.vecMul`) and `w₁, v̄` nonzero and `a_piv ≠ 0`, both
`cornerUnit0` and `cornerUnit1` are `> 0`. This is the concrete SUFFICIENT condition behind the corner
endpoint's abstract `a ≤ U_k` hypothesis. One-directional: the converse fails (a rank-deficient `A₂`
not annihilating the test vectors also gives positive units). -/
theorem cornerUnits_pos {A₂ : Matrix (Fin 2) (Fin q) ℝ} (hinj : Function.Injective A₂.vecMul)
    {w₁ w₂ vbar : Fin 2 → ℝ} {δ apiv : ℝ} (hw1 : w₁ ≠ 0) (hvbar : vbar ≠ 0) (hapiv : apiv ≠ 0) :
    0 < cornerUnit0 A₂ w₁ w₂ δ ∧ 0 < cornerUnit1 A₂ vbar apiv := by
  refine ⟨?_, ?_⟩
  · have hpos := sum_sq_pos_of_ne_zero (vecMul_ne_zero_of_injective hinj hw1)
    have hnn : 0 ≤ δ ^ 2 * (∑ j, (w₂ ᵥ* A₂) j ^ 2) :=
      mul_nonneg (sq_nonneg _) (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    unfold cornerUnit0; linarith
  · have hpos := sum_sq_pos_of_ne_zero (vecMul_ne_zero_of_injective hinj hvbar)
    have hapiv2 : 0 < apiv ^ 2 := lt_of_le_of_ne (sq_nonneg apiv) (Ne.symm (pow_ne_zero 2 hapiv))
    unfold cornerUnit1
    exact mul_pos hapiv2 hpos

/-! ## 3. The decorated corner-slice integral: finiteness on the sector, divergence off it -/

/-- **The `(3,3,3,4)` `t=1` decorated corner-slice integral** at deep data `A₂`. The additive
two-block corner loss `u₀²·U₀ + u₁²·U₁` (built by the indicator `prependColumn`, §1) raised to
`−c'`, times the accumulated radial Jacobian `|u₀|³·|u₁|²` (block dims `4,3` at the binding corank-2
cut `t=1`; Jacobian powers `p_k−1 = 3, 2`), integrated over the radial unit box. The units are the
concrete deep-data units `cornerUnit0/1 A₂`, constant in the radial variables — the FIXED vertical
slice (angular/deep data fixed); the general recursion integrates over that data (Tonelli), the
follow-on. -/
noncomputable def cornerSlice334Integral (A₂ : Matrix (Fin 2) (Fin q) ℝ)
    (w₁ w₂ vbar : Fin 2 → ℝ) (δ apiv : ℝ) (c' : NNReal) : ℝ≥0∞ :=
  ∫⁻ u in unitBox 2,
    ENNReal.ofReal ((u 0 ^ 2 * cornerUnit0 A₂ w₁ w₂ δ + u 1 ^ 2 * cornerUnit1 A₂ vbar apiv)
      ^ (-(c' : ℝ)) * (|u 0| ^ 3 * |u 1| ^ 2))

/-- **The corner-slice is finite below `7/2` when the units are positive.** Given `U₀,U₁ > 0`
(the sector), the decorated corner-slice integral is `< ⊤` for every `c' < 7/2`. The units are
constants in the radial variables, so the corner endpoint applies with the constant lower bound
`a = min(U₀,U₁) > 0`. This is the weighted-AM-GM min-cut / codimensions-ADD branch (`4+3 → 7/2`),
NOT the scalar-split min (`→ 3/2`). -/
theorem cornerSlice334_lt_top_of_units_pos (A₂ : Matrix (Fin 2) (Fin q) ℝ)
    (w₁ w₂ vbar : Fin 2 → ℝ) (δ apiv : ℝ) (c' : NNReal) (hc' : (c' : ℝ) < 7 / 2)
    (hU0 : 0 < cornerUnit0 A₂ w₁ w₂ δ) (hU1 : 0 < cornerUnit1 A₂ vbar apiv) :
    cornerSlice334Integral A₂ w₁ w₂ vbar δ apiv c' < ⊤ := by
  set U0 := cornerUnit0 A₂ w₁ w₂ δ with hU0def
  set U1 := cornerUnit1 A₂ vbar apiv with hU1def
  set a := min U0 U1 with hadef
  have ha : 0 < a := lt_min hU0 hU1
  unfold cornerSlice334Integral
  exact sjSlice334_corner_lintegral_lt_top c' hc' (fun _ => U0) (fun _ => U1) a ha
    (fun _ _ => min_le_left _ _) (fun _ _ => min_le_right _ _)

/-- **The SECTOR slice (`A₂` full row rank): finite at `7/2`, unconditionally.** On the generic-minor
sector `{A₂ : full row rank}` — `Function.Injective A₂.vecMul`, with the test directions `w₁, v̄`
nonzero and `a_piv ≠ 0` — the units are positive (`cornerUnits_pos`), so the decorated corner-slice
integral is `< ⊤` for every `c' < 7/2 = ½·minAdm(3,3,3,4)`. This is the good branch, closed by the
banked additive-corner endpoint; no external hypothesis. -/
theorem sjCorner334_sector_slice_lt_top {A₂ : Matrix (Fin 2) (Fin q) ℝ}
    (hinj : Function.Injective A₂.vecMul) {w₁ w₂ vbar : Fin 2 → ℝ} {δ apiv : ℝ}
    (hw1 : w₁ ≠ 0) (hvbar : vbar ≠ 0) (hapiv : apiv ≠ 0)
    (c' : NNReal) (hc' : (c' : ℝ) < 7 / 2) :
    cornerSlice334Integral A₂ w₁ w₂ vbar δ apiv c' < ⊤ := by
  obtain ⟨hU0, hU1⟩ := cornerUnits_pos hinj hw1 hvbar hapiv
  exact cornerSlice334_lt_top_of_units_pos A₂ w₁ w₂ vbar δ apiv c' hc' hU0 hU1

/-- **The `monomialIntegrand` shape of the slice loss when `U₁` vanishes.** When `U₁ = 0`, the loss
is `u₀²·U₀`, so the integrand equals `U₀^{−c'}·monomialIntegrand 2 ![1,0] ![3,2] c'` — a constant
times a monomial with Jacobian exponents `(3,2)` and loss exponents `2·(1,0)`. -/
private theorem monomialIntegrand_334_axis0 (c' : ℝ) (u : Fin 2 → ℝ) :
    monomialIntegrand 2 ![1, 0] ![3, 2] c' u = |u 0| ^ 3 * |u 1| ^ 2 * (|u 0| ^ 2) ^ (-c') := by
  unfold monomialIntegrand
  rw [Fin.prod_univ_two, Fin.prod_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  norm_num

/-- **The `monomialIntegrand` shape of the slice loss when `U₀` vanishes.** Symmetric to
`monomialIntegrand_334_axis0`, binding axis `1`. -/
private theorem monomialIntegrand_334_axis1 (c' : ℝ) (u : Fin 2 → ℝ) :
    monomialIntegrand 2 ![0, 1] ![3, 2] c' u = |u 0| ^ 3 * |u 1| ^ 2 * (|u 1| ^ 2) ^ (-c') := by
  unfold monomialIntegrand
  rw [Fin.prod_univ_two, Fin.prod_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  norm_num

/-- **A nonneg constant times the `(3,3,3,4)` monomial with a binding axis diverges on the box.** For
`0 < K` and a binding axis `j₀` whose one-variable exponent is `≤ −1`, the constant-times-monomial
slice integral over the unit box is `⊤`. Reduces to `monomialIntegrand_lintegral_box_eq_top_of_axis`
(the banked S2-free box divergence). -/
private theorem const_mul_monomial_334_eq_top (K : ℝ) (hK : 0 < K) (k h : Fin 2 → ℕ) (c' : ℝ)
    (j₀ : Fin 2) (hexp : (h j₀ : ℝ) - 2 * (k j₀ : ℝ) * c' ≤ -1) :
    ∫⁻ u in unitBox 2,
        ENNReal.ofReal (K ^ (-c') * monomialIntegrand 2 k h c' u) = ⊤ := by
  have hbox : ∫⁻ u in unitBox 2, ENNReal.ofReal (monomialIntegrand 2 k h c' u) = ⊤ := by
    have hax := monomialIntegrand_lintegral_box_eq_top_of_axis 2 k h c' j₀ hexp (ε := 1) one_pos
    rw [show unitBox 2 = Set.univ.pi (fun _ : Fin 2 => Set.Icc (0 : ℝ) 1) from rfl, ← hax]
    refine setLIntegral_congr_fun (MeasurableSet.univ_pi (fun _ => measurableSet_Icc))
      (fun u _ => ?_)
    rw [abs_of_nonneg (monomialIntegrand_nonneg' 2 k h c' u)]
  have hKrp : 0 < K ^ (-c') := Real.rpow_pos_of_pos hK _
  calc ∫⁻ u in unitBox 2, ENNReal.ofReal (K ^ (-c') * monomialIntegrand 2 k h c' u)
      = ∫⁻ u in unitBox 2,
          ENNReal.ofReal (K ^ (-c')) * ENNReal.ofReal (monomialIntegrand 2 k h c' u) := by
        refine setLIntegral_congr_fun (MeasurableSet.univ_pi (fun _ => measurableSet_Icc))
          (fun u _ => ?_)
        rw [ENNReal.ofReal_mul hKrp.le]
    _ = ENNReal.ofReal (K ^ (-c')) * ∫⁻ u in unitBox 2,
          ENNReal.ofReal (monomialIntegrand 2 k h c' u) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ⊤ := by rw [hbox, ENNReal.mul_top (ENNReal.ofReal_pos.mpr hKrp).ne']

/-- **Divergence direction — a vanishing `U₁` forces `⊤` (mapping the boundary).** If `U₁ = 0 < U₀`
and `c' ≥ 2`, the decorated corner-slice integral is `⊤`. The loss becomes the single-axis
`u₀²·U₀`, whose `u₀`-marginal `∫₀¹ u₀^{3−2c'}` diverges for `c' ≥ 2` (banked
`abs_rpow_lintegral_Ioo_eq_top`, lifted through `monomialIntegrand_lintegral_box_eq_top_of_axis`). So
the units-positive hypothesis of `sjCorner334_sector_slice_lt_top` is NECESSARY, not merely sufficient:
a rank-drop of `A₂` that annihilates `v̄` (`U₁ = 0`) genuinely diverges below `7/2`. -/
theorem cornerSlice334_eq_top_of_unit1_zero {A₂ : Matrix (Fin 2) (Fin q) ℝ}
    (w₁ w₂ vbar : Fin 2 → ℝ) (δ apiv : ℝ) (c' : NNReal)
    (hU0 : 0 < cornerUnit0 A₂ w₁ w₂ δ) (hU1 : cornerUnit1 A₂ vbar apiv = 0)
    (hc' : (2 : ℝ) ≤ (c' : ℝ)) :
    cornerSlice334Integral A₂ w₁ w₂ vbar δ apiv c' = ⊤ := by
  have hpt : ∀ u : Fin 2 → ℝ,
      ENNReal.ofReal ((u 0 ^ 2 * cornerUnit0 A₂ w₁ w₂ δ + u 1 ^ 2 * cornerUnit1 A₂ vbar apiv)
          ^ (-(c' : ℝ)) * (|u 0| ^ 3 * |u 1| ^ 2))
        = ENNReal.ofReal (cornerUnit0 A₂ w₁ w₂ δ ^ (-(c' : ℝ))
            * monomialIntegrand 2 ![1, 0] ![3, 2] (c' : ℝ) u) := by
    intro u
    rw [hU1, mul_zero, add_zero, monomialIntegrand_334_axis0]
    congr 1
    rw [show u 0 ^ 2 = |u 0| ^ 2 from (sq_abs _).symm, Real.mul_rpow (by positivity) hU0.le]
    ring
  unfold cornerSlice334Integral
  exact (setLIntegral_congr_fun (MeasurableSet.univ_pi (fun _ => measurableSet_Icc))
      (fun u _ => hpt u)).trans
    (const_mul_monomial_334_eq_top (cornerUnit0 A₂ w₁ w₂ δ) hU0 ![1, 0] ![3, 2] (c' : ℝ) 0
      (by norm_num; linarith))

/-- **Divergence direction — a vanishing `U₀` forces `⊤`.** Symmetric to
`cornerSlice334_eq_top_of_unit1_zero`: if `U₀ = 0 < U₁` and `c' ≥ 3/2`, the slice integral is `⊤`
(binding axis `1`, `u₁`-marginal `∫₀¹ u₁^{2−2c'}` diverges for `c' ≥ 3/2`). -/
theorem cornerSlice334_eq_top_of_unit0_zero {A₂ : Matrix (Fin 2) (Fin q) ℝ}
    (w₁ w₂ vbar : Fin 2 → ℝ) (δ apiv : ℝ) (c' : NNReal)
    (hU0 : cornerUnit0 A₂ w₁ w₂ δ = 0) (hU1 : 0 < cornerUnit1 A₂ vbar apiv)
    (hc' : (3 : ℝ) / 2 ≤ (c' : ℝ)) :
    cornerSlice334Integral A₂ w₁ w₂ vbar δ apiv c' = ⊤ := by
  have hpt : ∀ u : Fin 2 → ℝ,
      ENNReal.ofReal ((u 0 ^ 2 * cornerUnit0 A₂ w₁ w₂ δ + u 1 ^ 2 * cornerUnit1 A₂ vbar apiv)
          ^ (-(c' : ℝ)) * (|u 0| ^ 3 * |u 1| ^ 2))
        = ENNReal.ofReal (cornerUnit1 A₂ vbar apiv ^ (-(c' : ℝ))
            * monomialIntegrand 2 ![0, 1] ![3, 2] (c' : ℝ) u) := by
    intro u
    rw [hU0, mul_zero, zero_add, monomialIntegrand_334_axis1]
    congr 1
    rw [show u 1 ^ 2 = |u 1| ^ 2 from (sq_abs _).symm, Real.mul_rpow (by positivity) hU1.le]
    ring
  unfold cornerSlice334Integral
  exact (setLIntegral_congr_fun (MeasurableSet.univ_pi (fun _ => measurableSet_Icc))
      (fun u _ => hpt u)).trans
    (const_mul_monomial_334_eq_top (cornerUnit1 A₂ vbar apiv) hU1 ![0, 1] ![3, 2] (c' : ℝ) 1
      (by norm_num; linarith))

/-! ## 4. Tie to the charge and non-vacuity -/

/-- **The threshold `7/2` IS `½·minAdm(3,3,3,4)`.** Re-exposes the banked charge computation so the
corner-slice theorems can be read at the honest "branch threshold = ½·minAdm" precision. -/
theorem sjCorner334_threshold_eq_half_minAdm :
    (7 : ℝ) / 2 = (minAdm (![3, 3, 3, 4] : Fin 4 → ℕ) : ℝ) / 2 := by
  rw [sjSlice334_minAdm_eq]; norm_num

/-- **Non-vacuity witness (sector).** At `q = 2`, `A₂ = 1` (the `2×2` identity, full row rank), test
directions `w₁ = v̄ = ![1,1]`, `a_piv = 1`, the sector hypotheses are jointly satisfiable and the
corner-slice is finite below `7/2` — the sector finiteness is not vacuously true. -/
example (c' : NNReal) (hc' : (c' : ℝ) < 7 / 2) :
    cornerSlice334Integral (1 : Matrix (Fin 2) (Fin 2) ℝ) ![1, 1] ![1, 1] ![1, 1] 1 1 c' < ⊤ := by
  have hinj : Function.Injective (1 : Matrix (Fin 2) (Fin 2) ℝ).vecMul := by
    intro x y hxy; simpa using hxy
  have hne : (![1, 1] : Fin 2 → ℝ) ≠ 0 := by
    intro h; have := congrFun h 0; simp at this
  exact sjCorner334_sector_slice_lt_top hinj hne hne one_ne_zero c' hc'

/-- **Non-vacuity witness (divergence).** At `q = 2`, the rank-1 `A₂ = diagonal ![1,0]` (`¬ injective`)
with `w₁ = w₂ = ![1,0]` (so `w₁ᵥ*A₂ = ![1,0] ≠ 0`, `U₀ = 2 > 0`) and `v̄ = ![0,1]` (so `v̄ᵥ*A₂ = 0`,
`U₁ = 0`): the slice integral is `⊤` for `c' ≥ 2` — the reviewer's boundary witness, confirming the
divergence direction is not vacuous. -/
example (c' : NNReal) (hc' : (2 : ℝ) ≤ (c' : ℝ)) :
    cornerSlice334Integral (Matrix.diagonal ![1, 0] : Matrix (Fin 2) (Fin 2) ℝ)
      ![1, 0] ![1, 0] ![0, 1] 1 1 c' = ⊤ := by
  refine cornerSlice334_eq_top_of_unit1_zero _ _ _ _ _ _ ?_ ?_ hc'
  · unfold cornerUnit0
    simp only [Matrix.vecMul_diagonal, Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    norm_num
  · unfold cornerUnit1
    simp only [Matrix.vecMul_diagonal, Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    norm_num

end DLNFibre.DLN.RLCT
