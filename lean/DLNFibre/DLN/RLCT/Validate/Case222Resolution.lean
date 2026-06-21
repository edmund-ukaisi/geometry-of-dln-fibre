import DLNFibre.DLN.RLCT.Validate.Case222Cover
import DLNFibre.DLN.RLCT.Validate.Case222Lemma2
import DLNFibre.DLN.RLCT.Foundations.S1G5Charts

/-!
# `DLNFibre.DLN.RLCT.Validate.Case222Resolution` — the `(2,2,2)` concrete resolution cover

The top-level `(2,2,2)` assembly: the explicit loss `myF222 = ‖A·B‖²` in flat coordinates
(`a00=x0..b11=x7`), its resolution chart tree, and the RLCT value
`rlctAtOn myF222 0 = ⨅ᵢ monomialThreshold (dᵢ)(kᵢ)(hᵢ)` (the cover-form; `fm`'s `⨅ = 3/2` wraps it).

The architecture (Codex 2026-06-21, asymmetric): everything at the lintegral level (the blow-up nodes
are NOT homeomorphisms — only `lemma2Hom` is, entering as a single-chart change-of-variables inside an
integral, never an `rlctAtOn` transport). The `≤` direction needs only ONE binding leaf chart
(`rlctAtOn_le_of_box_diverges` + `monomialIntegrand_lintegral_box_eq_top`); the `≥` direction needs
the full `Σ_24` cover (all leaves finite below `⨅` ⟹ `U`-integral finite, `cover_integral_lt_top_iff`).

The chart tree (`r1-222-cover-handoff-split.md`): step-1 (A-pivot blow-up, `|det| = x³`) → Lemma-2
(`lemma2Hom`, regular change, `|det| = 1`) → step-2 (`{E,F0,δ}`-pivot blow-up, `|det| = s²`) →
[`δ`-branch: step-3 (4-block blow-up, `|det| = u³`)]. 8 unit leaves + 16 block leaves = 24.

This file is built incrementally (each node factorization a committable sub-lemma). Currently:
`myF222` + the step-1 A-pivot factorization (`myF222 ∘ φ₁ = x² · Q`).
-/

open MeasureTheory
open scoped BigOperators ENNReal
namespace DLNFibre.DLN.RLCT

/-- The explicit `(2,2,2)` loss in flat coordinates `(a00,a01,a10,a11,b00,b01,b10,b11) = (x0,…,x7)`:
`myF222 = ‖A·B‖²` for `A = [[x0,x1],[x2,x3]]`, `B = [[x4,x5],[x6,x7]]`. The function whose RLCT the
cover computes; the seam (`rlctAtOn_dlnLoss222_transport`) identifies `dlnLoss H222 0 = myF222 ∘ e222`.
-/
noncomputable def myF222 (x : Fin 8 → ℝ) : ℝ :=
  (x 0 * x 4 + x 1 * x 6) ^ 2 + (x 0 * x 5 + x 1 * x 7) ^ 2
    + (x 2 * x 4 + x 3 * x 6) ^ 2 + (x 2 * x 5 + x 3 * x 7) ^ 2

/-- **Step-1 A-pivot chart** `φ₁` (pivot `a00 = y0`): `a00 = y0`, `a01 = y0·y1`, `a10 = y0·y2`,
`a11 = y0·y3`; `B` (slots `4..7`) passes through. The blow-up of the `A`-block along the `a00`
direction (Jacobian `y0³`). -/
noncomputable def step1A (y : Fin 8 → ℝ) : Fin 8 → ℝ :=
  ![y 0, y 0 * y 1, y 0 * y 2, y 0 * y 3, y 4, y 5, y 6, y 7]

/-- **Step-1 factorization.** Pulling `myF222` back through the A-pivot chart factors out the pivot
square: `myF222 (φ₁ y) = y0² · Q(y)`, where `Q = ‖Â·B‖²` (`Â = [[1,y1],[y2,y3]]`) is the residual the
Lemma-2 node resolves. The `y0`-exceptional divisor (`k = 1`, `h = 3` after the `³`-Jacobian; axis
ratio `2`). Pure algebra (`ring` after the chart substitution). -/
theorem myF222_step1A (y : Fin 8 → ℝ) :
    myF222 (step1A y)
      = (y 0) ^ 2 * ((y 4 + y 1 * y 6) ^ 2 + (y 5 + y 1 * y 7) ^ 2
          + (y 2 * y 4 + y 3 * y 6) ^ 2 + (y 2 * y 5 + y 3 * y 7) ^ 2) := by
  unfold myF222 step1A
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val,
    Fin.isValue]
  ring

/-- The step-1 residual `Q = ‖Â·B‖²` on the seven non-pivot coordinates `(t1,t2,t3,b00,b01,b10,b11) =
(v0..v6)`: `(b00+t1·b10)² + (b01+t1·b11)² + (t2·b00+t3·b10)² + (t2·b01+t3·b11)²`. The factor the
Lemma-2 node resolves (the `Q` bracket in `myF222_step1A`, reindexed `y1..y7 ↦ v0..v6`). -/
noncomputable def step1Residual (v : Fin 7 → ℝ) : ℝ :=
  (v 3 + v 0 * v 5) ^ 2 + (v 4 + v 0 * v 6) ^ 2
    + (v 1 * v 3 + v 2 * v 5) ^ 2 + (v 1 * v 4 + v 2 * v 6) ^ 2

/-- The resolved quadratic on the Lemma-2 output coordinates `(t1,E,F0,δ,q,G,H)` (slots `0..6`):
`E² + F0² + (q·E + δ·G)² + (q·F0 + δ·H)²` — the normal form whose vertex `{E=F0=δ=0}` step-2 blows
up. -/
noncomputable def resolvedForm (w : Fin 7 → ℝ) : ℝ :=
  (w 1) ^ 2 + (w 2) ^ 2 + (w 4 * w 1 + w 3 * w 5) ^ 2 + (w 4 * w 2 + w 3 * w 6) ^ 2

/-- **Lemma-2 resolution (the regular-change identity).** The step-1 residual `Q` equals the resolved
form read in the Lemma-2 coordinates: `step1Residual v = resolvedForm (lemma2Fwd v)`. This is the
det-(`−1`) regular change of variables (sympy-verified, `r1_222_lemma2_explicit.py`); pure algebra
(`ring`). Since `lemma2Hom` is a measure-preserving homeomorphism (`measurePreserving_lemma2Hom`), the
residual integral transports across it — the splice between step-1 and step-2 (at the lintegral level,
NOT an `rlctAtOn` transport). -/
theorem step1Residual_eq_resolvedForm (v : Fin 7 → ℝ) :
    step1Residual v = resolvedForm (lemma2Fwd v) := by
  unfold step1Residual resolvedForm lemma2Fwd
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Fin.isValue]
  ring

/-- **Step-2 E-pivot chart** `φ₂` (pivot `E = z1`): `E = z1`, `F0 = z1·z2`, `δ = z1·z3`; `q, G, H`
(slots `0,4,5,6`) pass through. The blow-up of the resolved form's vertex `{E=F0=δ=0}` along the `E`
direction (Jacobian `z1²`). The `E`/`F0`-pivot branches give UNIT leaves; the `δ`-pivot branch needs
step-3. -/
noncomputable def step2E (z : Fin 7 → ℝ) : Fin 7 → ℝ :=
  ![z 0, z 1, z 1 * z 2, z 1 * z 3, z 4, z 5, z 6]

/-- **Step-2 E-pivot factorization (the UNIT leaf).** Pulling the resolved form through the E-pivot
chart factors out the pivot square against a **unit**: `resolvedForm (φ₂ z) = z1² · U`, where
`U = 1 + z2² + (q + δ̂·G)² + (q·v + δ̂·H)²` (here `z2 = F0/E`, `z3 = δ/E`, `z4 = q`, …) satisfies
`U ≥ 1 > 0` everywhere (a sum of `1` and squares) — so the leaf integrand is `monomial · unit` with
`|unit|` bounded below by `1`, feeding `integrableOn_monomial_mul_unit_iff` (the `0 < a` hypothesis,
`a = 1`). The `z1`-exceptional divisor (`k = 1`, `h = 2` after the `²`-Jacobian; axis ratio `3/2` —
the binding divisor). Pure algebra (`ring`). -/
theorem resolvedForm_step2E (z : Fin 7 → ℝ) :
    resolvedForm (step2E z)
      = (z 1) ^ 2 * (1 + (z 2) ^ 2 + (z 4 + z 3 * z 5) ^ 2 + (z 4 * z 2 + z 3 * z 6) ^ 2) := by
  unfold resolvedForm step2E
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Fin.isValue]
  ring

/-- The step-2 E-pivot residual `U = 1 + z2² + (q+δ̂G)² + (qv+δ̂H)²` is `≥ 1`, hence bounded below by a
positive constant (`a = 1`) — the unit-leaf nonvanishing input to `integrableOn_monomial_mul_unit_iff`.
-/
theorem step2E_unit_ge_one (z : Fin 7 → ℝ) :
    (1 : ℝ) ≤ 1 + (z 2) ^ 2 + (z 4 + z 3 * z 5) ^ 2 + (z 4 * z 2 + z 3 * z 6) ^ 2 := by
  nlinarith [sq_nonneg (z 2), sq_nonneg (z 4 + z 3 * z 5), sq_nonneg (z 4 * z 2 + z 3 * z 6)]

/-- **Step-2 δ-pivot chart** `φ₂'` (pivot `δ = z1`): `δ = z1`, `E = z1·z2`, `F0 = z1·z3`; `q, G, H`
pass through. The blow-up of the resolved vertex along the `δ` direction — the branch whose residual
`block` VANISHES at the centre (`= G² + H²`), so it is NOT a unit and needs step-3 (the BLOCK leaves).
-/
noncomputable def step2D (z : Fin 7 → ℝ) : Fin 7 → ℝ :=
  ![z 0, z 1 * z 2, z 1 * z 3, z 1, z 4, z 5, z 6]

/-- **Step-2 δ-pivot factorization (the BLOCK branch).** `resolvedForm (φ₂' z) = z1² · block`, where
`block = E'² + F0'² + (q·E' + G)² + (q·F0' + H)²` (`E' = z2 = E/δ`, `F0' = z3 = F0/δ`) is a
4-variable sum of squares vanishing at the centre — so step-3 must blow it up further. Pure algebra. -/
theorem resolvedForm_step2D (z : Fin 7 → ℝ) :
    resolvedForm (step2D z)
      = (z 1) ^ 2 * ((z 2) ^ 2 + (z 3) ^ 2 + (z 4 * z 2 + z 5) ^ 2 + (z 4 * z 3 + z 6) ^ 2) := by
  unfold resolvedForm step2D
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Fin.isValue]
  ring

/-- The step-2 δ-branch block `block(q, v, w, G, H) = v² + w² + (q·v + G)² + (q·w + H)²` (on the four
`v = E', w = F0', G, H` plus spectator `q`). The input to step-3. -/
noncomputable def blockForm (q v w G H : ℝ) : ℝ :=
  v ^ 2 + w ^ 2 + (q * v + G) ^ 2 + (q * w + H) ^ 2

/-- **Step-3 block factorization (the BLOCK leaf).** Blowing up the block vertex along the `v = u`
direction (`v = u`, `w = u·a1`, `G = u·a2`, `H = u·a3`; `q` spectator) factors out `u²` against a
**unit**: `blockForm q u (u·a1) (u·a2) (u·a3) = u² · res`, with
`res = (q·a1 + a3)² + (q + a2)² + a1² + 1 ≥ 1 > 0` (`step3_unit_ge_one`). The `u`-exceptional divisor
(`k = 1`, `h = 3` after the `³`-Jacobian; axis ratio `2`). Pure algebra. -/
theorem blockForm_step3 (q u a1 a2 a3 : ℝ) :
    blockForm q u (u * a1) (u * a2) (u * a3)
      = u ^ 2 * ((q * a1 + a3) ^ 2 + (q + a2) ^ 2 + a1 ^ 2 + 1) := by
  unfold blockForm; ring

/-- The step-3 block residual `res = (q·a1+a3)² + (q+a2)² + a1² + 1 ≥ 1` — the block-leaf nonvanishing
input (`0 < a`, `a = 1`) to `integrableOn_monomial_mul_unit_iff`. -/
theorem step3_unit_ge_one (q a1 a2 a3 : ℝ) :
    (1 : ℝ) ≤ (q * a1 + a3) ^ 2 + (q + a2) ^ 2 + a1 ^ 2 + 1 := by
  nlinarith [sq_nonneg (q * a1 + a3), sq_nonneg (q + a2), sq_nonneg a1]

/-! ## The composite unit-leaf chart (the `≤`-direction single binding leaf)

The `≤` direction (`rlctAtOn_le_of_box_diverges`) needs ONE binding leaf chart `φ` whose pulled-back
integrand diverges. The unit-leaf composite (Codex 2026-06-21): `φ = step1A ∘ (Lemma-2, y0 spectator)
∘ step2E`, parametrised `φ u = step1A (cons u0 (lemma2Inv (step2E (tail u))))` — `lemma2Inv` because
`step1Residual = resolvedForm ∘ lemma2Fwd`, so `lemma2Fwd v = step2E z` ⟹ `v = lemma2Inv (step2E z)`.
Chaining the three factorizations: `myF222 (φ u) = u0² · z1² · U` (`z1 = (tail u) 1`, `U ≥ 1`). With
the iterated Jacobians (`y0³ · 1 · z1²`) the leaf integrand is `monomialIntegrand`-shaped on the two
exceptional axes `(u0, z1)` (`k = 1, h = (3,2)`) times the unit `U^{−c}`. -/

/-- `myF222 ∘ step1A` via `step1Residual` of the tail (the bracket in `myF222_step1A` is exactly
`step1Residual (Fin.tail y)`, the `y1..y7` reindex `v0..v6`). -/
theorem myF222_step1A' (y : Fin 8 → ℝ) :
    myF222 (step1A y) = (y 0) ^ 2 * step1Residual (Fin.tail y) := by
  rw [myF222_step1A]; congr 1

/-- **`step1A` is a pivot blow-up.** `step1A = pivotBlowupOn {0,1,2,3} 0` (the `A`-block blow-up with
pivot `a00`). Lets the step-1 chart reuse the gated `pivotBlowupOn` infrastructure — derivative
(`pivotBlowupOn_hasFDerivWithinAt`), determinant (`pivotBlowupOnDeriv_det`, `= (x 0)^{card−1} =
x0³`), injectivity (`pivotBlowupOn_injOn`), image (`pivotBlowupOn_image`) — in the change-of-variables
for the `≤`-direction, instead of a hand-derived composite Jacobian. -/
theorem step1A_eq_pivotBlowupOn (y : Fin 8 → ℝ) :
    step1A y = pivotBlowupOn ({0, 1, 2, 3} : Finset (Fin 8)) 0 y := by
  funext i
  unfold step1A pivotBlowupOn
  fin_cases i <;> simp [Matrix.cons_val]

/-- The composite unit-leaf chart `φ` (step-1 A-pivot ∘ Lemma-2⁻¹ ∘ step-2 E-pivot), parametrised on
`u : Fin 8 → ℝ` (`u0` the step-1 pivot, `tail u` the step-2 chart coordinates). -/
noncomputable def phiUnit (u : Fin 8 → ℝ) : Fin 8 → ℝ :=
  step1A (Fin.cons (u 0) (lemma2Inv (step2E (Fin.tail u))))

/-- **Composite unit-leaf factorization.** `myF222 (φ u) = u0² · resolvedForm (step2E (tail u))` —
chaining `myF222_step1A'` (step-1), `step1Residual_eq_resolvedForm` + `lemma2Fwd_lemma2Inv` (the
Lemma-2 splice cancels), leaving the step-2-ready resolved form. With `resolvedForm_step2E` this is
`u0² · ((tail u) 1)² · U`, the monomial-times-unit the box-divergence atom consumes. -/
theorem myF222_phiUnit (u : Fin 8 → ℝ) :
    myF222 (phiUnit u) = (u 0) ^ 2 * resolvedForm (step2E (Fin.tail u)) := by
  unfold phiUnit
  rw [myF222_step1A', Fin.cons_zero, Fin.tail_cons,
    step1Residual_eq_resolvedForm, lemma2Fwd_lemma2Inv]

/-- **Composite unit-leaf, monomial-times-unit form.** `myF222 (φ u) = u0² · z1² · U`, where
`z1 = (tail u) 1` and `U = 1 + z2² + (q+δ̂G)² + (qv+δ̂H)² ≥ 1` (`step2E_unit_ge_one`). The two
exceptional axes `(u0, z1)` carry the binding behaviour (`k = 1`, loss exponents `2, 2`); after the
Jacobian `u0³·z1²` (`h = 3, 2`) the integrand is `monomialIntegrand 2 ![1,1] ![3,2] · U^{−c}`. -/
theorem myF222_phiUnit_monomial (u : Fin 8 → ℝ) :
    myF222 (phiUnit u)
      = (u 0) ^ 2 * ((Fin.tail u) 1) ^ 2
          * (1 + ((Fin.tail u) 2) ^ 2 + ((Fin.tail u) 4 + (Fin.tail u) 3 * (Fin.tail u) 5) ^ 2
              + ((Fin.tail u) 4 * (Fin.tail u) 2 + (Fin.tail u) 3 * (Fin.tail u) 6) ^ 2) := by
  rw [myF222_phiUnit, resolvedForm_step2E]; ring

/-! ## The `d = 8` binding-monomial threshold (the `≤`-direction divergence input)

The post-c-o-v leaf integrand on `Fin 8 → ℝ` is `monomialIntegrand 8 unitK8 unitH8 c' · U^{−c'}` — the
Jacobian `|u0|³·|z1|²` (`= ∏ |uⱼ|^{unitH8 j}`, `unitH8 = (3,0,2,0,…)`) against the loss base
`(|u0|²·|z1|²)^{−c'}` (`= (∏|uⱼ|^{2·unitK8 j})^{−c'}`, `unitK8 = (1,0,1,0,…)`). For the
box-divergence atom (`monomialIntegrand_lintegral_box_eq_top`) the hypothesis is
`monomialThreshold ≤ ofReal c'`; here it suffices that the threshold is `≤ 3/2` (the binding `z1`-axis
`(k,h) = (1,2) = (1, 3−1)`), since `c' > 3/2`. The spectator axes have `k = 0` (so the multiplicity
lower-bound lemma does NOT apply — but it is not needed; only the single binding axis bounds the
threshold above). -/

/-- The `(2,2,2)` unit-leaf binding-monomial exponents on `Fin 8` (the loss base `∏|uⱼ|^{2kⱼ}`): `k =
1` on the two exceptional axes `u0` (step-1 pivot) and `u2` (`= z1`, step-2 pivot), `0` on the six
spectators. -/
def unitK8 : Fin 8 → ℕ := ![1, 0, 1, 0, 0, 0, 0, 0]

/-- The `(2,2,2)` unit-leaf binding-monomial Jacobian exponents on `Fin 8` (`∏|uⱼ|^{hⱼ}`): `h = 3` on
`u0` (`|det| = u0³`), `h = 2` on `u2 = z1` (`|det| = z1²`), `0` on the six spectators. -/
def unitH8 : Fin 8 → ℕ := ![3, 0, 2, 0, 0, 0, 0, 0]

/-- **The unit-leaf monomial threshold is `≤ 3/2`** (the binding `z1`-axis `(k,h) = (1,2) = (1, 3−1)`
realises `3/2` via `monomialThreshold_le_regularSeq`). The `≤`-direction input: for `c' > 3/2`, the
`d = 8` monomial diverges (`monomialThreshold ≤ 3/2 < c'`). The spectator `k = 0` axes don't obstruct
the upper bound (one binding axis suffices). -/
theorem unitMonomialThreshold_le : monomialThreshold 8 unitK8 unitH8 ≤ 3 / 2 := by
  have := monomialThreshold_le_regularSeq 8 unitK8 unitH8 3 (by norm_num) 2 (by rfl) (by rfl)
  rwa [show ((3 : ℕ) : ℝ≥0∞) / 2 = 3 / 2 by norm_num] at this

/-- The binding axis `u2 = z1` has `unitK8 2 = 1 ≠ 0` — the singular-axis witness for
`monomialIntegrand_lintegral_box_eq_top` / `exists_binding_axis`. -/
theorem unitK8_binding : unitK8 2 ≠ 0 := by decide

/-! ## The step-1 change-of-variables (reusing the gated `pivotBlowupOn` infrastructure)

`step1A = pivotBlowupOn {0,1,2,3} 0` (`step1A_eq_pivotBlowupOn`), so the change-of-variables
(`lintegral_image_eq_lintegral_abs_det_fderiv_mul`) plugs the gated infra directly: the derivative
(`pivotBlowupOn_hasFDerivWithinAt`), injectivity off the pivot-zero locus (`pivotBlowupOn_injOn`),
and the determinant (`pivotBlowupOnDeriv_det`, `= (x 0)^{card−1} = (x 0)³`). The first node of the
`≤`-direction lower bound. -/

/-- **Step-1 change-of-variables.** For a measurable `V` (off the pivot-zero locus `{x0 = 0}`),
`∫⁻_{step1A '' (V \ {x0=0})} g = ∫⁻_{V \ {x0=0}} |det Dφ₁| · (g ∘ step1A)` — the
`lintegral_image_eq_lintegral_abs_det_fderiv_mul` applied to `step1A = pivotBlowupOn {0,1,2,3} 0`,
discharging the derivative / injectivity from the gated `pivotBlowupOn` infrastructure. -/
theorem step1A_lintegral_image (V : Set (Fin 8 → ℝ)) (hV : MeasurableSet V)
    (g : (Fin 8 → ℝ) → ℝ≥0∞) :
    ∫⁻ x in step1A '' (V \ {x | x 0 = 0}), g x
      = ∫⁻ x in V \ {x | x 0 = 0},
          ENNReal.ofReal |(pivotBlowupOnDeriv ({0, 1, 2, 3} : Finset (Fin 8)) 0 x).det|
            * g (step1A x) := by
  simp_rw [step1A_eq_pivotBlowupOn]
  rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume
    (hV.diff (measurableSet_eq_fun (measurable_pi_apply 0) measurable_const))
    (fun x _ => pivotBlowupOn_hasFDerivWithinAt _ _ _ x) (pivotBlowupOn_injOn _ _ _)]

/-- The step-1 Jacobian determinant on the active set: `|det Dφ₁| = |x0|³` (`pivotBlowupOnDeriv_det`
with `card {0,1,2,3} − 1 = 3`). -/
theorem step1A_det (x : Fin 8 → ℝ) :
    (pivotBlowupOnDeriv ({0, 1, 2, 3} : Finset (Fin 8)) 0 x).det = (x 0) ^ 3 := by
  rw [pivotBlowupOnDeriv_det _ _ (by decide)]
  norm_num [show ({0, 1, 2, 3} : Finset (Fin 8)).card = 4 from by decide]

/-- **`step2E` is a pivot blow-up.** `step2E = pivotBlowupOn {1,2,3} 1` (the resolved-form blow-up,
pivot `E = z1`), reusing the gated `pivotBlowupOn` infra for the step-2 node's c-o-v (determinant
`(z 1)^{card−1} = z1²`, injectivity off `{z1 = 0}`). -/
theorem step2E_eq_pivotBlowupOn (z : Fin 7 → ℝ) :
    step2E z = pivotBlowupOn ({1, 2, 3} : Finset (Fin 7)) 1 z := by
  funext i
  unfold step2E pivotBlowupOn
  fin_cases i <;> simp [Matrix.cons_val]

/-- The step-2 Jacobian determinant: `|det Dφ₂| = |z1|²` (`pivotBlowupOnDeriv_det`,
`card {1,2,3} − 1 = 2`). -/
theorem step2E_det (z : Fin 7 → ℝ) :
    (pivotBlowupOnDeriv ({1, 2, 3} : Finset (Fin 7)) 1 z).det = (z 1) ^ 2 := by
  rw [pivotBlowupOnDeriv_det _ _ (by decide)]
  norm_num [show ({1, 2, 3} : Finset (Fin 7)).card = 3 from by decide]

/-- **Step-2 change-of-variables** (parallel to `step1A_lintegral_image`): for measurable `V` off the
pivot-zero locus `{z1 = 0}`, `∫⁻_{step2E '' (V \ {z1=0})} g = ∫⁻_{V \ {z1=0}} |det Dφ₂| · (g ∘
step2E)`. -/
theorem step2E_lintegral_image (V : Set (Fin 7 → ℝ)) (hV : MeasurableSet V)
    (g : (Fin 7 → ℝ) → ℝ≥0∞) :
    ∫⁻ x in step2E '' (V \ {x | x 1 = 0}), g x
      = ∫⁻ x in V \ {x | x 1 = 0},
          ENNReal.ofReal |(pivotBlowupOnDeriv ({1, 2, 3} : Finset (Fin 7)) 1 x).det|
            * g (step2E x) := by
  simp_rw [step2E_eq_pivotBlowupOn]
  rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume
    (hV.diff (measurableSet_eq_fun (measurable_pi_apply 1) measurable_const))
    (fun x _ => pivotBlowupOn_hasFDerivWithinAt _ _ _ x) (pivotBlowupOn_injOn _ _ _)]

/-! ## The composite chart's continuity + image containment (the `≤`-direction localisation input)

For the `≤`-direction lower bound `∫⁻_{cubeBox 8 ε} ≥ ∫⁻_{φ '' V}`, the chart image must sit inside the
cube: `phiUnit '' (cubeBox 8 δ) ⊆ cubeBox 8 ε` for a small `δ`. By continuity (`phiUnit` polynomial,
`phiUnit 0 = 0`) the preimage of the open cube `(−ε, ε)^8` is an open neighbourhood of `0`, hence
contains a `cubeBox 8 δ` (Codex 2026-06-21 — the continuity route avoids explicit polynomial bounds).
-/

theorem continuous_step1A : Continuous step1A := by
  unfold step1A
  refine Continuous.matrixVecCons ?_ (Continuous.matrixVecCons ?_ (Continuous.matrixVecCons ?_
    (Continuous.matrixVecCons ?_ (Continuous.matrixVecCons ?_ (Continuous.matrixVecCons ?_
      (Continuous.matrixVecCons ?_ (Continuous.matrixVecCons ?_ continuous_const)))))))
  all_goals fun_prop

theorem continuous_step2E : Continuous step2E := by
  unfold step2E
  refine Continuous.matrixVecCons ?_ (Continuous.matrixVecCons ?_ (Continuous.matrixVecCons ?_
    (Continuous.matrixVecCons ?_ (Continuous.matrixVecCons ?_ (Continuous.matrixVecCons ?_
      (Continuous.matrixVecCons ?_ continuous_const))))))
  all_goals fun_prop

/-- The composite leaf chart `phiUnit` is continuous (`step1A`, `step2E` polynomial; `lemma2Inv`
continuous; `Fin.cons` / `Fin.tail` continuous). -/
theorem continuous_phiUnit : Continuous phiUnit := by
  unfold phiUnit
  refine continuous_step1A.comp (Continuous.finCons (continuous_apply 0) ?_)
  exact continuous_lemma2Inv.comp (continuous_step2E.comp
    (by fun_prop : Continuous (Fin.tail : (Fin 8 → ℝ) → Fin 7 → ℝ)))

/-- `phiUnit` fixes the origin (the deepest point maps to the cube centre). -/
theorem phiUnit_zero : phiUnit (0 : Fin 8 → ℝ) = 0 := by
  have htail : Fin.tail (0 : Fin 8 → ℝ) = 0 := by funext i; simp [Fin.tail]
  unfold phiUnit
  rw [Pi.zero_apply, htail]
  rw [show step2E (0 : Fin 7 → ℝ) = 0 from by
        funext i; unfold step2E; fin_cases i <;> simp [Matrix.cons_val],
    show lemma2Inv (0 : Fin 7 → ℝ) = 0 from by
        funext i; unfold lemma2Inv; fin_cases i <;> simp [Matrix.cons_val],
    show Fin.cons (0 : ℝ) (0 : Fin 7 → ℝ) = (0 : Fin 8 → ℝ) from by
        funext i; rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩ <;> simp [Fin.cons]]
  funext i; unfold step1A; fin_cases i <;> simp [Matrix.cons_val]

/-- **Composite-chart image containment.** For any `ε > 0`, a small enough cube `cubeBox 8 δ` maps
into `cubeBox 8 ε` under `phiUnit` (continuity + `phiUnit 0 = 0`; the preimage of the open cube
`(−ε, ε)^8` is an open neighbourhood of `0`, hence contains a `cubeBox 8 δ` via
`cubeBox_subset_of_isOpen`). The `φ '' V ⊆ cubeBox` input to the `≤`-direction lower bound. -/
theorem phiUnit_image_subset_cubeBox (ε : ℝ) (hε : 0 < ε) :
    ∃ δ > 0, phiUnit '' (cubeBox 8 δ) ⊆ cubeBox 8 ε := by
  have hopen : IsOpen (Set.univ.pi (fun _ : Fin 8 => Set.Ioo (-ε) ε)) :=
    isOpen_set_pi Set.finite_univ (fun _ _ => isOpen_Ioo)
  have hmem : (0 : Fin 8 → ℝ) ∈ phiUnit ⁻¹' (Set.univ.pi (fun _ : Fin 8 => Set.Ioo (-ε) ε)) := by
    simp only [Set.mem_preimage, phiUnit_zero, Set.mem_pi, Set.mem_univ, true_implies,
      Set.mem_Ioo, Pi.zero_apply]
    exact fun i => ⟨by linarith, hε⟩
  obtain ⟨δ, hδ, hsub⟩ := cubeBox_subset_of_isOpen (hopen.preimage continuous_phiUnit) hmem
  refine ⟨δ, hδ, ?_⟩
  rintro y ⟨x, hx, rfl⟩
  have hxmem := hsub hx
  simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Ioo] at hxmem
  intro i _; exact ⟨(hxmem i).1.le, (hxmem i).2.le⟩

/-! ## The spectator-lift (`tailLift`) for the composite change-of-variables

The composite chart `phiUnit` applies maps to the `Fin 7` tail with `u0` a spectator. `tailLift F u =
Fin.cons (u 0) (F (Fin.tail u))` packages this; it factors through `finPeel 7` (`(Fin 8 → ℝ) ≃ₜ ℝ ×
(Fin 7 → ℝ)`, `u ↦ (u0, tail u)`) as `(finPeel 7).symm ∘ (id × F) ∘ finPeel 7`. The composite c-o-v
peels `u0` via the measure-preserving `finPeel 7` (route B, Codex 2026-06-21): the `Fin 7` blow-up
(`step2E`) and the Lemma-2 splice act on the tail factor. -/

/-- The spectator lift: apply a `Fin 7` map to the tail, keeping coordinate `0` fixed. -/
def tailLift (F : (Fin 7 → ℝ) → Fin 7 → ℝ) (u : Fin 8 → ℝ) : Fin 8 → ℝ :=
  Fin.cons (u 0) (F (Fin.tail u))

/-- `finPeel 7 u = (u 0, Fin.tail u)` (the `0`-th coordinate peeled off). -/
theorem finPeel7_apply (u : Fin 8 → ℝ) : (finPeel 7) u = (u 0, Fin.tail u) := by
  unfold finPeel; simp only [Homeomorph.homeomorph_mk_coe]; rfl

/-- `(finPeel 7).symm (a, r) = Fin.cons a r` (reassemble; `piFinSuccAbove.symm = insertNth 0`). -/
theorem finPeel7_symm_apply (a : ℝ) (r : Fin 7 → ℝ) :
    (finPeel 7).symm (a, r) = Fin.cons a r := by
  unfold finPeel; simp only [Homeomorph.homeomorph_mk_coe]; exact Fin.insertNth_zero' a r

/-- `tailLift` factors through `finPeel 7` as `(finPeel 7).symm ∘ (id × F) ∘ finPeel 7` (the
spectator-product structure for the measure-preserving peel). -/
theorem tailLift_eq_finPeel (F : (Fin 7 → ℝ) → Fin 7 → ℝ) (u : Fin 8 → ℝ) :
    tailLift F u = (finPeel 7).symm (Prod.map id F (finPeel 7 u)) := by
  rw [finPeel7_apply, Prod.map_apply, id_eq, finPeel7_symm_apply]; rfl

/-- `lemma2Inv` is measure-preserving (the inverse of the measure-preserving `lemma2Hom`). -/
theorem measurePreserving_lemma2Inv :
    MeasurePreserving lemma2Inv (volume : Measure (Fin 7 → ℝ)) volume :=
  measurePreserving_lemma2Hom.symm lemma2Hom.toMeasurableEquiv

/-- **`phiUnit` as a `Fin 8` chain.** `phiUnit = step1A ∘ tailLift lemma2Inv ∘ tailLift step2E`
(`Fin.cons_zero` / `Fin.tail_cons` collapse the nested cons/tail). The composite c-o-v then peels the
`u0`-spectator (`finPeel 7`) so the Fin-7 tail receives the gated `step2E_lintegral_image` and the
Lemma-2 measure-preserving splice (route B, Codex 2026-06-21). -/
theorem phiUnit_eq_comp (u : Fin 8 → ℝ) :
    phiUnit u = step1A (tailLift lemma2Inv (tailLift step2E u)) := by
  unfold phiUnit tailLift
  rw [Fin.cons_zero, Fin.tail_cons]

/-- **`lintegral` transport under a measure-preserving measurable equivalence.** For `e : M ≃ᵐ N`
measure-preserving, `∫⁻_{e '' S} g = ∫⁻_S (g ∘ e)` (`setLIntegral_comp_preimage_emb` +
`preimage_image_eq` via injectivity). The clean transport for the Lemma-2 splice (which is m.p., not
a blow-up). -/
theorem setLIntegral_image_of_mp {M N : Type*} [MeasureSpace M] [MeasureSpace N]
    [MeasurableSpace.CountablyGenerated N] (e : M ≃ᵐ N)
    (he : MeasurePreserving e volume volume) (S : Set M) (g : N → ℝ≥0∞) :
    ∫⁻ y in e '' S, g y = ∫⁻ x in S, g (e x) := by
  rw [← he.setLIntegral_comp_preimage_emb e.measurableEmbedding,
    Set.preimage_image_eq _ e.injective]

/-- **The Lemma-2 spectator-lift is measure-preserving.** `tailLift lemma2Inv = (finPeel 7).symm ∘
(id × lemma2Inv) ∘ finPeel 7`, a composition of measure-preserving maps (`finPeel_mp`,
`measurePreserving_lemma2Inv` in the product). So the Lemma-2 splice transports `lintegral`s by
`setLIntegral_image_of_mp` — no Jacobian (det `±1`). -/
theorem measurePreserving_tailLift_lemma2Inv :
    MeasurePreserving (tailLift lemma2Inv) (volume : Measure (Fin 8 → ℝ)) volume := by
  have hprodvol : (volume : Measure (ℝ × (Fin 7 → ℝ))) = (volume : Measure ℝ).prod volume :=
    Measure.volume_eq_prod _ _
  have hfp : MeasurePreserving (finPeel 7) (volume : Measure (Fin 8 → ℝ)) volume := finPeel_mp 7
  have hmid : MeasurePreserving (Prod.map (id : ℝ → ℝ) lemma2Inv)
      (volume : Measure (ℝ × (Fin 7 → ℝ))) volume := by
    rw [hprodvol]; exact (MeasurePreserving.id volume).prod measurePreserving_lemma2Inv
  have hfps : MeasurePreserving (finPeel 7).symm (volume : Measure (ℝ × (Fin 7 → ℝ)))
      (volume : Measure (Fin 8 → ℝ)) := by
    have := (finPeel_mp 7).symm; rwa [hprodvol] at this
  have hcomp := (hfps.comp hmid).comp hfp
  have heq : (⇑(finPeel 7).symm ∘ Prod.map (id : ℝ → ℝ) lemma2Inv) ∘ (finPeel 7)
      = tailLift lemma2Inv := by
    funext u; simp only [Function.comp_apply]; exact (tailLift_eq_finPeel lemma2Inv u).symm
  rwa [heq] at hcomp

end DLNFibre.DLN.RLCT
