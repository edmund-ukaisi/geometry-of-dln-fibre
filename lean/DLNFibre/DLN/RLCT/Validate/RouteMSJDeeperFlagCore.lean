import DLNFibre.DLN.RLCT.Validate.RouteMSJStrongBlock
import DLNFibre.DLN.RLCT.Validate.RouteMSJCornerComparator
import DLNFibre.DLN.RLCT.Validate.RouteMSJShellCharge
import DLNFibre.DLN.RLCT.Validate.RouteMSJResolution
import DLNFibre.DLN.RLCT.Validate.RouteMSJChartShear
import DLNFibre.DLN.RLCT.Validate.DeepestCoreNonvanishing
import DLNFibre.DLN.RLCT.Validate.RouteMSJHeadSplitFrame

set_option linter.style.longLine false

/-!
# `RouteMSJDeeperFlagCore` — L1 (off-sector core → comparator) + the headline `deeperFlag_shell_le`

**Thread `genm-inj-injon` (aoyagi-full Stage 2), T-Obl3b OWED-3, the CORRECTED deeper-cut route.** The
controller's L1-first ladder (de-risk gate STEP 1 → STEP 2). This module lands, sorry-free, the
reachable analytic content of the mountain and STATES the headline reduced to the single genuinely-new
seam **S1** (the head-split spine→core CoV, isolated as ONE correct-statement `sorry`).

## What lands here (the analytic labour, sorry-free)

* **`strongBlock_lintegral_le_unif`** (S3) — the reduced strong-block weight is bounded by a
  `U_s`-UNIFORM finite constant: the orthogonal extension `U` of `U_s` has entries `≤ 1`, so the rotated
  box sits inside the fixed box `matBox b' M₂ (M₂²)`, and the right-mult CoV Jacobian `|det U| = 1`.
  Strengthens `strongBlock_lintegral_lt_top` from `< ⊤` to a uniform `≤ C_strong_unif`.
* **`shellCorankWeight_le_unif`** (S3) — the shell corank weight `∫ det((A·Z)(A·Z)ᵀ)^{−a/2}` is bounded
  by `ε^{−ab}·C_strong_unif`, a constant INDEPENDENT of `Z` (given the shell PSD hypothesis).
* **`shell_corankOffSector_le_unif`** (S3) — `shell_corankOffSector_le` with the `Z`-uniform constant:
  `∀ w > 0, ∫_{A_cor}∫_Γ (w + frobSq(Ccross + Γ·(A_cor·Z)))^{−c'} ≤ Cunif · w^{−(c'−ab/2)}`, `Cunif` free
  of `Z`, `Ccross`, `w`.
* **`deeperFlag_shell_core_le`** (L1) — the per-shell domination at the off-sector-core level: the core
  integrand integrated over the reduced params `z ∈ paramsBoxM (redChain u M) 1` and exceptional
  coordinates `v ∈ unitBox d`, with the pivot energy `w = commonDivisor(v)²·frobSq(prod (redChain u M) z)`
  (S4, definitional), is bounded by `Cunif · (cornerComparator (redChain u M) k jc).integral (c' −
  ½·peelCharge M u)`. Consumes `shell_corankOffSector_le_unif` + `cornerComparator_decLoss`.

## The two isolated bricks (F, D — cert-pinned correct-statement `sorry`s)

The S1-good head-split spine→core CoV (`deeperFlag_spineToCore`, scoped to good/non-waist chains via
`hpiv`/`hcvg`/`hrange`) is now ASSEMBLED sorry-free MODULO exactly two isolated bricks, plus the fully
proved in-tide assembly (nat clauses, `ε'>0`, endpoint index, `hconv`, the `hpos` positivity
`deeperFlagCore_decLoss_pos_ae`, and the `hbeta` monomial threshold). The corrected statement carries the
rescaled floor `ε' = ε/√(M₁M₂)` and the finite reorganization constant `C_hle`.

* **`exists_headSplitFrame` (Brick F)** — the measurable piecewise `m`-frame selector (`= Z_deep` on the
  good set `G`, fixed full-rank `V` off `G`): orthonormal `U_sf`, rank `≥ m`, the Loewner floor at `ε'`,
  agreeing with `Z_deep` on `G` (`weakEigCount ε' ≤ M₂ − m`). Content: Borel functional calculus. Cert:
  `s1-spine-headsplit-cert` §B.3. **WIRED sorry-free** to the banked clean-three implementation
  `exists_headSplitFrame_impl` (`RouteMSJHeadSplitFrame`, on the isolated `measurableEigendecomp` primitive).
* **`headSplit_domination` (Brick D)** — the head-split domination with finite constant: given the frame
  data, `∃ Ccrossf sΓf C_hle < ⊤, shellSpine ≤ C_hle · deeperFlagCore`. Content: row-split, `prod_headSplit`,
  the P-radial blow-up, the `B₁₂→Γ'` shear, `C_hle` finite via the codim-`u·ρ` linear-image argument
  (gated by `hpiv`), Ky-Fan → shell ⊆ G, S3/L1 assembly. Cert: `s1-spine-headsplit-cert` Part A +
  `s1-Chle-angular-integrability-cert`.

* **`deeperFlag_spineToCore` (S1-good)** — ASSEMBLED: `= exists_headSplitFrame ∘ headSplit_domination` +
  the proved-in-tide clauses. Sorry-free modulo D (F now wired sorry-free).
* **`deeperFlag_shell_le`** — the headline = `deeperFlag_spineToCore` (S1-good) ∘ `deeperFlag_shell_core_le`
  (L1) + the decorated IH via `cornerComparator_adm`, folding `C := C_hle · C_L1`. Scoped to good chains;
  waists route through the separate `deeperFlag_waist` SVD-qPeel base case (task #156).

S2-FREE. Axiom-clean `[propext, Classical.choice, Quot.sound]` for the sorry-free results (L1, the S3
uniform bricks, and the in-tide assembly clauses incl. `deeperFlagCore_decLoss_pos_ae`); `deeperFlag_spineToCore`
(S1-good) and `deeperFlag_shell_le` (headline) carry `sorryAx` = exactly D, the one remaining tracked
`(□)`-rung (F wired sorry-free to `exists_headSplitFrame_impl`, `RouteMSJHeadSplitFrame`).
-/

namespace DLNFibre.DLN.RLCT

open Matrix MeasureTheory
open scoped ENNReal BigOperators

/-! ## S3 — the `U_s`-uniform reduced strong-block weight -/

/-- **The reduced strong-block weight is bounded by a `U_s`-uniform finite constant.** For `U_s : M₂×m`
with `U_sᵀU_s = 1`, `b' ≤ m`, in the convergent regime `a' < m − b' + 1`, the reduced corank weight over
`A·U_s` is bounded by the integral over the FIXED box `matBox b' M₂ (M₂²)` of the `m`-first-columns Gram
weight — a constant free of `U_s`. Route: `strongBlock_lintegral_lt_top` verbatim through the
right-mult CoV, then (i) the orthogonal extension `U` has `|det U| = 1` so the CoV Jacobian is `1`, and
(ii) `U`'s entries are `≤ 1` (orthonormal columns), so its `[−T,T]` bounding box has `T ≤ M₂²` and the
rotated domain `s ⊆ matBox b' M₂ (M₂²)`. -/
theorem strongBlock_lintegral_le_unif {b' m M₂ : ℕ} (hmM : m ≤ M₂)
    (U_s : Matrix (Fin M₂) (Fin m) ℝ) (hUs : U_sᵀ * U_s = 1) {a' : ℝ} :
    (∫⁻ A in matBox b' M₂ 1,
        ENNReal.ofReal (((Matrix.of A * U_s) * (Matrix.of A * U_s)ᵀ).det ^ (-a' / 2)))
      ≤ ∫⁻ X in matBox b' M₂ ((M₂ : ℝ) ^ 2),
          ENNReal.ofReal
            ((((Matrix.of X).submatrix id ⇑(Fin.castLEEmb hmM))
                * ((Matrix.of X).submatrix id ⇑(Fin.castLEEmb hmM))ᵀ).det ^ (-a' / 2)) := by
  classical
  set κ : Fin m ↪ Fin M₂ := Fin.castLEEmb hmM with hκdef
  obtain ⟨U, hUU, hUsub⟩ := exists_ortho_ext hmM U_s hUs
  have hUUt : U * Uᵀ = 1 := mul_eq_one_comm.mp hUU
  have hUdet : U.det ≠ 0 := by
    intro h
    have h1 : (Uᵀ * U).det = 1 := by rw [hUU, Matrix.det_one]
    rw [Matrix.det_mul, Matrix.det_transpose, h, mul_zero] at h1
    exact zero_ne_one h1
  have hUsub' : U.submatrix id (⇑κ) = U_s := hUsub
  -- `|det U| = 1`
  have hdetU_abs : |U.det| = 1 := by
    have h1 : (Uᵀ * U).det = 1 := by rw [hUU, Matrix.det_one]
    rw [Matrix.det_mul, Matrix.det_transpose] at h1
    have : U.det ^ 2 = 1 := by rw [sq]; linarith [h1]
    have h2 : |U.det| ^ 2 = 1 := by rw [sq_abs]; exact this
    nlinarith [abs_nonneg U.det, h2]
  -- entries of `U` bounded by 1 (columns orthonormal)
  have hUentry : ∀ i j : Fin M₂, |U i j| ≤ 1 := by
    intro i j
    have hcol : ∑ k, U k j * U k j = 1 := by
      have := congrFun (congrFun hUU j) j
      simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply_eq] at this
      exact this
    have hle : (U i j) ^ 2 ≤ ∑ k, U k j * U k j := by
      rw [sq]
      refine Finset.single_le_sum (f := fun k => U k j * U k j) (fun k _ => mul_self_nonneg _)
        (Finset.mem_univ i)
    rw [hcol] at hle
    nlinarith [abs_nonneg (U i j), sq_abs (U i j)]
  -- the column-restricted integrand `g`
  set g : (Fin b' → Fin M₂ → ℝ) → ℝ≥0∞ :=
    fun Y => ENNReal.ofReal
      ((((Matrix.of Y).submatrix id (⇑κ)) * ((Matrix.of Y).submatrix id (⇑κ))ᵀ).det ^ (-a' / 2))
    with hgdef
  have hcolmeas : Measurable (fun Y : Fin b' → Fin M₂ → ℝ => (fun i k => Y i (κ k))) :=
    measurable_pi_lambda _ (fun i =>
      measurable_pi_lambda _ (fun k => (measurable_pi_apply (κ k)).comp (measurable_pi_apply i)))
  have hgmeas : Measurable g := (measurable_detGram b' m a').comp hcolmeas
  have hof : ∀ A : Fin b' → Fin M₂ → ℝ, Matrix.of (fun i => A i ᵥ* U) = Matrix.of A * U := by
    intro A; ext i j
    simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.vecMul, dotProduct]
  have hsubmul : ∀ A : Fin b' → Fin M₂ → ℝ,
      (Matrix.of A * U).submatrix id (⇑κ) = Matrix.of A * (U.submatrix id (⇑κ)) := by
    intro A; ext i k
    simp only [Matrix.submatrix_apply, Matrix.mul_apply, id_eq, Matrix.of_apply]
  have hint : ∀ A : Fin b' → Fin M₂ → ℝ,
      ENNReal.ofReal (((Matrix.of A * U_s) * (Matrix.of A * U_s)ᵀ).det ^ (-a' / 2))
        = g (fun i => A i ᵥ* U) := by
    intro A
    rw [hgdef]
    have hstep : (Matrix.of (fun i => A i ᵥ* U)).submatrix id (⇑κ) = Matrix.of A * U_s := by
      rw [hof A, hsubmul A, hUsub']
    simp only [hstep]
  set s : Set (Fin b' → Fin M₂ → ℝ) := {Y | (fun i => Y i ᵥ* Uᵀ) ∈ matBox b' M₂ 1} with hsdef
  have hsmeasmap : Measurable (fun Y : Fin b' → Fin M₂ → ℝ => (fun i => Y i ᵥ* Uᵀ)) := by
    refine measurable_pi_lambda _ (fun i => measurable_pi_lambda _ (fun j => ?_))
    simp only [Matrix.vecMul, dotProduct]
    exact Finset.measurable_sum _ (fun k _ =>
      (((measurable_pi_apply k).comp (measurable_pi_apply i)).mul measurable_const))
  have hsmeas : MeasurableSet s := hsmeasmap (matBox_measurableSet b' M₂ 1)
  have hfun : ∀ A : Fin b' → Fin M₂ → ℝ, (fun i => (A i ᵥ* U) ᵥ* Uᵀ) = A := by
    intro A; funext i
    rw [Matrix.vecMul_vecMul, hUUt, Matrix.vecMul_one]
  have hmem : ∀ A : Fin b' → Fin M₂ → ℝ,
      (fun i => A i ᵥ* U) ∈ s ↔ A ∈ matBox b' M₂ 1 := by
    intro A; simp only [hsdef, Set.mem_setOf_eq, hfun A]
  -- the box enclosure `s ⊆ matBox b' M₂ (M₂²)` (entries of `U` ≤ 1 ⟹ `T ≤ M₂²`)
  have hsub : s ⊆ matBox b' M₂ ((M₂ : ℝ) ^ 2) := by
    intro Y hY
    simp only [hsdef, Set.mem_setOf_eq, matBox, Set.mem_setOf_eq] at hY ⊢
    intro i j
    rw [Set.mem_Icc]
    have hYrec : (Y i ᵥ* Uᵀ) ᵥ* U = Y i := by
      rw [Matrix.vecMul_vecMul, hUU, Matrix.vecMul_one]
    have hentry : Y i j = ∑ k, (Y i ᵥ* Uᵀ) k * U k j := by
      conv_lhs => rw [← hYrec]
      simp only [Matrix.vecMul, dotProduct]
    have habs : |Y i j| ≤ (M₂ : ℝ) ^ 2 := by
      rw [hentry]
      calc |∑ k, (Y i ᵥ* Uᵀ) k * U k j|
          ≤ ∑ k, |(Y i ᵥ* Uᵀ) k * U k j| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _k : Fin M₂, (1 : ℝ) := by
            refine Finset.sum_le_sum (fun k _ => ?_)
            rw [abs_mul]
            have hmb := hY i k
            rw [Set.mem_Icc] at hmb
            have h1 : |(Y i ᵥ* Uᵀ) k| ≤ 1 := abs_le.mpr hmb
            nlinarith [hUentry k j, abs_nonneg ((Y i ᵥ* Uᵀ) k), abs_nonneg (U k j), h1]
        _ = (M₂ : ℝ) := by simp
        _ ≤ (M₂ : ℝ) ^ 2 := by exact_mod_cast Nat.le_self_pow (by norm_num) M₂
    exact abs_le.mp habs
  -- assemble
  rw [show (∫⁻ A in matBox b' M₂ 1,
        ENNReal.ofReal (((Matrix.of A * U_s) * (Matrix.of A * U_s)ᵀ).det ^ (-a' / 2)))
      = ∫⁻ A in matBox b' M₂ 1, g (fun i => A i ᵥ* U) from lintegral_congr (fun A => hint A)]
  rw [← lintegral_indicator (matBox_measurableSet b' M₂ 1)]
  rw [show (∫⁻ A, (matBox b' M₂ 1).indicator (fun A => g (fun i => A i ᵥ* U)) A)
      = ∫⁻ A, (s.indicator g) (fun i => A i ᵥ* U) from lintegral_congr (fun A => by
        by_cases hA : A ∈ matBox b' M₂ 1
        · rw [Set.indicator_of_mem hA, Set.indicator_of_mem ((hmem A).mpr hA)]
        · rw [Set.indicator_of_notMem hA,
            Set.indicator_of_notMem (fun h => hA ((hmem A).mp h))])]
  rw [lintegral_comp_rightMulₚ b' U hUdet (s.indicator g) (hgmeas.indicator hsmeas),
    lintegral_indicator hsmeas]
  rw [hdetU_abs, one_pow, inv_one, ENNReal.ofReal_one, one_mul]
  calc ∫⁻ A in s, g A
      ≤ ∫⁻ A in matBox b' M₂ ((M₂ : ℝ) ^ 2), g A := lintegral_mono_set hsub
    _ = _ := rfl

/-- **The fixed-box uniform strong-block constant is finite.** `∫_{matBox b' M₂ (M₂²)} det(Gram of the
first `m` columns)^{−a'/2} < ⊤` in the convergent regime `a' < m − b' + 1` — a `U_s`-free finite
majorant (`detGram_firstCols_lintegral_box_lt_top` at `T = M₂²`). -/
theorem strongBlock_unif_const_lt_top {b' m M₂ : ℕ} (hmM : m ≤ M₂) (hbm : b' ≤ m) {a' : ℝ}
    (ha' : a' < (m : ℝ) - b' + 1) :
    (∫⁻ X in matBox b' M₂ ((M₂ : ℝ) ^ 2),
        ENNReal.ofReal
          ((((Matrix.of X).submatrix id ⇑(Fin.castLEEmb hmM))
              * ((Matrix.of X).submatrix id ⇑(Fin.castLEEmb hmM))ᵀ).det ^ (-a' / 2))) < ⊤ :=
  detGram_firstCols_lintegral_box_lt_top (Fin.castLEEmb hmM) hbm ha' ((M₂ : ℝ) ^ 2)

/-- **The shell corank weight is bounded by a `Z`-uniform finite constant.** On the shell
`Z Zᵀ ⪰ ε²·(U_s U_sᵀ)`, the corank weight `∫ det((A·Z)(A·Z)ᵀ)^{−a/2}` is bounded by
`ε^{−ab} · C_strong_unif`, where `C_strong_unif` is the fixed-box strong-block constant — a value free
of `Z` (given `hshell` holds). Composes OWED-1 `uniformWenn_proj_le` (Wenn ≤ ε^{−ab}·strong block) with
the uniform strong-block bound `strongBlock_lintegral_le_unif`. -/
theorem shellCorankWeight_le_unif {a b M₂ m n : ℕ} (Z : Matrix (Fin M₂) (Fin n) ℝ)
    (U_s : Matrix (Fin M₂) (Fin m) ℝ) (hUs : U_sᵀ * U_s = 1) (hbm : b ≤ m) (hmM : m ≤ M₂)
    {ε : ℝ} (hε : 0 < ε)
    (hshell : (Z * Zᵀ - (ε ^ 2) • (U_s * U_sᵀ)).PosSemidef) :
    (∫⁻ A in matBox b M₂ 1,
        ENNReal.ofReal (((Matrix.of A * Z) * (Matrix.of A * Z)ᵀ).det ^ (-(a : ℝ) / 2)))
      ≤ ENNReal.ofReal (ε ^ (-((a : ℝ) * b)))
        * ∫⁻ X in matBox b M₂ ((M₂ : ℝ) ^ 2),
            ENNReal.ofReal
              ((((Matrix.of X).submatrix id ⇑(Fin.castLEEmb hmM))
                  * ((Matrix.of X).submatrix id ⇑(Fin.castLEEmb hmM))ᵀ).det ^ (-(a : ℝ) / 2)) :=
  le_trans (uniformWenn_proj_le Z U_s hUs hbm hε hshell)
    (mul_le_mul_left' (strongBlock_lintegral_le_unif hmM U_s hUs) _)

/-- **The `Z`-uniform per-shell constant.** `Cresid(ab)c' · (ε^{−ab} · C_strong_unif)` — the finite,
`Z`/`Ccross`/`w`-free constant of the per-shell interior bound. Named so `shell_corankOffSector_le_unif`
and L1 (`deeperFlag_shell_core_le`) reference the identical term (avoids the nat-sub-cast mismatch). -/
noncomputable def deeperFlagUnifConst (a b m M₂ : ℕ) (hmM : m ≤ M₂) (ε c' : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (Cresid (a * b) c')
    * (ENNReal.ofReal (ε ^ (-((a : ℝ) * b)))
      * ∫⁻ X in matBox b M₂ ((M₂ : ℝ) ^ 2),
          ENNReal.ofReal
            ((((Matrix.of X).submatrix id ⇑(Fin.castLEEmb hmM))
                * ((Matrix.of X).submatrix id ⇑(Fin.castLEEmb hmM))ᵀ).det ^ (-(a : ℝ) / 2)))

/-- **The `Z`-uniform per-shell constant is finite** (in the convergent regime `a < m − b + 1`). -/
theorem deeperFlagUnifConst_lt_top (a b m M₂ : ℕ) (hmM : m ≤ M₂) (hbm : b ≤ m)
    (hconv : (a : ℝ) < (m : ℝ) - b + 1) (ε c' : ℝ) :
    deeperFlagUnifConst a b m M₂ hmM ε c' < ⊤ := by
  rw [deeperFlagUnifConst]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (strongBlock_unif_const_lt_top hmM hbm hconv))

/-! ## S3 — the `Z`-uniform per-shell interior bound -/

/-- **The `Z`-uniform per-shell interior bound.** `shell_corankOffSector_le` with the constant made
INDEPENDENT of `Z`, `Ccross`, and `w`: on the shell `Z Zᵀ ⪰ ε²·(U_s U_sᵀ)` (`U_sᵀU_s=1`, `b ≤ m ≤ M₂`,
`m ≤ Z.rank`), in the reduced convergent regime `a < m − b + 1` with `ab/2 < c'`,

    ∫_{A_cor ∈ matBox b M₂ 1} ∫_{Γ∈sΓ} (w + frobSq(Ccross + Γ·(A_cor·Z)))^{−c'}
      ≤ Cunif · w^{−(c' − ab/2)}

where `Cunif = ofReal(Cresid(ab)c') · (ofReal(ε^{−ab}) · C_strong_unif)` reads only `ε` and the dims.
The `Z`-uniformity (replacing `shell_corankOffSector_le`'s `Cresid·Wenn(Z)` by the uniform
`shellCorankWeight_le_unif` bound) is what lets the reduced-param `z`-integral in L1 pull the constant
out. Proof: the corner atom `corankBlock_morsePeel_setLE` (`Apiv := 0`) pointwise on the full-row-rank
set, then integrate and bound the corank weight uniformly. -/
theorem shell_corankOffSector_le_unif {a b M₂ m n : ℕ} (Z : Matrix (Fin M₂) (Fin n) ℝ)
    (U_s : Matrix (Fin M₂) (Fin m) ℝ) (hUs : U_sᵀ * U_s = 1) (hbm : b ≤ m) (hmM : m ≤ M₂)
    (hmZ : m ≤ Z.rank) {ε : ℝ} (hε : 0 < ε)
    (hshell : (Z * Zᵀ - (ε ^ 2) • (U_s * U_sᵀ)).PosSemidef)
    (Ccross : Matrix (Fin a) (Fin n) ℝ) (c' : ℝ) (hc' : (a * b : ℝ) / 2 < c')
    (sΓ : Set (Fin a → Fin b → ℝ)) (w : ℝ) (hw : 0 < w) :
    ∫⁻ A_cor in matBox b M₂ 1,
        ∫⁻ Γ in sΓ, ENNReal.ofReal
          ((w + frobSq (Ccross + (Matrix.of Γ) * (Matrix.of A_cor * Z))) ^ (-c'))
      ≤ deeperFlagUnifConst a b m M₂ hmM ε c'
        * ENNReal.ofReal (w ^ (-(c' - (a * b : ℝ) / 2))) := by
  classical
  rw [deeperFlagUnifConst]
  set Wunif : ℝ≥0∞ := ENNReal.ofReal (ε ^ (-((a : ℝ) * b)))
    * ∫⁻ X in matBox b M₂ ((M₂ : ℝ) ^ 2),
        ENNReal.ofReal
          ((((Matrix.of X).submatrix id ⇑(Fin.castLEEmb hmM))
              * ((Matrix.of X).submatrix id ⇑(Fin.castLEEmb hmM))ᵀ).det ^ (-(a : ℝ) / 2)) with hWunif
  set F : (Fin b → Fin M₂ → ℝ) → ℝ≥0∞ := fun A =>
    ∫⁻ Γ in sΓ, ENNReal.ofReal
      ((w + frobSq (Ccross + (Matrix.of Γ) * (Matrix.of A * Z))) ^ (-c')) with hFdef
  have hmeasbox : MeasurableSet (matBox b M₂ 1) := matBox_measurableSet b M₂ 1
  have hbZ : b ≤ Z.rank := le_trans hbm hmZ
  have hfz : frobSq (0 : Matrix (Fin 0) (Fin n) ℝ) = 0 := by simp [frobSq]
  have hcorepow : ∀ X : Matrix (Fin a) (Fin n) ℝ,
      (w + frobSq (0 : Matrix (Fin 0) (Fin n) ℝ) + frobSq X) ^ (-(c' - (a * b : ℝ) / 2))
        ≤ w ^ (-(c' - (a * b : ℝ) / 2)) := fun X =>
    Real.rpow_le_rpow_of_nonpos hw
      (by rw [hfz, add_zero]; exact le_add_of_nonneg_right (frobSq_nonneg _))
      (by linarith [hc'])
  have hpt : ∀ A : Fin b → Fin M₂ → ℝ, (Matrix.of A * Z).rank = b →
      F A ≤ ENNReal.ofReal (Cresid (a * b) c' * w ^ (-(c' - (a * b : ℝ) / 2)))
              * ENNReal.ofReal (((Matrix.of A * Z) * (Matrix.of A * Z)ᵀ).det ^ (-(a : ℝ) / 2)) := by
    intro A hrank
    have hPD := posDef_gram_of_rank_eq (Matrix.of A * Z) hrank
    have hatom := corankBlock_morsePeel_setLE (Apiv := (0 : Matrix (Fin 0) (Fin n) ℝ))
      (Ccross := Ccross) (Qb := Matrix.of A * Z) hPD c' hc' w hw sΓ
    have hFeq : F A = ∫⁻ Γ in sΓ, ENNReal.ofReal
        ((w + frobSq (0 : Matrix (Fin 0) (Fin n) ℝ)
          + frobSq (Ccross + (Matrix.of Γ) * (Matrix.of A * Z))) ^ (-c')) := by
      simp only [hFdef]
      exact lintegral_congr (fun Γ => by rw [hfz, add_zero])
    rw [hFeq]
    refine le_trans hatom ?_
    rw [← ENNReal.ofReal_mul
      (mul_nonneg (Cresid_nonneg (a * b) c') (Real.rpow_nonneg hw.le _))]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [show Cresid (a * b) c' * w ^ (-(c' - (a * b : ℝ) / 2))
          * ((Matrix.of A * Z) * (Matrix.of A * Z)ᵀ).det ^ (-(a : ℝ) / 2)
        = ((Matrix.of A * Z) * (Matrix.of A * Z)ᵀ).det ^ (-(a : ℝ) / 2)
            * Cresid (a * b) c' * w ^ (-(c' - (a * b : ℝ) / 2)) from by ring]
    exact mul_le_mul_of_nonneg_left (hcorepow _)
      (mul_nonneg (Real.rpow_nonneg (posSemidef_mul_transpose _).det_nonneg _)
        (Cresid_nonneg (a * b) c'))
  calc ∫⁻ A in matBox b M₂ 1, F A
      ≤ ∫⁻ A in matBox b M₂ 1,
          ENNReal.ofReal (Cresid (a * b) c' * w ^ (-(c' - (a * b : ℝ) / 2)))
            * ENNReal.ofReal (((Matrix.of A * Z) * (Matrix.of A * Z)ᵀ).det ^ (-(a : ℝ) / 2)) := by
        refine lintegral_mono_ae ((ae_restrict_iff' hmeasbox).mpr ?_)
        filter_upwards [corank_survival_ae Z hbZ] with A hrank _hAbox
        exact hpt A hrank
    _ = ENNReal.ofReal (Cresid (a * b) c' * w ^ (-(c' - (a * b : ℝ) / 2)))
          * ∫⁻ A in matBox b M₂ 1,
              ENNReal.ofReal (((Matrix.of A * Z) * (Matrix.of A * Z)ᵀ).det ^ (-(a : ℝ) / 2)) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (Cresid (a * b) c' * w ^ (-(c' - (a * b : ℝ) / 2))) * Wunif := by
        exact mul_le_mul_left' (shellCorankWeight_le_unif Z U_s hUs hbm hmM hε hshell) _
    _ = (ENNReal.ofReal (Cresid (a * b) c') * Wunif)
          * ENNReal.ofReal (w ^ (-(c' - (a * b : ℝ) / 2))) := by
        rw [ENNReal.ofReal_mul (Cresid_nonneg (a * b) c')]; ring

/-! ## L1 — the per-shell off-sector-core → comparator domination -/

variable {L : ℕ}

/-- **The off-sector-core integrand at the deeper cut `u`** — L1's LHS and S1's output shape. The
freed-corner core (pivot energy taken to be the comparator loss `(cornerComparator …).decLoss v z`,
S4-definitional), integrated over the reduced params `z ∈ paramsBoxM (redChain u M) 1` and the
exceptional coordinates `v ∈ unitBox d` against the accumulated Jacobian monomial `∏|v_ℓ|^{jc_ℓ}`. Named
so `deeperFlag_spineToCore` (S1) and `deeperFlag_shell_core_le` (L1) reference the identical term. -/
noncomputable def deeperFlagCoreIntegrand {d M₂ n : ℕ} (M : Fin (L + 1 + 1 + 1) → ℕ) (u : ℕ)
    (k jc : Fin d → ℕ)
    (Zf : Params (redChain u M) → Matrix (Fin M₂) (Fin n) ℝ)
    (Ccrossf : Params (redChain u M) → Matrix (Fin (M 0 - u)) (Fin n) ℝ)
    (sΓf : Params (redChain u M) → Set (Fin (M 0 - u) → Fin (M 1 - u) → ℝ))
    (c' : ℝ) : ℝ≥0∞ :=
  ∫⁻ z in paramsBoxM (redChain u M) 1, ∫⁻ v in unitBox d,
    ENNReal.ofReal (∏ ℓ, |v ℓ| ^ (jc ℓ))
      * (∫⁻ A_cor in matBox (M 1 - u) M₂ 1, ∫⁻ Γ in sΓf z,
          ENNReal.ofReal
            (((cornerComparator (redChain u M) k jc).decLoss v z
                + frobSq (Ccrossf z + (Matrix.of Γ) * (Matrix.of A_cor * Zf z))) ^ (-c')))

/-- **L1 — the per-shell off-sector-core domination onto the reduced comparator.** The off-sector-core
integrand — for the reduced comparator `D = cornerComparator (redChain u M) k jc` with its pivot energy
taken to be the comparator loss `w = D.decLoss v z` (S4, DEFINITIONAL) — integrated over the reduced
params `z ∈ paramsBoxM (redChain u M) 1` and the exceptional coordinates `v ∈ unitBox d` against the
accumulated Jacobian monomial `∏|v_ℓ|^{jc_ℓ}`, is bounded by a `z`-uniform finite constant times the
reduced comparator's integral at the shifted exponent `c' − ½·peelCharge M u`:

    ∫_z ∫_v (∏|v_ℓ|^{jc_ℓ}) · [∫_{A_cor}∫_Γ (D.decLoss v z + frobSq(Ccross z + Γ·(A_cor·Z z)))^{−c'}]
      ≤ C · D.integral (c' − ½·peelCharge M u).

The corner dims are `a = M₀−u`, `b = M₁−u`, so `a·b = peelCharge M u` (definitional). Consumes the
`Z`-uniform interior bound `shell_corankOffSector_le_unif` (pointwise in `(z,v)` at `w = D.decLoss v z`,
which is `> 0` a.e. by `hpos` — the `{w=0}`-null side-condition, dischargeable from product-nonvanishing
+ the exceptional monomial), then the reduced-param integration collapses to `D.integral` by unfolding
(`w = decLoss` matched definitionally). The `∃ C < ⊤` form supplies the compose exactly what the decorated
IH needs (comparator finite ⟹ core finite). NO IH used here (pure domination). -/
theorem deeperFlag_shell_core_le {d M₂ m n : ℕ} (M : Fin (L + 1 + 1 + 1) → ℕ) (u : ℕ)
    (k jc : Fin d → ℕ)
    (Zf : Params (redChain u M) → Matrix (Fin M₂) (Fin n) ℝ)
    (Ccrossf : Params (redChain u M) → Matrix (Fin (M 0 - u)) (Fin n) ℝ)
    (U_sf : Params (redChain u M) → Matrix (Fin M₂) (Fin m) ℝ)
    (sΓf : Params (redChain u M) → Set (Fin (M 0 - u) → Fin (M 1 - u) → ℝ))
    {ε : ℝ} (hε : 0 < ε)
    (hUs : ∀ z, (U_sf z)ᵀ * U_sf z = 1) (hbm : M 1 - u ≤ m) (hmM : m ≤ M₂)
    (hmZ : ∀ z, m ≤ (Zf z).rank)
    (hshell : ∀ z, (Zf z * (Zf z)ᵀ - (ε ^ 2) • (U_sf z * (U_sf z)ᵀ)).PosSemidef)
    (c' : ℝ) (hconv : ((M 0 - u : ℕ) : ℝ) < (m : ℝ) - ((M 1 - u : ℕ) : ℝ) + 1)
    (hc' : (((M 0 - u) * (M 1 - u) : ℕ) : ℝ) / 2 < c')
    (hpos : ∀ᵐ z ∂(volume.restrict (paramsBoxM (redChain u M) 1)),
        ∀ᵐ v ∂(volume.restrict (unitBox d)),
          0 < (cornerComparator (redChain u M) k jc).decLoss v z) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧
      deeperFlagCoreIntegrand M u k jc Zf Ccrossf sΓf c'
        ≤ C * (cornerComparator (redChain u M) k jc).integral (c' - (peelCharge M u : ℝ) / 2) := by
  classical
  rw [deeperFlagCoreIntegrand]
  set D := cornerComparator (redChain u M) k jc with hD
  set e : ℝ := c' - (peelCharge M u : ℝ) / 2 with he
  -- the named `Z`-uniform constant
  set C : ℝ≥0∞ := deeperFlagUnifConst (M 0 - u) (M 1 - u) m M₂ hmM ε c' with hC
  have hCfin : C < ⊤ :=
    deeperFlagUnifConst_lt_top (M 0 - u) (M 1 - u) m M₂ hmM hbm hconv ε c'
  refine ⟨C, hCfin, ?_⟩
  -- exponent bookkeeping: `↑a·↑b = a·b(:ℝ) = peelCharge M u(:ℝ)`, so `c' − ↑a·↑b/2 = e`.
  have hc'' : (((M 0 - u : ℕ) : ℝ) * ((M 1 - u : ℕ) : ℝ)) / 2 < c' := by
    rw [← Nat.cast_mul]; exact hc'
  have hexp : c' - ((M 0 - u : ℕ) : ℝ) * ((M 1 - u : ℕ) : ℝ) / 2 = e := by
    rw [he, peelCharge, Nat.cast_mul]
  -- the pointwise-a.e. interior bound, then integrate.
  have hstep : (∫⁻ z in paramsBoxM (redChain u M) 1, ∫⁻ v in unitBox d,
        ENNReal.ofReal (∏ ℓ, |v ℓ| ^ (jc ℓ))
          * (∫⁻ A_cor in matBox (M 1 - u) M₂ 1, ∫⁻ Γ in sΓf z,
              ENNReal.ofReal
                ((D.decLoss v z
                    + frobSq (Ccrossf z + (Matrix.of Γ) * (Matrix.of A_cor * Zf z))) ^ (-c'))))
      ≤ ∫⁻ z in paramsBoxM (redChain u M) 1, ∫⁻ v in unitBox d,
          C * ENNReal.ofReal ((∏ ℓ, |v ℓ| ^ (jc ℓ)) * (D.decLoss v z) ^ (-e)) := by
    refine lintegral_mono_ae ?_
    filter_upwards [hpos] with z hzv
    refine lintegral_mono_ae ?_
    filter_upwards [hzv] with v hvpos
    -- pointwise at `(z, v)`, `w := D.decLoss v z > 0`
    have hbound := shell_corankOffSector_le_unif (Zf z) (U_sf z) (hUs z) hbm hmM (hmZ z) hε
      (hshell z) (Ccrossf z) c' hc'' (sΓf z) (D.decLoss v z) hvpos
    rw [← hC, hexp] at hbound
    calc ENNReal.ofReal (∏ ℓ, |v ℓ| ^ (jc ℓ))
            * (∫⁻ A_cor in matBox (M 1 - u) M₂ 1, ∫⁻ Γ in sΓf z,
                ENNReal.ofReal
                  ((D.decLoss v z
                      + frobSq (Ccrossf z + (Matrix.of Γ) * (Matrix.of A_cor * Zf z))) ^ (-c')))
        ≤ ENNReal.ofReal (∏ ℓ, |v ℓ| ^ (jc ℓ))
            * (C * ENNReal.ofReal ((D.decLoss v z) ^ (-e))) :=
          mul_le_mul_left' hbound _
      _ = C * ENNReal.ofReal ((∏ ℓ, |v ℓ| ^ (jc ℓ)) * (D.decLoss v z) ^ (-e)) := by
          rw [ENNReal.ofReal_mul (Finset.prod_nonneg (fun ℓ _ => by positivity))]
          ring
  refine le_trans hstep ?_
  -- pull `C` out and recognise the comparator integral
  rw [show (∫⁻ z in paramsBoxM (redChain u M) 1, ∫⁻ v in unitBox d,
        C * ENNReal.ofReal ((∏ ℓ, |v ℓ| ^ (jc ℓ)) * (D.decLoss v z) ^ (-e)))
      = C * ∫⁻ z in paramsBoxM (redChain u M) 1, ∫⁻ v in unitBox d,
          ENNReal.ofReal ((∏ ℓ, |v ℓ| ^ (jc ℓ)) * (D.decLoss v z) ^ (-e)) from ?_]
  · exact le_refl _
  · rw [← lintegral_const_mul' C _ hCfin.ne]
    refine lintegral_congr (fun z => ?_)
    rw [← lintegral_const_mul' C _ hCfin.ne]

/-! ## The literal spine integrand + the headline `deeperFlag_shell_le` (S1 ∘ L1) -/

/-- **The literal cut-`u` shell-restricted spine integrand** — the `RouteMSJDecoratedPeelStep`
`innerCorankDescent` freed-Γ triple at cut `u`, with the outer `A'` restricted to the shell
`{A' | prod (tailChain M) A' ∈ singularShell ε r jf}`. This is the T-peel spine's per-shell output. -/
noncomputable def shellSpineIntegrand {L : ℕ} (M : Fin (L + 1 + 1 + 1) → ℕ) (u : ℕ)
    (κ : Fin u ↪ Fin (M 1)) (ε : ℝ) (r : ℕ) (jf : Fin (r + 1)) (c' : ℝ) : ℝ≥0∞ :=
  ∫⁻ A' in paramsBoxM (tailChain M) 1
      ∩ {A' | prod (tailChain M) A' ∈ singularShell ε r jf},
    ∫⁻ x in outerDom u (M 0 - u) (M 1 - u) 1,
      ∫⁻ Γ in {Γ : Fin (M 0 - u) → Fin (M 1 - u) → ℝ |
          Γ + schurShift x ∈ genBox (Fin (M 0 - u)) (Fin (M 1 - u)) 1},
        ENNReal.ofReal
          ((freedSchurLoss x Γ ((prod (tailChain M) A').submatrix (blockSplitEquiv κ) id)) ^ (-c'))

/-- **The tail-chain generic rank** `ρ = min(M₁, M₂, …, M_last)` — the generic rank of the deep-tail
layer product `prod (tailChain M)` (an `M₁ × M_last` product of the widths `M₁, M₂, …, M_last`). The
pivot-admissibility criterion `hpiv : minAdm (redChain u M) ≤ u·ρ` (gating `C_hle < ⊤`, the P-block
absorbed integral's codim-`u·ρ` finiteness) is stated against it. -/
def tailMinWidth {L : ℕ} (M : Fin (L + 1 + 1 + 1) → ℕ) : ℕ :=
  (Finset.univ : Finset (Fin (L + 1 + 1))).inf' ⟨0, Finset.mem_univ 0⟩ (fun i => M i.succ)

/-- **The deep-tail layer product as a function of the reduced params `z`.** Via the banked head split
(`paramsHeadSplit`): `Z_deep z = prod (dropHead (redChain u M)) (z ∘ succ)` (an `M₂ × n` matrix,
`M₂ = redChain u M 1 = M 2`, `n = M_last`, depending only on the deep layers of `z`). This is the deep
factor of the head-split `prod (redChain u M) z = (z 0) · Z_deep z`; the corank block on the RHS core is
`A_cor · Z_deep z`. -/
noncomputable def deeperFlagZdeep {L : ℕ} (M : Fin (L + 1 + 1 + 1) → ℕ) (u : ℕ)
    (z : Params (redChain u M)) :
    Matrix (Fin (dropHead (redChain u M) 0)) (Fin (dropHead (redChain u M) (Fin.last L))) ℝ :=
  prod (dropHead (redChain u M)) (paramsHeadSplit (redChain u M) z).2

/-- The row-width of `deeperFlagZdeep` is `M 2` (`= redChain u M 1`, the deep-tail leading width). -/
theorem dropHead_redChain_zero {L : ℕ} (M : Fin (L + 1 + 1 + 1) → ℕ) (u : ℕ) :
    dropHead (redChain u M) 0 = M 2 := by
  simp only [dropHead, Fin.succ_zero_eq_one]
  rfl

/-- The column-width of `deeperFlagZdeep` is `M_last`. -/
theorem dropHead_redChain_last {L : ℕ} (M : Fin (L + 1 + 1 + 1) → ℕ) (u : ℕ) :
    dropHead (redChain u M) (Fin.last L) = M (Fin.last (L + 1 + 1)) := by
  rw [dropHead, ← Fin.succ_last, redChain_succ, Fin.succ_last, Fin.succ_last]

/-! ## The two isolated bricks (F: frame selector; D: domination) — cert-pinned contracts -/

/-- **Brick F (isolated, `s1-spine-headsplit-cert` §B.3) — the measurable piecewise `m`-frame selector.**
For any measurable deep-matrix family `Zdeep : X → M₂×n`, with `m ≤ M₂`, `m ≤ n`, and a floor `ε' > 0`,
there is a piecewise `(Zf, U_sf)` — `= Zdeep` on the good set `G = {z | at least m eigenvalues of
Zdeep·Zdeepᵀ are ≥ ε'²}` (i.e. `weakEigCount ε' (Zdeep z) ≤ M₂ − m`), a fixed full-rank `V` off `G` —
that is measurable, has an orthonormal `m`-frame `U_sf`, rank `≥ m`, and the Loewner floor
`Zf·Zfᵀ ⪰ ε'²·U_sf·U_sfᵀ` UNCONDITIONALLY (on `G` from the top-`m` eigenframe, off `G` by construction).
The agreement `Zf = Zdeep on G` is the connection Brick D consumes (the shell image sits inside `G`).
Content: Borel functional calculus (`B ↦ 𝟙_{[ε'²,∞)}(B)` Borel) for the measurable frame. -/
theorem exists_headSplitFrame {X : Type*} [MeasurableSpace X] {M₂ n m : ℕ}
    (hmM₂ : m ≤ M₂) (hmn : m ≤ n) {ε' : ℝ} (hε' : 0 < ε')
    (Zdeep : X → Matrix (Fin M₂) (Fin n) ℝ) (hZ : Measurable Zdeep) :
    ∃ (Zf : X → Matrix (Fin M₂) (Fin n) ℝ) (U_sf : X → Matrix (Fin M₂) (Fin m) ℝ),
      Measurable Zf ∧ Measurable U_sf
      ∧ (∀ z, (U_sf z)ᵀ * U_sf z = 1)
      ∧ (∀ z, m ≤ (Zf z).rank)
      ∧ (∀ z, (Zf z * (Zf z)ᵀ - (ε' ^ 2) • (U_sf z * (U_sf z)ᵀ)).PosSemidef)
      ∧ (∀ z, weakEigCount ε' (Zdeep z) ≤ M₂ - m → Zf z = Zdeep z) :=
  -- Wired to the banked clean-three implementation (`RouteMSJHeadSplitFrame`): the measurable
  -- eigendecomposition + top-`m` eigenframe assembly. Statement is identical, so this is pure wiring.
  exists_headSplitFrame_impl hmM₂ hmn hε' Zdeep hZ

/-- **Brick D (isolated, `s1-spine-headsplit-cert` Part A + `s1-Chle-angular-integrability-cert`) — the
head-split domination with a FINITE reorganization constant.** Given the frame data from Brick F (at
`M₂ = M 2`, `n = M_last`, `m = min(M₁,n)−j`, floor `ε' = ε/√(M₁M₂)`), and the pivot-admissibility `hpiv`
+ convergence `hcvg` + range `hrange`, there exist `Ccrossf`, `sΓf`, and a FINITE `C_hle` for which the
cut-`u`/shell-`j` spine integrand is `≤ C_hle ·` the off-sector-core integrand at the clean comparator
data `k = ![1]`, `jc = ![minAdm(redChain u M) − 1]`. Content: the row-split `A' ↔ (z, A_cor)`, the
head-split `Q_b = A_cor·Zf z`, the P-radial blow-up (`P = commonDivisor(v)·P̂`, det-1 clear → the pivot
energy `commonDivisor(v)²·frobSq(prod(redChain u M) z) = decLoss` + Jacobian monomial), the exact `B₁₂→Γ'`
shear, `C_hle` finite via the codim-`u·ρ` linear-image argument (gated by `hpiv`), Ky-Fan → shell ⊆ G,
S3/L1 assembly. -/
theorem headSplit_domination {L : ℕ} (M : Fin (L + 1 + 1 + 1) → ℕ) (t j : ℕ)
    (κ : Fin (t + j) ↪ Fin (M 1)) {ε : ℝ} (hε : 0 < ε) (c' : ℝ)
    (ht : t ≤ min (M 0) (M 1)) (hj : j ≤ min (M 0 - t) (M 1 - t))
    (ht1 : 1 ≤ t) (hnd : ∀ i, 1 ≤ M i)
    (hpiv : minAdm (redChain (t + j) M) ≤ (t + j) * tailMinWidth M)
    (hcvg : (M 0 - (t + j)) + (M 1 - (t + j))
        ≤ min (M 1) (M (Fin.last (L + 1 + 1))) - j)
    (hrange : min (M 1) (M (Fin.last (L + 1 + 1))) - j ≤ M 2)
    {ε' : ℝ} (hε' : 0 < ε')
    (Zf : Params (redChain (t + j) M)
        → Matrix (Fin (dropHead (redChain (t + j) M) 0))
            (Fin (dropHead (redChain (t + j) M) (Fin.last L))) ℝ)
    (U_sf : Params (redChain (t + j) M)
        → Matrix (Fin (dropHead (redChain (t + j) M) 0))
            (Fin (min (M 1) (M (Fin.last (L + 1 + 1))) - j)) ℝ)
    (hZfMeas : Measurable Zf) (hUsMeas : Measurable U_sf)
    (hUs : ∀ z, (U_sf z)ᵀ * U_sf z = 1)
    (hrank : ∀ z, (min (M 1) (M (Fin.last (L + 1 + 1))) - j) ≤ (Zf z).rank)
    (hfloor : ∀ z, (Zf z * (Zf z)ᵀ - (ε' ^ 2) • (U_sf z * (U_sf z)ᵀ)).PosSemidef)
    (hagree : ∀ z, weakEigCount ε' (deeperFlagZdeep M (t + j) z)
        ≤ dropHead (redChain (t + j) M) 0 - (min (M 1) (M (Fin.last (L + 1 + 1))) - j)
        → Zf z = deeperFlagZdeep M (t + j) z) :
    ∃ (Ccrossf : Params (redChain (t + j) M)
          → Matrix (Fin (M 0 - (t + j))) (Fin (dropHead (redChain (t + j) M) (Fin.last L))) ℝ)
        (sΓf : Params (redChain (t + j) M)
          → Set (Fin (M 0 - (t + j)) → Fin (M 1 - (t + j)) → ℝ))
        (C_hle : ℝ≥0∞),
      C_hle < ⊤
      ∧ shellSpineIntegrand M (t + j) κ ε (min (M 0 - t) (M 1 - t)) ⟨j, Nat.lt_succ_of_le hj⟩ c'
          ≤ C_hle * deeperFlagCoreIntegrand M (t + j) (![1] : Fin 1 → ℕ)
              (![minAdm (redChain (t + j) M) - 1] : Fin 1 → ℕ) Zf Ccrossf sΓf c' := by
  sorry

/-- **The comparator's decorated loss is a.e. positive** (the `hpos` clause of S1-good). At the clean
comparator data `k = ![1]`, `jc = ![minAdm − 1]`, `decLoss v z = |v 0|² · frobSq(prod (redChain u M) z)`
(`cornerComparator_decLoss`, `commonDivisor = |v 0|`); both factors are `> 0` a.e.: `v 0 ≠ 0` a.e. on
`[0,1]`, and `prod (redChain u M) z ≠ 0` a.e. (all reduced widths `≥ 1` via `ht1`/`hnd`, the banked
general-`L` polynomial-nonvanishing `DeepestCoreNonvanishing`). Reachable, self-contained. -/
theorem deeperFlagCore_decLoss_pos_ae {L : ℕ} (M : Fin (L + 1 + 1 + 1) → ℕ) (t j : ℕ)
    (ht1 : 1 ≤ t) (hnd : ∀ i, 1 ≤ M i) :
    ∀ᵐ z ∂(volume.restrict (paramsBoxM (redChain (t + j) M) 1)),
      ∀ᵐ v ∂(volume.restrict (unitBox 1)),
        0 < (cornerComparator (redChain (t + j) M) (![1] : Fin 1 → ℕ)
            (![minAdm (redChain (t + j) M) - 1] : Fin 1 → ℕ)).decLoss v z := by
  classical
  -- Every reduced width is `≥ 1` (`redChain u M 0 = u ≥ 1` via `ht1`; deeper widths via `hnd`).
  have hposW : ∀ s, 1 ≤ redChain (t + j) M s := by
    intro s
    refine Fin.cases ?_ (fun i => ?_) s
    · rw [redChain_zero]; omega
    · rw [redChain_succ]; exact hnd _
  -- The endpoint witness index for the comparator's nonempty `ι`.
  have hu1 : 0 < redChain (t + j) M 0 := by rw [redChain_zero]; omega
  have hlastw : redChain (t + j) M (Fin.last (L + 1)) = M (Fin.last (L + 1 + 1)) := by
    rw [← Fin.succ_last, redChain_succ, Fin.succ_last, Fin.succ_last]
  have hlast1 : 0 < redChain (t + j) M (Fin.last (L + 1)) := by rw [hlastw]; exact hnd _
  set i₀ : Fin (redChain (t + j) M 0) × Fin (redChain (t + j) M (Fin.last (L + 1)))
      := (⟨0, hu1⟩, ⟨0, hlast1⟩) with hi₀
  -- `prod (redChain u M) z ≠ 0` a.e.: the core polynomial is nonzero (all widths ≥ 1), so its zero set
  -- is null (`DeepestCoreNonvanishing`), pulled back along the measure-preserving flatten.
  obtain ⟨Aw, hAw⟩ := dlnLoss_deepest_core_ne_zero_witness (redChain (t + j) M) hposW
  have hP_ne : corePoly (redChain (t + j) M) ≠ 0 := by
    intro hP0
    apply hAw
    have he := eval_corePoly (redChain (t + j) M) (paramsEquivFlat (redChain (t + j) M) Aw)
    rw [hP0, map_zero] at he
    rw [show (paramsEquivFlat (redChain (t + j) M)).symm (paramsEquivFlat (redChain (t + j) M) Aw)
        = Aw from by simp] at he
    exact he.symm
  have hdf : ∀ A, dlnLoss (redChain (t + j) M)
      (0 : Matrix (Fin (redChain (t + j) M 0)) (Fin (redChain (t + j) M (Fin.last (L + 1)))) ℝ) A
      = frobSq (prod (redChain (t + j) M) A) := by
    intro A
    simp only [dlnLoss, frobSq, Matrix.sub_apply, Matrix.zero_apply, sub_zero]
  have haeflat := MvPolynomial.ae_eval_ne_zero (corePoly (redChain (t + j) M)) hP_ne
  have haeP : ∀ᵐ A ∂(volume : Measure (Params (redChain (t + j) M))),
      frobSq (prod (redChain (t + j) M) A) ≠ 0 := by
    have hpull := (measurePreserving_paramsEquivFlat (redChain (t + j) M)).quasiMeasurePreserving.ae
      haeflat
    filter_upwards [hpull] with A hA
    rw [eval_corePoly] at hA
    rw [show (paramsEquivFlat (redChain (t + j) M)).symm (paramsEquivFlat (redChain (t + j) M) A)
        = A from by simp, hdf] at hA
    exact hA
  -- `v 0 ≠ 0` a.e. on the unit box (the singleton `{0}` is Lebesgue-null; transport by `funUnique`).
  have hv0 : ∀ᵐ v ∂(volume : Measure (Fin 1 → ℝ)), v 0 ≠ 0 := by
    have h1 : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ 0 := by
      rw [ae_iff]; simp
    have hpull := (volume_preserving_funUnique (Fin 1) ℝ).quasiMeasurePreserving.ae h1
    filter_upwards [hpull] with v hv
    simpa using hv
  -- Assemble: `decLoss v z = commonDivisor(v)² · frobSq(prod z)` (both factors `> 0` a.e.).
  refine (ae_restrict_of_ae haeP).mono (fun z hzne => ?_)
  have hzpos : 0 < frobSq (prod (redChain (t + j) M) z) :=
    lt_of_le_of_ne (frobSq_nonneg _) (Ne.symm hzne)
  refine (ae_restrict_of_ae hv0).mono (fun v hvne => ?_)
  letI := (cornerComparator (redChain (t + j) M) (![1] : Fin 1 → ℕ)
    (![minAdm (redChain (t + j) M) - 1] : Fin 1 → ℕ)).fι
  letI := (cornerComparator (redChain (t + j) M) (![1] : Fin 1 → ℕ)
    (![minAdm (redChain (t + j) M) - 1] : Fin 1 → ℕ)).fν
  haveI : Nonempty (cornerComparator (redChain (t + j) M) (![1] : Fin 1 → ℕ)
    (![minAdm (redChain (t + j) M) - 1] : Fin 1 → ℕ)).ι := ⟨i₀⟩
  rw [cornerComparator_decLoss (redChain (t + j) M) (![1] : Fin 1 → ℕ)
    (![minAdm (redChain (t + j) M) - 1] : Fin 1 → ℕ) i₀ v z]
  have hd1 : (cornerComparator (redChain (t + j) M) (![1] : Fin 1 → ℕ)
      (![minAdm (redChain (t + j) M) - 1] : Fin 1 → ℕ)).d = 1 := rfl
  haveI hne0 : NeZero (cornerComparator (redChain (t + j) M) (![1] : Fin 1 → ℕ)
      (![minAdm (redChain (t + j) M) - 1] : Fin 1 → ℕ)).d := ⟨by rw [hd1]; omega⟩
  haveI hss : Subsingleton (Fin (cornerComparator (redChain (t + j) M) (![1] : Fin 1 → ℕ)
      (![minAdm (redChain (t + j) M) - 1] : Fin 1 → ℕ)).d) := by rw [hd1]; infer_instance
  have hcd : 0 < commonDivisor
      (cornerComparator (redChain (t + j) M) (![1] : Fin 1 → ℕ)
        (![minAdm (redChain (t + j) M) - 1] : Fin 1 → ℕ)).carrier.supp v := by
    unfold commonDivisor
    apply Finset.prod_pos
    intro ℓ _
    refine pow_pos (abs_pos.mpr ?_) _
    have heq : v ℓ = v (0 : Fin (cornerComparator (redChain (t + j) M) (![1] : Fin 1 → ℕ)
        (![minAdm (redChain (t + j) M) - 1] : Fin 1 → ℕ)).d) := by
      congr 1; exact Subsingleton.elim ℓ 0
    rw [heq]; exact hvne
  exact mul_pos (pow_pos hcd 2) hzpos

/-- **S1-good (the ISOLATED sorry) — the head-split spine→core reduction, at a binding cut on shell `j`,
in the good-chain (non-waist) scope.** For a legal binding cut `t★` (`ht`) and shell index
`j ≤ r = min(M₀−t★, M₁−t★)` (`hj`), the cut-`u` (`u = t★+j`) / shell-`j` spine integrand is bounded by a
FINITE constant `C_hle` times L1's off-sector-core integrand, for head-split data satisfying the L1 +
comparator hypotheses. This is the ~65–75%-genuinely-new decorated-peel head-split change-of-variables
(`RouteMSJDecorated`, resolved by `s1-spine-headsplit-cert.md` + `s1-Chle-angular-integrability-cert.md`):
the row-split `A' ↔ (z, A_cor)` via `blockSplitEquiv κ`; `prod_headSplit` exposes the corank block
`Q_b = A_cor·Z_deep`; the P-radial blow-up (`P = commonDivisor(v)·P̂`, det-1 clear) reorganizes the pivot
energy `frobSq(P·Q_p)` to `commonDivisor(v)²·frobSq(Q̃_p) = decLoss v z` plus the Jacobian monomial
`∏|v_ℓ|^{jc_ℓ}`; `B₁₂` absorbs exactly into the Γ-shear (`Γ' = Γ + C·P⁻¹B₁₂`); the `C`/angular directions
integrate to the finite `C_hle`; the piecewise `Zf` (`= Z_deep` on the good set `G`, fixed full-rank `V`
off `G`) makes L1's `∀z` rank/PSD hyps literally TRUE at the rescaled floor `ε' = ε/√(M₁M₂)`.

**Scope (LOAD-BEARING, per the certs).** `hpiv` (`minAdm (redChain u M) ≤ u·tailMinWidth M`, the pivot
criterion) gates `C_hle < ⊤` — it is STRICTLY stronger than convergence on `M₂>M₁` wide chains
(`s1-Chle-cert` §6, witness `(3,3,4,4)`); `hcvg`/`hrange` encode the `hconv` clause's TWO parts (cert B.4):
`a+b ≤ m` (corank convergence) and `m ≤ M₂` (range/nonvacuity — else the shell `S_j` is EMPTY and the
existential is unsatisfiable), with `m = min(M₁,n) − j`. Waists (`hpiv` fails) are a SEPARATE base case
(`deeperFlag_waist`, SVD-qPeel, task #156), NOT this theorem. -/
theorem deeperFlag_spineToCore {L : ℕ} (M : Fin (L + 1 + 1 + 1) → ℕ) (t j : ℕ)
    (κ : Fin (t + j) ↪ Fin (M 1)) {ε : ℝ} (hε : 0 < ε) (c' : ℝ)
    (ht : t ≤ min (M 0) (M 1)) (hj : j ≤ min (M 0 - t) (M 1 - t))
    (ht1 : 1 ≤ t) (hnd : ∀ i, 1 ≤ M i)
    (hpiv : minAdm (redChain (t + j) M) ≤ (t + j) * tailMinWidth M)
    (hcvg : (M 0 - (t + j)) + (M 1 - (t + j))
        ≤ min (M 1) (M (Fin.last (L + 1 + 1))) - j)
    (hrange : min (M 1) (M (Fin.last (L + 1 + 1))) - j ≤ M 2) :
    ∃ (M₂ m n d : ℕ) (ε' : ℝ) (k jc : Fin d → ℕ) (C_hle : ℝ≥0∞)
      (Zf : Params (redChain (t + j) M) → Matrix (Fin M₂) (Fin n) ℝ)
      (Ccrossf : Params (redChain (t + j) M) → Matrix (Fin (M 0 - (t + j))) (Fin n) ℝ)
      (U_sf : Params (redChain (t + j) M) → Matrix (Fin M₂) (Fin m) ℝ)
      (sΓf : Params (redChain (t + j) M) → Set (Fin (M 0 - (t + j)) → Fin (M 1 - (t + j)) → ℝ))
      (_i₀ : Fin ((redChain (t + j) M) 0) × Fin ((redChain (t + j) M) (Fin.last (L + 1)))),
      0 < ε' ∧ C_hle < ⊤
      ∧ (∀ z, (U_sf z)ᵀ * U_sf z = 1) ∧ (M 1 - (t + j) ≤ m) ∧ (m ≤ M₂) ∧ (∀ z, m ≤ (Zf z).rank)
      ∧ (∀ z, (Zf z * (Zf z)ᵀ - (ε' ^ 2) • (U_sf z * (U_sf z)ᵀ)).PosSemidef)
      ∧ (((M 0 - (t + j) : ℕ) : ℝ) < (m : ℝ) - ((M 1 - (t + j) : ℕ) : ℝ) + 1)
      ∧ (∀ᵐ z ∂(volume.restrict (paramsBoxM (redChain (t + j) M) 1)),
          ∀ᵐ v ∂(volume.restrict (unitBox d)),
            0 < (cornerComparator (redChain (t + j) M) k jc).decLoss v z)
      ∧ (1 ≤ d)
      ∧ ((minAdm (redChain (t + j) M) : ℝ≥0∞) / 2 ≤ monomialThreshold d k jc)
      ∧ shellSpineIntegrand M (t + j) κ ε (min (M 0 - t) (M 1 - t)) ⟨j, Nat.lt_succ_of_le hj⟩ c'
          ≤ C_hle * deeperFlagCoreIntegrand M (t + j) k jc Zf Ccrossf sΓf c' := by
  classical
  -- The rescaled floor `ε' = ε/√(M₁·M₂)` is positive.
  have hM1 : (1 : ℕ) ≤ M 1 := hnd 1
  have hM2 : (1 : ℕ) ≤ M 2 := hnd 2
  have hprodpos : (0 : ℝ) < (M 1 : ℝ) * (M 2 : ℝ) := by
    have : (0 : ℝ) < (M 1 : ℝ) := by exact_mod_cast hM1
    have : (0 : ℝ) < (M 2 : ℝ) := by exact_mod_cast hM2
    positivity
  have hsqrtpos : (0 : ℝ) < Real.sqrt ((M 1 : ℝ) * (M 2 : ℝ)) := Real.sqrt_pos.mpr hprodpos
  set ε' : ℝ := ε / Real.sqrt ((M 1 : ℝ) * (M 2 : ℝ)) with hε'def
  have hε' : 0 < ε' := div_pos hε hsqrtpos
  -- Width bookkeeping: `M₂ = dropHead (redChain u M) 0 = M 2`, `n = … = M_last`.
  have hM₂eq : dropHead (redChain (t + j) M) 0 = M 2 := dropHead_redChain_zero M (t + j)
  have hneq : dropHead (redChain (t + j) M) (Fin.last L) = M (Fin.last (L + 1 + 1)) :=
    dropHead_redChain_last M (t + j)
  set m : ℕ := min (M 1) (M (Fin.last (L + 1 + 1))) - j with hmdef
  have hmM₂ : m ≤ dropHead (redChain (t + j) M) 0 := by rw [hM₂eq]; exact hrange
  have hmn : m ≤ dropHead (redChain (t + j) M) (Fin.last L) := by rw [hneq, hmdef]; omega
  -- The deep-tail product is measurable (entrywise: continuous `prod`-entry ∘ head-split projection).
  have hproj : Measurable (fun z : Params (redChain (t + j) M) =>
      (paramsHeadSplit (redChain (t + j) M) z).2) :=
    measurable_snd.comp (paramsHeadSplit (redChain (t + j) M)).measurable
  have hZdeepMeas : Measurable (deeperFlagZdeep M (t + j)) :=
    measurable_pi_lambda _ (fun i => measurable_pi_lambda _ (fun jj =>
      ((continuous_prod (dropHead (redChain (t + j) M))).matrix_elem i jj).measurable.comp hproj))
  -- Brick F: the measurable piecewise `m`-frame.
  obtain ⟨Zf, U_sf, _hZfMeas, _hUsMeas, hUs, hrank, hfloor, hagree⟩ :=
    exists_headSplitFrame (m := m) hmM₂ hmn hε' (deeperFlagZdeep M (t + j)) hZdeepMeas
  -- Brick D: the head-split domination with finite constant.
  obtain ⟨Ccrossf, sΓf, C_hle, hChle, hdom⟩ :=
    headSplit_domination M t j κ hε c' ht hj ht1 hnd hpiv hcvg hrange hε' Zf U_sf
      _hZfMeas _hUsMeas hUs hrank hfloor hagree
  -- The endpoint witness index (`redChain u M 0 = u ≥ 1`; `redChain u M last = M_last ≥ 1`).
  have hu1 : 0 < redChain (t + j) M 0 := by rw [redChain_zero]; omega
  have hlastw : redChain (t + j) M (Fin.last (L + 1)) = M (Fin.last (L + 1 + 1)) := by
    rw [← Fin.succ_last, redChain_succ, Fin.succ_last, Fin.succ_last]
  have hlast1 : 0 < redChain (t + j) M (Fin.last (L + 1)) := by rw [hlastw]; exact hnd _
  refine ⟨dropHead (redChain (t + j) M) 0, m, dropHead (redChain (t + j) M) (Fin.last L), 1, ε',
    (![1] : Fin 1 → ℕ), (![minAdm (redChain (t + j) M) - 1] : Fin 1 → ℕ), C_hle, Zf, Ccrossf, U_sf,
    sΓf, (⟨0, hu1⟩, ⟨0, hlast1⟩), hε', hChle, hUs, ?hbm, hmM₂, hrank, hfloor, ?hconv, ?hpos,
    le_refl 1, ?hbeta, hdom⟩
  case hbm => omega
  case hconv =>
    have h1 : ((M 0 - (t + j) : ℕ) : ℝ) + ((M 1 - (t + j) : ℕ) : ℝ) ≤ (m : ℝ) := by
      exact_mod_cast hcvg
    linarith [h1]
  case hpos => exact deeperFlagCore_decLoss_pos_ae M t j ht1 hnd
  case hbeta =>
    rw [monomialThreshold_eq_iInf_axisRatio]
    refine le_iInf (fun jidx => ?_)
    have hk1 : (![1] : Fin 1 → ℕ) jidx = 1 := by simp [Matrix.cons_val_fin_one]
    have hjc : (![minAdm (redChain (t + j) M) - 1] : Fin 1 → ℕ) jidx
        = minAdm (redChain (t + j) M) - 1 := by simp [Matrix.cons_val_fin_one]
    rw [hk1, hjc]
    rcases Nat.eq_zero_or_pos (minAdm (redChain (t + j) M)) with hm0 | hmpos
    · rw [hm0]; simp
    · rw [show minAdm (redChain (t + j) M) - 1
            = (minAdm (redChain (t + j) M) - 1 + 1) - 1 from by omega,
        axisRatio_regularSeq (minAdm (redChain (t + j) M) - 1 + 1) (by omega),
        show minAdm (redChain (t + j) M) - 1 + 1 = minAdm (redChain (t + j) M) from by omega]

/-- **The headline `deeperFlag_shell_le` — the T-Obl3b off-sector shell-stratification mountain (per
shell, corrected deeper-cut route), scoped to good (non-waist) chains.** At a legal binding cut `t★` and
shell `j ≤ r`, the literal cut-`u` (`u = t★+j`) / shell-`j` spine integrand is dominated by a finite
constant times the reduced comparator's integral at the shifted exponent `c' − ½·peelCharge M u`, with the
comparator `adm`-admissible (so the decorated IH closes it in the compose). Proof =
`deeperFlag_spineToCore` (S1-good) ∘ `deeperFlag_shell_core_le` (L1, the clean analytic core, consumed at
the rescaled floor `ε'`) + `cornerComparator_adm`, folding `C := C_hle · C_L1`. The `hpiv`/`hcvg`/`hrange`
scope (pivot criterion + convergence + range) is the good-chain condition; waists route through the
separate `deeperFlag_waist` SVD-qPeel base case (task #156). `hc'` is the freed-corner peel regime. -/
theorem deeperFlag_shell_le {L : ℕ} (M : Fin (L + 1 + 1 + 1) → ℕ) (t j : ℕ)
    (κ : Fin (t + j) ↪ Fin (M 1)) {ε : ℝ} (hε : 0 < ε) (c' : ℝ)
    (ht : t ≤ min (M 0) (M 1)) (hj : j ≤ min (M 0 - t) (M 1 - t))
    (ht1 : 1 ≤ t) (hnd : ∀ i, 1 ≤ M i)
    (hpiv : minAdm (redChain (t + j) M) ≤ (t + j) * tailMinWidth M)
    (hcvg : (M 0 - (t + j)) + (M 1 - (t + j))
        ≤ min (M 1) (M (Fin.last (L + 1 + 1))) - j)
    (hrange : min (M 1) (M (Fin.last (L + 1 + 1))) - j ≤ M 2)
    (hc' : (((M 0 - (t + j)) * (M 1 - (t + j)) : ℕ) : ℝ) / 2 < c') :
    ∃ (d : ℕ) (k jc : Fin d → ℕ) (C : ℝ≥0∞), C < ⊤
      ∧ adm (L + 1) (redChain (t + j) M) (cornerComparator (redChain (t + j) M) k jc)
      ∧ shellSpineIntegrand M (t + j) κ ε (min (M 0 - t) (M 1 - t)) ⟨j, Nat.lt_succ_of_le hj⟩ c'
          ≤ C * (cornerComparator (redChain (t + j) M) k jc).integral
              (c' - (peelCharge M (t + j) : ℝ) / 2) := by
  obtain ⟨M₂, m, n, d, ε', k, jc, C_hle, Zf, Ccrossf, U_sf, sΓf, i₀, hε', hChle, hUs, hbm, hmM, hmZ,
    hshell, hconv, hpos, hd, hbeta, hle⟩ :=
    deeperFlag_spineToCore M t j κ hε c' ht hj ht1 hnd hpiv hcvg hrange
  obtain ⟨C, hCfin, hcore⟩ :=
    deeperFlag_shell_core_le M (t + j) k jc Zf Ccrossf U_sf sΓf hε' hUs hbm hmM hmZ hshell c'
      hconv hc' hpos
  refine ⟨d, k, jc, C_hle * C, ENNReal.mul_lt_top hChle hCfin,
    cornerComparator_adm (redChain (t + j) M) k jc hd i₀ hbeta, ?_⟩
  calc shellSpineIntegrand M (t + j) κ ε (min (M 0 - t) (M 1 - t)) ⟨j, Nat.lt_succ_of_le hj⟩ c'
      ≤ C_hle * deeperFlagCoreIntegrand M (t + j) k jc Zf Ccrossf sΓf c' := hle
    _ ≤ C_hle * (C * (cornerComparator (redChain (t + j) M) k jc).integral
          (c' - (peelCharge M (t + j) : ℝ) / 2)) := mul_le_mul_left' hcore C_hle
    _ = C_hle * C * (cornerComparator (redChain (t + j) M) k jc).integral
          (c' - (peelCharge M (t + j) : ℝ) / 2) := (mul_assoc _ _ _).symm

end DLNFibre.DLN.RLCT
