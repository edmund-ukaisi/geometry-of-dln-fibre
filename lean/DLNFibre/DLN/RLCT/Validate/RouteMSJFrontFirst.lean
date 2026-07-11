import DLNFibre.DLN.RLCT.Validate.RouteMSJFrontSpectral
import DLNFibre.DLN.RLCT.Validate.RouteMSJTwoBlockRadial
import DLNFibre.DLN.RLCT.Validate.RouteMSJCorankResidual

set_option linter.style.longLine false

/-!
# `DLNFibre.DLN.RLCT.Validate.RouteMSJFrontFirst` — the front-first box-exponent bound `g(Q)` (shared)

**Thread `genm-sj5-schur`, the front-first joint route (bridge-derisk §4), SHARED by lane-1 (#121) and
the §5 lane (#125).** After recombining `(x,Γ)→A₀` (banked MP shear `chartInner_schurShearFree_eq`),
the joint front-chart integral is `g(Q) = ∫_{A₀∈box} frobSq(A₀·Q)^{−c'} dA₀`, and the load-bearing
bound is `g(Q) ≤ C·σ_q(Q)^{−α}`, `α = max{0, 2c' − M₀(r−1)}` (the box keeps the collapsing direction
`O(1)`, no `σ⁻¹`; bridge-derisk §4). The `A'`-tube then closes it (`∫_{A'} σ_q^{−α} < ∞ ⟺ α < D`,
banked `minAdm_eq_frontPeel` + #127).

## What lands here (the CONDITIONAL bound — safe regardless of the sector-from-region adjudication)

The sector `sjSector κ P` is a hypothesis ON `P` (the tail), not on `A₀`, so the conditional bound
needs NO `A₀`-cover — the two-block lower bound holds for every `A₀`.

* **`twoBlockLoss`** — the two-block form of `frobSq_ge_twoBlock_of_sector`: the collapsing v-block
  (weight `⨅ λ = sigMin P²`) plus the bounded-below u-block (weight `κ²`), in the Gram spectral basis.
* **`twoBlockLoss_le_frobSq`, `twoBlockLoss_pos_of_ne`** — the pure-algebra facts (dominates `frobSq`
  on the sector; strictly positive off `{A₀ = 0}` when `P` is full-rank).
* **`front_frobSq_le_twoBlock`** — the a.e. integrand transfer (rpow-antitone, `{A₀=0}` null).

## Steps 3–4: the reshape + `twoBlock_radial_le` (complete, sorry-free)

* **`colSplitReshape`** — the measure-preserving `(Fin m → Fin (r'+1) → ℝ) ≃ᵐ EuclideanSpace(m·r') ×
  EuclideanSpace(m)` splitting the collapsing column `c` (`v`-block) from the rest (`u`-block, flattened):
  per-row `piFinSuccAbove` + `arrowProdEquivProdArrow` + `prodComm` + `eMatFlat`/`toLp`, with norm
  identities `‖u‖² = ∑_{j≠c}∑ᵢ(Γ i j)²`, `‖v‖² = ∑ᵢ(Γ i c)²` (`colSplitReshape_normSq_{fst,snd}`).
* **`colSplit_reshape_le`** — the Frobenius-ball two-block integral ≤ the product-ball integral
  `twoBlock_radial_le` consumes (reshape into `ball_u × ball_v`).
* **`lintegral_frobBall_orthRightMul`** — the ball-restricted orthogonal CoV `A₀ ↦ A₀·U` (indicator
  trick on the banked full-space `lintegral_comp_orthRightMulₚ`; the ball is `U`-invariant).
* **`frontBox_abstract`** — the measure core over ABSTRACT orthogonal `U` and small-value `σ` (perf
  restatement: no spectral term in the `whnf`/`isDefEq` checks).
* **`frontBox_twoBlock_le`** — `∫_{A₀∈box} twoBlockLoss^{−c'} ≤ C·sigMin P^{−α'}`, the thin
  instantiation of `frontBox_abstract` at `U = eigenvectorUnitary`, `σ = sigMin P`.

* **`frontFirst_g_le_of_sector`** — the conditional `g(Q)` bound. Consumed by BOTH lanes. (Only step 6,
  the `sjSector`-from-region adjudication, remains a hypothesis, held pending genm-sj5-cover cert #130.)
-/

namespace DLNFibre.DLN.RLCT

open Matrix MeasureTheory
open scoped BigOperators ENNReal

variable {m r n : ℕ}

/-- **The abstract two-block loss** over a plain spectral triple `(lam, U, c)` — the v-block (weight
`⨅ lam`) plus the u-block (weight `κ²`). Stating the loss over abstract `lam, U, c` (rather than the
spectral `(posSemidef_mul_transpose P).eigenvalues/eigenvectorUnitary` inline) is the perf-aware
restatement: the heavy spectral terms become single bound arguments, so proofs never re-elaborate them
(the `isDefEq`/`whnf` heartbeat-timeout fix). -/
noncomputable def twoBlockLossAux (lam : Fin r → ℝ) (U : Matrix (Fin r) (Fin r) ℝ)
    (c : Fin r) (κ : ℝ) (A₀ : Matrix (Fin m) (Fin r) ℝ) : ℝ :=
  (⨅ i, lam i) * (∑ i, ((A₀ * U) i c) ^ 2)
    + κ ^ 2 * (∑ j ∈ Finset.univ.erase c, ∑ i, ((A₀ * U) i j) ^ 2)

/-- **`twoBlockLossAux` is strictly positive off `{A₀ = 0}`** (abstract; no spectral term, so no
timeout): `⨅ lam > 0`, `κ > 0`, `U` a unit ⟹ `A₀ ≠ 0` gives `A₀·U ≠ 0`, a nonzero column, positivity. -/
theorem twoBlockLossAux_pos_of_ne (lam : Fin r → ℝ) (U : Matrix (Fin r) (Fin r) ℝ)
    (c : Fin r) {κ : ℝ} (A₀ : Matrix (Fin m) (Fin r) ℝ)
    (hlam : 0 < ⨅ i, lam i) (hκ : 0 < κ) (hUunit : IsUnit U) (hA₀ : A₀ ≠ 0) :
    0 < twoBlockLossAux lam U c κ A₀ := by
  have hAU : A₀ * U ≠ 0 := by
    intro h
    obtain ⟨V, hV⟩ := hUunit.exists_right_inv
    apply hA₀
    have hz : A₀ * U * V = 0 := by rw [h, Matrix.zero_mul]
    rwa [Matrix.mul_assoc, hV, Matrix.mul_one] at hz
  obtain ⟨i, j, hij⟩ : ∃ i j, (A₀ * U) i j ≠ 0 := by
    by_contra h; push_neg at h; exact hAU (by ext i j; simp [h i j])
  have hcolpos : 0 < ∑ i', ((A₀ * U) i' j) ^ 2 :=
    Finset.sum_pos' (fun i' _ => sq_nonneg _)
      ⟨i, Finset.mem_univ i, by rw [← sq_abs]; exact pow_pos (abs_pos.mpr hij) 2⟩
  rw [twoBlockLossAux]
  have hnn2 : 0 ≤ κ ^ 2 * (∑ j ∈ Finset.univ.erase c, ∑ i, ((A₀ * U) i j) ^ 2) :=
    mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)
  have hnn1 : 0 ≤ (⨅ i, lam i) * (∑ i, ((A₀ * U) i c) ^ 2) :=
    mul_nonneg hlam.le (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  rcases eq_or_ne j c with hjc | hjc
  · subst hjc
    exact add_pos_of_pos_of_nonneg (mul_pos hlam hcolpos) hnn2
  · refine add_pos_of_nonneg_of_pos hnn1 (mul_pos (pow_pos hκ 2) ?_)
    exact Finset.sum_pos' (fun j' _ => Finset.sum_nonneg (fun i' _ => sq_nonneg _))
      ⟨j, Finset.mem_erase.mpr ⟨hjc, Finset.mem_univ j⟩, hcolpos⟩

/-- **The two-block loss** for the tail `P` — `twoBlockLossAux` at the Gram spectral data of `P·Pᵀ`
(eigenvalues, eigenvectorUnitary, collapsing index). -/
noncomputable def twoBlockLoss (P : Matrix (Fin r) (Fin n) ℝ) (hr : 0 < r) (κ : ℝ)
    (A₀ : Matrix (Fin m) (Fin r) ℝ) : ℝ :=
  twoBlockLossAux (posSemidef_mul_transpose P).isHermitian.eigenvalues
    ((posSemidef_mul_transpose P).isHermitian.eigenvectorUnitary : Matrix (Fin r) (Fin r) ℝ)
    (collapseIndex P hr) κ A₀

/-- `twoBlockLoss ≤ frobSq (A₀·P)` on the sector (restatement of `frobSq_ge_twoBlock_of_sector`). -/
theorem twoBlockLoss_le_frobSq (A₀ : Matrix (Fin m) (Fin r) ℝ) (P : Matrix (Fin r) (Fin n) ℝ)
    (hr : 0 < r) {κ : ℝ} (hsec : sjSector κ P hr) :
    twoBlockLoss P hr κ A₀ ≤ frobSq (A₀ * P) := by
  rw [twoBlockLoss, twoBlockLossAux]
  exact frobSq_ge_twoBlock_of_sector A₀ P hr hsec

/-- **`twoBlockLoss` is strictly positive off `{A₀ = 0}`** (full-rank `P`: `0 < sigMin P`, so
`⨅ λ = sigMin P² > 0`). Instantiates `twoBlockLossAux_pos_of_ne` at the spectral data —
`Unitary.isUnit_coe` for the unit `U`, `sigMin_sq_eq_iInf_eigenvalues` for `⨅ λ > 0`. -/
theorem twoBlockLoss_pos_of_ne (A₀ : Matrix (Fin m) (Fin r) ℝ) (P : Matrix (Fin r) (Fin n) ℝ)
    (hr : 0 < r) {κ : ℝ} (hκ : 0 < κ) (hσ : 0 < sigMin P) (hA₀ : A₀ ≠ 0) :
    0 < twoBlockLoss P hr κ A₀ := by
  rw [twoBlockLoss]
  refine twoBlockLossAux_pos_of_ne _ _ _ A₀ ?_ hκ Unitary.isUnit_coe hA₀
  rw [← sigMin_sq_eq_iInf_eigenvalues P hr]; exact pow_pos hσ 2

/-- **The a.e. integrand transfer (steps 1–2).** Given the sector and full-rank `P` (`0 < sigMin P`),
the front box integral of `frobSq(A₀·P)^{−c'}` is bounded by that of `twoBlockLoss^{−c'}`. Off the null
set `{A₀ = 0}`: `twoBlockLoss ≤ frobSq(A₀·P)`, both `> 0`, so `frobSq^{−c'} ≤ twoBlockLoss^{−c'}`
(`Real.rpow_le_rpow_of_nonpos`). -/
theorem front_frobSq_le_twoBlock (P : Matrix (Fin r) (Fin n) ℝ) (hr : 0 < r) {κ c' : ℝ}
    (hκ : 0 < κ) (hσ : 0 < sigMin P) (hsec : sjSector κ P hr) (hc' : 0 < c') :
    (∫⁻ A₀ in matBox m r 1, ENNReal.ofReal ((frobSq (Matrix.of A₀ * P)) ^ (-c')))
      ≤ ∫⁻ A₀ in matBox m r 1, ENNReal.ofReal ((twoBlockLoss P hr κ (Matrix.of A₀)) ^ (-c')) := by
  refine lintegral_mono_ae ((ae_restrict_iff' (matBox_measurableSet m r 1)).mpr ?_)
  filter_upwards with A₀ _hmem
  by_cases hA₀ : Matrix.of A₀ = 0
  · rw [show frobSq (Matrix.of A₀ * P) = twoBlockLoss P hr κ (Matrix.of A₀) from by
      rw [hA₀]; simp [twoBlockLoss, twoBlockLossAux, frobSq]]
  · have hpos : 0 < twoBlockLoss P hr κ (Matrix.of A₀) :=
      twoBlockLoss_pos_of_ne (Matrix.of A₀) P hr hκ hσ hA₀
    have hle : twoBlockLoss P hr κ (Matrix.of A₀) ≤ frobSq (Matrix.of A₀ * P) :=
      twoBlockLoss_le_frobSq (Matrix.of A₀) P hr hsec
    exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_nonpos hpos hle (by linarith))

/-! ## Part D — the column-split reshape (matrix box → the two-block Euclidean product) -/

/-- **The column-split reshape** `(Fin m → Fin (r'+1) → ℝ) ≃ᵐ (EuclideanSpace (m·r') × EuclideanSpace m)`
sending `Γ` to `(u, v)` with `v` = the collapsing column `c` and `u` = the flattened other columns
(`Fin r'` reindexed off `c` by `Fin.succAbove`). Composite: per-row `piFinSuccAbove` at `c` (split each
row's `Fin (r'+1)` into the `c`-entry and the `Fin r'` rest), distribute the arrow over the product
(`arrowProdEquivProdArrow`), swap to `(rest, col c)` (`prodComm`), then flatten (`eMatFlat`) + `toLp` the
`u`-block and `toLp` the `v`-block. Every node is a banked measure-preserving equiv. -/
noncomputable def colSplitReshape (m r' : ℕ) (c : Fin (r' + 1)) :
    (Fin m → Fin (r' + 1) → ℝ) ≃ᵐ
      (EuclideanSpace ℝ (Fin (m * r')) × EuclideanSpace ℝ (Fin m)) :=
  (MeasurableEquiv.arrowCongr' (Equiv.refl (Fin m))
      (MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) c)).trans
    ((MeasurableEquiv.arrowProdEquivProdArrow ℝ (Fin r' → ℝ) (Fin m)).trans
      ((@MeasurableEquiv.prodComm (Fin m → ℝ) (Fin m → Fin r' → ℝ) _ _).trans
        (MeasurableEquiv.prodCongr
          ((eMatFlat m r').trans (MeasurableEquiv.toLp 2 (Fin (m * r') → ℝ)))
          (MeasurableEquiv.toLp 2 (Fin m → ℝ)))))

/-- `colSplitReshape` is measure-preserving (composite of banked measure-preserving nodes). Assembled
with `MeasurePreserving.comp`; the composite `⇑e3 ∘ Prod.swap ∘ ⇑e1 ∘ ⇑e0` is defeq to `⇑colSplitReshape`
(the `MeasurableEquiv.trans`/`prodCongr`/`prodComm` coes reduce to composition/`Prod.map`/`Prod.swap`). -/
theorem measurePreserving_colSplitReshape (m r' : ℕ) (c : Fin (r' + 1)) :
    MeasurePreserving (colSplitReshape m r' c)
      (volume : Measure (Fin m → Fin (r' + 1) → ℝ))
      (volume : Measure (EuclideanSpace ℝ (Fin (m * r')) × EuclideanSpace ℝ (Fin m))) := by
  have h0 := volume_preserving_arrowCongr' (Equiv.refl (Fin m))
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (r' + 1) => ℝ) c)
      (volume_preserving_piFinSuccAbove (fun _ : Fin (r' + 1) => ℝ) c)
  have h1 := volume_measurePreserving_arrowProdEquivProdArrow ℝ (Fin r' → ℝ) (Fin m)
  have h2 : MeasurePreserving (Prod.swap : ((Fin m → ℝ) × (Fin m → Fin r' → ℝ)) →
      ((Fin m → Fin r' → ℝ) × (Fin m → ℝ))) volume volume :=
    MeasureTheory.Measure.measurePreserving_swap
  have hu := (PiLp.volume_preserving_toLp (Fin (m * r'))).comp (measurePreserving_eMatFlat m r')
  have h3 := hu.prod (PiLp.volume_preserving_toLp (Fin m))
  exact h3.comp (h2.comp (h1.comp h0))

/-- `‖toLp x‖² = ∑ᵢ (x i)²` for a real coordinate vector (the `EuclideanSpace` L2 norm). -/
theorem norm_sq_toLp {k : ℕ} (x : Fin k → ℝ) :
    ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin k))‖ ^ 2 = ∑ i, (x i) ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]

/-- The `v`-block of the reshape is `toLp` of the collapsing column `c`. -/
theorem colSplitReshape_snd (m r' : ℕ) (c : Fin (r' + 1)) (Γ : Fin m → Fin (r' + 1) → ℝ) :
    (colSplitReshape m r' c Γ).2 = WithLp.toLp 2 (fun i => Γ i c) := rfl

/-- The `u`-block of the reshape is `toLp` of the flattened off-`c` columns. -/
theorem colSplitReshape_fst (m r' : ℕ) (c : Fin (r' + 1)) (Γ : Fin m → Fin (r' + 1) → ℝ) :
    (colSplitReshape m r' c Γ).1
      = WithLp.toLp 2 (eMatFlat m r' (fun i j => Γ i (c.succAbove j))) := rfl

/-- `‖v-block‖² = ∑ᵢ (Γ i c)²`. -/
theorem colSplitReshape_normSq_snd (m r' : ℕ) (c : Fin (r' + 1)) (Γ : Fin m → Fin (r' + 1) → ℝ) :
    ‖(colSplitReshape m r' c Γ).2‖ ^ 2 = ∑ i, (Γ i c) ^ 2 := by
  rw [colSplitReshape_snd, norm_sq_toLp]

/-- `‖u-block‖² = ∑_{j ≠ c} ∑ᵢ (Γ i j)²` — the off-`c` columns (`Fin.succAbove` bijects `Fin r'` with
`univ.erase c`, and the flatten preserves the entry sum). -/
theorem colSplitReshape_normSq_fst (m r' : ℕ) (c : Fin (r' + 1)) (Γ : Fin m → Fin (r' + 1) → ℝ) :
    ‖(colSplitReshape m r' c Γ).1‖ ^ 2 = ∑ j ∈ Finset.univ.erase c, ∑ i, (Γ i j) ^ 2 := by
  have key : ∀ F : Fin (r' + 1) → ℝ,
      ∑ j : Fin r', F (c.succAbove j) = ∑ j ∈ Finset.univ.erase c, F j := by
    intro F
    have h1 : F c + ∑ j : Fin r', F (c.succAbove j) = ∑ j, F j :=
      (Fin.sum_univ_succAbove F c).symm
    have h2 : F c + ∑ j ∈ Finset.univ.erase c, F j = ∑ j, F j :=
      Finset.add_sum_erase _ F (Finset.mem_univ c)
    exact add_left_cancel (h1.trans h2.symm)
  rw [colSplitReshape_fst, norm_sq_toLp, ← frobSq_eq_flatSum]
  simp only [frobSq]
  rw [Finset.sum_comm]
  exact key (fun j => ∑ i, (Γ i j) ^ 2)

/-- **The column-split reshape bound (STAGE B).** The Frobenius-ball integral of the direct two-block
loss (collapsing column `c` weight `σ²`, off-`c` columns weight `κ²`) is bounded by the product-ball
integral `twoBlock_radial_le` consumes. Route: the integrand equals `H ∘ colSplitReshape` (norm
identities); the Frobenius ball `{frobSq Γ < R²}` maps into `ball_u R × ball_v R` (each block norm ≤
Frobenius norm); measure-preserving CoV. -/
theorem colSplit_reshape_le (m r' : ℕ) (c : Fin (r' + 1)) {σ κ c' R : ℝ} (hR : 0 < R) :
    (∫⁻ Γ in {Γ : Fin m → Fin (r' + 1) → ℝ | frobSq Γ < R ^ 2},
        ENNReal.ofReal ((σ ^ 2 * (∑ i, (Γ i c) ^ 2)
          + κ ^ 2 * (∑ j ∈ Finset.univ.erase c, ∑ i, (Γ i j) ^ 2)) ^ (-c')))
      ≤ ∫⁻ p in (Metric.ball (0 : EuclideanSpace ℝ (Fin (m * r'))) R
                  ×ˢ Metric.ball (0 : EuclideanSpace ℝ (Fin m)) R),
          ENNReal.ofReal ((κ ^ 2 * ‖p.1‖ ^ 2 + σ ^ 2 * ‖p.2‖ ^ 2) ^ (-c')) := by
  set e := colSplitReshape m r' c with he
  have hmp := measurePreserving_colSplitReshape m r' c
  set S : Set (Fin m → Fin (r' + 1) → ℝ) := {Γ | frobSq Γ < R ^ 2} with hS
  set H : (EuclideanSpace ℝ (Fin (m * r')) × EuclideanSpace ℝ (Fin m)) → ℝ≥0∞ :=
    fun p => ENNReal.ofReal ((κ ^ 2 * ‖p.1‖ ^ 2 + σ ^ 2 * ‖p.2‖ ^ 2) ^ (-c')) with hH
  -- S is measurable (`frobSq` is continuous)
  have hfrobmeas : Measurable (frobSq : (Fin m → Fin (r' + 1) → ℝ) → ℝ) := by
    unfold frobSq; fun_prop
  have hSmeas : MeasurableSet S := hfrobmeas measurableSet_Iio
  -- the direct integrand equals `H ∘ e` (norm identities)
  have hpt : ∀ Γ, ENNReal.ofReal ((σ ^ 2 * (∑ i, (Γ i c) ^ 2)
        + κ ^ 2 * (∑ j ∈ Finset.univ.erase c, ∑ i, (Γ i j) ^ 2)) ^ (-c')) = H (e Γ) := by
    intro Γ
    rw [hH]
    refine congrArg ENNReal.ofReal (congrArg (· ^ (-c')) ?_)
    rw [he, colSplitReshape_normSq_fst, colSplitReshape_normSq_snd]; ring
  -- Frobenius ball ⊆ preimage of the product of balls
  have hST : S ⊆ e ⁻¹' (Metric.ball (0 : EuclideanSpace ℝ (Fin (m * r'))) R
                          ×ˢ Metric.ball (0 : EuclideanSpace ℝ (Fin m)) R) := by
    intro Γ hΓ
    have hΓ' : frobSq Γ < R ^ 2 := hΓ
    simp only [Set.mem_preimage, Set.mem_prod, Metric.mem_ball, dist_zero_right]
    have hu2 : ‖(e Γ).1‖ ^ 2 < R ^ 2 := by
      rw [he, colSplitReshape_normSq_fst]
      calc ∑ j ∈ Finset.univ.erase c, ∑ i, (Γ i j) ^ 2
          ≤ ∑ j, ∑ i, (Γ i j) ^ 2 :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
              (fun j _ _ => Finset.sum_nonneg (fun i _ => sq_nonneg _))
        _ = frobSq Γ := by simp only [frobSq]; rw [Finset.sum_comm]
        _ < R ^ 2 := hΓ'
    have hv2 : ‖(e Γ).2‖ ^ 2 < R ^ 2 := by
      rw [he, colSplitReshape_normSq_snd]
      calc ∑ i, (Γ i c) ^ 2
          ≤ ∑ i, ∑ j, (Γ i j) ^ 2 :=
            Finset.sum_le_sum
              (fun i _ => Finset.single_le_sum (fun j _ => sq_nonneg _) (Finset.mem_univ c))
        _ = frobSq Γ := by simp only [frobSq]
        _ < R ^ 2 := hΓ'
    exact ⟨lt_of_pow_lt_pow_left₀ 2 hR.le hu2, lt_of_pow_lt_pow_left₀ 2 hR.le hv2⟩
  calc ∫⁻ Γ in S, ENNReal.ofReal ((σ ^ 2 * (∑ i, (Γ i c) ^ 2)
          + κ ^ 2 * (∑ j ∈ Finset.univ.erase c, ∑ i, (Γ i j) ^ 2)) ^ (-c'))
      = ∫⁻ Γ in S, H (e Γ) := setLIntegral_congr_fun hSmeas (fun Γ _ => hpt Γ)
    _ ≤ ∫⁻ Γ in e ⁻¹' (Metric.ball 0 R ×ˢ Metric.ball 0 R), H (e Γ) := lintegral_mono_set hST
    _ = ∫⁻ p in (Metric.ball 0 R ×ˢ Metric.ball 0 R), H p :=
        hmp.setLIntegral_comp_preimage_emb e.measurableEmbedding H _

/-- **Ball-restricted orthogonal right-multiplication CoV.** For orthogonal `U` (`U · Uᵀ = 1`) and any
measurable `g`, the Frobenius-ball integral is invariant under the per-row right-multiply `Γ ↦ Γ·U`
(the ball is `U`-invariant since `frobSq (Γ·U) = frobSq Γ`; indicator trick on the banked full-space
`lintegral_comp_orthRightMulₚ`). Kept standalone (abstract `g, U`) so its `isDefEq`/`whnf` cost is
bounded, not accumulated into the front-box `calc`. -/
theorem lintegral_frobBall_orthRightMul {m q : ℕ} (U : Matrix (Fin q) (Fin q) ℝ)
    (hUorth : U * Uᵀ = 1) (R : ℝ) (g : (Fin m → Fin q → ℝ) → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ Γ in {Γ : Fin m → Fin q → ℝ | frobSq Γ < R ^ 2}, g (fun i => Γ i ᵥ* U))
      = ∫⁻ Γ in {Γ : Fin m → Fin q → ℝ | frobSq Γ < R ^ 2}, g Γ := by
  set FB : Set (Fin m → Fin q → ℝ) := {Γ | frobSq Γ < R ^ 2} with hFB
  have hentry : ∀ (A₀ : Fin m → Fin q → ℝ) (i j), (Matrix.of A₀ * U) i j = (A₀ i ᵥ* U) j := by
    intro A₀ i j; rw [Matrix.mul_apply]; simp only [Matrix.of_apply]; rfl
  have hfrobU : ∀ A₀ : Fin m → Fin q → ℝ, frobSq (fun i => A₀ i ᵥ* U) = frobSq A₀ := by
    intro A₀
    have e1 : (fun i => A₀ i ᵥ* U) = (Matrix.of A₀ * U) := by
      funext i j; exact (hentry A₀ i j).symm
    rw [e1,
      show frobSq (Matrix.of A₀ * U)
          = Matrix.trace ((Matrix.of A₀ * U) * (Matrix.of A₀ * U)ᵀ) from frobSq_eq_trace _,
      show frobSq A₀ = Matrix.trace ((Matrix.of A₀) * (Matrix.of A₀)ᵀ) from frobSq_eq_trace _]
    congr 1
    rw [Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc U Uᵀ, hUorth, Matrix.one_mul]
  have hFBmeas : MeasurableSet FB := by
    have hfrobmeas : Measurable (frobSq : (Fin m → Fin q → ℝ) → ℝ) := by unfold frobSq; fun_prop
    exact hfrobmeas measurableSet_Iio
  have hfull := lintegral_comp_orthRightMulₚ m U hUorth (FB.indicator g) (hg.indicator hFBmeas)
  have hmem_iff : ∀ Γ : Fin m → Fin q → ℝ, (fun i => Γ i ᵥ* U) ∈ FB ↔ Γ ∈ FB := by
    intro Γ; change frobSq (fun i => Γ i ᵥ* U) < R ^ 2 ↔ frobSq Γ < R ^ 2; rw [hfrobU]
  have hLHS : (fun Γ => (FB.indicator g) (fun i => Γ i ᵥ* U))
      = FB.indicator (fun Γ => g (fun i => Γ i ᵥ* U)) := by
    funext Γ
    by_cases hΓ : Γ ∈ FB
    · rw [Set.indicator_of_mem ((hmem_iff Γ).mpr hΓ), Set.indicator_of_mem hΓ]
    · rw [Set.indicator_of_notMem (fun h => hΓ ((hmem_iff Γ).mp h)), Set.indicator_of_notMem hΓ]
  rw [← lintegral_indicator hFBmeas (fun Γ => g (fun i => Γ i ᵥ* U)), ← hLHS, hfull,
    lintegral_indicator hFBmeas]

/-- **The abstract front-box bound (steps 3–4, the measure core).** For ANY orthogonal `U`
(`U · Uᵀ = 1`), a collapsing column `c`, a small-value `0 < σ ≤ B`, and `max(0, 2c' − m·r') < α' < m`,
the box integral of the direct two-block loss (v-block = column `c` weight `σ²`, u-block = off-`c`
columns weight `κ²`, read off `A₀·U`) is `≤ C·σ^{−α'}`. Stating this over abstract `U, σ` (not the
`eigenvectorUnitary`/`sigMin P` inline) is the perf-aware restatement — the heavy spectral terms never
enter the measure-theory `whnf`/`isDefEq` checks (the heartbeat-timeout fix; see `lean/CLAUDE.md`).
Route: box ⊆ Frobenius ball; ball-restricted orthogonal CoV `A₀ ↦ A₀·U` (indicator trick +
`frobSq` invariance); the column-split reshape (`colSplit_reshape_le`); the banked `twoBlock_radial_le`. -/
theorem frontBox_abstract (m r' : ℕ) (c : Fin (r' + 1))
    (U : Matrix (Fin (r' + 1)) (Fin (r' + 1)) ℝ) (hUorth : U * Uᵀ = 1) {σ κ c' α' B : ℝ}
    (hκ : 0 < κ) (hc' : 0 < c') (hσ : 0 < σ) (hσB : σ ≤ B)
    (hα0 : 0 < α') (hαlo : 2 * c' - (m : ℝ) * (r' : ℝ) < α') (hαhi : α' < m) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧
      (∫⁻ A₀ in matBox m (r' + 1) 1, ENNReal.ofReal
        ((σ ^ 2 * (∑ i, ((Matrix.of A₀ * U) i c) ^ 2)
          + κ ^ 2 * (∑ j ∈ Finset.univ.erase c, ∑ i, ((Matrix.of A₀ * U) i j) ^ 2)) ^ (-c')))
        ≤ ENNReal.ofReal (σ ^ (-α')) * C := by
  have hm : 0 < m := by exact_mod_cast lt_trans hα0 hαhi
  set R : ℝ := Real.sqrt ((m : ℝ) * ((r' : ℝ) + 1) + 1) with hRdef
  have hR : (0 : ℝ) < R := Real.sqrt_pos.mpr (by positivity)
  have hαlo' : 2 * c' - ((m * r' : ℕ) : ℝ) < α' := by rw [Nat.cast_mul]; exact hαlo
  obtain ⟨C, hC, hbound⟩ := twoBlock_radial_le (du := m * r') (dv := m) hm
    hc' hκ hσ hσB hR hα0 hαlo' hαhi
  refine ⟨C, hC, ?_⟩
  -- the direct (U-applied) two-block integrand, read off `Γ = A₀·U`
  set GDir : (Fin m → Fin (r' + 1) → ℝ) → ℝ≥0∞ :=
    fun Γ => ENNReal.ofReal ((σ ^ 2 * (∑ i, (Γ i c) ^ 2)
      + κ ^ 2 * (∑ j ∈ Finset.univ.erase c, ∑ i, (Γ i j) ^ 2)) ^ (-c')) with hGDir
  have hGDirmeas : Measurable GDir := by
    rw [hGDir]
    refine ENNReal.measurable_ofReal.comp
      (Measurable.comp (g := fun t : ℝ => t ^ (-c')) (by fun_prop) ?_)
    fun_prop
  -- entry bridge: `(of A₀ · U) i j = (A₀ i ᵥ* U) j`
  have hentry : ∀ (A₀ : Fin m → Fin (r' + 1) → ℝ) (i j), (Matrix.of A₀ * U) i j = (A₀ i ᵥ* U) j := by
    intro A₀ i j
    rw [Matrix.mul_apply]
    simp only [Matrix.of_apply]
    rfl
  -- the box integrand equals `GDir (A₀ ·ᵥ* U)`
  have habs : ∀ A₀ : Fin m → Fin (r' + 1) → ℝ,
      ENNReal.ofReal ((σ ^ 2 * (∑ i, ((Matrix.of A₀ * U) i c) ^ 2)
        + κ ^ 2 * (∑ j ∈ Finset.univ.erase c, ∑ i, ((Matrix.of A₀ * U) i j) ^ 2)) ^ (-c'))
        = GDir (fun i => A₀ i ᵥ* U) := by
    intro A₀; simp only [hGDir, hentry]
  -- box ⊆ Frobenius ball of radius `R`
  have hmatFB : matBox m (r' + 1) 1 ⊆ {Γ : Fin m → Fin (r' + 1) → ℝ | frobSq Γ < R ^ 2} := by
    intro A₀ hA₀
    change frobSq A₀ < R ^ 2
    have hle : frobSq A₀ ≤ (m : ℝ) * ((r' : ℝ) + 1) := by
      unfold frobSq
      calc ∑ i : Fin m, ∑ j : Fin (r' + 1), (A₀ i j) ^ 2
          ≤ ∑ _i : Fin m, ∑ _j : Fin (r' + 1), (1 : ℝ) := by
            refine Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => ?_))
            have hij := hA₀ i j; rw [Set.mem_Icc] at hij; nlinarith [hij.1, hij.2]
        _ = (m : ℝ) * ((r' : ℝ) + 1) := by
            simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
              Nat.cast_add, Nat.cast_one]; ring
    have hR2 : R ^ 2 = (m : ℝ) * ((r' : ℝ) + 1) + 1 := by
      rw [hRdef, Real.sq_sqrt (by positivity)]
    linarith
  -- assemble
  calc ∫⁻ A₀ in matBox m (r' + 1) 1, ENNReal.ofReal
          ((σ ^ 2 * (∑ i, ((Matrix.of A₀ * U) i c) ^ 2)
            + κ ^ 2 * (∑ j ∈ Finset.univ.erase c, ∑ i, ((Matrix.of A₀ * U) i j) ^ 2)) ^ (-c'))
      = ∫⁻ A₀ in matBox m (r' + 1) 1, GDir (fun i => A₀ i ᵥ* U) :=
        setLIntegral_congr_fun (matBox_measurableSet m (r' + 1) 1) (fun A₀ _ => habs A₀)
    _ ≤ ∫⁻ A₀ in {Γ : Fin m → Fin (r' + 1) → ℝ | frobSq Γ < R ^ 2}, GDir (fun i => A₀ i ᵥ* U) :=
        lintegral_mono_set hmatFB
    _ = ∫⁻ Γ in {Γ : Fin m → Fin (r' + 1) → ℝ | frobSq Γ < R ^ 2}, GDir Γ :=
        lintegral_frobBall_orthRightMul U hUorth R GDir hGDirmeas
    _ ≤ ∫⁻ p in (Metric.ball (0 : EuclideanSpace ℝ (Fin (m * r'))) R
                  ×ˢ Metric.ball (0 : EuclideanSpace ℝ (Fin m)) R),
          ENNReal.ofReal ((κ ^ 2 * ‖p.1‖ ^ 2 + σ ^ 2 * ‖p.2‖ ^ 2) ^ (-c')) :=
        colSplit_reshape_le m r' c hR
    _ ≤ ENNReal.ofReal (σ ^ (-α')) * C := hbound

/-- **The reshape + `twoBlock_radial_le` (steps 3–4).** For full-rank `P` (`0 < sigMin P ≤ B`) and
`max(0, 2c' − m·(r−1)) < α' < m`, the front box integral of `twoBlockLoss^{−c'}` is `≤ C·sigMin P^{−α'}`
with `C < ⊤`. Thin instantiation of `frontBox_abstract` at `U = eigenvectorUnitary`, `σ = sigMin P`,
`c = collapseIndex`: unfolds `twoBlockLoss` (`⨅ λ = sigMin P²` via `sigMin_sq_eq_iInf_eigenvalues`) to
the abstract direct loss. -/
theorem frontBox_twoBlock_le (P : Matrix (Fin r) (Fin n) ℝ) (hr : 0 < r) {κ c' α' B : ℝ}
    (hκ : 0 < κ) (hc' : 0 < c') (hσ : 0 < sigMin P) (hσB : sigMin P ≤ B)
    (hα0 : 0 < α') (hαlo : 2 * c' - (m : ℝ) * ((r : ℝ) - 1) < α') (hαhi : α' < m) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧
      (∫⁻ A₀ in matBox m r 1, ENNReal.ofReal ((twoBlockLoss P hr κ (Matrix.of A₀)) ^ (-c')))
        ≤ ENNReal.ofReal (sigMin P ^ (-α')) * C := by
  obtain ⟨r', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hr.ne'
  set U : Matrix (Fin (r' + 1)) (Fin (r' + 1)) ℝ :=
    ((posSemidef_mul_transpose P).isHermitian.eigenvectorUnitary :
      Matrix (Fin (r' + 1)) (Fin (r' + 1)) ℝ) with hU
  set c : Fin (r' + 1) := collapseIndex P hr with hc
  have hUorth : U * Uᵀ = 1 := by
    have hmem := SetLike.coe_mem (posSemidef_mul_transpose P).isHermitian.eigenvectorUnitary
    have h := Matrix.mem_unitaryGroup_iff.mp hmem
    rwa [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] at h
  have hαlo2 : 2 * c' - (m : ℝ) * (r' : ℝ) < α' := by
    have hcast : (m : ℝ) * ((((r' + 1 : ℕ)) : ℝ) - 1) = (m : ℝ) * (r' : ℝ) := by push_cast; ring
    rw [← hcast]; exact hαlo
  obtain ⟨C, hC, hbound⟩ :=
    frontBox_abstract m r' c U hUorth hκ hc' hσ hσB hα0 hαlo2 hαhi
  refine ⟨C, hC, le_trans (le_of_eq ?_) hbound⟩
  refine setLIntegral_congr_fun (matBox_measurableSet m (r' + 1) 1) (fun A₀ _ => ?_)
  rw [twoBlockLoss, twoBlockLossAux, ← sigMin_sq_eq_iInf_eigenvalues P hr, ← hU, ← hc]

/-- **The conditional front-first bound `g(Q) ≤ C·σ_q^{−α'}` (given the sector).** The a.e. transfer
(`front_frobSq_le_twoBlock`) then the reshape/radial bound (`frontBox_twoBlock_le`). The shared brick
both lanes consume; the §5 lane wraps it with the banked recombine (`chartInner_schurShearFree_eq`) and
the `A'`-tube. The sector `sjSector` is the hypothesis whose derivation-from-region (step 6) is the sole
held piece (genm-sj5-cover cert #130). -/
theorem frontFirst_g_le_of_sector (P : Matrix (Fin r) (Fin n) ℝ) (hr : 0 < r) {κ c' α' B : ℝ}
    (hκ : 0 < κ) (hc' : 0 < c') (hσ : 0 < sigMin P) (hσB : sigMin P ≤ B)
    (hsec : sjSector κ P hr)
    (hα0 : 0 < α') (hαlo : 2 * c' - (m : ℝ) * ((r : ℝ) - 1) < α') (hαhi : α' < m) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧
      (∫⁻ A₀ in matBox m r 1, ENNReal.ofReal ((frobSq (Matrix.of A₀ * P)) ^ (-c')))
        ≤ ENNReal.ofReal (sigMin P ^ (-α')) * C := by
  obtain ⟨C, hC, hbound⟩ := frontBox_twoBlock_le (m := m) P hr hκ hc' hσ hσB hα0 hαlo hαhi
  exact ⟨C, hC, le_trans (front_frobSq_le_twoBlock P hr hκ hσ hsec hc') hbound⟩

end DLNFibre.DLN.RLCT
