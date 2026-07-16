import DLNFibre.DLN.RLCT.Validate.RouteMSchurCorankSlab
import DLNFibre.DLN.RLCT.Validate.RouteMSJProductTube
import DLNFibre.DLN.RLCT.Validate.RouteMSJDecoratedPeelMeas
import DLNFibre.DLN.RLCT.Validate.RouteMSJOrthoExtend
import DLNFibre.DLN.RLCT.Foundations.ParamsFlat

set_option linter.style.longLine false

open MeasureTheory Set Matrix
open scoped ENNReal BigOperators InnerProductSpace

namespace DLNFibre.DLN.RLCT

/-! # `RouteMSchurCorankSlabD` — the (D) `b ≥ 2` inner charge slab

The `b`-general lift of `corankSlab_charge_sint_le` (the `b = 1` slab): the deep factor `S` is integrated
over its box `matBox n p 1`, the corank `Acor` is FIXED, and the charge Gram integral is bounded by a
uniform constant times the corank-Gram det:

    ∫_{S ∈ matBox n p 1} det((Acor·S)(Acor·S)ᵀ)^{−a/2}  ≤  C · det(Acor·Acorᵀ)^{−a/2}

for `b ≤ n` and `a + b ≤ p` (the sharp threshold). This is exactly the `‖·‖⁻¹ → det(··ᵀ)^{−a/2}`
generalisation of the `b = 1` slab.

## Route (couplerad §w3-Drec, the co-isometry / O(n) reduction — NON-SPECTRAL)

For rank-deficient `Acor` (`det(Acor·Acorᵀ) = 0`) the charge Gram vanishes pointwise
(`chargeGramDet_eq_zero_of_corank_singular`), so both sides are `0` (`a ≥ 1`); `a = 0` is the trivial
integrand-`≡ 1` branch.

For full-row-rank `Acor`, enclose the box in the ball `{S : cols in ball_n(√n)}` and use the
`O(n)`-invariance of the ball integral (`S ↦ Oᵀ·S` is a column-wise isometry, measure- and
ball-preserving) to rotate `Acor` to the canonical form `Acor·Oᵀ = [L | 0]` (`L` invertible `b×b`; the last
`n−b` columns land in `ker Acor`). Then `[L|0]·S = L·(first b rows of S)`, so the charge Gram factors as
`(det L)²·det(S'·S'ᵀ)` (`S'` = first `b` rows), giving `det(Acor·Acorᵀ)^{−a/2}` out front. The residual
`∫ det(S'·S'ᵀ)^{−a/2}` splits (Fubini) over the first-`b` / last-`(n−b)` rows: the last rows contribute a
finite ball-volume factor, and the first-`b`-rows integral is dominated by the banked
`qbox_lintegral_lt_top` (`{cols in ball_b(√n)} ⊆ {rows in ball_p(√(pn))}`, finite iff `a < p − b + 1`
`⟺ a + b ≤ p`). The constant `L₀ = vol(ball_{n−b}(√n))^p · qbox` is uniform in `Acor`.
-/

namespace CorankSlabD

/-! ## The measure-preserving transpose `Fin n → Fin p → ℝ ≃ᵐ Fin p → Fin n → ℝ`

The `O(n)` column action needs the column index (`Fin n`) to be the INNER pi index so the banked
`mulLeftₚ` per-column left-multiplication CoV applies. The transpose reindex (`piCurry` +
`arrowCongr'` with `prodComm`, following `matToFlatRect`) puts it there. -/

/-- The transpose measurable equiv, `(transp n p S) k i = S i k`. -/
noncomputable def transp (n p : ℕ) : (Fin n → Fin p → ℝ) ≃ᵐ (Fin p → Fin n → ℝ) :=
  (MeasurableEquiv.piCurry (fun (_ : Fin n) (_ : Fin p) => ℝ)).symm.trans
    ((MeasurableEquiv.arrowCongr'
        (((Equiv.sigmaEquivProd (Fin n) (Fin p)).trans (Equiv.prodComm (Fin n) (Fin p))).trans
          (Equiv.sigmaEquivProd (Fin p) (Fin n)).symm)
        (MeasurableEquiv.refl ℝ)).trans
      (MeasurableEquiv.piCurry (fun (_ : Fin p) (_ : Fin n) => ℝ)))

@[simp] theorem transp_apply (n p : ℕ) (S : Fin n → Fin p → ℝ) (k : Fin p) (i : Fin n) :
    transp n p S k i = S i k := rfl

theorem measurePreserving_transp (n p : ℕ) :
    MeasurePreserving (transp n p) (volume : Measure (Fin n → Fin p → ℝ))
      (volume : Measure (Fin p → Fin n → ℝ)) := by
  have h1 : MeasurePreserving (MeasurableEquiv.piCurry (fun (_ : Fin n) (_ : Fin p) => ℝ)).symm
      (volume : Measure (Fin n → Fin p → ℝ))
      (volume : Measure ((Σ _ : Fin n, Fin p) → ℝ)) :=
    (measurePreserving_piCurry (fun (_ : Fin n) (_ : Fin p) => ℝ) (fun _ _ => volume)).symm _
  have h2 : MeasurePreserving
      (MeasurableEquiv.arrowCongr'
        (((Equiv.sigmaEquivProd (Fin n) (Fin p)).trans (Equiv.prodComm (Fin n) (Fin p))).trans
          (Equiv.sigmaEquivProd (Fin p) (Fin n)).symm) (MeasurableEquiv.refl ℝ))
      (volume : Measure ((Σ _ : Fin n, Fin p) → ℝ))
      (volume : Measure ((Σ _ : Fin p, Fin n) → ℝ)) :=
    volume_preserving_arrowCongr' _ (MeasurableEquiv.refl ℝ) (MeasurePreserving.id _)
  have h3 : MeasurePreserving (MeasurableEquiv.piCurry (fun (_ : Fin p) (_ : Fin n) => ℝ))
      (volume : Measure ((Σ _ : Fin p, Fin n) → ℝ))
      (volume : Measure (Fin p → Fin n → ℝ)) :=
    measurePreserving_piCurry (fun (_ : Fin p) (_ : Fin n) => ℝ) (fun _ _ => volume)
  exact (h1.trans h2).trans h3

/-! ## The `O(n)` column change-of-variables

`colMulLeft O S` left-multiplies each column of `S` by `O` (`Matrix.of ↦ O * Matrix.of S`). Via the
transpose it is `transp.symm ∘ mulLeftₚ p O ∘ transp`, so the banked `lintegral_comp_mulLeftₚ` (per-column
left-mult CoV, Jacobian `(det O)^p`) transports through `transp`'s measure-preservation. For orthogonal
`O` the Jacobian is `1`. -/

/-- Left-multiply each column of `S` by `O`: `(colMulLeft O S) i k = ∑ⱼ O i j · S j k`. -/
noncomputable def colMulLeft {n p : ℕ} (O : Matrix (Fin n) (Fin n) ℝ) (S : Fin n → Fin p → ℝ) :
    Fin n → Fin p → ℝ :=
  fun i k => O *ᵥ (fun j => S j k) <| i

theorem colMulLeft_eq_transp {n p : ℕ} (O : Matrix (Fin n) (Fin n) ℝ) (S : Fin n → Fin p → ℝ) :
    colMulLeft O S = transp p n (mulLeftₚ p O (transp n p S)) := by
  funext i k
  have hinner : (transp n p S) k = (fun j => S j k) := by funext j; rw [transp_apply]
  rw [transp_apply, mulLeftₚ_apply, hinner]
  rfl

/-- `colMulLeft` composes: `Matrix.of (colMulLeft O S) = O * Matrix.of S`. -/
theorem of_colMulLeft {n p : ℕ} (O : Matrix (Fin n) (Fin n) ℝ) (S : Fin n → Fin p → ℝ) :
    Matrix.of (colMulLeft O S) = O * Matrix.of S := by
  ext i k
  simp only [colMulLeft, Matrix.of_apply, Matrix.mul_apply, Matrix.mulVec, dotProduct]

theorem measurable_colMulLeft {n p : ℕ} (O : Matrix (Fin n) (Fin n) ℝ) :
    Measurable (colMulLeft (p := p) O) := by
  rw [show (colMulLeft (p := p) O) = fun S => transp p n (mulLeftₚ p O (transp n p S)) from
    funext (fun S => colMulLeft_eq_transp O S)]
  exact (transp p n).measurable.comp
    ((mulLeftₚ p O).continuous_of_finiteDimensional.measurable.comp (transp n p).measurable)

/-- **`mulLeftₚ` by a determinant-`±1` matrix is measure-preserving.** The Jacobian `(det K)^c` has
absolute value `1`, so `map_linearMap_addHaar_eq_smul_addHaar` gives `map = volume`. -/
theorem measurePreserving_mulLeftₚ {c t : ℕ} (K : Matrix (Fin t) (Fin t) ℝ) (hK : |K.det| = 1) :
    MeasurePreserving (mulLeftₚ c K) (volume : Measure (Fin c → Fin t → ℝ)) volume := by
  have hKdet : K.det ≠ 0 := by intro h; rw [h, abs_zero] at hK; norm_num at hK
  have hdet : LinearMap.det (mulLeftₚ c K) ≠ 0 := by rw [det_mulLeftₚ]; exact pow_ne_zero _ hKdet
  refine ⟨(mulLeftₚ c K).continuous_of_finiteDimensional.measurable, ?_⟩
  rw [Measure.map_linearMap_addHaar_eq_smul_addHaar volume hdet, det_mulLeftₚ,
    show |((K.det) ^ c)⁻¹| = 1 from by rw [abs_inv, abs_pow, hK, one_pow, inv_one],
    ENNReal.ofReal_one, one_smul]

/-- **`colMulLeft` by an orthogonal matrix is measure-preserving.** As the composite
`transp ∘ mulLeftₚ p O ∘ transp`, each factor measure-preserving (`O.det² = 1` ⟹ Jacobian `1`). -/
theorem measurePreserving_colMulLeft {n p : ℕ} (O : Matrix (Fin n) (Fin n) ℝ)
    (hO : O * Oᵀ = 1) :
    MeasurePreserving (colMulLeft (p := p) O) (volume : Measure (Fin n → Fin p → ℝ)) volume := by
  have hdet1 : |O.det| = 1 := by
    have h : O.det * O.det = 1 := by
      have := congrArg Matrix.det hO
      rwa [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at this
    have h2 : |O.det| ^ 2 = 1 := by rw [sq, ← abs_mul, h, abs_one]
    nlinarith [abs_nonneg O.det, h2]
  have hcomp : (colMulLeft (p := p) O)
      = (transp p n) ∘ (mulLeftₚ p O) ∘ (transp n p) :=
    funext (fun S => colMulLeft_eq_transp O S)
  rw [hcomp]
  exact (measurePreserving_transp p n).comp
    ((measurePreserving_mulLeftₚ O hdet1).comp (measurePreserving_transp n p))

/-! ## The residual leaf: the `b×p` column-ball Gram integral is finite

`∫_{X : b×p, cols in ball_b(√n)} det(X·Xᵀ)^{−a/2} < ⊤` for `a + b ≤ p`. Each column having norm `≤ √n`
forces each row norm `≤ √(pn)`, so the domain sits inside the row-ball of radius `√(pn)+1`; transport by
`rowsEquiv` and apply the banked `qbox_lintegral_lt_top`. -/

/-- The `b×p` matrix column-ball with squared radius `(n:ℝ)`: every column has `∑ᵢ Xᵢₖ² ≤ n`. -/
def colBallMat (b p n : ℕ) : Set (Fin b → Fin p → ℝ) :=
  {X | ∀ k, ∑ i, (X i k) ^ 2 ≤ (n : ℝ)}

theorem measurableSet_colBallMat (b p n : ℕ) : MeasurableSet (colBallMat b p n) := by
  rw [colBallMat, Set.setOf_forall]
  refine MeasurableSet.iInter (fun k => ?_)
  exact measurableSet_le (by fun_prop) measurable_const

/-- **The residual leaf.** For `b ≤ p` and `a < p − b + 1`, the column-ball Gram integral is finite. -/
theorem bRowGram_colBall_lt_top {b p n : ℕ} (hbp : b ≤ p) {a : ℝ} (haq : a < (p : ℝ) - b + 1) :
    (∫⁻ X in colBallMat b p n,
        ENNReal.ofReal ((Matrix.of X * (Matrix.of X)ᵀ).det ^ (-a / 2))) < ⊤ := by
  set R : ℝ := Real.sqrt (p * n) + 1 with hR
  set e := rowsEquiv b p with he
  set F : (Fin b → EuclideanSpace ℝ (Fin p)) → ℝ≥0∞ :=
    fun Q => ENNReal.ofReal ((Matrix.gram ℝ Q).det ^ (-a / 2)) with hF
  -- enclose the column-ball in the row-ball of radius `R`
  have hsub : colBallMat b p n ⊆ e ⁻¹' (Set.univ.pi
      (fun _ : Fin b => Metric.ball (0 : EuclideanSpace ℝ (Fin p)) R)) := by
    intro X hX
    simp only [he, Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Metric.mem_ball,
      dist_zero_right, rowsEquiv_apply]
    intro i
    have hrow : ∑ k, (X i k) ^ 2 ≤ (p : ℝ) * n := by
      calc ∑ k, (X i k) ^ 2 ≤ ∑ k, ∑ i', (X i' k) ^ 2 := by
            refine Finset.sum_le_sum (fun k _ => ?_)
            exact Finset.single_le_sum (f := fun i' => (X i' k) ^ 2)
              (fun i' _ => sq_nonneg _) (Finset.mem_univ i)
        _ ≤ ∑ _k : Fin p, (n : ℝ) := Finset.sum_le_sum (fun k _ => hX k)
        _ = (p : ℝ) * n := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
              nsmul_eq_mul]
    have hnorm2 : ‖(WithLp.toLp 2 (X i) : EuclideanSpace ℝ (Fin p))‖ ^ 2 ≤ (p : ℝ) * n := by
      rw [EuclideanSpace.norm_sq_eq]
      refine le_trans (le_of_eq (Finset.sum_congr rfl (fun k _ => ?_))) hrow
      rw [Real.norm_eq_abs, sq_abs]
    have hnorm : ‖(WithLp.toLp 2 (X i) : EuclideanSpace ℝ (Fin p))‖ ≤ Real.sqrt (p * n) := by
      rw [← Real.sqrt_sq (norm_nonneg _)]
      exact Real.sqrt_le_sqrt hnorm2
    rw [hR]; linarith [hnorm]
  -- transport and bound by qbox
  have hmp := measurePreserving_rowsEquiv b p
  have hCoV := hmp.setLIntegral_comp_preimage_emb e.measurableEmbedding F
    (Set.univ.pi (fun _ : Fin b => Metric.ball (0 : EuclideanSpace ℝ (Fin p)) R))
  have hleft : (∫⁻ X in colBallMat b p n,
        ENNReal.ofReal ((Matrix.of X * (Matrix.of X)ᵀ).det ^ (-a / 2)))
      = ∫⁻ X in colBallMat b p n, F (e X) := by
    refine setLIntegral_congr_fun (measurableSet_colBallMat b p n) (fun X _ => ?_)
    rw [hF]; simp only; rw [gram_rowsEquiv]
  calc (∫⁻ X in colBallMat b p n,
          ENNReal.ofReal ((Matrix.of X * (Matrix.of X)ᵀ).det ^ (-a / 2)))
      = ∫⁻ X in colBallMat b p n, F (e X) := hleft
    _ ≤ ∫⁻ X in e ⁻¹' (Set.univ.pi
          (fun _ : Fin b => Metric.ball (0 : EuclideanSpace ℝ (Fin p)) R)), F (e X) :=
        lintegral_mono_set hsub
    _ = ∫⁻ Q in Set.univ.pi (fun _ : Fin b => Metric.ball (0 : EuclideanSpace ℝ (Fin p)) R), F Q :=
        hCoV
    _ < ⊤ := qbox_lintegral_lt_top b hbp (by linarith) R

/-! ## The corank action of `O` and `colMulLeft` -/

/-- The corank matrix right-multiplied by `O`: `corankMul Acor O i j = (Matrix.of Acor * O) i j`. -/
noncomputable def corankMul {b n : ℕ} (Acor : Fin b → Fin n → ℝ) (O : Matrix (Fin n) (Fin n) ℝ) :
    Fin b → Fin n → ℝ := fun i j => (Matrix.of Acor * O) i j

theorem of_corankMul {b n : ℕ} (Acor : Fin b → Fin n → ℝ) (O : Matrix (Fin n) (Fin n) ℝ) :
    Matrix.of (corankMul Acor O) = Matrix.of Acor * O := rfl

/-- **Charge Gram absorbs the column action.** `chargeGramDet Acor (colMulLeft O S) = chargeGramDet
(Acor·O) S`: the `O` on the columns of `S` moves onto the corank matrix. -/
theorem chargeGramDet_colMulLeft {b n p : ℕ} (Acor : Fin b → Fin n → ℝ)
    (O : Matrix (Fin n) (Fin n) ℝ) (S : Fin n → Fin p → ℝ) :
    chargeGramDet Acor (colMulLeft O S) = chargeGramDet (corankMul Acor O) S := by
  unfold chargeGramDet
  rw [of_rmatMul, of_rmatMul, of_colMulLeft, of_corankMul, ← Matrix.mul_assoc]

theorem colMulLeft_comp {n p : ℕ} (O K : Matrix (Fin n) (Fin n) ℝ) (S : Fin n → Fin p → ℝ) :
    colMulLeft O (colMulLeft K S) = colMulLeft (O * K) S := by
  funext i k
  show (O *ᵥ (fun j => colMulLeft K S j k)) i = ((O * K) *ᵥ (fun j => S j k)) i
  rw [show (fun j => colMulLeft K S j k) = K *ᵥ (fun j => S j k) from rfl, Matrix.mulVec_mulVec]

theorem colMulLeft_one {n p : ℕ} (S : Fin n → Fin p → ℝ) : colMulLeft 1 S = S := by
  funext i k; simp only [colMulLeft, Matrix.one_mulVec]

/-! ## The column ball, its invariance, and the box enclosure -/

theorem box_subset_colBall {n p : ℕ} : matBox n p 1 ⊆ colBallMat n p n := by
  intro S hS k
  calc ∑ i, (S i k) ^ 2 ≤ ∑ _i : Fin n, (1 : ℝ) := by
        refine Finset.sum_le_sum (fun i _ => ?_)
        have h := hS i k; rw [Set.mem_Icc] at h; nlinarith [h.1, h.2]
    _ = (n : ℝ) := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]

/-- The column norms are preserved by `colMulLeft O` for orthogonal `O`, so `colBallMat` is invariant. -/
theorem colMulLeft_preimage_colBall {n p : ℕ} (O : Matrix (Fin n) (Fin n) ℝ) (hO : O * Oᵀ = 1) :
    colMulLeft O ⁻¹' colBallMat n p n = colBallMat n p n := by
  have hOtO : Oᵀ * O = 1 := by rwa [Matrix.mul_eq_one_comm] at hO
  have hpres : ∀ (S : Fin n → Fin p → ℝ) (k : Fin p),
      ∑ i, ((colMulLeft O S) i k) ^ 2 = ∑ i, (S i k) ^ 2 := by
    intro S k
    have h1 : ∑ i, ((colMulLeft O S) i k) ^ 2
        = (O *ᵥ (fun j => S j k)) ⬝ᵥ (O *ᵥ (fun j => S j k)) := by
      rw [dotProduct]; exact Finset.sum_congr rfl (fun i _ => by rw [colMulLeft]; ring)
    have h2 : ∑ i, (S i k) ^ 2 = (fun j => S j k) ⬝ᵥ (fun j => S j k) := by
      rw [dotProduct]; exact Finset.sum_congr rfl (fun i _ => by ring)
    rw [h1, h2, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, Matrix.mulVec_mulVec,
      hOtO, Matrix.one_mulVec]
  ext S
  simp only [Set.mem_preimage, colBallMat, Set.mem_setOf_eq]
  constructor
  · intro h k; rw [← hpres S k]; exact h k
  · intro h k; rw [hpres S k]; exact h k

/-- `colMulLeft` by an orthogonal matrix as a measurable equivalence (inverse `colMulLeft Oᵀ`). -/
noncomputable def colMulLeftEquiv {n p : ℕ} (O : Matrix (Fin n) (Fin n) ℝ) (hO : O * Oᵀ = 1) :
    (Fin n → Fin p → ℝ) ≃ᵐ (Fin n → Fin p → ℝ) where
  toFun := colMulLeft O
  invFun := colMulLeft Oᵀ
  left_inv := fun S => by
    rw [colMulLeft_comp]; rw [Matrix.mul_eq_one_comm.mp hO]; exact colMulLeft_one S
  right_inv := fun S => by rw [colMulLeft_comp, hO]; exact colMulLeft_one S
  measurable_toFun := measurable_colMulLeft O
  measurable_invFun := measurable_colMulLeft Oᵀ

/-- **The `O(n)` change of variables over the column ball.** For orthogonal `O` and measurable nonneg
`g`, the column-ball integral of `g ∘ colMulLeft O` equals that of `g`. -/
theorem cov_colBall {n p : ℕ} (O : Matrix (Fin n) (Fin n) ℝ) (hO : O * Oᵀ = 1)
    (g : (Fin n → Fin p → ℝ) → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ S in colBallMat n p n, g (colMulLeft O S)) = ∫⁻ S in colBallMat n p n, g S := by
  have hmp := measurePreserving_colMulLeft (p := p) O hO
  have hemb : MeasurableEmbedding (colMulLeft (p := p) O) :=
    (colMulLeftEquiv O hO).measurableEmbedding
  have := hmp.setLIntegral_comp_preimage_emb hemb g (colBallMat n p n)
  rw [colMulLeft_preimage_colBall O hO] at this
  exact this

/-! ## The active-rows selection (`Acor·O = [0 | L]`, kernel columns first) -/

/-- The last `b` rows of an `n`-row matrix (`b ≤ n`), as a `b × p` matrix. -/
def activeRows {b n p : ℕ} (hbn : b ≤ n) (S : Fin n → Fin p → ℝ) : Fin b → Fin p → ℝ :=
  fun i k => S ⟨(n - b) + i, by omega⟩ k

/-- The active-rows Gram determinant `det(activeRows·activeRowsᵀ)`. -/
noncomputable def activeGram {b n p : ℕ} (hbn : b ≤ n) (S : Fin n → Fin p → ℝ) : ℝ :=
  (Matrix.of (activeRows hbn S) * (Matrix.of (activeRows hbn S))ᵀ).det

/-- **Full row rank from the nonsingular corank Gram.** `det(Acor·Acorᵀ) ≠ 0 ⟹ rank Acor = b`. -/
theorem rank_of_gram_det_ne_zero {b n : ℕ} (Acor : Fin b → Fin n → ℝ)
    (hb : (Matrix.of Acor * (Matrix.of Acor)ᵀ).det ≠ 0) : (Matrix.of Acor).rank = b := by
  have hunit : IsUnit (Matrix.of Acor * (Matrix.of Acor)ᵀ) := by
    rw [Matrix.isUnit_iff_isUnit_det]; exact isUnit_iff_ne_zero.mpr hb
  have h1 : (Matrix.of Acor * (Matrix.of Acor)ᵀ).rank = b := by
    rw [Matrix.rank_of_isUnit _ hunit, Fintype.card_fin]
  rwa [Matrix.rank_self_mul_transpose] at h1

/-- **An orthonormal `n × (n−b)` matrix whose columns lie in `ker Acor`** — the isolated gap.
Recipe (Codex-vetted): `T := Matrix.toEuclideanLin (of Acor)`; `K := ker T`; rank–nullity +
`rank_of_gram_det_ne_zero` give `finrank K = n − b`; take `(stdOrthonormalBasis ℝ K).reindex (finCongr …)`
and read its coordinates into `U`; `Uᵀ·U = 1` is `ob.orthonormal` through `Submodule.coe_inner`, and
`Acor·U = 0` is membership in `ker T` via `toEuclideanLin_apply`. -/
theorem exists_ker_ortho_matrix {b n : ℕ} (hbn : b ≤ n) (Acor : Fin b → Fin n → ℝ)
    (hrank : (Matrix.of Acor).rank = b) :
    ∃ U : Matrix (Fin n) (Fin (n - b)) ℝ, Uᵀ * U = 1 ∧ Matrix.of Acor * U = 0 := by
  classical
  set M := Matrix.of Acor with hM
  set T : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin b) :=
    Matrix.toEuclideanLin M with hT
  set K : Submodule ℝ (EuclideanSpace ℝ (Fin n)) := LinearMap.ker T with hKdef
  -- `finrank K = n - b` via `ker T = toLp '' (ker mulVecLin)` and rank–nullity on `mulVecLin`
  have hkermul : Module.finrank ℝ (LinearMap.ker M.mulVecLin) = n - b := by
    have hrn := M.mulVecLin.finrank_range_add_finrank_ker
    have hrng : Module.finrank ℝ (LinearMap.range M.mulVecLin) = b := hrank
    rw [hrng, Module.finrank_fin_fun] at hrn
    omega
  have hkmap : K = (LinearMap.ker M.mulVecLin).map
      (WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).symm.toLinearMap := by
    apply Submodule.ext; intro v
    simp only [hKdef, Submodule.mem_map, LinearMap.mem_ker, Matrix.mulVecLin_apply,
      LinearEquiv.coe_coe, WithLp.linearEquiv_symm_apply]
    constructor
    · intro hv
      refine ⟨WithLp.equiv 2 (Fin n → ℝ) v, ?_, rfl⟩
      have := congrArg (WithLp.equiv 2 (Fin b → ℝ)) hv
      simpa [hT, Matrix.toEuclideanLin_apply] using this
    · rintro ⟨w, hw, rfl⟩
      simp [hT, Matrix.toEuclideanLin_apply, hw]
  have hfk : Module.finrank ℝ K = n - b := by
    rw [hkmap, LinearEquiv.finrank_map_eq, hkermul]
  -- an orthonormal basis of `K` indexed by `Fin (n − b)`
  set ob : OrthonormalBasis (Fin (n - b)) ℝ K :=
    (stdOrthonormalBasis ℝ K).reindex (finCongr hfk) with hob
  refine ⟨Matrix.of fun i j => ((ob j : EuclideanSpace ℝ (Fin n)) i), ?_, ?_⟩
  · -- orthonormal columns
    ext j l
    have hon := ob.orthonormal
    rw [orthonormal_iff_ite] at hon
    have hcoe : (inner ℝ (ob j) (ob l) : ℝ)
        = (inner ℝ (ob j : EuclideanSpace ℝ (Fin n)) (ob l : EuclideanSpace ℝ (Fin n)) : ℝ) := rfl
    have hbb : (inner ℝ (ob j : EuclideanSpace ℝ (Fin n)) (ob l : EuclideanSpace ℝ (Fin n)) : ℝ)
        = (fun i => (ob l : EuclideanSpace ℝ (Fin n)) i)
            ⬝ᵥ star (fun i => (ob j : EuclideanSpace ℝ (Fin n)) i) :=
      EuclideanSpace.inner_toLp_toLp _ _
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, Matrix.one_apply]
    rw [← hon j l, hcoe, hbb]
    simp only [dotProduct, Pi.star_apply, star_trivial]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  · -- columns lie in `ker Acor`
    ext i j
    simp only [Matrix.mul_apply, Matrix.of_apply, hM, Matrix.zero_apply]
    have hTz : T (ob j : EuclideanSpace ℝ (Fin n)) = 0 := (ob j).2
    rw [hT, Matrix.toEuclideanLin_apply] at hTz
    have h0 : (Matrix.of Acor) *ᵥ (fun l => (ob j : EuclideanSpace ℝ (Fin n)) l) = 0 := by
      have := congrArg (WithLp.equiv 2 (Fin b → ℝ)) hTz
      simpa [hM] using this
    have := congrFun h0 i
    simpa [Matrix.mulVec, dotProduct] using this

/-- **The canonical form (via banked `exists_ortho_ext` + `exists_ker_ortho_matrix`).** Full-row-rank
`Acor` rotates by an orthogonal `O` (`O·Oᵀ = 1`) so that `Acor·O = [0 | L]` (kernel columns first), and the
charge Gram factors as `det(Acor·Acorᵀ)·activeGram`. Assembly: `exists_ker_ortho_matrix` builds the
orthonormal kernel block `U_s`; `exists_ortho_ext` extends it to `O` (first `n−b` columns `= U_s`);
`O·Oᵀ = 1` from `Oᵀ·O = 1` via `Matrix.mul_eq_one_comm`; the first `n−b` columns of `Acor·O` vanish (`= 0`
since `Acor·U_s = 0`), so `(Acor·O)·S = L·activeRows S` and `(Acor·O)(Acor·O)ᵀ = L·Lᵀ` with
`det(L·Lᵀ) = det(Acor·Acorᵀ)`. -/
theorem exists_canonical {b n p : ℕ} (hbn : b ≤ n) (Acor : Fin b → Fin n → ℝ)
    (hb : (Matrix.of Acor * (Matrix.of Acor)ᵀ).det ≠ 0) :
    ∃ O : Matrix (Fin n) (Fin n) ℝ, O * Oᵀ = 1 ∧
      ∀ S : Fin n → Fin p → ℝ,
        chargeGramDet (corankMul Acor O) S
          = (Matrix.of Acor * (Matrix.of Acor)ᵀ).det * activeGram hbn S := by
  classical
  have hrank := rank_of_gram_det_ne_zero Acor hb
  obtain ⟨U, hUU, hAU⟩ := exists_ker_ortho_matrix hbn Acor hrank
  have hmM : n - b ≤ n := by omega
  obtain ⟨O, hOtO, hsub⟩ := exists_ortho_ext hmM U hUU
  have hO : O * Oᵀ = 1 := Matrix.mul_eq_one_comm.mp hOtO
  refine ⟨O, hO, fun S => ?_⟩
  set KO : Matrix (Fin b) (Fin n) ℝ := Matrix.of Acor * O with hKO
  set L : Matrix (Fin b) (Fin b) ℝ := KO.submatrix id (fun j' => (⟨(n - b) + j', by omega⟩ : Fin n))
    with hL
  -- the first `n − b` columns of `KO` vanish (their `O`-columns lie in `ker Acor`)
  have hzero : ∀ (i : Fin b) (l : Fin n), (l : ℕ) < n - b → KO i l = 0 := by
    intro i l hl
    have hcol : ∀ l' : Fin n, O l' l = U l' ⟨l, hl⟩ := by
      intro l'
      have hs : O l' (Fin.castLE hmM ⟨l, hl⟩) = U l' ⟨l, hl⟩ := by
        have := congrFun (congrFun hsub l') ⟨l, hl⟩
        simpa [Matrix.submatrix_apply] using this
      rw [← hs]; congr 1
    have he : KO i l = (Matrix.of Acor * U) i ⟨l, hl⟩ := by
      rw [hKO, Matrix.mul_apply, Matrix.mul_apply]
      exact Finset.sum_congr rfl (fun l' _ => by rw [hcol l'])
    rw [he, hAU]; rfl
  -- a function vanishing on the first `n − b` indices sums over the last `b`
  have hnb : n - b + b = n := Nat.sub_add_cancel hbn
  set e : Fin (n - b) ⊕ Fin b ≃ Fin n := finSumFinEquiv.trans (finCongr hnb) with he
  have heInr : ∀ j' : Fin b, (e (Sum.inr j') : Fin n) = (⟨(n - b) + j', by omega⟩ : Fin n) := by
    intro j'; apply Fin.ext
    rw [he, Equiv.trans_apply, finSumFinEquiv_apply_right, finCongr_apply, Fin.coe_cast,
      Fin.val_natAdd]
  have heInl : ∀ i' : Fin (n - b), ((e (Sum.inl i') : Fin n) : ℕ) < n - b := by
    intro i'
    rw [he, Equiv.trans_apply, finSumFinEquiv_apply_left, finCongr_apply, Fin.coe_cast,
      Fin.coe_castAdd]
    exact i'.isLt
  have sumSplit : ∀ (g : Fin n → ℝ), (∀ l : Fin n, (l : ℕ) < n - b → g l = 0) →
      ∑ l, g l = ∑ j' : Fin b, g (⟨(n - b) + j', by omega⟩ : Fin n) := by
    intro g hg
    rw [← Equiv.sum_comp e g, Fintype.sum_sum_type,
      Finset.sum_eq_zero (fun i' _ => hg _ (heInl i')), zero_add]
    exact Finset.sum_congr rfl (fun j' _ => by rw [heInr j'])
  -- F1: `KO · S = L · activeRows S`
  have hF1 : KO * Matrix.of S = L * Matrix.of (activeRows hbn S) := by
    ext i k
    rw [Matrix.mul_apply,
      sumSplit (fun l => KO i l * (Matrix.of S) l k) (fun l hl => by
        simp only [hzero i l hl, zero_mul]),
      Matrix.mul_apply]
    exact Finset.sum_congr rfl (fun j' _ => by rw [hL]; simp only [Matrix.submatrix_apply, id_eq]; rfl)
  -- F2: `KO · KOᵀ = L · Lᵀ`
  have hF2 : KO * KOᵀ = L * Lᵀ := by
    ext i i'
    rw [Matrix.mul_apply,
      sumSplit (fun l => KO i l * KOᵀ l i')
        (fun l hl => by simp only [hzero i l hl, zero_mul]),
      Matrix.mul_apply]
    refine Finset.sum_congr rfl (fun j' _ => ?_)
    rw [hL]; simp only [Matrix.submatrix_apply, Matrix.transpose_apply, id_eq]
  -- `KO · KOᵀ = Acor · Acorᵀ`
  have hKOgram : KO * KOᵀ = Matrix.of Acor * (Matrix.of Acor)ᵀ := by
    rw [hKO, Matrix.transpose_mul, ← Matrix.mul_assoc, Matrix.mul_assoc (Matrix.of Acor) O Oᵀ, hO,
      Matrix.mul_one]
  -- assemble the determinant factorization
  have hchg : chargeGramDet (corankMul Acor O) S
      = ((L * Matrix.of (activeRows hbn S)) * (L * Matrix.of (activeRows hbn S))ᵀ).det := by
    unfold chargeGramDet
    rw [of_rmatMul, of_corankMul, ← hKO, hF1]
  rw [hchg, activeGram, Matrix.transpose_mul,
    show L * Matrix.of (activeRows hbn S) * ((Matrix.of (activeRows hbn S))ᵀ * Lᵀ)
      = L * (Matrix.of (activeRows hbn S) * (Matrix.of (activeRows hbn S))ᵀ) * Lᵀ from by
        rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc],
    Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
    show (Matrix.of Acor * (Matrix.of Acor)ᵀ).det = (L * Lᵀ).det from by rw [← hF2, hKOgram],
    Matrix.det_mul, Matrix.det_transpose]
  ring

/-- The column ball is closed and bounded, hence compact, hence has finite volume. -/
theorem colBallMat_volume_lt_top (b p n : ℕ) : volume (colBallMat b p n) < ⊤ := by
  have hclosed : IsClosed (colBallMat b p n) := by
    rw [colBallMat, Set.setOf_forall]
    exact isClosed_iInter (fun k => isClosed_le (by fun_prop) continuous_const)
  have hbdd : Bornology.IsBounded (colBallMat b p n) := by
    refine Bornology.IsBounded.subset
      (Metric.isBounded_closedBall (x := (0 : Fin b → Fin p → ℝ)) (r := Real.sqrt n)) ?_
    intro X hX
    rw [Metric.mem_closedBall, dist_zero_right]
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr (fun i => ?_)
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr (fun j => ?_)
    have hle : (X i j) ^ 2 ≤ (n : ℝ) :=
      le_trans (Finset.single_le_sum (f := fun i' => (X i' j) ^ 2)
        (fun _ _ => sq_nonneg _) (Finset.mem_univ i)) (hX j)
    rw [Real.norm_eq_abs, ← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt hle
  exact (Metric.isCompact_iff_isClosed_bounded.mpr ⟨hclosed, hbdd⟩).measure_lt_top

/-- **The residual leaf is finite (Acor-independent).** `∫_{colBall} activeGram^{−a/2} < ⊤`, by the
row-split (integrate out the passive `n−b` rows over a finite column-ball) + the banked column-ball leaf. -/
theorem activeGram_colBall_lt_top {a : ℝ} {b n p : ℕ} (hbn : b ≤ n) (hbp : b ≤ p)
    (haq : a < (p : ℝ) - b + 1) :
    (∫⁻ S in colBallMat n p n, ENNReal.ofReal ((activeGram hbn S) ^ (-a / 2))) < ⊤ := by
  classical
  have hnb : n - b + b = n := Nat.sub_add_cancel hbn
  set eIdx : Fin (n - b) ⊕ Fin b ≃ Fin n := finSumFinEquiv.trans (finCongr hnb) with heIdx
  set ρ : (Fin n → Fin p → ℝ) ≃ᵐ
      ((Fin (n - b) → Fin p → ℝ) × (Fin b → Fin p → ℝ)) :=
    (MeasurableEquiv.piCongrLeft (fun _ : Fin n => Fin p → ℝ) eIdx).symm.trans
      (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin (n - b) ⊕ Fin b => Fin p → ℝ)) with hρ
  have hρmp : MeasurePreserving ρ (volume : Measure (Fin n → Fin p → ℝ)) volume :=
    ((volume_measurePreserving_piCongrLeft (fun _ : Fin n => Fin p → ℝ) eIdx).symm _).trans
      (volume_measurePreserving_sumPiEquivProdPi (fun _ : Fin (n - b) ⊕ Fin b => Fin p → ℝ))
  -- both components of `ρ` read off blocks of rows
  have hval : ∀ (S : Fin n → Fin p → ℝ),
      (∀ i, (ρ S).1 i = fun k => S (eIdx (Sum.inl i)) k)
        ∧ (∀ i, (ρ S).2 i = fun k => S (eIdx (Sum.inr i)) k) :=
    fun S => ⟨fun i => rfl, fun i => rfl⟩
  have hidx : ∀ i : Fin b, eIdx (Sum.inr i) = (⟨(n - b) + i, by omega⟩ : Fin n) := by
    intro i; apply Fin.ext
    rw [heIdx, Equiv.trans_apply, finSumFinEquiv_apply_right, finCongr_apply, Fin.coe_cast,
      Fin.val_natAdd]
  have hact : ∀ S : Fin n → Fin p → ℝ, (ρ S).2 = activeRows hbn S := by
    intro S; funext i k
    have h1 : (ρ S).2 i k = S (eIdx (Sum.inr i)) k := by rw [(hval S).2 i]
    have h2 : activeRows hbn S i k = S (⟨(n - b) + i, by omega⟩ : Fin n) k := rfl
    rw [h1, h2, hidx i]
  -- a partial column sum over an injective row-selection is ≤ the full column sum
  have partial_le : ∀ {m : ℕ} (σ : Fin m ↪ Fin n)
      (S : Fin n → Fin p → ℝ) (k : Fin p), ∑ i, (S (σ i) k) ^ 2 ≤ ∑ j, (S j k) ^ 2 := by
    intro m σ S k
    rw [show (∑ i, (S (σ i) k) ^ 2)
          = ∑ x ∈ Finset.univ.map σ, (S x k) ^ 2 from
        (Finset.sum_map Finset.univ σ (fun j => (S j k) ^ 2)).symm]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun j _ _ => sq_nonneg _)
  set G : (Fin b → Fin p → ℝ) → ℝ≥0∞ :=
    fun X => ENNReal.ofReal ((Matrix.of X * (Matrix.of X)ᵀ).det ^ (-a / 2)) with hGdef
  have hGmeas : Measurable G := measurable_detGram b p a
  have hFeq : ∀ S : Fin n → Fin p → ℝ,
      ENNReal.ofReal ((activeGram hbn S) ^ (-a / 2)) = G ((ρ S).2) := by
    intro S; rw [hact S, hGdef]; rfl
  -- domain inclusion into the product of column balls
  have hincl : colBallMat n p n
      ⊆ ρ ⁻¹' (colBallMat (n - b) p n ×ˢ colBallMat b p n) := by
    intro S hS
    simp only [Set.mem_preimage, Set.mem_prod]
    refine ⟨fun k => ?_, fun k => ?_⟩
    · rw [show (∑ i, ((ρ S).1 i k) ^ 2) = ∑ i, (S (eIdx (Sum.inl i)) k) ^ 2 from
        Finset.sum_congr rfl (fun i _ => by rw [(hval S).1 i])]
      exact le_trans (partial_le ⟨fun i => eIdx (Sum.inl i),
        fun x y h => Sum.inl_injective (eIdx.injective h)⟩ S k) (hS k)
    · rw [show (∑ i, ((ρ S).2 i k) ^ 2) = ∑ i, (S (eIdx (Sum.inr i)) k) ^ 2 from
        Finset.sum_congr rfl (fun i _ => by rw [(hval S).2 i])]
      exact le_trans (partial_le ⟨fun i => eIdx (Sum.inr i),
        fun x y h => Sum.inr_injective (eIdx.injective h)⟩ S k) (hS k)
  -- transport by `ρ`, then Tonelli over the product
  have hmeasF : Measurable (fun S : Fin n → Fin p → ℝ =>
      ENNReal.ofReal ((activeGram hbn S) ^ (-a / 2))) := by
    have : (fun S : Fin n → Fin p → ℝ => ENNReal.ofReal ((activeGram hbn S) ^ (-a / 2)))
        = (fun S => G ((ρ S).2)) := funext hFeq
    rw [this]; exact hGmeas.comp (measurable_snd.comp ρ.measurable)
  calc (∫⁻ S in colBallMat n p n, ENNReal.ofReal ((activeGram hbn S) ^ (-a / 2)))
      ≤ ∫⁻ S in ρ ⁻¹' (colBallMat (n - b) p n ×ˢ colBallMat b p n),
          ENNReal.ofReal ((activeGram hbn S) ^ (-a / 2)) := lintegral_mono_set hincl
    _ = ∫⁻ S in ρ ⁻¹' (colBallMat (n - b) p n ×ˢ colBallMat b p n), (G ∘ Prod.snd) (ρ S) := by
        refine setLIntegral_congr_fun (ρ.measurable (by
          exact (measurableSet_colBallMat _ _ _).prod (measurableSet_colBallMat _ _ _)))
          (fun S _ => ?_)
        exact hFeq S
    _ = ∫⁻ y in colBallMat (n - b) p n ×ˢ colBallMat b p n, (G ∘ Prod.snd) y :=
        hρmp.setLIntegral_comp_preimage_emb ρ.measurableEmbedding (G ∘ Prod.snd) _
    _ = ∫⁻ x in colBallMat (n - b) p n, ∫⁻ y in colBallMat b p n, (G ∘ Prod.snd) (x, y) := by
        rw [Measure.volume_eq_prod]
        exact setLIntegral_prod _ ((hGmeas.comp measurable_snd).aemeasurable)
    _ = (∫⁻ y in colBallMat b p n, G y) * volume (colBallMat (n - b) p n) := by
        simp only [Function.comp_apply]
        rw [setLIntegral_const]
    _ < ⊤ := ENNReal.mul_lt_top (bRowGram_colBall_lt_top hbp haq)
        (colBallMat_volume_lt_top _ _ _)

/-- **The (D) `b ≥ 2` inner charge slab.** For `b ≤ n` and `a + b ≤ p`, the charge Gram integral over the
deep-factor box is bounded by a uniform constant times the corank-Gram det. The `b`-general lift of
`corankSlab_charge_sint_le`. -/
theorem corankSlabD_charge_sint_le {a b n p : ℕ} (hbn : b ≤ n) (hap : a + b ≤ p) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ Acor : Fin b → Fin n → ℝ,
      (∫⁻ S in matBox n p 1, ENNReal.ofReal ((chargeGramDet Acor S) ^ (-(a : ℝ) / 2)))
        ≤ C * ENNReal.ofReal (((Matrix.of Acor * (Matrix.of Acor)ᵀ).det) ^ (-(a : ℝ) / 2)) := by
  classical
  have hbp : b ≤ p := by omega
  have haq : (a : ℝ) < (p : ℝ) - b + 1 := by
    have : (a : ℝ) + b ≤ p := by exact_mod_cast hap
    linarith
  -- the uniform constant is the (Acor-independent) residual integral
  refine ⟨∫⁻ S in colBallMat n p n, ENNReal.ofReal ((activeGram hbn S) ^ (-(a : ℝ) / 2)),
    activeGram_colBall_lt_top hbn hbp haq, fun Acor => ?_⟩
  set G : ℝ := (Matrix.of Acor * (Matrix.of Acor)ᵀ).det with hG
  have hGnn : 0 ≤ G := (posSemidef_mul_transpose (Matrix.of Acor)).det_nonneg
  by_cases hb : G = 0
  · -- rank-deficient corank: the charge Gram vanishes pointwise
    have hcg0 : ∀ S : Fin n → Fin p → ℝ, chargeGramDet Acor S = 0 :=
      fun S => chargeGramDet_eq_zero_of_corank_singular Acor S hb
    rcases eq_or_ne (a : ℝ) 0 with ha0 | ha0
    · -- exponent `0`: every integrand is `1`; `μ(box) ≤ μ(colBall) = C`, RHS `= C·1`
      have hexp : (-(a : ℝ) / 2) = 0 := by rw [ha0]; ring
      have hone : ∀ (x : ℝ), ENNReal.ofReal (x ^ (-(a : ℝ) / 2)) = 1 := by
        intro x; rw [hexp, Real.rpow_zero, ENNReal.ofReal_one]
      rw [show (∫⁻ S in matBox n p 1, ENNReal.ofReal ((chargeGramDet Acor S) ^ (-(a : ℝ) / 2)))
            = ∫⁻ _S in matBox n p 1, (1 : ℝ≥0∞) from lintegral_congr (fun S => hone _),
        show (∫⁻ S in colBallMat n p n, ENNReal.ofReal ((activeGram hbn S) ^ (-(a : ℝ) / 2)))
            = ∫⁻ _S in colBallMat n p n, (1 : ℝ≥0∞) from lintegral_congr (fun S => hone _),
        hG, hone _, mul_one, setLIntegral_const, setLIntegral_const, one_mul, one_mul]
      exact measure_mono box_subset_colBall
    · -- exponent nonzero: `0^(-a/2) = 0`, so the LHS integral is `0`
      have hLHS : (∫⁻ S in matBox n p 1,
          ENNReal.ofReal ((chargeGramDet Acor S) ^ (-(a : ℝ) / 2))) = 0 := by
        rw [← lintegral_zero (μ := volume.restrict (matBox n p 1))]
        refine lintegral_congr (fun S => ?_)
        rw [hcg0 S, Real.zero_rpow (by intro h; apply ha0; linarith), ENNReal.ofReal_zero]
      rw [hLHS]; exact zero_le _
  · -- full row rank: rotate to canonical form and factor
    obtain ⟨O, hO, hfac⟩ := exists_canonical hbn Acor hb
    have hmeas : Measurable (fun S : Fin n → Fin p → ℝ =>
        ENNReal.ofReal ((chargeGramDet Acor S) ^ (-(a : ℝ) / 2))) := by
      unfold chargeGramDet
      apply ENNReal.measurable_ofReal.comp
      apply Measurable.comp (g := fun t : ℝ => t ^ (-(a : ℝ) / 2)) (by fun_prop)
      apply Continuous.measurable
      apply Continuous.matrix_det
      refine continuous_matrix (fun i j => ?_)
      simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, rmatMul]
      fun_prop
    calc (∫⁻ S in matBox n p 1, ENNReal.ofReal ((chargeGramDet Acor S) ^ (-(a : ℝ) / 2)))
        ≤ ∫⁻ S in colBallMat n p n, ENNReal.ofReal ((chargeGramDet Acor S) ^ (-(a : ℝ) / 2)) :=
          lintegral_mono_set box_subset_colBall
      _ = ∫⁻ S in colBallMat n p n,
            ENNReal.ofReal ((chargeGramDet (corankMul Acor O) S) ^ (-(a : ℝ) / 2)) := by
          rw [← cov_colBall O hO _ hmeas]
          refine setLIntegral_congr_fun (measurableSet_colBallMat n p n) (fun S _ => ?_)
          rw [chargeGramDet_colMulLeft]
      _ = ∫⁻ S in colBallMat n p n,
            ENNReal.ofReal (G ^ (-(a : ℝ) / 2)) * ENNReal.ofReal ((activeGram hbn S) ^ (-(a : ℝ) / 2)) := by
          refine setLIntegral_congr_fun (measurableSet_colBallMat n p n) (fun S _ => ?_)
          have hact : (0:ℝ) ≤ activeGram hbn S := by
            rw [activeGram]; exact (posSemidef_mul_transpose _).det_nonneg
          rw [hfac S, ← hG, Real.mul_rpow hGnn hact,
            ENNReal.ofReal_mul (Real.rpow_nonneg hGnn _)]
      _ = ENNReal.ofReal (G ^ (-(a : ℝ) / 2))
            * ∫⁻ S in colBallMat n p n, ENNReal.ofReal ((activeGram hbn S) ^ (-(a : ℝ) / 2)) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ = (∫⁻ S in colBallMat n p n, ENNReal.ofReal ((activeGram hbn S) ^ (-(a : ℝ) / 2)))
            * ENNReal.ofReal (G ^ (-(a : ℝ) / 2)) := by rw [mul_comm]

end CorankSlabD

end DLNFibre.DLN.RLCT
