import DLNFibre.DLN.RLCT.Validate.RouteMSJFrontCollapse
import DLNFibre.DLN.RLCT.Validate.RouteMSJDecoratedPeelMeas
import DLNFibre.Core.Matrix.OrthoRowComplement

/-!
# `DLNFibre.DLN.RLCT.Validate.RouteMSJFrontCoV` — the fixed-`F` two-matrix change-of-variables bound

The GS-route absorption bound for the front-collapse step (d1design Lane-1, NO Cauchy–Binet). For a
FIXED wide full-row-rank front `F : m×n` (`m ≤ n`, entries in `[−1,1]`, Gram-nonsingular) and a
measurable `ℝ≥0∞`-integrand `g` reading the product `W = F·A₁`, the box integral over the free tail
matrix `A₁` is bounded by the free-`F` Gram Jacobian times an `F`-independent finite factor times a
`W`-box integral of `g`:

    ∫⁻_{A₁ ∈ box(1)} g(F·A₁)
      ≤ det(F·Fᵀ)^{−p/2} · (2n)^{(n−m)p} · ∫⁻_{W ∈ box(n)} g(W).

**Route (fully elementary, block-Gram not Cauchy–Binet).** Extend `F` by an orthonormal
row-complement `S` (`Core.exists_ortho_complement_rows`) to a square `G = [F; S]` (`n×n`); then
`(det G)² = det(F·Fᵀ)` (the block-Gram identity `det_gram_fromRows_of_orthonormal`, off-diagonal
`S·Fᵀ = 0`), so `G` is invertible and `|det G|^p = det(F·Fᵀ)^{p/2}`. Left-multiplication `A₁ ↦ G·A₁`
is an invertible linear change of variables with Jacobian `|det G|^p` (`lintegral_comp_rmatMulLeft`,
the row-major transcription of `mulLeftₚ`); its top `m` rows are `W = F·A₁`, its bottom `n−m` rows the
orthonormal slack. Since every entry of `G` has `|·| ≤ 1` (top: `hFbox`; bottom: `S·Sᵀ = 1` ⟹ unit
rows), `A₁ ∈ box(1)` forces `G·A₁ ∈ box(n)`. The bottom slack rows are Fubini-integrated out at cost
the box volume `(2n)^{(n−m)p}` (`lintegral_topRows_box`); `g` reads only the top rows, so the residual
is the `W`-box integral.

S2-FREE except the cited orthonormal-complement engine brick. Axiom-clean
`[propext, Classical.choice, Quot.sound]`.
-/

namespace DLNFibre.DLN.RLCT

open MeasureTheory
open scoped ENNReal BigOperators Matrix

/-! ## The transpose linear equivalence (row-major ↔ column-major) -/

/-- **The transpose linear equivalence** `(Fin a → Fin b → ℝ) ≃ₗ (Fin b → Fin a → ℝ)`,
`Y ↦ (j,i) ↦ Y i j`.
Conjugating column-major left-multiplication (`mulLeftₚ`) by this equivalence turns it into the
row-major left-multiplication used by the front-collapse integrand. -/
def transposeLE (a b : ℕ) : (Fin a → Fin b → ℝ) ≃ₗ[ℝ] (Fin b → Fin a → ℝ) :=
  { toFun := fun Y j i => Y i j
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl
    invFun := fun Z i j => Z j i
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }

@[simp] theorem transposeLE_apply (a b : ℕ) (Y : Fin a → Fin b → ℝ) (j : Fin b) (i : Fin a) :
    transposeLE a b Y j i = Y i j := rfl

@[simp] theorem transposeLE_symm_apply (a b : ℕ) (Z : Fin b → Fin a → ℝ) (i : Fin a) (j : Fin b) :
    (transposeLE a b).symm Z i j = Z j i := rfl

/-! ## Row-major left-multiplication change of variables -/

/-- **The row-major left-multiplication CoV.** For an invertible square `G : Fin N × Fin N` and a
measurable `ℝ≥0∞`-integrand `φ` on `Fin N → Fin p → ℝ`, precomposing with the (per-column) left
multiplication `A ↦ (i,j) ↦ ∑ₖ Gᵢₖ·Aₖⱼ` scales the full-space integral by the reciprocal Jacobian
`|det G|^{−p}`. The row-major transcription of `lintegral_comp_mulLeftₚ`: conjugate the column-major
`mulLeftₚ p G` by the transpose equivalence `transposeLE`, so the determinant is `(det G)^p`
(`LinearMap.det_conj` + `det_mulLeftₚ`) and `map_linearMap_addHaar_eq_smul_addHaar` fires on the raw
pi type (no `Matrix.module`/`NormedSpace.toModule` diamond). -/
theorem lintegral_comp_rmatMulLeft {N p : ℕ} (G : Matrix (Fin N) (Fin N) ℝ) (hG : G.det ≠ 0)
    (φ : (Fin N → Fin p → ℝ) → ℝ≥0∞) (hφ : Measurable φ) :
    ∫⁻ A : Fin N → Fin p → ℝ, φ (fun i j => ∑ k, G i k * A k j)
      = ENNReal.ofReal (|G.det| ^ p)⁻¹ * ∫⁻ B, φ B := by
  set τ := transposeLE p N with hτ
  set T : (Fin N → Fin p → ℝ) →ₗ[ℝ] (Fin N → Fin p → ℝ) :=
    (τ : (Fin p → Fin N → ℝ) →ₗ[ℝ] (Fin N → Fin p → ℝ)) ∘ₗ (mulLeftₚ p G) ∘ₗ
      (τ.symm : (Fin N → Fin p → ℝ) →ₗ[ℝ] (Fin p → Fin N → ℝ)) with hTdef
  have hTapply : ∀ (A : Fin N → Fin p → ℝ) (i : Fin N) (j : Fin p),
      T A i j = ∑ k, G i k * A k j := by
    intro A i j
    rw [hTdef]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, hτ]
    rw [transposeLE_apply, mulLeftₚ_apply]
    simp only [Matrix.mulVec, dotProduct, transposeLE_symm_apply]
  have hdetT : LinearMap.det T = (G.det) ^ p := by
    rw [hTdef, LinearMap.det_conj (mulLeftₚ p G) τ, det_mulLeftₚ]
  have hdetTne : LinearMap.det T ≠ 0 := by rw [hdetT]; exact pow_ne_zero _ hG
  have hTmeas : Measurable T := T.continuous_of_finiteDimensional.measurable
  have hlhs : (∫⁻ A : Fin N → Fin p → ℝ, φ (fun i j => ∑ k, G i k * A k j))
      = ∫⁻ A, φ (T A) := rfl
  have habs : |((G.det) ^ p)⁻¹| = (|G.det| ^ p)⁻¹ := by rw [abs_inv, abs_pow]
  rw [hlhs, ← lintegral_map hφ hTmeas,
    Measure.map_linearMap_addHaar_eq_smul_addHaar volume hdetTne,
    lintegral_smul_measure, hdetT, habs, smul_eq_mul]

/-! ## The bottom-rows Fubini split -/

/-- **The top-rows box Fubini split.** For a row reindex `e : (Fin m ⊕ Fin K) ≃ Fin N` and a
measurable integrand `g` reading only the `e∘inl` (top-`m`) rows, the box integral over the full
`N`-row box factors: the bottom `K` rows contribute their box volume, the top `m` rows the free
`W`-box integral. Proved by the coordinate reindex `sumPiEquivProdPi ∘ piCongrLeft e` (measure
preserving) + Tonelli (`setLIntegral_prod`). -/
theorem lintegral_topRows_box {m K N p : ℕ} (e : (Fin m ⊕ Fin K) ≃ Fin N) (R : ℝ)
    (g : (Fin m → Fin p → ℝ) → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻ B in matBox N p R, g (fun i' j => B (e (Sum.inl i')) j)
      = volume (matBox K p R) * ∫⁻ W in matBox m p R, g W := by
  classical
  -- The coordinate reindex product ≃ᵐ Fin-N pi.
  set Ψ : ((Fin m → Fin p → ℝ) × (Fin K → Fin p → ℝ)) ≃ᵐ (Fin N → Fin p → ℝ) :=
    (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin m ⊕ Fin K => Fin p → ℝ)).symm.trans
      (MeasurableEquiv.piCongrLeft (fun _ : Fin N => Fin p → ℝ) e) with hΨdef
  have hΨmp : MeasurePreserving Ψ volume volume := by
    rw [hΨdef]
    exact (volume_measurePreserving_piCongrLeft (fun _ : Fin N => Fin p → ℝ) e).comp
      (volume_measurePreserving_sumPiEquivProdPi_symm (fun _ : Fin m ⊕ Fin K => Fin p → ℝ))
  -- Ψ evaluates the top (inl) rows to the first factor, bottom (inr) rows to the second.
  have hΨ_inl : ∀ (x : (Fin m → Fin p → ℝ) × (Fin K → Fin p → ℝ)) (i' : Fin m),
      Ψ x (e (Sum.inl i')) = x.1 i' := by
    intro x i'
    rw [hΨdef]
    show (MeasurableEquiv.piCongrLeft (fun _ : Fin N => Fin p → ℝ) e)
        ((MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin m ⊕ Fin K => Fin p → ℝ)).symm x)
        (e (Sum.inl i')) = x.1 i'
    rw [MeasurableEquiv.piCongrLeft_apply_apply, MeasurableEquiv.coe_sumPiEquivProdPi_symm]
    rfl
  have hΨ_inr : ∀ (x : (Fin m → Fin p → ℝ) × (Fin K → Fin p → ℝ)) (k : Fin K),
      Ψ x (e (Sum.inr k)) = x.2 k := by
    intro x k
    rw [hΨdef]
    show (MeasurableEquiv.piCongrLeft (fun _ : Fin N => Fin p → ℝ) e)
        ((MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin m ⊕ Fin K => Fin p → ℝ)).symm x)
        (e (Sum.inr k)) = x.2 k
    rw [MeasurableEquiv.piCongrLeft_apply_apply, MeasurableEquiv.coe_sumPiEquivProdPi_symm]
    rfl
  -- The preimage of the box under Ψ is the product of the two smaller boxes.
  have hpre : Ψ ⁻¹' (matBox N p R) = matBox m p R ×ˢ matBox K p R := by
    ext x
    simp only [Set.mem_preimage, matBox, Set.mem_setOf_eq, Set.mem_prod]
    constructor
    · intro hB
      refine ⟨fun i' j => ?_, fun k j => ?_⟩
      · have := hB (e (Sum.inl i')) j; rwa [hΨ_inl] at this
      · have := hB (e (Sum.inr k)) j; rwa [hΨ_inr] at this
    · rintro ⟨hW, hSl⟩ i j
      obtain ⟨y, rfl⟩ := e.surjective i
      cases y with
      | inl i' => rw [hΨ_inl]; exact hW i' j
      | inr k => rw [hΨ_inr]; exact hSl k j
  -- The integrand reads only the top rows: `g (topRows (Ψ x)) = g x.1`.
  have hint : ∀ x : (Fin m → Fin p → ℝ) × (Fin K → Fin p → ℝ),
      g (fun i' j => Ψ x (e (Sum.inl i')) j) = g x.1 := by
    intro x; congr 1; funext i' j; rw [hΨ_inl]
  have hgtop : Measurable
      (fun B : Fin N → Fin p → ℝ => g (fun i' j => B (e (Sum.inl i')) j)) := by
    refine hg.comp (measurable_pi_lambda _ fun i' => measurable_pi_lambda _ fun j => ?_)
    exact (measurable_pi_apply j).comp (measurable_pi_apply (e (Sum.inl i')))
  -- Change variables through Ψ, then Tonelli off the bottom rows.
  calc ∫⁻ B in matBox N p R, g (fun i' j => B (e (Sum.inl i')) j)
      = ∫⁻ B in matBox N p R, g (fun i' j => B (e (Sum.inl i')) j) ∂(Measure.map Ψ volume) := by
        rw [hΨmp.map_eq]
    _ = ∫⁻ x in Ψ ⁻¹' (matBox N p R),
          g (fun i' j => Ψ x (e (Sum.inl i')) j) ∂volume :=
        setLIntegral_map (matBox_measurableSet N p R) hgtop Ψ.measurable
    _ = ∫⁻ x in matBox m p R ×ˢ matBox K p R, g x.1
          ∂((volume : Measure (Fin m → Fin p → ℝ)).prod volume) := by
        rw [hpre, Measure.volume_eq_prod]
        exact setLIntegral_congr_fun
          ((matBox_measurableSet m p R).prod (matBox_measurableSet K p R))
          (fun x _ => hint x)
    _ = ∫⁻ W in matBox m p R, ∫⁻ _Sl in matBox K p R, g W ∂volume ∂volume :=
        setLIntegral_prod _ ((hg.comp measurable_fst).aemeasurable)
    _ = ∫⁻ W in matBox m p R, g W * volume (matBox K p R) ∂volume := by
        refine lintegral_congr fun W => ?_
        rw [setLIntegral_const]
    _ = (∫⁻ W in matBox m p R, g W) * volume (matBox K p R) :=
        lintegral_mul_const _ hg
    _ = volume (matBox K p R) * ∫⁻ W in matBox m p R, g W := mul_comm _ _

/-! ## The fixed-`F` two-matrix change-of-variables bound -/

/-- **The fixed-`F` wide two-matrix CoV bound (GS route, NO Cauchy–Binet).** For a fixed wide
full-row-rank front `F : m×n` (`m ≤ n`, entries in `[−1,1]`, Gram-nonsingular) and a measurable
`ℝ≥0∞`-integrand `g`, the box integral over the free tail `A₁` of `g(F·A₁)` is bounded by the
free-`F` Gram Jacobian `det(F·Fᵀ)^{−p/2}` times the `F`-independent bottom-slack box volume
`(2n)^{(n−m)p}` times the `W`-box integral of `g`. The absorption change of variables extends `F` to
a square `G = [F; S]` (orthonormal row-complement `S`), whose determinant satisfies
`(det G)² = det(F·Fᵀ)`; `A₁ ↦ G·A₁` is invertible with top rows `F·A₁`, and every `G`-entry has
`|·| ≤ 1` so the image stays in the radius-`n` box, whose bottom `n−m` slack rows Fubini out. -/
theorem fixedF_wide_cov_bound {m n p : ℕ} (hmn : m ≤ n)
    (F : Fin m → Fin n → ℝ) (hFbox : ∀ i j, F i j ∈ Set.Icc (-1 : ℝ) 1)
    (hFdet : (Matrix.of F * (Matrix.of F)ᵀ).det ≠ 0)
    (g : (Fin m → Fin p → ℝ) → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻ A₁ in matBox n p 1, g (rmatMul F A₁)
      ≤ ENNReal.ofReal (((Matrix.of F * (Matrix.of F)ᵀ).det) ^ (-(p : ℝ) / 2))
        * (ENNReal.ofReal ((2 * (n : ℝ)) ^ ((n - m) * p))
            * ∫⁻ W in matBox m p (n : ℝ), g W) := by
  classical
  obtain ⟨S, hSF, hSS⟩ := exists_ortho_complement_rows hmn (Matrix.of F) hFdet
  set e : (Fin m ⊕ Fin (n - m)) ≃ Fin n :=
    finSumFinEquiv.trans (finCongr (Nat.add_sub_cancel' hmn)) with he
  set G : Matrix (Fin n) (Fin n) ℝ :=
    Matrix.reindex e (Equiv.refl (Fin n)) (Matrix.fromRows (Matrix.of F) S) with hGdef
  -- Entries of `G`: `H (e.symm ·)`, with the `inl` / `inr` rows reading `F` / `S`.
  have hG_entry : ∀ (i k : Fin n),
      G i k = Matrix.fromRows (Matrix.of F) S (e.symm i) k := by
    intro i k
    rw [hGdef, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.refl_symm, Equiv.refl_apply]
  have hG_inl : ∀ (i' : Fin m) (k : Fin n), G (e (Sum.inl i')) k = F i' k := by
    intro i' k
    rw [hG_entry, Equiv.symm_apply_apply, Matrix.fromRows_apply_inl, Matrix.of_apply]
  have hG_inr : ∀ (k' : Fin (n - m)) (k : Fin n), G (e (Sum.inr k')) k = S k' k := by
    intro k' k
    rw [hG_entry, Equiv.symm_apply_apply, Matrix.fromRows_apply_inr]
  -- Entrywise `|S| ≤ 1` from `S·Sᵀ = 1` (unit rows).
  have hSbd : ∀ (k' : Fin (n - m)) (k : Fin n), |S k' k| ≤ 1 := by
    intro k' k
    have hrow : ∑ j, S k' j * S k' j = 1 := by
      have h1 := congrFun (congrFun hSS k') k'
      rw [Matrix.mul_apply] at h1
      simp only [Matrix.transpose_apply, Matrix.one_apply_eq] at h1
      exact h1
    have hle1 : (S k' k) ^ 2 ≤ 1 := by
      rw [sq]
      calc S k' k * S k' k ≤ ∑ j, S k' j * S k' j :=
            Finset.single_le_sum (fun j _ => mul_self_nonneg _) (Finset.mem_univ k)
        _ = 1 := hrow
    exact (sq_le_one_iff_abs_le_one (S k' k)).mp hle1
  -- Entrywise `|G| ≤ 1`.
  have hGbd : ∀ (i k : Fin n), |G i k| ≤ 1 := by
    intro i k
    obtain ⟨y, rfl⟩ := e.surjective i
    cases y with
    | inl i' => rw [hG_inl]; exact abs_le.mpr ⟨(hFbox i' k).1, (hFbox i' k).2⟩
    | inr k' => rw [hG_inr]; exact hSbd k' k
  -- Block-Gram identity: `det(G·Gᵀ) = det(F·Fᵀ)`, hence `(det G)² = det(F·Fᵀ)` and `det G ≠ 0`.
  have hprod : G * Gᵀ = (Matrix.fromRows (Matrix.of F) S
      * (Matrix.fromRows (Matrix.of F) S)ᵀ).submatrix e.symm e.symm := by
    ext i i'
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.submatrix_apply, hG_entry]
  have hdetGGt : (G * Gᵀ).det = (Matrix.of F * (Matrix.of F)ᵀ).det := by
    rw [hprod, Matrix.det_submatrix_equiv_self,
      det_gram_fromRows_of_orthonormal (Matrix.of F) S hSF hSS]
  have hGsq : (G.det) ^ 2 = (Matrix.of F * (Matrix.of F)ᵀ).det := by
    have hmm : (G * Gᵀ).det = (G.det) ^ 2 := by rw [Matrix.det_mul, Matrix.det_transpose, sq]
    rw [← hmm, hdetGGt]
  have hGdetne : G.det ≠ 0 := by
    intro h; apply hFdet; rw [← hGsq, h]; ring
  -- The Jacobian rpow identity.
  have hrpow : ((Matrix.of F * (Matrix.of F)ᵀ).det) ^ (-(p : ℝ) / 2) = (|G.det| ^ p)⁻¹ := by
    rw [← hGsq, ← sq_abs G.det, ← Real.rpow_natCast (|G.det|) 2,
      ← Real.rpow_mul (abs_nonneg _),
      show ((2 : ℕ) : ℝ) * (-(p : ℝ) / 2) = -(p : ℝ) by push_cast; ring,
      Real.rpow_neg (abs_nonneg _), Real.rpow_natCast]
  -- The bottom-slack box volume `(2n)^{(n-m)p}`.
  have hvol : volume (matBox (n - m) p (n : ℝ))
      = ENNReal.ofReal ((2 * (n : ℝ)) ^ ((n - m) * p)) := by
    have hset : matBox (n - m) p (n : ℝ)
        = Set.univ.pi
            (fun _ : Fin (n - m) => Set.univ.pi (fun _ : Fin p => Set.Icc (-(n : ℝ)) n)) := by
      ext X; simp only [matBox, Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, true_implies]
    rw [hset, volume_pi_pi]
    have hinner : ∀ _i : Fin (n - m),
        volume (Set.univ.pi (fun _ : Fin p => Set.Icc (-(n:ℝ)) n))
          = ENNReal.ofReal (2 * (n : ℝ)) ^ p := by
      intro _
      rw [volume_pi_pi]
      simp only [Real.volume_Icc]
      rw [show (n:ℝ) - -(n:ℝ) = 2 * (n:ℝ) by ring, Finset.prod_const, Finset.card_univ,
        Fintype.card_fin]
    rw [Finset.prod_congr rfl (fun i _ => hinner i), Finset.prod_const, Finset.card_univ,
      Fintype.card_fin, ← pow_mul, ← ENNReal.ofReal_pow (by positivity), Nat.mul_comm]
  -- Measurability of the top-rows integrand.
  have hfunmeas : Measurable
      (fun B : Fin n → Fin p → ℝ => g (fun i' j => B (e (Sum.inl i')) j)) := by
    refine hg.comp (measurable_pi_lambda _ fun i' => measurable_pi_lambda _ fun j => ?_)
    exact (measurable_pi_apply j).comp (measurable_pi_apply (e (Sum.inl i')))
  set φ : (Fin n → Fin p → ℝ) → ℝ≥0∞ :=
    (matBox n p (n : ℝ)).indicator (fun B => g (fun i' j => B (e (Sum.inl i')) j)) with hφ
  have hφmeas : Measurable φ := by
    rw [hφ]; exact hfunmeas.indicator (matBox_measurableSet n p (n : ℝ))
  calc ∫⁻ A₁ in matBox n p 1, g (rmatMul F A₁)
      = ∫⁻ A₁ in matBox n p 1, φ (fun i j => ∑ k, G i k * A₁ k j) := by
        refine setLIntegral_congr_fun (matBox_measurableSet n p 1) fun A₁ hA₁ => ?_
        have himg : (fun i j => ∑ k, G i k * A₁ k j) ∈ matBox n p (n : ℝ) := by
          intro i j
          rw [Set.mem_Icc, ← abs_le]
          calc |∑ k, G i k * A₁ k j| ≤ ∑ k, |G i k * A₁ k j| := Finset.abs_sum_le_sum_abs _ _
            _ ≤ ∑ _k : Fin n, (1 : ℝ) := by
                refine Finset.sum_le_sum fun k _ => ?_
                rw [abs_mul]
                calc |G i k| * |A₁ k j| ≤ 1 * 1 :=
                      mul_le_mul (hGbd i k) (abs_le.mpr ⟨(hA₁ k j).1, (hA₁ k j).2⟩)
                        (abs_nonneg _) (by norm_num)
                  _ = 1 := by norm_num
            _ = (n : ℝ) := by simp
        rw [hφ, Set.indicator_of_mem himg]
        refine congrArg g ?_
        funext i' j
        simp only [hG_inl, rmatMul]
    _ ≤ ∫⁻ A₁ : Fin n → Fin p → ℝ, φ (fun i j => ∑ k, G i k * A₁ k j) := by
        conv_rhs => rw [← setLIntegral_univ]
        exact lintegral_mono_set (Set.subset_univ _)
    _ = ENNReal.ofReal (|G.det| ^ p)⁻¹ * ∫⁻ B, φ B :=
        lintegral_comp_rmatMulLeft G hGdetne φ hφmeas
    _ = ENNReal.ofReal (|G.det| ^ p)⁻¹ *
          (volume (matBox (n - m) p (n : ℝ)) * ∫⁻ W in matBox m p (n : ℝ), g W) := by
        rw [hφ, lintegral_indicator (matBox_measurableSet n p (n : ℝ)),
          lintegral_topRows_box e (n : ℝ) g hg]
    _ = ENNReal.ofReal (((Matrix.of F * (Matrix.of F)ᵀ).det) ^ (-(p : ℝ) / 2)) *
          (ENNReal.ofReal ((2 * (n : ℝ)) ^ ((n - m) * p)) * ∫⁻ W in matBox m p (n : ℝ), g W) := by
        rw [hrpow, hvol]

end DLNFibre.DLN.RLCT
