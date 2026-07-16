import DLNFibre.DLN.RLCT.Validate.RouteMSJEdgeWiring
import DLNFibre.DLN.RLCT.Validate.RouteMSJEdgeCShift

set_option linter.style.longLine false

/-!
# `RouteMSJEdgeFubini` — the b=1 edge Fubini transport (connective tissue, measure side)

Thread `genm-tideD` (edge dispatch arm, b=1 a<u brick). The **measure-side transport** turning the edge
cell's `coupledBoxIntegrand` inner `∫_x ∫_Γ` into the form the C-shift atoms (`edge_leaf_gamma_bound`,
`RouteMSJEdgeCShift`) close.

* `shearBox_lintegral_eq` — the schur-shear CoV `∫_Γ in shearBox = ∫_D in genBox` (translation
  `D = Γ + schurShift x`, measure-preserving), moving to the FRONT-DECOUPLED sheared loss
  (`freedSchurLoss_shear_eq`).
-/

namespace DLNFibre.DLN.RLCT

open Matrix MeasureTheory
open scoped BigOperators ENNReal

/-- **The schur-shear change-of-variables.** For fixed front `x` and deep factor `Q`, the inner
`Γ`-integral over the shear-image box `{Γ | Γ + schurShift x ∈ genBox}` equals the `D`-integral over the
centered `genBox` of the SHEARED loss `freedSchurLoss x (D − schurShift x) Q`. The translation
`D = Γ + schurShift x` is measure-preserving and maps the shear-image box onto `genBox`
(`measurePreserving_add_right` + `setLIntegral_comp_preimage_emb`, the `chartInner_schurShearFree_eq`
template in reverse). Composing with `freedSchurLoss_shear_eq` puts the corank term in the
front-decoupled `frobSq(C·Q_inl + D·Q_inr)` form. -/
theorem shearBox_lintegral_eq {u a b n : ℕ} (x : SJOuter u a b)
    (Q : Matrix (Fin u ⊕ Fin b) (Fin n) ℝ) (c' T : ℝ) :
    (∫⁻ Γ in {Γ : Fin a → Fin b → ℝ | Γ + schurShift x ∈ genBox (Fin a) (Fin b) T},
        ENNReal.ofReal ((freedSchurLoss x Γ Q) ^ (-c')))
      = ∫⁻ D in genBox (Fin a) (Fin b) T,
          ENNReal.ofReal ((freedSchurLoss x (D - schurShift x) Q) ^ (-c')) := by
  have hshear := (measurePreserving_add_right (volume : Measure (Fin a → Fin b → ℝ))
      (schurShift x)).setLIntegral_comp_preimage_emb
    (measurableEmbedding_addRight (schurShift x))
    (fun D => ENNReal.ofReal ((freedSchurLoss x (D - schurShift x) Q) ^ (-c')))
    (genBox (Fin a) (Fin b) T)
  rw [← hshear]
  simp only [add_sub_cancel_right]
  rfl

/-- **Volume of the b=1 corank box** `genBox (Fin a) (Fin 1) 1 = 2^a`. -/
theorem volume_genBox_corank_one (a : ℕ) :
    volume (genBox (Fin a) (Fin 1) (1 : ℝ)) = ENNReal.ofReal (2 ^ a) := by
  have hgb : genBox (Fin a) (Fin 1) (1 : ℝ)
      = Set.pi Set.univ (fun _ : Fin a => Set.pi Set.univ (fun _ : Fin 1 => Set.Icc (-1 : ℝ) 1)) := by
    ext X; simp only [genBox, Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, true_implies]
  rw [hgb, volume_pi_pi]
  have hrow : ∀ _ : Fin a,
      (volume : Measure (Fin 1 → ℝ)) (Set.pi Set.univ (fun _ : Fin 1 => Set.Icc (-1 : ℝ) 1))
        = ENNReal.ofReal 2 := by
    intro _
    rw [volume_pi_pi]
    simp only [Real.volume_Icc]
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      show (1 : ℝ) - (-1) = 2 from by ring, pow_one]
  rw [Finset.prod_congr rfl (fun i _ => hrow i), Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, ← ENNReal.ofReal_pow (by norm_num)]

/-- **The b=1 edge C-γ reduction (to the C-shift atom).** For a fragile direction `v' : Fin (u'+1) → ℝ`
with `v' j₀ ≠ 0`, scalar `σ`, and pivot energy `W > 0`, the coupled `(D, C)`-box integral of the shifted
fragile residual (`D : Fin a → Fin 1 → ℝ` the corank column over the b=1 `genBox`, `C` the pivot core over
the `[−1,1]^{a×(u'+1)}` box) is dominated by `2^a·2^{a·u'}·|v'_{j₀}|^{−a}` times the full-space radial:

    ∫_D ∫_C (W + ‖(of C)·v' + σ·D·,0‖²)^{−c'}  ≤  2^a·(2^{a·u'}·|v'_{j₀}|^{−a}) · ∫_{ℝ^a}(W+‖x‖²)^{−c'}.

The b=1 form (`D : Fin a → Fin 1 → ℝ`, shift `σ·D i 0`) of `edge_leaf_gamma_bound`: apply `edge_C_shift_bound`
per corank slice `D` (β-invariant, shift `β i = σ·D i 0`), then integrate the constant bound over the corank
box (`volume genBox (Fin a) (Fin 1) 1 = 2^a`). The `radial` carries the `W^{a/2−c'}` pivot-energy dependence
(`scaledRadialEuclid`); finite for `a < 2c'`. -/
theorem edge_CD_reduction {a u' : ℕ} (v' : Fin (u' + 1) → ℝ) (j₀ : Fin (u' + 1)) (hj₀ : v' j₀ ≠ 0)
    (σ : ℝ) {W c' : ℝ} (hW : 0 < W) :
    (∫⁻ D in genBox (Fin a) (Fin 1) (1 : ℝ),
        ∫⁻ C in Set.pi Set.univ (fun _ : Fin a =>
            Set.pi Set.univ (fun _ : Fin (u' + 1) => Set.Icc (-1 : ℝ) 1)),
          ENNReal.ofReal ((W + ∑ i, ((Matrix.of C).mulVec v' i + σ * (D i 0)) ^ 2) ^ (-c')))
      ≤ ENNReal.ofReal (2 ^ a * (2 ^ (a * u') * (|v' j₀| ^ a)⁻¹))
          * ∫⁻ x : EuclideanSpace ℝ (Fin a), ENNReal.ofReal ((W + ‖x‖ ^ 2) ^ (-c')) := by
  set radial := ∫⁻ x : EuclideanSpace ℝ (Fin a), ENNReal.ofReal ((W + ‖x‖ ^ 2) ^ (-c')) with hradial
  set K : ℝ≥0∞ := ENNReal.ofReal (2 ^ (a * u') * (|v' j₀| ^ a)⁻¹) with hK
  calc (∫⁻ D in genBox (Fin a) (Fin 1) (1 : ℝ),
          ∫⁻ C in Set.pi Set.univ (fun _ : Fin a =>
              Set.pi Set.univ (fun _ : Fin (u' + 1) => Set.Icc (-1 : ℝ) 1)),
            ENNReal.ofReal ((W + ∑ i, ((Matrix.of C).mulVec v' i + σ * (D i 0)) ^ 2) ^ (-c')))
      ≤ ∫⁻ _D in genBox (Fin a) (Fin 1) (1 : ℝ), K * radial :=
        lintegral_mono (fun D => edge_C_shift_bound v' j₀ hj₀ (fun i => σ * (D i 0)) hW)
    _ = K * radial * ENNReal.ofReal (2 ^ a) := by rw [setLIntegral_const, volume_genBox_corank_one]
    _ = ENNReal.ofReal (2 ^ a * (2 ^ (a * u') * (|v' j₀| ^ a)⁻¹)) * radial := by
        rw [hK, mul_right_comm, ← ENNReal.ofReal_mul (by positivity),
          mul_comm (2 ^ (a * u') * (|v' j₀| ^ a)⁻¹)]

/-- **The b=1 edge per-slice corank charge (the assembled connective tissue).** For a fixed front pivot
pair `pb = (P, B₁₂)` and deep factor `Q`, with pivot energy `W = frobSq(P·Q̃ₚ) > 0`, single corank row
`Q_b 0 = σ • ω` (`ω` unit), and non-degenerate fragile direction `v' = Q_inl·ω` (`v'_{j₀} ≠ 0`), the
coupled `(C, Γ)`-box integral of the freed Schur loss (`C` the corank left-block over the pivot cube, `Γ`
the corank column over the schur-shear box) is dominated by the corank charge `2^a·2^{a·u'}·|v'_{j₀}|^{−a}`
times the full-space radial `∫_{ℝ^a}(W+‖x‖²)^{−c'}`:

    ∫_C ∫_Γ (freedSchurLoss (pb, C) Γ Q)^{−c'}  ≤  2^a·(2^{a·u'}·|v'_{j₀}|^{−a}) · radial(W).

Per `C`: schur-shear CoV (`shearBox_lintegral_eq`) to the front-decoupled loss, then the b=1 sheared R1
(`freedSchurLoss_shear_corank_one_le`) to the C-shift integrand at `v' = Q_inl·ω`; Tonelli reorder
(`lintegral_lintegral_swap`) to `∫_Γ ∫_C`, then the C-shift atom (`edge_CD_reduction`). `W`, `q_b`, `v'`
are all fixed here (independent of the integration variables `C`, `Γ`), so the bound is genuinely pointwise
— the a.e. positivity of `W`/`q_b` enters only in the outer `(pb, z, A_cor)` assembly. -/
theorem coupledInner_slice_le {u' a n : ℕ}
    (pb : (Fin (u' + 1) → Fin (u' + 1) → ℝ) × (Fin (u' + 1) → Fin 1 → ℝ))
    (Q : Matrix (Fin (u' + 1) ⊕ Fin 1) (Fin n) ℝ) (ω : Fin n → ℝ) (σ : ℝ)
    (hω : ∑ j, (ω j) ^ 2 = 1) (hqb : ∀ j, (Q.submatrix Sum.inr id) 0 j = σ * ω j)
    (j₀ : Fin (u' + 1)) (hj₀ : (Q.submatrix Sum.inl id).mulVec ω j₀ ≠ 0) {c' : ℝ}
    (hW : 0 < frobSq (Matrix.of pb.1 * (Q.submatrix Sum.inl id
        + (Matrix.of pb.1)⁻¹ * Matrix.of pb.2 * Q.submatrix Sum.inr id)))
    (hc' : 0 ≤ c') :
    (∫⁻ C in Set.pi Set.univ (fun _ : Fin a =>
          Set.pi Set.univ (fun _ : Fin (u' + 1) => Set.Icc (-1 : ℝ) 1)),
        ∫⁻ Γ in {Γ : Fin a → Fin 1 → ℝ | Γ + schurShift ((pb, C) : SJOuter (u' + 1) a 1)
            ∈ genBox (Fin a) (Fin 1) 1},
          ENNReal.ofReal ((freedSchurLoss ((pb, C) : SJOuter (u' + 1) a 1) Γ Q) ^ (-c')))
      ≤ ENNReal.ofReal (2 ^ a * (2 ^ (a * u') * (|(Q.submatrix Sum.inl id).mulVec ω j₀| ^ a)⁻¹))
          * ∫⁻ x : EuclideanSpace ℝ (Fin a),
              ENNReal.ofReal ((frobSq (Matrix.of pb.1 * (Q.submatrix Sum.inl id
                  + (Matrix.of pb.1)⁻¹ * Matrix.of pb.2 * Q.submatrix Sum.inr id)) + ‖x‖ ^ 2) ^ (-c')) := by
  set W : ℝ := frobSq (Matrix.of pb.1 * (Q.submatrix Sum.inl id
      + (Matrix.of pb.1)⁻¹ * Matrix.of pb.2 * Q.submatrix Sum.inr id)) with hWdef
  set v' : Fin (u' + 1) → ℝ := (Q.submatrix Sum.inl id).mulVec ω with hv'
  have hgmeas : Measurable (fun z : (Fin a → Fin (u' + 1) → ℝ) × (Fin a → Fin 1 → ℝ) =>
      ENNReal.ofReal ((W + ∑ i, ((Matrix.of z.1).mulVec v' i + σ * (z.2 i 0)) ^ 2) ^ (-c'))) := by
    apply ENNReal.measurable_ofReal.comp
    have hbase : Continuous (fun z : (Fin a → Fin (u' + 1) → ℝ) × (Fin a → Fin 1 → ℝ) =>
        W + ∑ i, ((Matrix.of z.1).mulVec v' i + σ * (z.2 i 0)) ^ 2) := by
      simp only [Matrix.mulVec, dotProduct, Matrix.of_apply]
      fun_prop
    exact (hbase.rpow_const (fun z => Or.inl (by positivity))).measurable
  -- Step 1+2: per C, shear CoV then the b=1 sheared R1
  have hstep : ∀ C : Fin a → Fin (u' + 1) → ℝ,
      (∫⁻ Γ in {Γ : Fin a → Fin 1 → ℝ | Γ + schurShift ((pb, C) : SJOuter (u' + 1) a 1)
          ∈ genBox (Fin a) (Fin 1) 1},
        ENNReal.ofReal ((freedSchurLoss ((pb, C) : SJOuter (u' + 1) a 1) Γ Q) ^ (-c')))
        ≤ ∫⁻ D in genBox (Fin a) (Fin 1) 1,
            ENNReal.ofReal ((W + ∑ i, ((Matrix.of C).mulVec v' i + σ * (D i 0)) ^ 2) ^ (-c')) := by
    intro C
    rw [shearBox_lintegral_eq ((pb, C) : SJOuter (u' + 1) a 1) Q c' 1]
    refine lintegral_mono (fun D => ?_)
    exact freedSchurLoss_shear_corank_one_le ((pb, C) : SJOuter (u' + 1) a 1) D Q ω σ hω hqb hW hc'
  calc (∫⁻ C in Set.pi Set.univ (fun _ : Fin a =>
            Set.pi Set.univ (fun _ : Fin (u' + 1) => Set.Icc (-1 : ℝ) 1)),
          ∫⁻ Γ in {Γ : Fin a → Fin 1 → ℝ | Γ + schurShift ((pb, C) : SJOuter (u' + 1) a 1)
              ∈ genBox (Fin a) (Fin 1) 1},
            ENNReal.ofReal ((freedSchurLoss ((pb, C) : SJOuter (u' + 1) a 1) Γ Q) ^ (-c')))
      ≤ ∫⁻ C in Set.pi Set.univ (fun _ : Fin a =>
            Set.pi Set.univ (fun _ : Fin (u' + 1) => Set.Icc (-1 : ℝ) 1)),
          ∫⁻ D in genBox (Fin a) (Fin 1) 1,
            ENNReal.ofReal ((W + ∑ i, ((Matrix.of C).mulVec v' i + σ * (D i 0)) ^ 2) ^ (-c')) :=
        lintegral_mono hstep
    _ = ∫⁻ D in genBox (Fin a) (Fin 1) 1,
          ∫⁻ C in Set.pi Set.univ (fun _ : Fin a =>
            Set.pi Set.univ (fun _ : Fin (u' + 1) => Set.Icc (-1 : ℝ) 1)),
            ENNReal.ofReal ((W + ∑ i, ((Matrix.of C).mulVec v' i + σ * (D i 0)) ^ 2) ^ (-c')) :=
        lintegral_lintegral_swap hgmeas.aemeasurable
    _ ≤ ENNReal.ofReal (2 ^ a * (2 ^ (a * u') * (|v' j₀| ^ a)⁻¹))
          * ∫⁻ x : EuclideanSpace ℝ (Fin a), ENNReal.ofReal ((W + ‖x‖ ^ 2) ^ (-c')) :=
        edge_CD_reduction v' j₀ hj₀ σ hW

end DLNFibre.DLN.RLCT
