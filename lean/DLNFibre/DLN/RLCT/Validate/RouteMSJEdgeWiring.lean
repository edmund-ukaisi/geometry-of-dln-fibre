import DLNFibre.DLN.RLCT.Validate.RouteMSJEdgeLeaf
import DLNFibre.DLN.RLCT.Validate.RouteMSJChartShear

set_option linter.style.longLine false

/-!
# `RouteMSJEdgeWiring` — the b=1 freedSchurLoss → corank-atom wiring (connective tissue)

Thread `genm-tideD` (edge dispatch arm, b=1 a<u brick). The **freedSchurLoss wiring**: instantiate the
landed R1 a-fortiori (`corank_integrand_le`, `RouteMSJEdgeLeaf`) at the ACTUAL `freedSchurLoss` shape that
`coupledBoxIntegrand` carries on the b=1 edge cell.

At corank `b = 1` the corank row-block `Q_b = Q.submatrix Sum.inr id` is a single row `q_b`; write it as
`q_b = σ • ω` (`σ = ‖q_b‖`, `ω` unit) and the corank term of `freedSchurLoss x Γ Q`,
`frobSq (C·Q̃ₚ + Γ·Q_b)`, becomes `frobSq (C·Q̃ₚ + (σ γ) ⊗ ω)` (`γ = Γ·,0`) — the `corank_afortiori`
input. So `(freedSchurLoss x Γ Q)^{−c'}` is bounded above by the single-fragile-direction power
`(W + ‖C·v + σγ‖²)^{−c'}` (`W = frobSq(P·Q̃ₚ)`, `v = Q̃ₚ·ω`), the exact integrand the C-shift atoms
(`edge_C_shift_bound`, `edge_leaf_gamma_bound`) consume.
-/

namespace DLNFibre.DLN.RLCT

open Matrix
open scoped BigOperators ENNReal

/-- **The b=1 corank product is the scaled outer product.** For a single-column `Γ : Fin a → Fin 1 → ℝ`
and a single-row corank block `Q_b : Matrix (Fin 1) (Fin n)` written `q_b = σ • ω` (`Q_b 0 j = σ ω j`),
the matrix product `Γ · Q_b` is the rank-one outer product `(σ γ) ⊗ ω` (`γ = Γ·,0`):
`(Matrix.of Γ * Q_b) i j = σ · Γ i 0 · ω j`. `Matrix.mul_apply` + `Fin.sum_univ_one`. -/
theorem of_gamma_mul_corank_row {a n : ℕ} (Γ : Fin a → Fin 1 → ℝ)
    (Qb : Matrix (Fin 1) (Fin n) ℝ) (ω : Fin n → ℝ) (σ : ℝ)
    (hqb : ∀ j, Qb 0 j = σ * ω j) :
    (Matrix.of Γ * Qb) = Matrix.of (fun (i : Fin a) (j : Fin n) => σ * Γ i 0 * ω j) := by
  ext i j
  rw [Matrix.mul_apply, Fin.sum_univ_one, Matrix.of_apply, Matrix.of_apply, hqb j]
  ring

/-- **Unit-scale decomposition of a nonzero row.** Any nonzero `q : Fin n → ℝ` is `σ • ω` for
`σ = ‖q‖ > 0` and a unit `ω = q/σ` (`∑ ωⱼ² = 1`). Supplies the `(σ, ω)` data `coupledInner_slice_le`
(and the edge descent) consume from `q_b ≠ 0`. -/
theorem exists_unit_scale {n : ℕ} (q : Fin n → ℝ) (hq : q ≠ 0) :
    ∃ (σ : ℝ) (ω : Fin n → ℝ), 0 < σ ∧ (∑ j, (ω j) ^ 2 = 1) ∧ (∀ j, q j = σ * ω j) := by
  set S : ℝ := ∑ j, (q j) ^ 2 with hS
  have hSpos : 0 < S := by
    obtain ⟨j, hj⟩ := Function.ne_iff.1 hq
    exact Finset.sum_pos' (fun i _ => sq_nonneg _)
      ⟨j, Finset.mem_univ j, lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hj))⟩
  set σ : ℝ := Real.sqrt S with hσ
  have hσpos : 0 < σ := Real.sqrt_pos.mpr hSpos
  have hσsq : σ ^ 2 = S := Real.sq_sqrt hSpos.le
  refine ⟨σ, fun j => q j / σ, hσpos, ?_, fun j => by field_simp⟩
  have : ∑ j, (q j / σ) ^ 2 = (∑ j, (q j) ^ 2) / σ ^ 2 := by
    rw [Finset.sum_div]; exact Finset.sum_congr rfl (fun j _ => by rw [div_pow])
  rw [this, hσsq, ← hS, div_self (ne_of_gt hSpos)]

/-- **The b=1 corank row against the unit fragile direction is the scalar `σ`.** For `Q_b 0 = σ • ω`
(`ω` unit), `Q_b.mulVec ω = fun _ => σ`: `(Q_b.mulVec ω) 0 = ∑ⱼ σ ωⱼ · ωⱼ = σ·∑ⱼ ωⱼ² = σ`. -/
theorem corank_row_mulVec_omega {n : ℕ} (Qb : Matrix (Fin 1) (Fin n) ℝ) (ω : Fin n → ℝ) (σ : ℝ)
    (hω : ∑ j, (ω j) ^ 2 = 1) (hqb : ∀ j, Qb 0 j = σ * ω j) :
    Qb.mulVec ω = fun _ => σ := by
  funext k
  have hk : k = 0 := Subsingleton.elim k 0
  subst hk
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_congr rfl (fun j _ => by rw [hqb j]; ring :
      ∀ j ∈ Finset.univ, Qb 0 j * ω j = σ * (ω j) ^ 2), ← Finset.mul_sum, hω, mul_one]

/-- **The shear-cancel identity (b=1).** For the freed pivot factor `Q̃ₚ = Q_inl + PB·Q_inr`
(`PB = P⁻¹·B₁₂ : Matrix (Fin u) (Fin 1)`, single-row `Q_inr 0 = σ • ω`), the fragile direction
`v = Q̃ₚ·ω` decomposes as `Q_inl·ω + σ·(PB·,0)`. The `PB·Q_inr` cross-term contributes only
`σ·(PB·,0)` (since `Q_inr·ω = σ`), so subtracting it recovers the pivot-rows direction `Q_inl·ω` —
the C-shift target `v'` after the schur-shear substitution `D = Γ + C·PB`, INDEPENDENT of the front
`(P, B₁₂)`. -/
theorem qtp_mulVec_corank_one {u n : ℕ} (Qinl : Matrix (Fin u) (Fin n) ℝ)
    (PB : Matrix (Fin u) (Fin 1) ℝ) (Qinr : Matrix (Fin 1) (Fin n) ℝ) (ω : Fin n → ℝ) (σ : ℝ)
    (hω : ∑ j, (ω j) ^ 2 = 1) (hqb : ∀ j, Qinr 0 j = σ * ω j) :
    (Qinl + PB * Qinr).mulVec ω = Qinl.mulVec ω + σ • (fun i => PB i 0) := by
  rw [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, corank_row_mulVec_omega Qinr ω σ hω hqb]
  funext i
  simp only [Pi.add_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_one, Pi.smul_apply,
    smul_eq_mul]
  ring

/-- **The b=1 freedSchurLoss → corank-atom wiring (R1 at the edge-cell shape).** With the pivot core
`W = frobSq(P·Q̃ₚ) > 0` (`P = of x.1.1`, `Q̃ₚ = Q_inl + P⁻¹·B₁₂·Q_inr`) and the single corank row written
`Q_b 0 = σ • ω` (`ω` unit, `σ = ‖q_b‖`), the freed-Schur-loss power is bounded above by the
single-fragile-direction power the C-shift atoms consume:

    (freedSchurLoss x Γ Q)^{−c'} ≤ (W + ∑ᵢ ((of x.2)·(Q̃ₚ·ω) i + σ·Γ i 0)²)^{−c'}.

Rewrites the corank term `frobSq(C·Q̃ₚ + Γ·Q_b)` as `frobSq(C·Q̃ₚ + (σγ)⊗ω)` (`of_gamma_mul_corank_row`),
then applies the landed `corank_integrand_le`. The RHS is exactly `edge_C_shift_bound`'s integrand at
`v = Q̃ₚ·ω`, `β = σ·(Γ·,0)`. -/
theorem freedSchurLoss_corank_one_le {u a n : ℕ}
    (x : SJOuter u a 1) (Γ : Fin a → Fin 1 → ℝ) (Q : Matrix (Fin u ⊕ Fin 1) (Fin n) ℝ)
    (ω : Fin n → ℝ) (σ : ℝ) (hω : ∑ j, (ω j) ^ 2 = 1)
    (hqb : ∀ j, (Q.submatrix Sum.inr id) 0 j = σ * ω j) {c' : ℝ}
    (hW : 0 < frobSq (Matrix.of x.1.1 * (Q.submatrix Sum.inl id
        + (Matrix.of x.1.1)⁻¹ * Matrix.of x.1.2 * Q.submatrix Sum.inr id)))
    (hc' : 0 ≤ c') :
    ENNReal.ofReal ((freedSchurLoss x Γ Q) ^ (-c'))
      ≤ ENNReal.ofReal ((frobSq (Matrix.of x.1.1 * (Q.submatrix Sum.inl id
              + (Matrix.of x.1.1)⁻¹ * Matrix.of x.1.2 * Q.submatrix Sum.inr id))
            + ∑ i, ((Matrix.of x.2).mulVec ((Q.submatrix Sum.inl id
                + (Matrix.of x.1.1)⁻¹ * Matrix.of x.1.2 * Q.submatrix Sum.inr id).mulVec ω) i
              + σ * Γ i 0) ^ 2) ^ (-c')) := by
  set Qtp : Matrix (Fin u) (Fin n) ℝ := Q.submatrix Sum.inl id
      + (Matrix.of x.1.1)⁻¹ * Matrix.of x.1.2 * Q.submatrix Sum.inr id with hQtp
  -- the freed loss IS the R1 a-fortiori LHS: corank term = frobSq(C·Q̃ₚ + (σγ)⊗ω)
  have hfree : freedSchurLoss x Γ Q
      = frobSq (Matrix.of x.1.1 * Qtp)
        + frobSq (Matrix.of x.2 * Qtp
            + Matrix.of (fun (i : Fin a) (j : Fin n) => σ * Γ i 0 * ω j)) := by
    unfold freedSchurLoss
    rw [← hQtp, of_gamma_mul_corank_row Γ (Q.submatrix Sum.inr id) ω σ hqb]
  rw [hfree]
  exact corank_integrand_le x.2 Qtp (fun i => Γ i 0) ω σ hω hW hc'

/-- **The schur-shear cancellation (any `b`).** Substituting the corank block `Γ = D − schurShift x`
(`schurShift x = C·P⁻¹·B₁₂`) into `freedSchurLoss` collapses the cross-coupling: the corank term
`frobSq(C·Q̃ₚ + Γ·Q_b)` becomes `frobSq(C·Q_inl + D·Q_inr)` — the `C·P⁻¹·B₁₂·Q_inr` terms cancel
exactly. So the sheared loss reads the pivot rows `Q_inl` (deep factor) DIRECTLY, decoupled from the
front `(P, B₁₂)`; the pivot core `frobSq(P·Q̃ₚ)` is `Γ`-free and unchanged. This is the measure-side
shear (`D = Γ + schurShift` maps `shearBox → genBox`) at the value level; it makes the edge C-shift
target `v' = Q_inl·ω` (front-independent), the key decoupling of the b=1 leaf. -/
theorem freedSchurLoss_shear_eq {u a b n : ℕ} (x : SJOuter u a b) (D : Fin a → Fin b → ℝ)
    (Q : Matrix (Fin u ⊕ Fin b) (Fin n) ℝ) :
    freedSchurLoss x (D - schurShift x) Q
      = frobSq (Matrix.of x.1.1 * (Q.submatrix Sum.inl id
            + (Matrix.of x.1.1)⁻¹ * Matrix.of x.1.2 * Q.submatrix Sum.inr id))
        + frobSq (Matrix.of x.2 * Q.submatrix Sum.inl id
            + Matrix.of D * Q.submatrix Sum.inr id) := by
  unfold freedSchurLoss
  congr 1
  have hof : Matrix.of (D - schurShift x)
      = Matrix.of D - Matrix.of x.2 * (Matrix.of x.1.1)⁻¹ * Matrix.of x.1.2 := by
    ext i j
    simp only [schurShift, Matrix.of_apply, Matrix.sub_apply, Pi.sub_apply]
  rw [hof, Matrix.mul_add, Matrix.sub_mul]
  simp only [Matrix.mul_assoc]
  abel

/-- **The b=1 SHEARED freedSchurLoss → corank-atom wiring (the front-decoupled R1).** After the schur
shear (`Γ = D − schurShift x`), `(freedSchurLoss x (D−schurShift x) Q)^{−c'}` is bounded above by the
single-fragile-direction power with the FRONT-INDEPENDENT target `v' = Q_inl·ω`:

    (freedSchurLoss x (D−schurShift x) Q)^{−c'} ≤ (W + ∑ᵢ ((of x.2)·(Q_inl·ω) i + σ·D i 0)²)^{−c'}.

Composes `freedSchurLoss_shear_eq` (corank term = `frobSq(C·Q_inl + D·Q_inr)`), `of_gamma_mul_corank_row`
(`D·Q_inr = (σ (D·,0)) ⊗ ω` at b=1), and the landed `corank_integrand_le`. The RHS is
`edge_leaf_gamma_bound`'s integrand at `v = v' = Q_inl·ω`, `d = σ`, `γ = D·,0` — the target the
`|v'_{j₀}|^{−a}` (a<u) disposal consumes, decoupled from `(P, B₁₂)`. -/
theorem freedSchurLoss_shear_corank_one_le {u a n : ℕ}
    (x : SJOuter u a 1) (D : Fin a → Fin 1 → ℝ) (Q : Matrix (Fin u ⊕ Fin 1) (Fin n) ℝ)
    (ω : Fin n → ℝ) (σ : ℝ) (hω : ∑ j, (ω j) ^ 2 = 1)
    (hqb : ∀ j, (Q.submatrix Sum.inr id) 0 j = σ * ω j) {c' : ℝ}
    (hW : 0 < frobSq (Matrix.of x.1.1 * (Q.submatrix Sum.inl id
        + (Matrix.of x.1.1)⁻¹ * Matrix.of x.1.2 * Q.submatrix Sum.inr id)))
    (hc' : 0 ≤ c') :
    ENNReal.ofReal ((freedSchurLoss x (D - schurShift x) Q) ^ (-c'))
      ≤ ENNReal.ofReal ((frobSq (Matrix.of x.1.1 * (Q.submatrix Sum.inl id
              + (Matrix.of x.1.1)⁻¹ * Matrix.of x.1.2 * Q.submatrix Sum.inr id))
            + ∑ i, ((Matrix.of x.2).mulVec ((Q.submatrix Sum.inl id).mulVec ω) i
              + σ * D i 0) ^ 2) ^ (-c')) := by
  rw [freedSchurLoss_shear_eq, of_gamma_mul_corank_row D (Q.submatrix Sum.inr id) ω σ hqb]
  exact corank_integrand_le x.2 (Q.submatrix Sum.inl id) (fun i => D i 0) ω σ hω hW hc'

end DLNFibre.DLN.RLCT
