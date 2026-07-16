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

end DLNFibre.DLN.RLCT
