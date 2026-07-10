import DLNFibre.DLN.RLCT.Validate.RouteMSJFreedPeel

/-!
# `DLNFibre.DLN.RLCT.Validate.RouteMSJDecoratedPeelCore` — the peel CoV algebraic core (Phase 1)

**Thread `genm-decbuild`, Phase 1 (the certified CORE).** The transcribable, residual-0 algebraic
identities of the outer-descent peel change-of-variables, from the peelcert certificate
(`threads/genm-peelcert/cert.md`, §"THE CoV (i)+JACOBIAN (ii)"). These are the pointwise identities
the measure-theoretic CoV (the `|det P|^{−M₂}` Jacobian + the radial blow-up) consumes; both
matrix algebra, sorry-free.

## What lands here (sorry-free)

* **`freedSchurLoss_absorption`** — the (a) ABSORPTION rewrite. On the invertible-pivot chart
  (`IsUnit (Matrix.of x.1.1)`), the freed Schur loss re-expresses with `B₀ := P·Q̃ₚ` (the reduced
  leading product) as the primary variable and `C' := C·P⁻¹` the reduced coupling:
  `freedSchurLoss x Γ Q = frobSq B₀ + frobSq (C'·B₀ + Γ·Q_b)`. The content is `C·Q̃ₚ = C·P⁻¹·B₀`
  (`nonsing_inv_mul_cancel_left`).

* **`freedSchurLoss_smul`** — the (b) 2-HOMOGENEITY in the tail `Q`: `freedSchurLoss x Γ (c • Q) =
  c² · freedSchurLoss x Γ Q`. The radial-blow-up homogeneity (`(B,Y) = u·(B̂,Ŷ)`) at the loss level;
  combined with the Lebesgue Jacobian and the Gram power it yields `α = M₁M₂ − 1 − 2c′`.

## What is NOT here (the measure-theoretic CoV — the new obligation, Phase 1 continued)

The Lebesgue Jacobian `d(X) = |det P|^{−M₂} d(B)` of the linear absorption, the radial blow-up,
and the dominant-minor cover are NOT here. These identities are their pointwise integrand inputs.

S2-FREE: pure matrix algebra (banked `frobSq_smul`). Axiom-clean `[propext, Classical.choice,
Quot.sound]`.
-/

namespace DLNFibre.DLN.RLCT

open Matrix
open scoped BigOperators

/-- **The absorption rewrite of the freed Schur loss (cert step (a), residual-0).** On the
invertible-pivot chart, with `B₀ = P·Q̃ₚ` and `C' = C·P⁻¹`,
`freedSchurLoss x Γ Q = frobSq B₀ + frobSq (C'·B₀ + Γ·Q_b)`. Pure matrix algebra. -/
theorem freedSchurLoss_absorption {t a b q : ℕ} (x : SJOuter t a b) (Γ : Fin a → Fin b → ℝ)
    (Q : Matrix (Fin t ⊕ Fin b) (Fin q) ℝ) (hP : IsUnit (Matrix.of x.1.1)) :
    freedSchurLoss x Γ Q
      = frobSq (Matrix.of x.1.1 * (Q.submatrix Sum.inl id
            + (Matrix.of x.1.1)⁻¹ * Matrix.of x.1.2 * Q.submatrix Sum.inr id))
        + frobSq (Matrix.of x.2 * (Matrix.of x.1.1)⁻¹
              * (Matrix.of x.1.1 * (Q.submatrix Sum.inl id
                  + (Matrix.of x.1.1)⁻¹ * Matrix.of x.1.2 * Q.submatrix Sum.inr id))
            + Matrix.of Γ * Q.submatrix Sum.inr id) := by
  have hdet : IsUnit (Matrix.of x.1.1).det := (Matrix.isUnit_iff_isUnit_det _).mp hP
  unfold freedSchurLoss
  set Qtp := Q.submatrix Sum.inl id
    + (Matrix.of x.1.1)⁻¹ * Matrix.of x.1.2 * Q.submatrix Sum.inr id with hQtp
  have hkey : Matrix.of x.2 * (Matrix.of x.1.1)⁻¹ * (Matrix.of x.1.1 * Qtp)
      = Matrix.of x.2 * Qtp :=
    (Matrix.mul_assoc (Matrix.of x.2) (Matrix.of x.1.1)⁻¹ (Matrix.of x.1.1 * Qtp)).trans
      (congrArg (fun M => Matrix.of x.2 * M)
        (Matrix.nonsing_inv_mul_cancel_left (Matrix.of x.1.1) Qtp hdet))
  rw [hkey]

/-- **The freed Schur loss is 2-homogeneous in the tail (cert step (b) radial homogeneity).**
`freedSchurLoss x Γ (c • Q) = c² · freedSchurLoss x Γ Q`. The tail scale `c` (radial coordinate `u`)
pulls out as `u²`. Both `frobSq` arguments are linear in `Q`; `frobSq_smul` squares the scale. -/
theorem freedSchurLoss_smul {t a b q : ℕ} (x : SJOuter t a b) (Γ : Fin a → Fin b → ℝ)
    (c : ℝ) (Q : Matrix (Fin t ⊕ Fin b) (Fin q) ℝ) :
    freedSchurLoss x Γ (c • Q) = c ^ 2 * freedSchurLoss x Γ Q := by
  have e1 : ((c • Q).submatrix Sum.inl id : Matrix (Fin t) (Fin q) ℝ)
      = c • Q.submatrix Sum.inl id := rfl
  have e2 : ((c • Q).submatrix Sum.inr id : Matrix (Fin b) (Fin q) ℝ)
      = c • Q.submatrix Sum.inr id := rfl
  have hL1 : Matrix.of x.1.1 * ((c • Q).submatrix Sum.inl id
        + (Matrix.of x.1.1)⁻¹ * Matrix.of x.1.2 * (c • Q).submatrix Sum.inr id)
      = c • (Matrix.of x.1.1 * (Q.submatrix Sum.inl id
          + (Matrix.of x.1.1)⁻¹ * Matrix.of x.1.2 * Q.submatrix Sum.inr id)) := by
    rw [e1, e2, Matrix.mul_smul, ← smul_add, Matrix.mul_smul]
  have hL2 : Matrix.of x.2 * ((c • Q).submatrix Sum.inl id
          + (Matrix.of x.1.1)⁻¹ * Matrix.of x.1.2 * (c • Q).submatrix Sum.inr id)
        + Matrix.of Γ * (c • Q).submatrix Sum.inr id
      = c • (Matrix.of x.2 * (Q.submatrix Sum.inl id
            + (Matrix.of x.1.1)⁻¹ * Matrix.of x.1.2 * Q.submatrix Sum.inr id)
          + Matrix.of Γ * Q.submatrix Sum.inr id) := by
    rw [e1, e2, Matrix.mul_smul, ← smul_add, Matrix.mul_smul, Matrix.mul_smul, ← smul_add]
  unfold freedSchurLoss
  rw [hL1, hL2, frobSq_smul, frobSq_smul]
  ring

end DLNFibre.DLN.RLCT
