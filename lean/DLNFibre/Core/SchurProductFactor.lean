import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-!
# `DLNFibre.Core.SchurProductFactor` — the germ-preserving Schur factorisation

The exact matrix-algebra core of the L=2 D1 `≥`-leg explicit corner-elimination chart (Codex crux
steps 2–4, `threads/genm-hAtV`): for a two-layer product `M = A0 · A1` blocked at a common invertible
`r×r` pivot, the **Schur complement of the product factors as the product of the reduced blocks**:

    M22 − M21 · M11⁻¹ · M12 = A0red · A1red,    A0red = W − Z X⁻¹ Y,  A1red = V − U M11⁻¹ M12,

with `A0 = [[X, Y], [Z, W]]`, `A1 = [[S, T], [U, V]]`, product blocks `M11 = X S + Y U`,
`M12 = X T + Y V`, `M21 = Z S + W U`, `M22 = Z T + W V`, on the open set where `X` and `M11` are
invertible. Reduced blocks `A0red : (H0−r)×(H1−r)`, `A1red : (H1−r)×(H2−r)`, so `A0red · A1red` is the
reduced-core product `prod (H−r) (A0red, A1red)` — this pins the slice residual of the chart to
`dlnLoss (H−r) 0` (the reduced Aoyagi core).

This was previously only sympy-verified (`‖Δ‖ ≈ 1e-15` at the (4,4,4)/r=1 witness); here it is an
exact Lean theorem over any `CommRing`. It is `Ψsymm`-free (no existence-only IFT inverse): purely the
block algebra plus the two invertibility cancellations. Reusable for the L=2 chart certification AND
the ∀-`L` lift (the same corner elimination iterated across layers).
-/

open Matrix

namespace DLNFibre.Core

/-- **The Schur complement of a two-layer block product factors through the reduced blocks.**
With `A0 = [[X,Y],[Z,W]]`, `A1 = [[S,T],[U,V]]`, product blocks `M11 = X*S+Y*U` (invertible),
`M12 = X*T+Y*V`, `M21 = Z*S+W*U`, `M22 = Z*T+W*V`, and `X` invertible:

    (Z*T + W*V) − (Z*S + W*U) · ⅟M11 · (X*T + Y*V) = (W − Z·⅟X·Y) · (V − U·⅟M11·(X*T + Y*V)).

The right side is `A0red · A1red` with `A0red = W − Z⅟XY`, `A1red = V − U⅟M11 M12`. Proof: the middle
block `M21 = Z⅟X·M11 + A0red·U`, so `M21·⅟M11·M12 = Z⅟X·M12 + A0red·(U⅟M11 M12)`, and `Z⅟X·M12 =
Z*T + Z⅟XY·V` (both via `⅟X·X = 1`, `M11·⅟M11 = 1`); the remaining terms cancel additively. -/
theorem schur_product_factor {r p q p' : ℕ} {𝕜 : Type*} [CommRing 𝕜]
    (X : Matrix (Fin r) (Fin r) 𝕜) (Y : Matrix (Fin r) (Fin p) 𝕜)
    (Z : Matrix (Fin q) (Fin r) 𝕜) (W : Matrix (Fin q) (Fin p) 𝕜)
    (S : Matrix (Fin r) (Fin r) 𝕜) (T : Matrix (Fin r) (Fin p') 𝕜)
    (U : Matrix (Fin p) (Fin r) 𝕜) (V : Matrix (Fin p) (Fin p') 𝕜)
    [Invertible X] [Invertible (X * S + Y * U)] :
    (Z * T + W * V) - (Z * S + W * U) * ⅟(X * S + Y * U) * (X * T + Y * V)
      = (W - Z * ⅟X * Y) * (V - U * ⅟(X * S + Y * U) * (X * T + Y * V)) := by
  set M12 := X * T + Y * V with hM12
  set A0red := W - Z * ⅟X * Y with hA0red
  -- the two invertibility cancellations.
  have hZXX : Z * ⅟X * X = Z := Matrix.invOf_mul_cancel_right Z X
  have hZM11 : Z * ⅟X * (X * S + Y * U) * ⅟(X * S + Y * U) = Z * ⅟X :=
    Matrix.mul_invOf_cancel_right (Z * ⅟X) (X * S + Y * U)
  -- `M21 = Z⅟X·M11 + A0red·U`  (the middle-block identity).
  have hM21 : Z * S + W * U = Z * ⅟X * (X * S + Y * U) + A0red * U := by
    rw [hA0red, Matrix.mul_add, Matrix.sub_mul,
      ← Matrix.mul_assoc (Z * ⅟X) X S, hZXX, ← Matrix.mul_assoc (Z * ⅟X) Y U]
    abel
  -- `Z⅟X·M12 = Z*T + Z⅟X·Y·V`.
  have hZM12 : Z * ⅟X * M12 = Z * T + Z * ⅟X * Y * V := by
    rw [hM12, Matrix.mul_add, ← Matrix.mul_assoc (Z * ⅟X) X T, hZXX,
      ← Matrix.mul_assoc (Z * ⅟X) Y V]
  -- distribute `M21·⅟M11·M12` and collapse `M11·⅟M11`.
  have hmid : (Z * ⅟X * (X * S + Y * U) + A0red * U) * ⅟(X * S + Y * U) * M12
      = Z * ⅟X * M12 + A0red * U * ⅟(X * S + Y * U) * M12 := by
    rw [Matrix.add_mul, hZM11, Matrix.add_mul]
  -- reassociate the surviving cross term to match the RHS.
  have hassoc : A0red * U * ⅟(X * S + Y * U) * M12
      = A0red * (U * ⅟(X * S + Y * U) * M12) := by
    rw [Matrix.mul_assoc A0red U (⅟(X * S + Y * U)),
      Matrix.mul_assoc A0red (U * ⅟(X * S + Y * U)) M12]
  -- main assembly: substitute, distribute the remaining products, then cancel additively.
  rw [hM21, hmid, hZM12, hassoc, hA0red]
  simp only [Matrix.mul_sub, Matrix.sub_mul]
  abel

end DLNFibre.Core
