import DLNFibre.DLN.RLCT.Validate.RouteMSJGammaAtom

set_option linter.style.longLine false

/-!
# `RouteMSJLeafReduce` — the exact `ρ = deepTailMin` leaf reduction ALGEBRA (module (i-a))

**Thread `genm-sj5-stepbuild` (aoyagi-full Stage 2), step-3 module (i-a)** — the exact leaf reduction
(`genm-stepdesign/design.md §1`, VERIFIED numerically-exact, Codex-concurred).

The deep factor `Z` (an `M₂×n` layer product) generically has rank `ρ = deepTailMin M = min(M₂,…,M_last)`
(`< M₂` for narrow interior layers — the covarch `M₂`-polar TRAP, design §1(1)). Write the rank
factorisation `Z = S̃·Õ` with `S̃ : M₂×ρ` (full column rank) and `Õ : ρ×n` orthonormal ROWS
(`Õ Õᵀ = I_ρ`). The leaf variables are `Q̂_p = z0·S̃`, `Q̂_b = A_cor·S̃`; the full blocks are
`Q_p = z0·Z = Q̂_p·Õ`, `Q_b = A_cor·Z = Q̂_b·Õ`.

The ENTIRE front-charge integrand then equals the leaf integrand in dimension `ρ` — the three
identities (design §1):
- `det(Q_b Q_bᵀ) = det(Q̂_b Q̂_bᵀ)` (`leaf_det_eq`);
- `E_top = ‖P·Q̂_p + B·Q̂_b‖²` (`leaf_Etop_eq`);
- `E_tr = ‖C·(Q̂_p + P⁻¹B·Q̂_b)·(I_ρ − Π̂_b)‖²`, `Π̂_b = Q̂_bᵀ(Q̂_bQ̂_bᵀ)⁻¹Q̂_b` (`leaf_Etr_eq`) — the
  load-bearing key step, `Q̃_p(I_n − Π_b) = (Q̂_p+P⁻¹BQ̂_b)(I_ρ − Π̂_b)·Õ` then `‖·Õ‖_F = ‖·‖_F`.

Everything rides on three orthonormal-row primitives: `frobSq_mul_orthonormalRows` (`‖X·Õ‖_F = ‖X‖_F`,
from the banked `frobSq_mul_orthonormal_add`), `gram_mul_orthonormalRows` (`(X·Õ)(X·Õ)ᵀ = X·Xᵀ`), and
`proj_transport_orthonormalRows` (`Õ·(I_n − Õᵀ·Π̂·Õ) = (I_ρ − Π̂)·Õ`). This layer is det-charge-free
(pure algebra); the **measurable `S̃`-selector** (producing `S̃, Õ` from `Z` measurably a.e.-`z_tail`,
parallel to Brick F's frame selector) is the deferred "substance" (design §1 Lean-shape note).
-/

namespace DLNFibre.DLN.RLCT

open Matrix

variable {u b ρ n : ℕ}

/-! ## The three orthonormal-row primitives -/

/-- **`‖X·Õ‖_F = ‖X‖_F`** for `Õ` with orthonormal rows (`Õ Õᵀ = 1`). Right-multiplication by a
row-orthonormal `Õ` is a Frobenius isometry — the banked `frobSq_mul_orthonormal_add` at residual `0`. -/
theorem frobSq_mul_orthonormalRows (O : Matrix (Fin ρ) (Fin n) ℝ) (hO : O * Oᵀ = 1)
    {p : ℕ} (X : Matrix (Fin p) (Fin ρ) ℝ) : frobSq (X * O) = frobSq X := by
  have hz : frobSq (0 : Matrix (Fin p) (Fin n) ℝ) = 0 := by simp [frobSq]
  have h := frobSq_mul_orthonormal_add O hO X (0 : Matrix (Fin p) (Fin n) ℝ) (Matrix.zero_mul _)
  rw [add_zero, hz, add_zero] at h
  exact h

/-- **`(X·Õ)(X·Õ)ᵀ = X·Xᵀ`** for `Õ` row-orthonormal — the Gram is preserved (so the corank Gram and
its inverse are `Õ`-invariant). -/
theorem gram_mul_orthonormalRows (O : Matrix (Fin ρ) (Fin n) ℝ) (hO : O * Oᵀ = 1)
    {p : ℕ} (X : Matrix (Fin p) (Fin ρ) ℝ) : (X * O) * (X * O)ᵀ = X * Xᵀ := by
  rw [Matrix.transpose_mul, ← Matrix.mul_assoc, Matrix.mul_assoc X O Oᵀ, hO, Matrix.mul_one]

/-- **Projector transport** `Õ·(I_n − Õᵀ·Π̂·Õ) = (I_ρ − Π̂)·Õ` for `Õ` row-orthonormal. The full-space
projector `Π_b = Õᵀ·Π̂_b·Õ` pulls the transverse Schur complement back onto the `ρ`-leaf. -/
theorem proj_transport_orthonormalRows (O : Matrix (Fin ρ) (Fin n) ℝ) (hO : O * Oᵀ = 1)
    (Phat : Matrix (Fin ρ) (Fin ρ) ℝ) :
    O * (1 - Oᵀ * Phat * O) = (1 - Phat) * O := by
  rw [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul, Matrix.one_mul]
  congr 1
  rw [← Matrix.mul_assoc O (Oᵀ * Phat) O, ← Matrix.mul_assoc O Oᵀ Phat, hO, Matrix.one_mul]

/-! ## The three leaf-reduction identities -/

/-- **Leaf det identity** `det(Q_b Q_bᵀ) = det(Q̂_b Q̂_bᵀ)` (`Q_b = Q̂_b·Õ`) — the corank charge is
computed at the `ρ`-leaf. -/
theorem leaf_det_eq (O : Matrix (Fin ρ) (Fin n) ℝ) (hO : O * Oᵀ = 1)
    (Qhb : Matrix (Fin b) (Fin ρ) ℝ) :
    ((Qhb * O) * (Qhb * O)ᵀ).det = (Qhb * Qhbᵀ).det :=
  congrArg Matrix.det (gram_mul_orthonormalRows O hO Qhb)

/-- **Leaf pivot-energy identity** `‖P·Q_p + B·Q_b‖² = ‖P·Q̂_p + B·Q̂_b‖²` (`Q_p = Q̂_p·Õ`,
`Q_b = Q̂_b·Õ`) — the pivot energy `E_top` reduces to the `ρ`-leaf. -/
theorem leaf_Etop_eq (O : Matrix (Fin ρ) (Fin n) ℝ) (hO : O * Oᵀ = 1)
    (P : Matrix (Fin u) (Fin u) ℝ) (B : Matrix (Fin u) (Fin b) ℝ)
    (Qhp : Matrix (Fin u) (Fin ρ) ℝ) (Qhb : Matrix (Fin b) (Fin ρ) ℝ) :
    frobSq (P * (Qhp * O) + B * (Qhb * O)) = frobSq (P * Qhp + B * Qhb) := by
  rw [← Matrix.mul_assoc P Qhp O, ← Matrix.mul_assoc B Qhb O, ← Matrix.add_mul,
    frobSq_mul_orthonormalRows O hO]

/-- **Leaf transverse-Schur identity** `E_tr = ‖C·(Q̂_p + K·Q̂_b)·(I_ρ − Π̂_b)‖²`, `K = P⁻¹B`,
`Π̂_b = Q̂_bᵀ(Q̂_bQ̂_bᵀ)⁻¹Q̂_b` — the load-bearing key step (design §1): the full transverse Schur
`(C·Q̃_p)·(I_n − Π_b)` with `Q̃_p = Q_p + K·Q_b`, `Π_b = Q_bᵀ(Q_bQ_bᵀ)⁻¹Q_b`, equals the leaf one
right-multiplied by `Õ`, so `frobSq` (an `Õ`-isometry) reduces it to the `ρ`-leaf. -/
theorem leaf_Etr_eq (O : Matrix (Fin ρ) (Fin n) ℝ) (hO : O * Oᵀ = 1)
    {a : ℕ} (C : Matrix (Fin a) (Fin u) ℝ) (K : Matrix (Fin u) (Fin b) ℝ)
    (Qhp : Matrix (Fin u) (Fin ρ) ℝ) (Qhb : Matrix (Fin b) (Fin ρ) ℝ) :
    frobSq ((C * ((Qhp * O) + K * (Qhb * O)))
        * (1 - (Qhb * O)ᵀ * ((Qhb * O) * (Qhb * O)ᵀ)⁻¹ * (Qhb * O)))
      = frobSq ((C * (Qhp + K * Qhb))
        * (1 - Qhbᵀ * (Qhb * Qhbᵀ)⁻¹ * Qhb)) := by
  -- the projector `Π_b = Õᵀ·Π̂_b·Õ` (Gram-invariance folds the inverse onto the leaf)
  have hProj : (Qhb * O)ᵀ * ((Qhb * O) * (Qhb * O)ᵀ)⁻¹ * (Qhb * O)
      = Oᵀ * (Qhbᵀ * (Qhb * Qhbᵀ)⁻¹ * Qhb) * O := by
    rw [gram_mul_orthonormalRows O hO Qhb, Matrix.transpose_mul]
    simp only [Matrix.mul_assoc]
  -- the shifted pivot `Q̃_p = (Q̂_p + K·Q̂_b)·Õ`
  have hQtp : (Qhp * O) + K * (Qhb * O) = (Qhp + K * Qhb) * O := by
    rw [← Matrix.mul_assoc K Qhb O, ← Matrix.add_mul]
  -- the whole transverse-Schur argument is the leaf one, right-multiplied by `Õ`
  have harg : (C * ((Qhp * O) + K * (Qhb * O)))
        * (1 - (Qhb * O)ᵀ * ((Qhb * O) * (Qhb * O)ᵀ)⁻¹ * (Qhb * O))
      = ((C * (Qhp + K * Qhb)) * (1 - Qhbᵀ * (Qhb * Qhbᵀ)⁻¹ * Qhb)) * O := by
    rw [hProj, hQtp, ← Matrix.mul_assoc C (Qhp + K * Qhb) O,
      Matrix.mul_assoc (C * (Qhp + K * Qhb)) O (1 - Oᵀ * (Qhbᵀ * (Qhb * Qhbᵀ)⁻¹ * Qhb) * O),
      proj_transport_orthonormalRows O hO (Qhbᵀ * (Qhb * Qhbᵀ)⁻¹ * Qhb),
      ← Matrix.mul_assoc (C * (Qhp + K * Qhb)) (1 - Qhbᵀ * (Qhb * Qhbᵀ)⁻¹ * Qhb) O]
  exact (congrArg frobSq harg).trans (frobSq_mul_orthonormalRows O hO _)

end DLNFibre.DLN.RLCT
