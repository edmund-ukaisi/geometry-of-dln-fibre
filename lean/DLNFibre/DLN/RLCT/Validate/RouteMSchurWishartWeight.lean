import DLNFibre.DLN.RLCT.Validate.RouteMSJGramResidual

set_option linter.style.longLine false

/-!
# `RouteMSchurWishartWeight` — the b-general charge-weight (Wishart) finiteness

The shallow-cell charge-weight bound for the CHARGED corank recursion (couplerad §w3-atlas): for a `b×m`
matrix `B` (`b ≤ m`), the matrix-variate integral `∫_{B∈matBox b m T} det(B·Bᵀ)^{−a/2}` is finite when
`a < m − b + 1` (corneradj's confirmed threshold, at the rank-`m` floor). The `b=1` case is the banked
`corankWeight_lt_top`; general `b` peels one row via the banked Gram-det row-residual recursion
`RouteMSJGramResidual.det_gram_cons` (`det(gram(cons w u)) = det(gram u)·‖P_{V⊥}w‖²`), reducing to the
lower-`b` weight times a projection-radial integral `∫_w ‖P_{V⊥}w‖^{−a}` (finite for `a < dim V⊥`,
`dim V⊥ ≥ m−(b−1)`). Non-spectral.

## Status + RESUME LADDER (handoff, off HEAD @784eef727)

LANDED: `det_mulTranspose_eq_det_gram` (the Gram bridge — the entry point to `det_gram_cons`).

RESUME LADDER (build order; the pieces are banked, this is assembly-at-scale, no wall — corneradj-confirmed
convergence, couplerad §w3-atlas/§w3-deep design):
1. **Shallow Wishart weight** `∫_{B∈matBox b m T} det(B·Bᵀ)^{−a/2} < ⊤` for `a < m−b+1`. Peel one row via
   `det_gram_cons` (`RouteMSJGramResidual.lean:194`, `det(gram(cons w u)) = det(gram u)·‖P_{V⊥}w‖²`) through
   the Gram bridge above; Fubini (Tonelli, `∫⁻` nonneg) + the projection-radial integrability
   `∫_w ‖P_{V⊥}w‖^{−a} ≤ C` (finite/uniform for `a < dim V⊥`, `dim V⊥ ≥ m−(b−1)`; reduce to a radial
   integral in the `dim V⊥`-subspace). `b=1` is the banked `corankWeight_lt_top`
   (`RouteMSJOffSectorB1.lean:124`, with the full-rank floor `hZ`).
2. **S-rank-flag cover**: instantiate the banked `deepCover_aux` spine at `S` over `matBox n p` —
   `rankEqLocus_eq_iUnion_pivot_inter` (`RouteMSJDeepCover:50`), `exists_nonsingular_submatrix_of_le_rank`
   (`RouteMSJPivotChart:266`), `generalPivot_reduce_rank(_of)` (`RouteMSJDeepPivot:106/142`);
   `deepRankLE_lintegral_lt_top` glues. Per-cell σ-measure CoV = a new pivot-minor-det Jacobian (standard).
3. **Shallow bolt-on cells** (`rank S ≥ a+b`): on the pivot chart, det-monotone `(A) det_le_det_of_posSemidef_sub`
   (`RouteMSchurPSDDetMono.lean`) reduces `det(A_cor·SSᵀ·A_corᵀ) ≥ det(A_cor·(δ²·rank-(a+b))·A_corᵀ)`, so
   charge ≤ Wishart const (step 1); residual = banked uncharged `routeMBoxThresholdFinite_mnp`.
4. **b=1 deep cell** (`rank S ≤ 1`, all 3 witnesses a=1): charge weight `W(S) ~ ln(1/σ)` (couplerad §w3-deep),
   killed by the codim-`c≥1` σ-measure; Lean route (option II) `ln(1/σ) ≤ C_ε·σ^{−ε}` (any `ε∈(0,1)`, uniform
   since `c≥1` always) → `σ^{−ε}·σ^{c−1}` integrable; track `L(S)` finite via the uncharged mnp on the cell;
   `δ=0` so it doesn't eat the loss budget. (`a≥2`/`b≥2` deep cells use couplerad's power E-recursion §w3-atlas
   — PING couplerad for the exact per-step inequality; NOT needed for the 3 b=1 witnesses.)
5. **Assemble** the interior endpoint `ChargedRectSchurCore m n p a b c' T` scoped `a+b ≤ ρ` (ρ = min n p =
   tailMinWidth), finite for `c' < ½·minAdm(![m,n,p])`. THIS IS item-4 hfin: the coupledBox re-architecture
   (arch1build @1691dd192) routes `shellSpine ≤ ∫coupledBox → in-regime(a+b≤ρ) via coupledCell_le_frontCell
   → item-4`, so the IN-REGIME cells consume this directly. Edge `a+b=ρ+1` is (D)/dbuild's, NOT here.

The scaffold's `ChargedRectSchurRecStep`/`ChargedRectSchurLowerIH`/`chargedRectCore_schurGen_lt_top`
(`RouteMSchurRectCharged.lean`) are VESTIGIAL (the charge can't be carried down the shared-rank drop — H1);
replace with the direct endpoint above.
-/

open Matrix
open scoped Matrix InnerProductSpace BigOperators

namespace DLNFibre.DLN.RLCT

/-- **Gram bridge.** `det(B·Bᵀ)` equals the determinant of the Gram matrix of `B`'s rows viewed as
Euclidean vectors — the entry point to the banked `det_gram_cons` row-residual recursion. -/
theorem det_mulTranspose_eq_det_gram {b m : ℕ} (B : Fin b → Fin m → ℝ) :
    ((Matrix.of B) * (Matrix.of B)ᵀ).det
      = (Matrix.gram ℝ (fun i => (WithLp.equiv 2 (Fin m → ℝ)).symm (B i))).det := by
  congr 1
  ext i j
  rw [Matrix.gram_apply,
    show ⟪(WithLp.equiv 2 (Fin m → ℝ)).symm (B i), (WithLp.equiv 2 (Fin m → ℝ)).symm (B j)⟫_ℝ
        = (B j) ⬝ᵥ star (B i) from rfl,
    Matrix.mul_apply]
  simp only [dotProduct, star_trivial, Matrix.transpose_apply, Matrix.of_apply]
  exact Finset.sum_congr rfl (fun k _ => by ring)

end DLNFibre.DLN.RLCT
