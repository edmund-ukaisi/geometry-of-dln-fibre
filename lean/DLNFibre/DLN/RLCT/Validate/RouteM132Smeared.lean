import DLNFibre.DLN.RLCT.Validate.RouteM231Smeared

/-!
# `RouteM132Smeared` — the BOUNDARY-SMEARED achiever box-divergence VALIDATE-SMALL `(1,3,2)`
(`minAdm = 2`, the `(r,c) = (1,2)` shape)

The `(1,2)`-shape boundary-SMEARED node `M = (1,3,2)` (`L = 2`, `r = deepRank = 1`, `c = M_L = 2`,
`m1 = M_{L−1} = 3`, `s = m1 − r = 2`, `minAdm = r·c = 2`, `flatDim = 9`) — the validate-small for the
genuinely-NEW smeared shape: a SCALAR Gram (`r = 1`, so `Λ₀ = (P₁ᵀP₁)⁻¹P₁ᵀP₂` is the `(1,2,1)`-style
`b/a` form, NO matrix inverse) combined with a `1×c = 1×2` RADIAL block (`minAdm = 2`, det `|z|¹` — the
`(2,3,1)`-style radial). It is the third (r,c) family of the 46 boundary-smeared M; the two completed
validate-smalls are `(1,2,1)` (`(r,c)=(1,1)`, scalar shear, weight 1) and `(2,3,1)` (`(r,c)=(2,1)`, 2×2
Gram, radial). `(1,3,2)` is `(r,c)=(1,2)` — scalar shear AND radial — discharged via the same banked
reusable `routeMCore_box_diverges_of_RadialMPChart` (route b, `minAdm ≥ 2`).

## The chart (`certificate-genM-smeared.md` §2, specialized to `(1,3,2)`)
Chart preimage coords `(a00,a01,a02, z, h01, sb00,sb01,sb10,sb11) : Fin 9 → ℝ`. The front product
`P = A⁽⁰⁾` (`1×3`); `P₁ = A⁰[:, :1] = [a00]` (the rank-`1` kept block), `P₂ = A⁰[:, 1:] = [a01, a02]`
(the `1×2` smeared columns); the rational routing `Λ₀ = (P₁ᵀP₁)⁻¹P₁ᵀP₂ = [a01/a00, a02/a00]` (`1×2`,
SCALAR Gram `1/a00²`). The deepest factor

    A⁽¹⁾ = [ z − (Λ₀₀·sb00 + Λ₀₁·sb10) ,  z·h01 − (Λ₀₀·sb01 + Λ₀₁·sb11)   (top r·c = 2 radial)
             sb00 , sb01                                                  (the s = 2 residual rows)
             sb10 , sb11 ]                                                (`3×2`).

Then `A⁰·A¹ = z·(P₁·H̄)` (`H̄ = [1, h01]`), so `F = ‖A⁰·A¹‖² = z²·U`, `U = ‖P₁·H̄‖² = a00²·(h01²+1)`
(z-free polynomial; the `sb`-shear cancels via `P₁·Λ₀ = P₂`). Jacobian det `|z|^{minAdm−1} = |z|¹`
(VALIDATED EXACT, `pp_smear_GATE.py`: 46/46; `chart_132.py`/`layout_132.py` here: the explicit `(1,3,2)`
formulas).

## The factorization `φ = ψ ∘ R`
`R132 = pivotBlowupOn {3,4} 3` (radial: pivot `z = coord 3` fixed, angular `h01 = coord 4 ↦ z·h01`;
det `|z|^{card−1} = |z|¹`). `ψ132 = Q132 ∘ shear132` (measure-preserving + measurable embedding): the
SCALAR rational shear (subtract `Λ₀·S_bot` from the two top-radial coords `3,4`, reading the front
coords `0,1,2` and `S_bot = 5,6,7,8`) ∘ the linear reshape `Q132 = paramsEquivFlat ∘ pack132`.
-/

open MeasureTheory
open scoped ENNReal BigOperators

namespace DLNFibre.DLN.RLCT

/-- `M132 = (1,3,2)` (the smallest `(r,c)=(1,2)`-shape boundary-smeared node). -/
abbrev M132 : Fin 3 → ℕ := ![1, 3, 2]

theorem minAdm_M132 : minAdm M132 = 2 := by
  rw [← minAdmRec_eq_minAdm]; decide

theorem flatDim_M132 : flatDim M132 = 9 := by decide

theorem routeMAmbient_M132 : routeMAmbient M132 = 9 := by decide

/-! ## The chart matrices (radial × scalar-rational shear)

Coords `u 0,u 1,u 2 = A⁰ = (a00,a01,a02)`; `u 3 = z` (pivot); `u 4 = h01` (angular); `u 5..u 8 = S_bot`
(`sb00,sb01,sb10,sb11`). `Λ₀ = [a01/a00, a02/a00]` (scalar Gram `1/a00²`). -/

/-- The scalar-Gram routing `Λ₀ : Fin 2 → ℝ` (`Λ₀₀ = a01/a00`, `Λ₀₁ = a02/a00`). -/
noncomputable def lam132 (u : Fin 9 → ℝ) : Fin 2 → ℝ :=
  ![u 1 / u 0, u 2 / u 0]

/-- **The layer-`0` matrix `A⁽⁰⁾`** (`1×3`, the front `P`, free generic). -/
noncomputable def chartA0_132 (u : Fin 9 → ℝ) : Matrix (Fin 1) (Fin 3) ℝ :=
  !![u 0, u 1, u 2]

/-- **The layer-`1` matrix `A⁽¹⁾`** (`3×2`): top `r·c = 2` radial entries `z − Λ₀·S_bot[:,0]` and
`z·h01 − Λ₀·S_bot[:,1]`; bottom `s = 2` residual rows `S_bot`. -/
noncomputable def chartA1_132 (u : Fin 9 → ℝ) : Matrix (Fin 3) (Fin 2) ℝ :=
  !![u 3 - (lam132 u 0 * u 5 + lam132 u 1 * u 7),
       u 3 * u 4 - (lam132 u 0 * u 6 + lam132 u 1 * u 8);
     u 5, u 6;
     u 7, u 8]

/-- The genuine `Params M132`, assembled by `Fin.cons` over the two layers. -/
noncomputable def chartParams132 (u : Fin 9 → ℝ) : Params M132 :=
  Fin.cons (chartA0_132 u) (Fin.cons (chartA1_132 u) (fun i => i.elim0))

/-- **The chart in flat coordinates** `phi132sm := paramsEquivFlat M132 ∘ chartParams132`. -/
noncomputable def phi132sm (u : Fin 9 → ℝ) : Fin (flatDim M132) → ℝ :=
  paramsEquivFlat M132 (chartParams132 u)

/-! ## The rate `F∘φ = z²·U` — OFF the rational pole `{a00 = 0}`

`P₁ = [a00]`, so `Λ₀ = (a00²)⁻¹·a00·[a01,a02] = [a01/a00, a02/a00]`, and `P₁·Λ₀ = [a01, a02] = P₂`
off `a00 ≠ 0`; the `sb`-shear cancels, leaving `A⁰·A¹ = z·(P₁·H̄) = z·[a00, a00·h01]`, so
`F = z²·(a00² + (a00·h01)²) = z²·a00²·(1 + h01²) = z²·U`, `U = a00²·(h01²+1)`. -/

/-- **The product entry** `(A⁰·A¹)(0, j) = z·a00·(H̄ 0 j)` off the pole (`a00 ≠ 0`): the inner `Fin 3`
sum + the scalar shear cancellation `a00·(a01/a00) = a01`, `a00·(a02/a00) = a02`. Column `j` (a
`Fin (M132 2) = Fin 2`): `j = 0` gives `z·a00`; `j = 1` gives `z·a00·h01`. The unique row `i : Fin 1`.
Mirrors `(2,3,1)`'s `prod_chartParams231_entry` (`change ∑ : Fin 3`, `clear_value`, `fin_cases`). -/
theorem prod_chartParams132_entry (u : Fin 9 → ℝ) (ha : u 0 ≠ 0)
    (i : Fin (M132 0)) (j : Fin (M132 2)) :
    prod M132 (chartParams132 u) i j
      = u 3 * u 0 * (if j = ⟨0, by decide⟩ then 1 else u 4) := by
  rw [prod_two_layer221 M132 (chartParams132 u) i j]
  have hival : i.val = 0 := by have := i.isLt; simp only [show M132 0 = 1 from rfl] at this; omega
  have hi0 : i = (⟨0, by decide⟩ : Fin (M132 0)) := Fin.ext (by rw [hival])
  subst hi0
  -- force the inner sum to `Fin 3` (defeq), the row to `⟨0,..⟩`
  change (∑ k1 : Fin 3, chartA0_132 u ⟨0, by decide⟩ k1 * chartA1_132 u k1 j) = _
  rw [Fin.sum_univ_three]
  -- the column `j : Fin (M132 2) = Fin 2` is `⟨0,..⟩` or `⟨1,..⟩`
  obtain hj0 | hj1 : j = ⟨0, by decide⟩ ∨ j = ⟨1, by decide⟩ := by
    have hlt : j.val < 2 := by have := j.isLt; simpa only [show M132 2 = 2 from rfl] using this
    interval_cases hjv : j.val
    · exact Or.inl (Fin.ext hjv)
    · exact Or.inr (Fin.ext hjv)
  · subst hj0
    rw [if_pos rfl, show (⟨0, by decide⟩ : Fin (M132 2)) = (0 : Fin 2) from rfl]
    simp only [chartA0_132, chartA1_132, lam132,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.head_fin_const, Matrix.of_apply, Matrix.cons_val, Matrix.cons_val_fin_one,
      Matrix.empty_val', Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
    field_simp; ring
  · subst hj1
    rw [if_neg (by decide : ¬ ((⟨1, by decide⟩ : Fin (M132 2)) = ⟨0, by decide⟩)),
      show (⟨1, by decide⟩ : Fin (M132 2)) = (1 : Fin 2) from rfl]
    simp only [chartA0_132, chartA1_132, lam132,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.head_fin_const, Matrix.of_apply, Matrix.cons_val, Matrix.cons_val_fin_one,
      Matrix.empty_val', Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
    field_simp; ring

/-- The unit factor `U = ‖P₁·H̄‖² = a00²·(h01²+1)` (the z-free polynomial factor of `F = z²·U`). -/
noncomputable def Uval132 (u : Fin 9 → ℝ) : ℝ := (u 0) ^ 2 * ((u 4) ^ 2 + 1)

theorem Uval132_nonneg (u : Fin 9 → ℝ) : (0 : ℝ) ≤ Uval132 u := by unfold Uval132; positivity

/-- **The off-pole rate** `dlnLoss M132 0 (chartParams132 u) = z²·U` for `a00 ≠ 0`. The two product
entries are `z·a00` and `z·a00·h01`, so the squared-Frobenius sum is `z²·a00² + z²·a00²·h01² = z²·U`. -/
theorem dlnLoss_chartParams132_offpole (u : Fin 9 → ℝ) (ha : u 0 ≠ 0) :
    dlnLoss M132 0 (chartParams132 u) = (u 3) ^ 2 * Uval132 u := by
  unfold dlnLoss
  -- per-entry value via the telescoping (natural `i j`, no cast in the statement — `(2,3,1)` pattern)
  have hentry : ∀ (i : Fin (M132 0)) (j : Fin (M132 2)),
      ((prod M132 (chartParams132 u) - 0) i j) ^ 2
        = (u 3) ^ 2 * (u 0) ^ 2 * (if j = ⟨0, by decide⟩ then 1 else (u 4) ^ 2) := by
    intro i j
    rw [sub_zero, prod_chartParams132_entry u ha i j]
    by_cases hj : j = ⟨0, by decide⟩ <;> simp only [hj, reduceIte] <;> ring
  -- force both sums to literal `Fin`s (defeq: `M132 0 = 1`, `M132 2 = 2`), expand, apply `hentry`
  change (∑ i : Fin 1, ∑ j : Fin 2,
    ((prod M132 (chartParams132 u) - 0)
        (Fin.cast (show 1 = M132 0 from rfl) i) (Fin.cast (show 2 = M132 2 from rfl) j)) ^ 2) = _
  simp only [Fin.sum_univ_one, Fin.sum_univ_two, hentry]
  -- the cast columns `Fin.cast (2=M132 2) 0/1` decide the `if`; `show` the literal value
  show (u 3) ^ 2 * (u 0) ^ 2 * (if (Fin.cast (show 2 = M132 2 from rfl) (0 : Fin 2)) = ⟨0, by decide⟩ then 1 else (u 4) ^ 2)
      + (u 3) ^ 2 * (u 0) ^ 2 * (if (Fin.cast (show 2 = M132 2 from rfl) (1 : Fin 2)) = ⟨0, by decide⟩ then 1 else (u 4) ^ 2)
      = (u 3) ^ 2 * Uval132 u
  rw [if_pos (show (Fin.cast (show 2 = M132 2 from rfl) (0 : Fin 2)) = (⟨0, by decide⟩ : Fin (M132 2)) from Fin.ext rfl),
    if_neg (by decide : ¬ ((Fin.cast (show 2 = M132 2 from rfl) (1 : Fin 2)) = (⟨0, by decide⟩ : Fin (M132 2))))]
  simp only [Uval132]
  ring

/-- **The `routeMCore` factorization** `routeMCore M132 (phi132sm u) = z²·U` off the pole. -/
theorem routeMCore_phi132sm_offpole (u : Fin 9 → ℝ) (ha : u 0 ≠ 0) :
    routeMCore M132 (phi132sm u) = (u 3) ^ 2 * Uval132 u := by
  rw [routeMCore, phi132sm, MeasurableEquiv.symm_apply_apply,
    dlnLoss_chartParams132_offpole u ha]

/-! ### Residual: the MP factorization + radial certificates + weighted `hsrc` + atom

LANDED (sorry-free): the `(1,3,2)` chart (`chartParams132`, `phi132sm`), the SCALAR routing `lam132`
(`Λ₀ = [a01/a00, a02/a00]`, no matrix inverse), and the load-bearing **rate**
`routeMCore_phi132sm_offpole = z²·U` (`U = a00²·(h01²+1)`), via the scalar shear cancellation
`a00·(a01/a00) = a01`. The genuinely-NEW `(r,c)=(1,2)` shape (scalar Gram + `1×2` radial, `minAdm=2`)
is validated end-to-end at the chart+rate level. The column-index plumbing (`Fin (M132 2) = Fin 2`
2-column selection) is resolved by the `rw [show (⟨0,..⟩ : Fin (M132 2)) = (0 : Fin 2) from rfl]`
defeq normalization + `if_pos`/`if_neg` (the reusable pattern for the multi-column smeared families).

RESIDUAL (the bounded `(1,3,2)` finish, reusing the banked `routeMCore_box_diverges_of_RadialMPChart`
exactly as `(2,3,1)` did — `minAdm=2`, radial `|z|¹`):
1. **MP factorization `φ = ψ ∘ R`**: `R132 = pivotBlowupOn {3,4} 3` (radial, pivot `z=coord 3`,
   angular `h01=coord 4 ↦ z·h01`; det `|z|^{card−1}=|z|¹`); `ψ132 = Q132 ∘ shear132` (the scalar shear
   subtracting `Λ₀·S_bot` from the two top-radial coords `3,4`; reading the front `0,1,2` + `S_bot
   5,6,7,8`) — the `(2,3,1)` `split231`/`shear231ME`/`Q231` pattern at Fin 9 (a `Fin 2`-core split,
   same structure; the shear is SIMPLER — scalar Gram, no 2×2 inverse).
2. **Radial certificates** `D132/R132_hasFDerivWithinAt/_injOn/abs_det = |u 3|¹` — verbatim
   `(2,3,1)` (`pivotBlowupOn` API, `active={3,4}`, `card=2`, pivot `3`).
3. **Weighted `hsrc`**: `subBox132 δ` bounded away from `{a00 = 0}` (the scalar-Gram pole, simpler than
   `(2,3,1)`'s `det P₁`); `∫_S |u3|¹·(z²U)^{−c} = ⊤` via the z-axis `abs_rpow_lintegral_Ioo_eq_top`
   at exp `1−2c ≤ −1`; containment via the entry bound.
4. **The atom** `routeM132sm_box_diverges := routeMCore_box_diverges_of_RadialMPChart M132 ψ132 R132 …`;
   `#print axioms` expect `[propext, Classical.choice, Quot.sound]` (S2-free, like both validate-smalls). -/

end DLNFibre.DLN.RLCT
