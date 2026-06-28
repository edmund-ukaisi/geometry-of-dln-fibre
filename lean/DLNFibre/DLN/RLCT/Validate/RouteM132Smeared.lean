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

/-! ### The MP-factorization `φ = Q132 ∘ shear132 ∘ R132`

`R132 = pivotBlowupOn {3,4} 3` (radial: pivot `z = coord 3` fixed, angular `h01 = coord 4 ↦ z·h01`;
det `|z|^{card−1} = |z|¹`). `shear132` (z-free, MP): subtract `Λ₀·S_bot` from the two kept slots `3,4`
(reads the front coords `0,1,2` via `lam132` and `S_bot = coords 5,6,7,8`). `Q132 = paramsEquivFlat ∘
pack132` (the linear reshape). The pole `{a00 = 0}` is confined to `shear132`'s coefficient. -/

/-- **The reshape** `pack132 : (Fin 9 → ℝ) → Params M132`: coords `0,1,2 ↦ A⁰` (`1×3`), coords
`3..8 ↦ A¹` (`3×2`, row-major). Each output entry is one input coordinate. -/
noncomputable def pack132 (w : Fin 9 → ℝ) : Params M132 :=
  Fin.cons (!![w 0, w 1, w 2] : Matrix (Fin 1) (Fin 3) ℝ)
    (Fin.cons (!![w 3, w 4; w 5, w 6; w 7, w 8] : Matrix (Fin 3) (Fin 2) ℝ) (fun i => i.elim0))

/-- The explicit slot bijection `Fin 9 ≃ FlatIdx M132`. Layer `0` (`A⁰`, `1×3`): `(0,0),(0,1),(0,2) ↦
0,1,2`; layer `1` (`A¹`, `3×2`) row-major: `(0,0),(0,1),(1,0),(1,1),(2,0),(2,1) ↦ 3,4,5,6,7,8`. -/
noncomputable def fin9EquivFlatIdx132 : Fin 9 ≃ FlatIdx M132 where
  toFun := fun k =>
    match k with
    | ⟨0,_⟩ => ⟨⟨⟨0,by decide⟩,⟨0,by decide⟩⟩,⟨0,by decide⟩⟩
    | ⟨1,_⟩ => ⟨⟨⟨0,by decide⟩,⟨0,by decide⟩⟩,⟨1,by decide⟩⟩
    | ⟨2,_⟩ => ⟨⟨⟨0,by decide⟩,⟨0,by decide⟩⟩,⟨2,by decide⟩⟩
    | ⟨3,_⟩ => ⟨⟨⟨1,by decide⟩,⟨0,by decide⟩⟩,⟨0,by decide⟩⟩
    | ⟨4,_⟩ => ⟨⟨⟨1,by decide⟩,⟨0,by decide⟩⟩,⟨1,by decide⟩⟩
    | ⟨5,_⟩ => ⟨⟨⟨1,by decide⟩,⟨1,by decide⟩⟩,⟨0,by decide⟩⟩
    | ⟨6,_⟩ => ⟨⟨⟨1,by decide⟩,⟨1,by decide⟩⟩,⟨1,by decide⟩⟩
    | ⟨7,_⟩ => ⟨⟨⟨1,by decide⟩,⟨2,by decide⟩⟩,⟨0,by decide⟩⟩
    | ⟨8,_⟩ => ⟨⟨⟨1,by decide⟩,⟨2,by decide⟩⟩,⟨1,by decide⟩⟩
    | ⟨n+9,h⟩ => absurd h (by omega)
  invFun := fun q =>
    match q with
    | ⟨⟨⟨0,_⟩,⟨0,_⟩⟩,⟨0,_⟩⟩ => 0
    | ⟨⟨⟨0,_⟩,⟨0,_⟩⟩,⟨1,_⟩⟩ => 1
    | ⟨⟨⟨0,_⟩,⟨0,_⟩⟩,⟨2,_⟩⟩ => 2
    | ⟨⟨⟨1,_⟩,⟨0,_⟩⟩,⟨0,_⟩⟩ => 3
    | ⟨⟨⟨1,_⟩,⟨0,_⟩⟩,⟨1,_⟩⟩ => 4
    | ⟨⟨⟨1,_⟩,⟨1,_⟩⟩,⟨0,_⟩⟩ => 5
    | ⟨⟨⟨1,_⟩,⟨1,_⟩⟩,⟨1,_⟩⟩ => 6
    | ⟨⟨⟨1,_⟩,⟨2,_⟩⟩,⟨0,_⟩⟩ => 7
    | ⟨⟨⟨1,_⟩,⟨2,_⟩⟩,⟨1,_⟩⟩ => 8
  left_inv := by decide
  right_inv := by decide

theorem hpack132 (w : Fin 9 → ℝ) (q : FlatIdx M132) :
    pack132 w q.1.1 q.1.2 q.2 = w (fin9EquivFlatIdx132.symm q) := by
  obtain ⟨⟨s, i⟩, j⟩ := q
  fin_cases s <;> fin_cases i <;> fin_cases j <;> rfl

theorem measurePreserving_pack132 :
    MeasurePreserving pack132 (volume : Measure (Fin 9 → ℝ)) (volume : Measure (Params M132)) :=
  measurePreserving_paramsPack_of_flatIdxEquiv M132 fin9EquivFlatIdx132 pack132 hpack132

theorem measurePreserving_Q132 :
    MeasurePreserving (fun w : Fin 9 → ℝ => paramsEquivFlat M132 (pack132 w))
      (volume : Measure (Fin 9 → ℝ)) volume :=
  (measurePreserving_paramsEquivFlat M132).comp measurePreserving_pack132

/-- **The radial blow-up** `R132 = pivotBlowupOn {3,4} 3`: slot `3 = z` fixed (pivot), slot `4 ↦ z·h01`,
all else spectators. `det = z^{card−1} = z¹` (`active.card = 2`). -/
noncomputable def R132 : (Fin 9 → ℝ) → (Fin 9 → ℝ) := pivotBlowupOn ({3, 4} : Finset (Fin 9)) 3

theorem R132_apply (u : Fin 9 → ℝ) :
    R132 u = ![u 0, u 1, u 2, u 3, u 3 * u 4, u 5, u 6, u 7, u 8] := by
  funext i; fin_cases i <;> simp [R132, pivotBlowupOn, Matrix.cons_val]

/-- **The z-free scalar shear** `shear132`: subtract `Λ₀·S_bot` from the two kept slots `3,4` (reads
the front coords `0,1,2` via `lam132` and `S_bot = w 5,6,7,8`); all else fixed. -/
noncomputable def shear132 (w : Fin 9 → ℝ) : Fin 9 → ℝ :=
  fun i =>
    if i = 3 then w 3 - (lam132 w 0 * w 5 + lam132 w 1 * w 7)
    else if i = 4 then w 4 - (lam132 w 0 * w 6 + lam132 w 1 * w 8)
    else w i

theorem shear132_spectator (w : Fin 9 → ℝ) {k : Fin 9} (h3 : k ≠ 3) (h4 : k ≠ 4) :
    shear132 w k = w k := by simp only [shear132, if_neg h3, if_neg h4]

theorem shear132_kept (w : Fin 9 → ℝ) :
    shear132 w 3 = w 3 - (lam132 w 0 * w 5 + lam132 w 1 * w 7)
      ∧ shear132 w 4 = w 4 - (lam132 w 0 * w 6 + lam132 w 1 * w 8) := by
  refine ⟨?_, ?_⟩
  · simp only [shear132, if_true, reduceIte]
  · simp only [shear132, show (4 : Fin 9) = 3 ↔ False from by decide, if_false, if_true, reduceIte]

/-- `lam132` reads only coords `0,1,2`. -/
theorem lam132_spectator_eq (u v : Fin 9 → ℝ) (h0 : u 0 = v 0) (h1 : u 1 = v 1) (h2 : u 2 = v 2)
    (i : Fin 2) : lam132 u i = lam132 v i := by
  fin_cases i <;> simp only [lam132, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_fin_one, h0, h1, h2]

/-- **The factorization** `chartParams132 u = pack132 (shear132 (R132 u))`. -/
theorem chartParams132_eq_pack_shear_R (u : Fin 9 → ℝ) :
    chartParams132 u = pack132 (shear132 (R132 u)) := by
  have hlam : ∀ i, lam132 (R132 u) i = lam132 u i := by
    intro i; exact lam132_spectator_eq _ _ (by simp [R132_apply]) (by simp [R132_apply])
      (by simp [R132_apply]) i
  have hs : ∀ k : Fin 9, k ≠ 3 → k ≠ 4 → shear132 (R132 u) k = (R132 u) k :=
    fun k h3 h4 => shear132_spectator (R132 u) h3 h4
  obtain ⟨hk3, hk4⟩ := shear132_kept (R132 u)
  funext s
  fin_cases s
  · show chartA0_132 u = (pack132 (shear132 (R132 u))) 0
    have hp : (pack132 (shear132 (R132 u))) 0
        = (!![(shear132 (R132 u)) 0, (shear132 (R132 u)) 1, (shear132 (R132 u)) 2]
          : Matrix (Fin 1) (Fin 3) ℝ) := rfl
    rw [hp, hs 0 (by decide) (by decide), hs 1 (by decide) (by decide), hs 2 (by decide) (by decide)]
    funext i j
    fin_cases i <;> fin_cases j <;>
      simp [chartA0_132, R132_apply, Matrix.cons_val]
  · show chartA1_132 u = (pack132 (shear132 (R132 u))) 1
    have hp : (pack132 (shear132 (R132 u))) 1
        = (!![(shear132 (R132 u)) 3, (shear132 (R132 u)) 4;
            (shear132 (R132 u)) 5, (shear132 (R132 u)) 6;
            (shear132 (R132 u)) 7, (shear132 (R132 u)) 8] : Matrix (Fin 3) (Fin 2) ℝ) := rfl
    rw [hp, hk3, hk4, hs 5 (by decide) (by decide), hs 6 (by decide) (by decide),
      hs 7 (by decide) (by decide), hs 8 (by decide) (by decide), hlam 0, hlam 1]
    funext i j
    fin_cases i <;> fin_cases j <;>
      simp [chartA1_132, R132_apply, Matrix.cons_val] <;> ring

/-! ### `shear132` is a global measure-preserving measurable bijection (route b)

`shear132` translates coords `3,4` by `−Λ₀·S_bot` (reading the front `0,1,2` and `S_bot 5,6,7,8`),
identity elsewhere. MP via the explicit inverse + the single 2-core split `split132` (reg = coord 0,
core = `{3,4}`, spec = `{1,2,5,6,7,8}`) + the banked `coreShear_measurable 1 2 6`. -/

/-- **The inverse** `shear132Inv`: add `Λ₀·S_bot` back to coords `3,4`. -/
noncomputable def shear132Inv (v : Fin 9 → ℝ) : Fin 9 → ℝ :=
  fun i =>
    if i = 3 then v 3 + (lam132 v 0 * v 5 + lam132 v 1 * v 7)
    else if i = 4 then v 4 + (lam132 v 0 * v 6 + lam132 v 1 * v 8)
    else v i

theorem lam132_shear132 (u : Fin 9 → ℝ) (i : Fin 2) : lam132 (shear132 u) i = lam132 u i :=
  lam132_spectator_eq _ _ (shear132_spectator u (by decide) (by decide))
    (shear132_spectator u (by decide) (by decide)) (shear132_spectator u (by decide) (by decide)) i

theorem lam132_shear132Inv (u : Fin 9 → ℝ) (i : Fin 2) : lam132 (shear132Inv u) i = lam132 u i := by
  refine lam132_spectator_eq _ _ ?_ ?_ ?_ i <;>
    simp only [shear132Inv, if_neg (by decide : (0:Fin 9) ≠ 3), if_neg (by decide : (0:Fin 9) ≠ 4),
      if_neg (by decide : (1:Fin 9) ≠ 3), if_neg (by decide : (1:Fin 9) ≠ 4),
      if_neg (by decide : (2:Fin 9) ≠ 3), if_neg (by decide : (2:Fin 9) ≠ 4)]

theorem shear132_leftInv (u : Fin 9 → ℝ) : shear132Inv (shear132 u) = u := by
  funext i
  have hspec : ∀ k : Fin 9, k ≠ 3 → k ≠ 4 → shear132 u k = u k :=
    fun k h3 h4 => shear132_spectator u h3 h4
  obtain ⟨h3, h4⟩ := shear132_kept u
  rcases eq_or_ne i 3 with rfl | hi3
  · show shear132Inv (shear132 u) 3 = u 3
    simp only [shear132Inv, if_true, reduceIte, h3, lam132_shear132,
      hspec 5 (by decide) (by decide), hspec 7 (by decide) (by decide)]; ring
  rcases eq_or_ne i 4 with rfl | hi4
  · show shear132Inv (shear132 u) 4 = u 4
    simp only [shear132Inv, show (4:Fin 9)=3 ↔ False from by decide, if_false, if_true, reduceIte,
      h4, lam132_shear132, hspec 6 (by decide) (by decide), hspec 8 (by decide) (by decide)]; ring
  · show shear132Inv (shear132 u) i = u i
    simp only [shear132Inv, if_neg hi3, if_neg hi4, hspec i hi3 hi4]

theorem shear132_rightInv (v : Fin 9 → ℝ) : shear132 (shear132Inv v) = v := by
  funext i
  have hspec : ∀ k : Fin 9, k ≠ 3 → k ≠ 4 → shear132Inv v k = v k := by
    intro k h3 h4; simp only [shear132Inv, if_neg h3, if_neg h4]
  have h3 : shear132Inv v 3 = v 3 + (lam132 v 0 * v 5 + lam132 v 1 * v 7) := by
    simp only [shear132Inv, if_true, reduceIte]
  have h4 : shear132Inv v 4 = v 4 + (lam132 v 0 * v 6 + lam132 v 1 * v 8) := by
    simp only [shear132Inv, show (4:Fin 9)=3 ↔ False from by decide, if_false, if_true, reduceIte]
  rcases eq_or_ne i 3 with rfl | hi3
  · show shear132 (shear132Inv v) 3 = v 3
    simp only [shear132, if_true, reduceIte, h3, lam132_shear132Inv,
      hspec 5 (by decide) (by decide), hspec 7 (by decide) (by decide)]; ring
  rcases eq_or_ne i 4 with rfl | hi4
  · show shear132 (shear132Inv v) 4 = v 4
    simp only [shear132, show (4:Fin 9)=3 ↔ False from by decide, if_false, if_true, reduceIte,
      h4, lam132_shear132Inv, hspec 6 (by decide) (by decide), hspec 8 (by decide) (by decide)]; ring
  · show shear132 (shear132Inv v) i = v i
    simp only [shear132, if_neg hi3, if_neg hi4, hspec i hi3 hi4]

theorem lam132_measurable (i : Fin 2) : Measurable (fun w : Fin 9 → ℝ => lam132 w i) := by
  have hpi : ∀ k : Fin 9, Measurable (fun w : Fin 9 → ℝ => w k) := measurable_pi_apply
  fin_cases i <;>
    simp only [lam132, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_fin_one]
  · exact (hpi 1).div (hpi 0)
  · exact (hpi 2).div (hpi 0)

theorem shear132_measurable : Measurable shear132 := by
  apply measurable_pi_iff.2; intro i
  have hpi : ∀ k : Fin 9, Measurable (fun w : Fin 9 → ℝ => w k) := measurable_pi_apply
  rcases eq_or_ne i 3 with rfl | hi3
  · simp only [shear132, if_true, reduceIte]
    exact (hpi 3).sub (((lam132_measurable 0).mul (hpi 5)).add ((lam132_measurable 1).mul (hpi 7)))
  rcases eq_or_ne i 4 with rfl | hi4
  · simp only [shear132, show (4:Fin 9)=3 ↔ False from by decide, if_false, if_true, reduceIte]
    exact (hpi 4).sub (((lam132_measurable 0).mul (hpi 6)).add ((lam132_measurable 1).mul (hpi 8)))
  · simp only [shear132, if_neg hi3, if_neg hi4]; exact hpi i

theorem shear132Inv_measurable : Measurable shear132Inv := by
  apply measurable_pi_iff.2; intro i
  have hpi : ∀ k : Fin 9, Measurable (fun w : Fin 9 → ℝ => w k) := measurable_pi_apply
  rcases eq_or_ne i 3 with rfl | hi3
  · simp only [shear132Inv, if_true, reduceIte]
    exact (hpi 3).add (((lam132_measurable 0).mul (hpi 5)).add ((lam132_measurable 1).mul (hpi 7)))
  rcases eq_or_ne i 4 with rfl | hi4
  · simp only [shear132Inv, show (4:Fin 9)=3 ↔ False from by decide, if_false, if_true, reduceIte]
    exact (hpi 4).add (((lam132_measurable 0).mul (hpi 6)).add ((lam132_measurable 1).mul (hpi 8)))
  · simp only [shear132Inv, if_neg hi3, if_neg hi4]; exact hpi i

noncomputable def shear132ME : (Fin 9 → ℝ) ≃ᵐ (Fin 9 → ℝ) where
  toFun := shear132
  invFun := shear132Inv
  left_inv := shear132_leftInv
  right_inv := shear132_rightInv
  measurable_toFun := shear132_measurable
  measurable_invFun := shear132Inv_measurable

/-- The `Fin 8 → ℝ ≃ᵐ (Fin 2 → ℝ) × (Fin 6 → ℝ)` peel pulling the core coords `3,4` (after coord `0`
removed; in `Fin 8` they sit at indices `2,3`). -/
noncomputable def coreSpec132 :
    (Fin 8 → ℝ) ≃ᵐ (Fin 2 → ℝ) × (Fin 6 → ℝ) :=
  (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 8 => ℝ) 2).trans
    (((MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ)
      ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin 7 => ℝ) 2).trans
        (MeasurableEquiv.prodCongr
          (MeasurableEquiv.funUnique (Fin 1) ℝ).symm
          (MeasurableEquiv.refl (Fin 6 → ℝ))))).trans
    (((MeasurableEquiv.prodAssoc :
        (ℝ × (Fin 1 → ℝ)) × (Fin 6 → ℝ) ≃ᵐ
          ℝ × ((Fin 1 → ℝ) × (Fin 6 → ℝ))).symm).trans
      (MeasurableEquiv.prodCongr
        (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 2 => ℝ) 0).symm
        (MeasurableEquiv.refl (Fin 6 → ℝ))))))

noncomputable def split132 :
    (Fin 9 → ℝ) ≃ᵐ (Fin 1 → ℝ) × ((Fin 2 → ℝ) × (Fin 6 → ℝ)) :=
  (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 9 => ℝ) 0).trans
    (MeasurableEquiv.prodCongr
      (MeasurableEquiv.funUnique (Fin 1) ℝ).symm
      coreSpec132)

theorem measurePreserving_coreSpec132 :
    MeasurePreserving (coreSpec132 : (Fin 8 → ℝ) → _) volume volume := by
  unfold coreSpec132
  refine (volume_preserving_piFinSuccAbove (fun _ : Fin 8 => ℝ) 2).trans ?_
  have hstep1 : MeasurePreserving
      ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin 7 => ℝ) 2).trans
        (MeasurableEquiv.prodCongr (MeasurableEquiv.funUnique (Fin 1) ℝ).symm
          (MeasurableEquiv.refl (Fin 6 → ℝ))))
      (volume : Measure (Fin 7 → ℝ)) volume := by
    refine (volume_preserving_piFinSuccAbove (fun _ : Fin 7 => ℝ) 2).trans ?_
    exact MeasurePreserving.prod
      (volume_preserving_funUnique (Fin 1) ℝ).symm
      (MeasurePreserving.id (volume : Measure (Fin 6 → ℝ)))
  refine (MeasurePreserving.prod (MeasurePreserving.id (volume : Measure ℝ)) hstep1).trans ?_
  refine ((volume_preserving_prodAssoc (α₁ := ℝ) (β₁ := Fin 1 → ℝ) (γ₁ := Fin 6 → ℝ)).symm
      MeasurableEquiv.prodAssoc).trans ?_
  exact MeasurePreserving.prod
    (volume_preserving_piFinSuccAbove (fun _ : Fin 2 => ℝ) 0).symm
    (MeasurePreserving.id (volume : Measure (Fin 6 → ℝ)))

theorem measurePreserving_split132 :
    MeasurePreserving (split132 : (Fin 9 → ℝ) → _) volume volume := by
  unfold split132
  refine (volume_preserving_piFinSuccAbove (fun _ : Fin 9 => ℝ) 0).trans ?_
  exact MeasurePreserving.prod
    (volume_preserving_funUnique (Fin 1) ℝ).symm
    measurePreserving_coreSpec132

/-- Reconstruct coords `{0,1,2,5,6,7,8}` (with `0` in core slots `3,4`) from the split base. -/
noncomputable def base132 (q : (Fin 1 → ℝ) × (Fin 6 → ℝ)) : Fin 9 → ℝ :=
  ![q.1 0, q.2 0, q.2 1, 0, 0, q.2 2, q.2 3, q.2 4, q.2 5]

/-- The `Fin 2` core shift `−Λ₀·S_bot` (col 0 from sb00=spec2, sb10=spec4; col 1 from sb01=spec3,
sb11=spec5). -/
noncomputable def shift132 :
    (Fin 1 → ℝ) × (Fin 6 → ℝ) → (Fin 2 → ℝ) :=
  fun q => ![- (lam132 (base132 q) 0 * q.2 2 + lam132 (base132 q) 1 * q.2 4),
             - (lam132 (base132 q) 0 * q.2 3 + lam132 (base132 q) 1 * q.2 5)]

theorem base132_measurable : Measurable base132 := by
  apply measurable_pi_iff.2; intro i
  have hf : Measurable (fun x : (Fin 1 → ℝ) × (Fin 6 → ℝ) => x.1 0) :=
    (measurable_pi_apply 0).comp measurable_fst
  have hs : ∀ k : Fin 6, Measurable (fun x : (Fin 1 → ℝ) × (Fin 6 → ℝ) => x.2 k) :=
    fun k => (measurable_pi_apply k).comp measurable_snd
  fin_cases i <;>
    simp only [base132, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.head_fin_const, Matrix.cons_val, Matrix.cons_val_fin_one,
      Matrix.empty_val', Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three,
      Matrix.cons_val_four]
  · exact hf
  · exact hs 0
  · exact hs 1
  · exact measurable_const
  · exact measurable_const
  · exact hs 2
  · exact hs 3
  · exact hs 4
  · exact hs 5

theorem lam132_base132_measurable (i : Fin 2) :
    Measurable (fun q : (Fin 1 → ℝ) × (Fin 6 → ℝ) => lam132 (base132 q) i) :=
  (lam132_measurable i).comp base132_measurable

theorem shift132_measurable : Measurable shift132 := by
  apply measurable_pi_iff.2; intro i
  have hs : ∀ k : Fin 6, Measurable (fun q : (Fin 1 → ℝ) × (Fin 6 → ℝ) => q.2 k) :=
    fun k => (measurable_pi_apply k).comp measurable_snd
  fin_cases i <;>
    simp only [shift132, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_fin_one]
  · exact (((lam132_base132_measurable 0).mul (hs 2)).add
      ((lam132_base132_measurable 1).mul (hs 4))).neg
  · exact (((lam132_base132_measurable 0).mul (hs 3)).add
      ((lam132_base132_measurable 1).mul (hs 5))).neg

set_option maxHeartbeats 1000000 in
theorem split132_shear132 (u : Fin 9 → ℝ) :
    split132 (shear132 u)
      = (fun q : (Fin 1 → ℝ) × ((Fin 2 → ℝ) × (Fin 6 → ℝ)) =>
          (q.1, (q.2.1 + shift132 (q.1, q.2.2), q.2.2))) (split132 u) := by
  apply Prod.ext
  · funext k
    fin_cases k
    simp [split132, coreSpec132, shear132, MeasurableEquiv.piFinSuccAbove,
      MeasurableEquiv.funUnique, MeasurableEquiv.prodCongr, MeasurableEquiv.prodAssoc,
      Fin.insertNthEquiv, Fin.removeNth, Fin.succAbove]
  apply Prod.ext
  · funext k
    fin_cases k <;>
      simp [split132, coreSpec132, shear132, shift132, base132, lam132,
        MeasurableEquiv.piFinSuccAbove, MeasurableEquiv.funUnique,
        MeasurableEquiv.prodCongr, MeasurableEquiv.prodAssoc,
        Fin.insertNthEquiv, Fin.removeNth, Fin.succAbove, Fin.tail] <;>
      ring
  · funext k
    fin_cases k <;>
      simp [split132, coreSpec132, shear132, MeasurableEquiv.piFinSuccAbove,
        MeasurableEquiv.funUnique, MeasurableEquiv.prodCongr, MeasurableEquiv.prodAssoc,
        Fin.insertNthEquiv, Fin.removeNth, Fin.succAbove, Fin.tail]

theorem shear132_eq_conj (u : Fin 9 → ℝ) :
    shear132 u = split132.symm
      ((fun q : (Fin 1 → ℝ) × ((Fin 2 → ℝ) × (Fin 6 → ℝ)) =>
          (q.1, (q.2.1 + shift132 (q.1, q.2.2), q.2.2))) (split132 u)) := by
  rw [← split132_shear132, MeasurableEquiv.symm_apply_apply]

theorem measurePreserving_shear132 :
    MeasurePreserving shear132 (volume : Measure (Fin 9 → ℝ)) volume := by
  have hcore := measurePreserving_coreShear_measurable 1 2 6 shift132 shift132_measurable
  have hconj : MeasurePreserving
      (split132.symm ∘
        (fun q : (Fin 1 → ℝ) × ((Fin 2 → ℝ) × (Fin 6 → ℝ)) =>
          (q.1, (q.2.1 + shift132 (q.1, q.2.2), q.2.2))) ∘
        split132)
      volume volume :=
    (measurePreserving_split132.symm split132).comp (hcore.comp measurePreserving_split132)
  refine hconj.congr shear132_measurable ?_
  filter_upwards with u
  exact (shear132_eq_conj u).symm

/-! ### `ψ132 = Q132 ∘ shear132` (measure-preserving + measurable embedding) and `φ = ψ ∘ R` -/

noncomputable def psi132 (w : Fin 9 → ℝ) : Fin (flatDim M132) → ℝ :=
  paramsEquivFlat M132 (pack132 (shear132 w))

theorem phi132sm_eq_psi_R (u : Fin 9 → ℝ) : phi132sm u = psi132 (R132 u) := by
  rw [phi132sm, psi132, chartParams132_eq_pack_shear_R]

theorem measurePreserving_psi132 :
    MeasurePreserving psi132 (volume : Measure (Fin 9 → ℝ)) volume := by
  have hmeas : Measurable psi132 := by
    have : psi132 = (fun w : Fin 9 → ℝ => paramsEquivFlat M132 (pack132 w)) ∘ shear132 :=
      funext (fun w => rfl)
    rw [this]; exact measurePreserving_Q132.measurable.comp shear132_measurable
  refine (measurePreserving_Q132.comp measurePreserving_shear132).congr hmeas ?_
  filter_upwards with u; rfl

noncomputable def psi132ME : (Fin 9 → ℝ) ≃ᵐ (Fin (flatDim M132) → ℝ) :=
  shear132ME.trans
    (((flatEquivOf M132 fin9EquivFlatIdx132).symm).trans (paramsEquivFlat M132))

theorem psi132ME_eq (u : Fin 9 → ℝ) : psi132ME u = psi132 u := by
  rw [psi132ME, psi132]
  show paramsEquivFlat M132 ((flatEquivOf M132 fin9EquivFlatIdx132).symm (shear132 u)) = _
  congr 1
  funext s i j
  exact (flatEquivOf_symm_coord M132 fin9EquivFlatIdx132 (shear132 u) ⟨⟨s, i⟩, j⟩).trans
    (hpack132 (shear132 u) ⟨⟨s, i⟩, j⟩).symm

theorem measurableEmbedding_psi132 : MeasurableEmbedding psi132 := by
  have h : psi132 = ⇑psi132ME := funext (fun u => (psi132ME_eq u).symm)
  rw [h]; exact psi132ME.measurableEmbedding

/-! ### The radial certificates (`R132`'s fderiv / injOn / |det| = |u 3|¹) -/

noncomputable def D132 (u : Fin 9 → ℝ) : (Fin 9 → ℝ) →L[ℝ] (Fin 9 → ℝ) :=
  pivotBlowupOnDeriv ({3, 4} : Finset (Fin 9)) 3 u

theorem R132_hasFDerivWithinAt (S : Set (Fin 9 → ℝ)) (u : Fin 9 → ℝ) :
    HasFDerivWithinAt R132 (D132 u) S u :=
  pivotBlowupOn_hasFDerivWithinAt _ _ S u

theorem D132_abs_det (u : Fin 9 → ℝ) : |(D132 u).det| = |u 3| ^ 1 := by
  rw [D132, pivotBlowupOnDeriv_det ({3, 4} : Finset (Fin 9)) 3 (by decide),
    show ({3, 4} : Finset (Fin 9)).card - 1 = 1 from by decide, abs_pow]

theorem R132_injOn (S : Set (Fin 9 → ℝ)) :
    Set.InjOn R132 (S \ {x | x 3 = 0}) := pivotBlowupOn_injOn _ _ S

/-! ### The bounded source sub-box `subBox132` + containment

`subBox132 δ`: `u0 ∈ [δ/2, δ]` (away from the scalar-Gram pole `{a00=0}` — keeps `U`/`Λ₀` bounded),
`u3 = z ∈ (0, δ)` (the binding radial axis, weight `|u3|¹`), `u1,u2,u4,u5,u6,u7,u8 ∈ [−δ/8, δ/8]`. On
it `a00 ≠ 0` and `U = a00²·(h01²+1) ≥ (δ/2)² > 0`. -/
def subBox132 (δ : ℝ) : Set (Fin 9 → ℝ) :=
  {u | u 0 ∈ Set.Icc (δ/2) δ ∧ u 1 ∈ Set.Icc (-(δ/8)) (δ/8) ∧ u 2 ∈ Set.Icc (-(δ/8)) (δ/8) ∧
    u 3 ∈ Set.Ioo (0:ℝ) δ ∧ u 4 ∈ Set.Icc (-(δ/8)) (δ/8) ∧ u 5 ∈ Set.Icc (-(δ/8)) (δ/8) ∧
    u 6 ∈ Set.Icc (-(δ/8)) (δ/8) ∧ u 7 ∈ Set.Icc (-(δ/8)) (δ/8) ∧ u 8 ∈ Set.Icc (-(δ/8)) (δ/8)}

theorem measurableSet_subBox132 (δ : ℝ) : MeasurableSet (subBox132 δ) := by
  unfold subBox132
  refine MeasurableSet.inter (measurableSet_preimage (measurable_pi_apply 0) measurableSet_Icc) ?_
  refine MeasurableSet.inter (measurableSet_preimage (measurable_pi_apply 1) measurableSet_Icc) ?_
  refine MeasurableSet.inter (measurableSet_preimage (measurable_pi_apply 2) measurableSet_Icc) ?_
  refine MeasurableSet.inter (measurableSet_preimage (measurable_pi_apply 3) measurableSet_Ioo) ?_
  refine MeasurableSet.inter (measurableSet_preimage (measurable_pi_apply 4) measurableSet_Icc) ?_
  refine MeasurableSet.inter (measurableSet_preimage (measurable_pi_apply 5) measurableSet_Icc) ?_
  refine MeasurableSet.inter (measurableSet_preimage (measurable_pi_apply 6) measurableSet_Icc) ?_
  exact MeasurableSet.inter (measurableSet_preimage (measurable_pi_apply 7) measurableSet_Icc)
    (measurableSet_preimage (measurable_pi_apply 8) measurableSet_Icc)

/-- `a00 = u0 ≠ 0` on `subBox132 δ` (`δ > 0`): `u0 ≥ δ/2 > 0`. -/
theorem subBox132_a_ne {δ : ℝ} (hδ : 0 < δ) {u : Fin 9 → ℝ} (hu : u ∈ subBox132 δ) : u 0 ≠ 0 := by
  obtain ⟨h0, _, _, _, _, _, _, _, _⟩ := hu
  simp only [Set.mem_Icc] at h0; exact ne_of_gt (lt_of_lt_of_le (by linarith) h0.1)

/-- `|lam132 u i| ≤ 1/4` on `subBox132 δ` (`δ > 0`): `|u1/u0| ≤ (δ/8)/(δ/2) = 1/4`. -/
theorem subBox132_lam_bound {δ : ℝ} (hδ : 0 < δ) {u : Fin 9 → ℝ} (hu : u ∈ subBox132 δ)
    (i : Fin 2) : |lam132 u i| ≤ 1 / 4 := by
  obtain ⟨h0, h1, h2, _, _, _, _, _, _⟩ := hu
  simp only [Set.mem_Icc] at h0 h1 h2
  have hu0 : 0 < u 0 := lt_of_lt_of_le (by linarith) h0.1
  fin_cases i
  · show |lam132 u 0| ≤ 1 / 4
    simp only [lam132, Matrix.cons_val_zero, Matrix.cons_val_fin_one]
    rw [abs_div, abs_of_pos hu0, div_le_iff₀ hu0]
    calc |u 1| ≤ δ/8 := abs_le.mpr ⟨h1.1, h1.2⟩
      _ ≤ 1/4 * u 0 := by nlinarith [h0.1]
  · show |lam132 u 1| ≤ 1 / 4
    simp only [lam132, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_fin_one]
    rw [abs_div, abs_of_pos hu0, div_le_iff₀ hu0]
    calc |u 2| ≤ δ/8 := abs_le.mpr ⟨h2.1, h2.2⟩
      _ ≤ 1/4 * u 0 := by nlinarith [h0.1]

theorem phi132sm_entry (u : Fin 9 → ℝ) (i : Fin (flatDim M132)) :
    phi132sm u i = (chartParams132 u)
      ((Fintype.equivFin (FlatIdx M132)).symm i).1.1
      ((Fintype.equivFin (FlatIdx M132)).symm i).1.2
      ((Fintype.equivFin (FlatIdx M132)).symm i).2 := rfl

/-- **Every matrix entry of `chartParams132 u` is `≤ 2δ` on `subBox132 δ`** (`0 < δ ≤ 1`). A⁰ entries
`u0,u1,u2 ≤ δ`; A¹ top entries `z − Λ·S_bot` (`≤ δ + (1/4)(δ/8)·2`), `z·h01 − Λ·S_bot`
(`z·h01 ≤ δ/8`), the `S_bot` rows `≤ δ/8`. -/
theorem chartParams132_entry_bound {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) {u : Fin 9 → ℝ}
    (hu : u ∈ subBox132 δ) (s : Fin 2) (i : Fin (M132 s.castSucc)) (j : Fin (M132 s.succ)) :
    |(chartParams132 u) s i j| ≤ 2 * δ := by
  have hlam0 := subBox132_lam_bound hδ hu 0
  have hlam1 := subBox132_lam_bound hδ hu 1
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩ := hu
  simp only [Set.mem_Icc] at h0 h1 h2 h4 h5 h6 h7 h8
  simp only [Set.mem_Ioo] at h3
  have b0 : |u 0| ≤ δ := abs_le.mpr ⟨by linarith, h0.2⟩
  have b1 : |u 1| ≤ δ := abs_le.mpr ⟨by linarith, by linarith⟩
  have b2 : |u 2| ≤ δ := abs_le.mpr ⟨by linarith, by linarith⟩
  have b3 : |u 3| ≤ δ := abs_le.mpr ⟨by linarith [h3.1], le_of_lt h3.2⟩
  have b4 : |u 4| ≤ δ/8 := abs_le.mpr ⟨h4.1, h4.2⟩
  have b5 : |u 5| ≤ δ/8 := abs_le.mpr ⟨h5.1, h5.2⟩
  have b6 : |u 6| ≤ δ/8 := abs_le.mpr ⟨h6.1, h6.2⟩
  have b7 : |u 7| ≤ δ/8 := abs_le.mpr ⟨h7.1, h7.2⟩
  have b8 : |u 8| ≤ δ/8 := abs_le.mpr ⟨h8.1, h8.2⟩
  -- the two nontrivial A¹ top entries
  have hsl0 : |lam132 u 0 * u 5 + lam132 u 1 * u 7| ≤ 2 * (1/4 * (δ/8)) := by
    calc |lam132 u 0 * u 5 + lam132 u 1 * u 7| ≤ |lam132 u 0 * u 5| + |lam132 u 1 * u 7| := abs_add_le _ _
      _ ≤ 1/4 * (δ/8) + 1/4 * (δ/8) := by
          rw [abs_mul, abs_mul]
          exact add_le_add (mul_le_mul hlam0 b5 (abs_nonneg _) (by norm_num))
            (mul_le_mul hlam1 b7 (abs_nonneg _) (by norm_num))
      _ = 2 * (1/4 * (δ/8)) := by ring
  have hA10 : |u 3 - (lam132 u 0 * u 5 + lam132 u 1 * u 7)| ≤ 2 * δ := by
    calc |u 3 - (lam132 u 0 * u 5 + lam132 u 1 * u 7)|
        ≤ |u 3| + |lam132 u 0 * u 5 + lam132 u 1 * u 7| := abs_sub _ _
      _ ≤ δ + 2 * (1/4 * (δ/8)) := by linarith
      _ ≤ 2 * δ := by linarith
  have hsl1 : |lam132 u 0 * u 6 + lam132 u 1 * u 8| ≤ 2 * (1/4 * (δ/8)) := by
    calc |lam132 u 0 * u 6 + lam132 u 1 * u 8| ≤ |lam132 u 0 * u 6| + |lam132 u 1 * u 8| := abs_add_le _ _
      _ ≤ 1/4 * (δ/8) + 1/4 * (δ/8) := by
          rw [abs_mul, abs_mul]
          exact add_le_add (mul_le_mul hlam0 b6 (abs_nonneg _) (by norm_num))
            (mul_le_mul hlam1 b8 (abs_nonneg _) (by norm_num))
      _ = 2 * (1/4 * (δ/8)) := by ring
  have hA11 : |u 3 * u 4 - (lam132 u 0 * u 6 + lam132 u 1 * u 8)| ≤ 2 * δ := by
    have hzh : |u 3 * u 4| ≤ δ * (δ/8) := by
      rw [abs_mul]; exact mul_le_mul b3 b4 (abs_nonneg _) (by linarith)
    calc |u 3 * u 4 - (lam132 u 0 * u 6 + lam132 u 1 * u 8)|
        ≤ |u 3 * u 4| + |lam132 u 0 * u 6 + lam132 u 1 * u 8| := abs_sub _ _
      _ ≤ δ * (δ/8) + 2 * (1/4 * (δ/8)) := by linarith
      _ ≤ 2 * δ := by nlinarith [hδ, hδ1]
  have hsimp : ∀ e : ℝ, |e| ≤ δ → |e| ≤ 2 * δ := fun e h => by linarith
  fin_cases s
  · fin_cases i <;> fin_cases j
    · show |chartA0_132 u 0 0| ≤ 2 * δ
      simp only [chartA0_132, Matrix.cons_val', Matrix.cons_val_zero, Matrix.head_cons,
        Matrix.of_apply, Matrix.cons_val, Matrix.empty_val', Matrix.cons_val_fin_one]
      exact hsimp _ b0
    · show |chartA0_132 u 0 1| ≤ 2 * δ
      simp only [chartA0_132, Matrix.cons_val', Matrix.cons_val_one, Matrix.cons_val_zero,
        Matrix.head_cons, Matrix.of_apply, Matrix.cons_val, Matrix.empty_val',
        Matrix.cons_val_fin_one]
      exact hsimp _ b1
    · show |chartA0_132 u 0 2| ≤ 2 * δ
      simp only [chartA0_132, Matrix.cons_val', Matrix.cons_val_two, Matrix.tail_cons,
        Matrix.head_cons, Matrix.of_apply, Matrix.cons_val, Matrix.empty_val',
        Matrix.cons_val_fin_one]
      exact hsimp _ b2
  · fin_cases i <;> fin_cases j
    · show |chartA1_132 u 0 0| ≤ 2 * δ
      simpa only [chartA1_132, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val,
        Matrix.cons_val_fin_one] using hA10
    · show |chartA1_132 u 0 1| ≤ 2 * δ
      simpa only [chartA1_132, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val, Matrix.cons_val_fin_one] using hA11
    · show |chartA1_132 u 1 0| ≤ 2 * δ
      simp only [chartA1_132, Matrix.cons_val', Matrix.cons_val_one, Matrix.cons_val_zero,
        Matrix.head_cons, Matrix.head_fin_const, Matrix.of_apply, Matrix.cons_val,
        Matrix.empty_val', Matrix.cons_val_fin_one]
      exact hsimp _ (by linarith [b5] : |u 5| ≤ δ)
    · show |chartA1_132 u 1 1| ≤ 2 * δ
      simp only [chartA1_132, Matrix.cons_val', Matrix.cons_val_one, Matrix.head_cons,
        Matrix.head_fin_const, Matrix.of_apply, Matrix.cons_val, Matrix.empty_val',
        Matrix.cons_val_fin_one]
      exact hsimp _ (by linarith [b6] : |u 6| ≤ δ)
    · show |chartA1_132 u 2 0| ≤ 2 * δ
      simp only [chartA1_132, Matrix.cons_val', Matrix.cons_val_two, Matrix.tail_cons,
        Matrix.cons_val_zero, Matrix.head_cons, Matrix.of_apply, Matrix.cons_val,
        Matrix.empty_val', Matrix.cons_val_fin_one]
      exact hsimp _ (by linarith [b7] : |u 7| ≤ δ)
    · show |chartA1_132 u 2 1| ≤ 2 * δ
      simp only [chartA1_132, Matrix.cons_val', Matrix.cons_val_two, Matrix.tail_cons,
        Matrix.cons_val_one, Matrix.head_cons, Matrix.head_fin_const, Matrix.of_apply,
        Matrix.cons_val, Matrix.empty_val', Matrix.cons_val_fin_one]
      exact hsimp _ (by linarith [b8] : |u 8| ≤ δ)

theorem subBox132_subset_preimage {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    subBox132 δ ⊆ phi132sm ⁻¹' (cubeBox (flatDim M132) (2 * δ)) := by
  intro u hu
  rw [Set.mem_preimage, cubeBox, Set.mem_pi]
  intro i _
  rw [Set.mem_Icc, ← abs_le, phi132sm_entry]
  exact chartParams132_entry_bound hδ hδ1 hu _ _ _

/-! ### The WEIGHTED divergence on `subBox132` (the radial `|u3|¹` absorbed into the z-axis) -/

theorem Uval132_insertNth_3_eq (x : ℝ) (y : Fin 8 → ℝ) :
    Uval132 (Fin.insertNth 3 x y) = (y 0) ^ 2 * ((y 3) ^ 2 + 1) := by
  unfold Uval132
  rw [show (0 : Fin 9) = Fin.succAbove 3 0 from by decide,
    show (4 : Fin 9) = Fin.succAbove 3 3 from by decide]
  simp only [Fin.insertNth_apply_succAbove]

theorem Uval132_insertNth_3 (x : ℝ) (y : Fin 8 → ℝ) :
    Uval132 (Fin.insertNth 3 x y) = Uval132 (Fin.insertNth 3 (0:ℝ) y) := by
  rw [Uval132_insertNth_3_eq, Uval132_insertNth_3_eq]

theorem Uval132_insertNth_3_measurable :
    Measurable (fun y : Fin 8 → ℝ => Uval132 (Fin.insertNth 3 (0:ℝ) y)) := by
  have : (fun y : Fin 8 → ℝ => Uval132 (Fin.insertNth 3 (0:ℝ) y))
      = fun y => (y 0) ^ 2 * ((y 3) ^ 2 + 1) :=
    funext (fun y => Uval132_insertNth_3_eq 0 y)
  rw [this]
  have hpi : ∀ k : Fin 8, Measurable (fun y : Fin 8 → ℝ => y k) := measurable_pi_apply
  exact ((hpi 0).pow_const 2).mul (((hpi 3).pow_const 2).add measurable_const)

/-- `U = Uval132 u > 0` on `subBox132 δ`: `U = u0²·(u4²+1) ≥ (δ/2)² > 0`. -/
theorem subBox132_U_pos {δ : ℝ} (hδ : 0 < δ) {u : Fin 9 → ℝ} (hu : u ∈ subBox132 δ) :
    0 < Uval132 u := by
  obtain ⟨h0, _, _, _, _, _, _, _, _⟩ := hu
  simp only [Set.mem_Icc] at h0
  have hu0 : 0 < u 0 := lt_of_lt_of_le (by linarith) h0.1
  unfold Uval132; positivity

theorem subBox132_eq_pi (δ : ℝ) :
    subBox132 δ = Set.univ.pi
      (fun i : Fin 9 => if i = 3 then Set.Ioo (0:ℝ) δ
        else if i = 0 then Set.Icc (δ/2) δ else Set.Icc (-(δ/8)) (δ/8)) := by
  ext u
  simp only [subBox132, Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, true_implies]
  constructor
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩ i
    fin_cases i <;> simp_all
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      [have := h 0; have := h 1; have := h 2; have := h 3; have := h 4; have := h 5; have := h 6;
        have := h 7; have := h 8] <;> simp_all

/-- **The weighted divergence on `subBox132`** `∫_{S} |u3|¹·(|loss∘φ|)^{−c'} = ⊤` for `0 < δ ≤ 1`,
`c' ≥ 1`. On `S` the rate is `(u3)²·U` (`a00 ≠ 0`), so the integrand `= |u3|^{1−2c'}·U^{−c'}`; peel the
z-axis (index 3) — the z-factor `∫_{(0,δ)} |u3|^{1−2c'} = ⊤` (`1−2c' ≤ −1`), the rest positive-finite. -/
theorem subBox132_diverges {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) {c' : ℝ} (hc' : (1:ℝ) ≤ c') :
    ∫⁻ u in subBox132 δ,
      ENNReal.ofReal (|u 3| ^ (1:ℕ)) * ENNReal.ofReal (|routeMCore M132 (phi132sm u)| ^ (-c')) = ⊤ := by
  have hrw : ∀ u ∈ subBox132 δ,
      ENNReal.ofReal (|u 3| ^ (1:ℕ)) * ENNReal.ofReal (|routeMCore M132 (phi132sm u)| ^ (-c'))
        = ENNReal.ofReal (|u 3| ^ (1 - 2*c')) * ENNReal.ofReal (Uval132 u ^ (-c')) := by
    intro u hu
    have hane := subBox132_a_ne hδ hu
    have hUpos := subBox132_U_pos hδ hu
    rw [routeMCore_phi132sm_offpole u hane]
    have h3pos : 0 < u 3 := by obtain ⟨_,_,_,h3,_,_,_,_,_⟩ := hu; exact (Set.mem_Ioo.mp h3).1
    have h3abs : (0:ℝ) < |u 3| := by rw [abs_pos]; exact ne_of_gt h3pos
    rw [pow_one, ← ENNReal.ofReal_mul (le_of_lt h3abs),
      ← ENNReal.ofReal_mul (Real.rpow_nonneg (abs_nonneg (u 3)) _)]
    congr 1
    rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ (u 3)^2 * Uval132 u),
      show (u 3)^2 * Uval132 u = |u 3|^2 * Uval132 u by rw [sq_abs],
      Real.mul_rpow (by positivity) (le_of_lt hUpos),
      ← Real.rpow_natCast |u 3| 2, ← Real.rpow_mul (abs_nonneg _)]
    rw [← mul_assoc, show |u 3| * |u 3| ^ (((2:ℕ):ℝ) * -c') = |u 3| ^ (1 - 2*c') by
      rw [show (1 - 2*c') = (1:ℝ) + ((2:ℕ):ℝ) * -c' by push_cast; ring,
        Real.rpow_add h3abs, Real.rpow_one]]
  rw [setLIntegral_congr_fun (measurableSet_subBox132 δ) (fun u hu => hrw u hu)]
  rw [subBox132_eq_pi]
  set ee := MeasurableEquiv.piFinSuccAbove (fun _ : Fin 9 => ℝ) 3 with hee
  have hmpS : MeasurePreserving ee.symm (volume : Measure (ℝ × (Fin 8 → ℝ))) volume := by
    have h := (volume_preserving_piFinSuccAbove (fun _ : Fin 9 => ℝ) 3).symm
    rwa [show (volume : Measure (ℝ × (Fin 8 → ℝ))) = (volume : Measure ℝ).prod volume from
      Measure.volume_eq_prod _ _] at h
  have hsymapp : ∀ x (y : Fin 8 → ℝ), ee.symm (x, y) = Fin.insertNth 3 x y :=
    fun x y => by rw [hee, MeasurableEquiv.piFinSuccAbove_symm_apply]; exact List.ofFn_inj.mp rfl
  set restSet : Set (Fin 8 → ℝ) := Set.univ.pi
    (fun k : Fin 8 => if (Fin.succAbove 3 k) = (0 : Fin 9)
      then Set.Icc (δ/2) δ else Set.Icc (-(δ/8)) (δ/8)) with hrestSet
  have hpre : ee.symm ⁻¹' (Set.univ.pi (fun i : Fin 9 => if i = 3 then Set.Ioo (0:ℝ) δ
        else if i = 0 then Set.Icc (δ/2) δ else Set.Icc (-(δ/8)) (δ/8)))
      = (Set.Ioo (0:ℝ) δ) ×ˢ restSet := by
    ext p; obtain ⟨x, y⟩ := p
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_prod, hsymapp,
      hrestSet]
    constructor
    · intro hall
      refine ⟨?_, fun k => ?_⟩
      · have := hall 3; rwa [Fin.insertNth_apply_same, if_pos rfl] at this
      · have := hall (Fin.succAbove 3 k); rw [Fin.insertNth_apply_succAbove] at this
        rwa [if_neg (Fin.succAbove_ne 3 k)] at this
    · rintro ⟨h0, hrest⟩ j
      rcases Fin.eq_self_or_eq_succAbove 3 j with rfl | ⟨k, rfl⟩
      · rwa [Fin.insertNth_apply_same, if_pos rfl]
      · rw [Fin.insertNth_apply_succAbove, if_neg (Fin.succAbove_ne 3 k)]; exact hrest k
  have htrans := hmpS.setLIntegral_comp_preimage_emb (MeasurableEquiv.measurableEmbedding _)
    (fun u : Fin 9 → ℝ => ENNReal.ofReal (|u 3| ^ (1 - 2*c')) * ENNReal.ofReal (Uval132 u ^ (-c')))
    (Set.univ.pi (fun i : Fin 9 => if i = 3 then Set.Ioo (0:ℝ) δ
        else if i = 0 then Set.Icc (δ/2) δ else Set.Icc (-(δ/8)) (δ/8)))
  rw [hpre] at htrans
  rw [← htrans]
  have hfac : ∀ x (y : Fin 8 → ℝ),
      ENNReal.ofReal (|ee.symm (x, y) 3| ^ (1 - 2*c')) * ENNReal.ofReal (Uval132 (ee.symm (x, y)) ^ (-c'))
        = ENNReal.ofReal (|x| ^ (1 - 2*c'))
          * ENNReal.ofReal (Uval132 (Fin.insertNth 3 x y) ^ (-c')) := by
    intro x y
    have e3 : ee.symm (x, y) 3 = x := by rw [hsymapp, Fin.insertNth_apply_same]
    rw [e3, hsymapp]
  simp_rw [hfac, Uval132_insertNth_3]
  rw [show (volume : Measure (ℝ × (Fin 8 → ℝ))) = (volume : Measure ℝ).prod volume from
    Measure.volume_eq_prod _ _]
  have hUmeas : Measurable (fun y : Fin 8 → ℝ => ENNReal.ofReal (Uval132 (Fin.insertNth 3 (0:ℝ) y) ^ (-c'))) := by
    have he : (fun y : Fin 8 → ℝ => ENNReal.ofReal (Uval132 (Fin.insertNth 3 (0:ℝ) y) ^ (-c')))
        = fun y => ENNReal.ofReal (((y 0) ^ 2 * ((y 3) ^ 2 + 1)) ^ (-c')) :=
      funext (fun y => by rw [Uval132_insertNth_3_eq])
    rw [he]; fun_prop
  rw [setLIntegral_prod _ (by
    apply Measurable.aemeasurable
    exact (by fun_prop : Measurable (fun p : ℝ × (Fin 8 → ℝ) =>
        ENNReal.ofReal (|p.1| ^ (1 - 2*c')))).mul (hUmeas.comp measurable_snd))]
  have hinner : ∀ x, (∫⁻ y in restSet, ENNReal.ofReal (|x| ^ (1 - 2*c'))
      * ENNReal.ofReal (Uval132 (Fin.insertNth 3 (0:ℝ) y) ^ (-c')) ∂(volume : Measure (Fin 8 → ℝ)))
      = ENNReal.ofReal (|x| ^ (1 - 2*c')) * (∫⁻ y in restSet,
        ENNReal.ofReal (Uval132 (Fin.insertNth 3 (0:ℝ) y) ^ (-c')) ∂(volume : Measure (Fin 8 → ℝ))) :=
    fun x => lintegral_const_mul _ hUmeas
  simp only [hinner]
  rw [lintegral_mul_const _ (by fun_prop : Measurable (fun x : ℝ => ENNReal.ofReal (|x| ^ (1 - 2*c'))))]
  rw [abs_rpow_lintegral_Ioo_eq_top _ δ hδ (by linarith)]
  refine ENNReal.top_mul (ne_of_gt ?_)
  rw [hrestSet, setLIntegral_pos_iff hUmeas]
  have hbox : 0 < (volume : Measure (Fin 8 → ℝ)) (Set.univ.pi
      (fun k : Fin 8 => if (Fin.succAbove 3 k) = (0 : Fin 9)
        then Set.Icc (δ/2) δ else Set.Icc (-(δ/8)) (δ/8))) := by
    rw [volume_pi_pi]
    refine CanonicallyOrderedAdd.prod_pos.mpr (fun k _ => ?_)
    by_cases hk : (Fin.succAbove 3 k) = (0 : Fin 9)
    · rw [if_pos hk, Real.volume_Icc, ENNReal.ofReal_pos]; linarith
    · rw [if_neg hk, Real.volume_Icc, ENNReal.ofReal_pos]; linarith
  apply lt_of_lt_of_le hbox
  apply measure_mono
  intro y hy
  refine ⟨?_, hy⟩
  rw [Function.mem_support, ne_eq, ENNReal.ofReal_eq_zero, not_le]
  refine Real.rpow_pos_of_pos ?_ _
  have hmem : Fin.insertNth 3 (δ/2) y ∈ subBox132 δ := by
    simp only [Set.mem_pi, Set.mem_univ, true_implies, hrestSet] at hy
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [show (0:Fin 9) = Fin.succAbove 3 0 from by decide, Fin.insertNth_apply_succAbove]
      have := hy 0; rwa [show (Fin.succAbove 3 (0:Fin 8) = (0:Fin 9)) from by decide,
        if_pos rfl] at this
    · rw [show (1:Fin 9) = Fin.succAbove 3 1 from by decide, Fin.insertNth_apply_succAbove]
      have := hy 1; rwa [if_neg (by decide)] at this
    · rw [show (2:Fin 9) = Fin.succAbove 3 2 from by decide, Fin.insertNth_apply_succAbove]
      have := hy 2; rwa [if_neg (by decide)] at this
    · rw [Fin.insertNth_apply_same]; exact Set.mem_Ioo.mpr ⟨by linarith, by linarith⟩
    · rw [show (4:Fin 9) = Fin.succAbove 3 3 from by decide, Fin.insertNth_apply_succAbove]
      have := hy 3; rwa [if_neg (by decide)] at this
    · rw [show (5:Fin 9) = Fin.succAbove 3 4 from by decide, Fin.insertNth_apply_succAbove]
      have := hy 4; rwa [if_neg (by decide)] at this
    · rw [show (6:Fin 9) = Fin.succAbove 3 5 from by decide, Fin.insertNth_apply_succAbove]
      have := hy 5; rwa [if_neg (by decide)] at this
    · rw [show (7:Fin 9) = Fin.succAbove 3 6 from by decide, Fin.insertNth_apply_succAbove]
      have := hy 6; rwa [if_neg (by decide)] at this
    · rw [show (8:Fin 9) = Fin.succAbove 3 7 from by decide, Fin.insertNth_apply_succAbove]
      have := hy 7; rwa [if_neg (by decide)] at this
  rw [show Uval132 (Fin.insertNth 3 (0:ℝ) y) = Uval132 (Fin.insertNth 3 (δ/2) y) from
    (Uval132_insertNth_3 0 y).trans (Uval132_insertNth_3 (δ/2) y).symm]
  exact subBox132_U_pos hδ hmem

/-! ### The `(1,3,2)` smeared achiever box-divergence atom (route b, the radial-MP assembly) -/

/-- **The `(1,3,2)` smeared box-divergence** — `∫⁻_{cubeBox 9 ε} |routeMCore M132|^{−c'} = ⊤` for `c'`
at-or-above `½·minAdm M132 = 1`, every `ε > 0`. The `(r,c)=(1,2)`-shape boundary-SMEARED atom (scalar
Gram + `1×2` radial), discharged via `routeMCore_box_diverges_of_RadialMPChart` (route b): `φ = ψ ∘ R`,
`ψ = Q132 ∘ shear132` (MP + measurable embedding), `R = R132` (radial, `|det| = |u 3|¹`), fed the
bounded-away weighted source `subBox132 δ`. -/
theorem routeM132sm_box_diverges (c' : NNReal) (hc' : (minAdm M132 : ℝ≥0∞) / 2 ≤ (c' : ℝ≥0∞))
    (ε : ℝ) (hε : 0 < ε) :
    ∫⁻ x in cubeBox (routeMAmbient M132) ε,
      ENNReal.ofReal (|routeMCore M132 x| ^ (-(c' : ℝ))) = ⊤ := by
  have hc'1 : (1:ℝ) ≤ (c' : ℝ) := by
    have h : (minAdm M132 : ℝ≥0∞) / 2 = 1 := by
      rw [minAdm_M132, show ((2:ℕ):ℝ≥0∞) = 2 from by norm_num, ENNReal.div_self (by norm_num) (by norm_num)]
    rw [h] at hc'
    rwa [show (1:ℝ≥0∞) = ((1:NNReal):ℝ≥0∞) by norm_num, ENNReal.coe_le_coe, ← NNReal.coe_le_coe,
      NNReal.coe_one] at hc'
  set δ : ℝ := min (ε/2) 1 with hδdef
  have hδ : 0 < δ := lt_min (by linarith) (by norm_num)
  have hδ1 : δ ≤ 1 := min_le_right _ _
  have h2δε : 2 * δ ≤ ε := by have : δ ≤ ε/2 := min_le_left _ _; linarith
  refine routeMCore_box_diverges_of_RadialMPChart M132 psi132 R132 D132
    (⟨3, by decide⟩ : Fin (routeMAmbient M132)) 1
    measurePreserving_psi132 measurableEmbedding_psi132 (c' : ℝ) ε
    ⟨subBox132 δ, measurableSet_subBox132 δ, ?_, ?_, ?_, ?_, ?_⟩
  · intro u hu
    rw [Set.mem_preimage, ← phi132sm_eq_psi_R]
    exact cubeBox_mono h2δε (subBox132_subset_preimage hδ hδ1 hu)
  · exact fun u _ => R132_hasFDerivWithinAt _ u
  · have hsub : subBox132 δ ⊆ subBox132 δ \ {x | x 3 = 0} := by
      intro u hu
      refine ⟨hu, ?_⟩
      obtain ⟨_,_,_,h3,_,_,_,_,_⟩ := hu
      simp only [Set.mem_setOf_eq]; exact ne_of_gt (Set.mem_Ioo.mp h3).1
    exact (R132_injOn (subBox132 δ)).mono hsub
  · exact fun u _ => D132_abs_det u
  · have heq : ∀ u, routeMCore M132 (psi132 (R132 u)) = routeMCore M132 (phi132sm u) :=
      fun u => by rw [phi132sm_eq_psi_R]
    simp only [heq]
    exact subBox132_diverges hδ hδ1 hc'1

end DLNFibre.DLN.RLCT
