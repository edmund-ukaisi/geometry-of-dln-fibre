import DLNFibre.DLN.RLCT.Validate.RouteM121Smeared

/-!
# `RouteM231Smeared` — the BOUNDARY-SMEARED achiever box-divergence VALIDATE-SMALL `(2,3,1)`
(`minAdm ≥ 2`)

The first `minAdm ≥ 2` boundary-SMEARED node `M = (2,3,1)` (`L = 2`, `r = Text(L) = 2`, `c = M_L =
1`,
`m1 = M_{L−1} = 3`, `s = m1 − r = 1`, `minAdm = r·c = 2`, `flatDim = 9`) — the validate-small that
exercises the RADIAL blow-up (det `|z|^{minAdm−1} = |z|¹ ≠ 1`, so the chart is NOT
measure-preserving)
composed with the rational shear, discharged via the reusable
`routeMCore_box_diverges_of_RadialMPChart`
(route b, the `minAdm ≥ 2` generalized assembly).

## The chart (`certificate-genM-smeared.md` §2, specialized to `(2,3,1)`)
Coords `(a00,a01,a02,a10,a11,a12, z, h1, sb) : Fin 9 → ℝ`. The front product `P = A⁽⁰⁾` (`2×3`);
`P₁ =
A⁰[:, :2]` (the rank-carrying `2×2` kept block), `P₂ = A⁰[:, 2:]` (the `2×1` smeared column); the
rational
routing `Λ₀ = (P₁ᵀP₁)⁻¹P₁ᵀP₂` (`2×1`). The deepest factor

    A⁽¹⁾ = [ z − Λ₀₀·sb ;  z·h1 − Λ₀₁·sb ;  sb ]   (`3×1`; the `r·c = 2` kept rows are the RADIAL block
            (scaled by the pivot `z`, the `(0,0)` entry fixed `= 1`, the `h1` angular), the bottom `s = 1`
            row is the free residual `sb`).

Then `A⁰·A¹ = z·(P₁·[1; h1])`, so `F = ‖A⁰·A¹‖² = z²·U`, `U = ‖P₁·[1; h1]‖²` (z-free, polynomial).
The
Jacobian det is `|z|^{minAdm−1} = |z|¹` (validated EXACT, `pp_smear_GATE.py` (D): 46/46 across the
class).

## The factorization `φ = ψ ∘ R` (for the radial-MP assembly)
`R` (radial, the ONLY Jacobian carrier): `pivotBlowupOn {z-slot, h1-slot} z` — scales the `r·c = 2`
kept
coords by `z` (det `|z|¹`, polynomial). `ψ = Q ∘ shear` (measure-preserving + measurable
embedding): the
rational `Λ₀`-shear (det 1, the pole `{det P₁ᵀP₁ = 0}` confined here) ∘ the linear reshape `Q =
paramsEquivFlat ∘ pack`. The weighted source certificate: `∫_S |z|¹·(loss∘φ)^{−c} = ⊤` (the radial
`|z|`
absorbed into the binding-axis divergence: exponent `minAdm−1−2c = 1−2c ≤ −1` from `c ≥ minAdm/2 =
1`).
-/

open MeasureTheory
open scoped ENNReal BigOperators

namespace DLNFibre.DLN.RLCT

/-- `M231 = (2,3,1)` (the smallest `minAdm ≥ 2` boundary-smeared node). -/
abbrev M231 : Fin 3 → ℕ := ![2, 3, 1]

theorem minAdm_M231 : minAdm M231 = 2 := by
  rw [← minAdmRec_eq_minAdm]; decide

theorem flatDim_M231 : flatDim M231 = 9 := by decide

theorem routeMAmbient_M231 : routeMAmbient M231 = 9 := by decide

/-! ## The chart matrices (radial × rational shear, `certificate-genM-smeared.md` §2)

Coords `(u 0..u 5) = A⁰` row-major (`a00,a01,a02,a10,a11,a12`), `u 6 = z` (pivot), `u 7 = h1`
(angular),
`u 8 = sb` (residual). `Λ₀ = (P₁ᵀP₁)⁻¹P₁ᵀP₂`, `P₁ = A⁰[:,:2]`, `P₂ = A⁰[:,2:]`. -/

/-- The `2×2` kept-block Gram inverse-times `P₁ᵀP₂` routing `Λ₀ : Fin 2 → ℝ` (its two entries
`Λ₀₀, Λ₀₁`). `P₁ = !![a00,a01; a10,a11]`, `P₂ = !![a02; a12]`; `Λ₀ = (P₁ᵀP₁)⁻¹ P₁ᵀ P₂`. -/
noncomputable def lam231 (u : Fin 9 → ℝ) : Fin 2 → ℝ :=
  fun i => (((!![u 0, u 1; u 3, u 4] : Matrix (Fin 2) (Fin 2) ℝ).transpose
      * !![u 0, u 1; u 3, u 4])⁻¹
    * (!![u 0, u 1; u 3, u 4] : Matrix (Fin 2) (Fin 2) ℝ).transpose
    * !![u 2; u 5]) i 0

/-- **The layer-`0` matrix `A⁽⁰⁾`** (`2×3`, the front product `P`, free generic). -/
noncomputable def chartA0_231 (u : Fin 9 → ℝ) : Matrix (Fin 2) (Fin 3) ℝ :=
  !![u 0, u 1, u 2; u 3, u 4, u 5]

/-- **The layer-`1` matrix `A⁽¹⁾`** (`3×1`): top `r·c = 2` radial rows `[z − Λ₀₀·sb ; z·h1 −
Λ₀₁·sb]`
(the `(0,0)` pivot `z`, the `h1` angular scaled by `z`), bottom `s = 1` residual row `sb`. -/
noncomputable def chartA1_231 (u : Fin 9 → ℝ) : Matrix (Fin 3) (Fin 1) ℝ :=
  !![u 6 - lam231 u 0 * u 8; u 6 * u 7 - lam231 u 1 * u 8; u 8]

/-- The genuine `Params M231`, assembled by `Fin.cons` over the two layers. -/
noncomputable def chartParams231 (u : Fin 9 → ℝ) : Params M231 :=
  Fin.cons (chartA0_231 u) (Fin.cons (chartA1_231 u) (fun i => i.elim0))

/-- **The chart in flat coordinates** `phi231sm := paramsEquivFlat M231 ∘ chartParams231`. -/
noncomputable def phi231sm (u : Fin 9 → ℝ) : Fin (flatDim M231) → ℝ :=
  paramsEquivFlat M231 (chartParams231 u)

/-! ## The rate `F∘φ = z²·U` — OFF the rational pole `{det P₁ = 0}`

The shear cancels: off `det P₁ ≠ 0`, `P₁` is invertible so `(P₁ᵀP₁)⁻¹P₁ᵀ = P₁⁻¹` and `P₁·Λ₀ = P₂`,
so
the `sb`-terms in `A⁰·A¹` cancel, leaving `A⁰·A¹ = z·(P₁·[1; h1])`. Hence `F = z²·U`,
`U = ‖P₁·[1; h1]‖²` (z-free polynomial). -/

/-- The `2×2` kept block `P₁ = !![a00,a01; a10,a11]`. -/
noncomputable def P1_231 (u : Fin 9 → ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![u 0, u 1; u 3, u 4]

/-- **The shear cancellation** `P₁ · Λ₀ = P₂` off the pole (`det P₁ ≠ 0`): `(P₁ᵀP₁)⁻¹P₁ᵀ = P₁⁻¹`
for an
invertible square `P₁`, so `P₁·Λ₀ = P₁·P₁⁻¹·P₂ = P₂`. -/
theorem P1_lam231 (u : Fin 9 → ℝ) (hdet : (P1_231 u).det ≠ 0) :
    ∀ i : Fin 2, (P1_231 u) i 0 * lam231 u 0 + (P1_231 u) i 1 * lam231 u 1
      = (!![u 2; u 5] : Matrix (Fin 2) (Fin 1) ℝ) i 0 := by
  -- `lam231 u = ((P₁ᵀP₁)⁻¹ P₁ᵀ P₂) · 0` ; with P₁ invertible, P₁·Λ₀ = P₂
  have hP1inv : IsUnit (P1_231 u).det := isUnit_iff_ne_zero.mpr hdet
  -- (P₁ᵀP₁)⁻¹ P₁ᵀ = P₁⁻¹ (P₁ᵀ)⁻¹ P₁ᵀ = P₁⁻¹
  have hTinv : (P1_231 u).det ≠ 0 := hdet
  have hkey : (P1_231 u) * (((P1_231 u).transpose * P1_231 u)⁻¹ * (P1_231 u).transpose
      * !![u 2; u 5]) = !![u 2; u 5] := by
    have hTT : ((P1_231 u).transpose * P1_231 u)⁻¹
        = (P1_231 u)⁻¹ * ((P1_231 u).transpose)⁻¹ := by
      rw [Matrix.mul_inv_rev]
    rw [hTT]
    rw [show (P1_231 u) * ((P1_231 u)⁻¹ * ((P1_231 u).transpose)⁻¹ * (P1_231 u).transpose
          * !![u 2; u 5])
        = ((P1_231 u) * (P1_231 u)⁻¹) * (((P1_231 u).transpose)⁻¹ * (P1_231 u).transpose)
          * !![u 2; u 5] by
      simp only [Matrix.mul_assoc]]
    rw [Matrix.mul_nonsing_inv _ hP1inv,
      Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (by rwa [Matrix.det_transpose])),
      Matrix.one_mul, Matrix.one_mul]
  intro i
  have := congrFun (congrFun hkey i) 0
  simp only [Matrix.mul_apply, Fin.sum_univ_two] at this
  rw [show lam231 u 0 = (((P1_231 u).transpose * P1_231 u)⁻¹ * (P1_231 u).transpose
        * !![u 2; u 5]) 0 0 from rfl,
    show lam231 u 1 = (((P1_231 u).transpose * P1_231 u)⁻¹ * (P1_231 u).transpose
        * !![u 2; u 5]) 1 0 from rfl]
  have hexp : ((P1_231 u) * (((P1_231 u).transpose * P1_231 u)⁻¹ * (P1_231 u).transpose
        * !![u 2; u 5])) i 0
      = (P1_231 u) i 0 * (((P1_231 u).transpose * P1_231 u)⁻¹ * (P1_231 u).transpose * !![u 2; u 5]) 0 0
        + (P1_231 u) i 1
          * (((P1_231 u).transpose * P1_231 u)⁻¹ * (P1_231 u).transpose * !![u 2; u 5]) 1 0 := by
    rw [Matrix.mul_apply, Fin.sum_univ_two]
  rw [← hexp, hkey]

/-! ### The rate `F∘φ = z²·U` off the pole (entry telescoping via `P1_lam231`) -/

/-- **The product entry** `(A⁰·A¹)(i,0) = z·(a_{i,0} + a_{i,1}·h1)` off the pole (`det P₁ ≠ 0`): the
inner `Fin 3` sum + the `sb`-shear cancellation (`P1_lam231`). Indices `i, j` substituted to concrete
`Fin.mk` (the `lean/CLAUDE.md` opaque-width kernel); `j` is the unique `Fin 1` element. -/
theorem prod_chartParams231_entry (u : Fin 9 → ℝ) (hdet : (P1_231 u).det ≠ 0)
    (i : Fin (M231 0)) (j : Fin (M231 2)) :
    prod M231 (chartParams231 u) i j
      = u 6 * (chartA0_231 u (Fin.cast (show M231 0 = 2 from rfl) i) 0
        + chartA0_231 u (Fin.cast (show M231 0 = 2 from rfl) i) 1 * u 7) := by
  rw [prod_two_layer221 M231 (chartParams231 u) i j]
  -- the chart matrices; `i` is a `Fin 2` row, `j` the unique `Fin 1` column
  set ii : Fin 2 := Fin.cast (show M231 0 = 2 from rfl) i with hii
  have hcancel := P1_lam231 u hdet ii
  simp only [P1_231, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.of_apply,
    Matrix.cons_val] at hcancel
  have hjval : j.val = 0 := by have := j.isLt; simp only [show M231 2 = 1 from rfl] at this; omega
  -- force the inner sum to `Fin 3` (defeq), and `i = ii` (defeq via `Fin.cast` of `rfl`)
  change (∑ k1 : Fin 3, chartA0_231 u ii k1 * chartA1_231 u k1 j) = _
  rw [Fin.sum_univ_three]
  have hj0 : j = (⟨0, by decide⟩ : Fin (M231 2)) := Fin.ext (by rw [hjval])
  subst hj0
  clear_value ii
  -- `lam231` stays FOLDED (so it matches `hcancel`); reduce the matrix-entry accessors fully
  fin_cases ii <;>
    simp only [chartA0_231, chartA1_231, P1_231, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.head_fin_const, Matrix.of_apply, Matrix.cons_val,
      Matrix.cons_val_fin_one, Matrix.empty_val', Fin.mk_zero, Fin.mk_one, Fin.isValue,
      Matrix.cons_val_two, Matrix.tail_cons] at hcancel ⊢ <;>
    linear_combination (-(u 8)) * hcancel

/-- The unit factor `U = ‖P₁·[1;h1]‖² = (a00+a01·h1)² + (a10+a11·h1)²` (the z-free factor of `F = z²·U`). -/
noncomputable def Uval231 (u : Fin 9 → ℝ) : ℝ :=
  (u 0 + u 1 * u 7) ^ 2 + (u 3 + u 4 * u 7) ^ 2

/-- `Uval231 ≥ 0`. -/
theorem Uval231_nonneg (u : Fin 9 → ℝ) : (0 : ℝ) ≤ Uval231 u := by unfold Uval231; positivity

/-- **The off-pole rate** `dlnLoss M231 0 (chartParams231 u) = z²·U` for `det P₁ ≠ 0`. Each of the two
product rows is `z·(a_{i0}+a_{i1}h1)` (`prod_chartParams231_entry`), so the squared-Frobenius sum is
`z²·((a00+a01h1)²+(a10+a11h1)²) = z²·U`. -/
theorem dlnLoss_chartParams231_offpole (u : Fin 9 → ℝ) (hdet : (P1_231 u).det ≠ 0) :
    dlnLoss M231 0 (chartParams231 u) = (u 6) ^ 2 * Uval231 u := by
  unfold dlnLoss
  -- per-entry value via the telescoping (constant in the unique `Fin 1` column `j`)
  have hentry : ∀ (i : Fin (M231 0)) (j : Fin (M231 2)),
      ((prod M231 (chartParams231 u) - 0) i j) ^ 2
        = (u 6) ^ 2 * (chartA0_231 u (Fin.cast (show M231 0 = 2 from rfl) i) 0
          + chartA0_231 u (Fin.cast (show M231 0 = 2 from rfl) i) 1 * u 7) ^ 2 := by
    intro i j
    rw [sub_zero, prod_chartParams231_entry u hdet i j]; ring
  -- force both sums to literal `Fin`s (defeq: `M231 0 = 2`, `M231 2 = 1`), then expand
  change (∑ i : Fin 2, ∑ j : Fin 1,
    ((prod M231 (chartParams231 u) - 0)
        (Fin.cast (show 2 = M231 0 from rfl) i) (Fin.cast (show 1 = M231 2 from rfl) j)) ^ 2) = _
  simp only [Fin.sum_univ_two, Fin.sum_univ_one, hentry]
  -- the double `Fin.cast` indices are defeq to the literal `Fin 2` rows; `show` the literal goal
  show u 6 ^ 2 * (chartA0_231 u 0 0 + chartA0_231 u 0 1 * u 7) ^ 2
      + u 6 ^ 2 * (chartA0_231 u 1 0 + chartA0_231 u 1 1 * u 7) ^ 2
      = u 6 ^ 2 * Uval231 u
  simp only [chartA0_231, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.of_apply, Matrix.cons_val, Uval231]
  ring

/-- **The `routeMCore` factorization** `routeMCore M231 (phi231sm u) = z²·U` off the pole. -/
theorem routeMCore_phi231sm_offpole (u : Fin 9 → ℝ) (hdet : (P1_231 u).det ≠ 0) :
    routeMCore M231 (phi231sm u) = (u 6) ^ 2 * Uval231 u := by
  rw [routeMCore, phi231sm, MeasurableEquiv.symm_apply_apply,
    dlnLoss_chartParams231_offpole u hdet]

/-! ### The MP-factorization `φ = Q231 ∘ shear231 ∘ R231`

`R231` (the ONLY Jacobian carrier): the radial blow-up `pivotBlowupOn {6,7} 6` — slot `6 = z` fixed
(the pivot), slot `7 = h1 ↦ z·h1` (scaled by the pivot), all else spectators; `det = z^{card−1} =
z¹`.
`shear231` (z-free, measure-preserving): subtract `Λ₀·sb` from the two kept slots `6, 7` (a det-1
translation reading only the A0 coords `0..5` and `sb = u 8`). `Q231 = paramsEquivFlat ∘ pack231`
(the linear reshape). The pole `{det P₁ = 0}` is confined to `shear231`'s coefficient. -/

/-- **The reshape** `pack231 : (Fin 9 → ℝ) → Params M231`: coords `0..5 ↦ A⁰` (`2×3`, row-major),
coords `6,7,8 ↦ A¹` (`3×1`). Each output entry is one input coordinate. -/
noncomputable def pack231 (w : Fin 9 → ℝ) : Params M231 :=
  Fin.cons (!![w 0, w 1, w 2; w 3, w 4, w 5] : Matrix (Fin 2) (Fin 3) ℝ)
    (Fin.cons (!![w 6; w 7; w 8] : Matrix (Fin 3) (Fin 1) ℝ) (fun i => i.elim0))

/-- The explicit slot bijection `Fin 9 ≃ FlatIdx M231` (flat coord → matrix slot), pinning
`pack231`. Layer `0` (`A⁰`, `2×3`) row-major: `(0,0),(0,1),(0,2),(1,0),(1,1),(1,2) ↦ 0..5`; layer
`1` (`A¹`, `3×1`): `(0,0),(1,0),(2,0) ↦ 6,7,8`. -/
noncomputable def fin9EquivFlatIdx231 : Fin 9 ≃ FlatIdx M231 where
  toFun := fun k =>
    match k with
    | ⟨0,_⟩ => ⟨⟨⟨0,by decide⟩,⟨0,by decide⟩⟩,⟨0,by decide⟩⟩
    | ⟨1,_⟩ => ⟨⟨⟨0,by decide⟩,⟨0,by decide⟩⟩,⟨1,by decide⟩⟩
    | ⟨2,_⟩ => ⟨⟨⟨0,by decide⟩,⟨0,by decide⟩⟩,⟨2,by decide⟩⟩
    | ⟨3,_⟩ => ⟨⟨⟨0,by decide⟩,⟨1,by decide⟩⟩,⟨0,by decide⟩⟩
    | ⟨4,_⟩ => ⟨⟨⟨0,by decide⟩,⟨1,by decide⟩⟩,⟨1,by decide⟩⟩
    | ⟨5,_⟩ => ⟨⟨⟨0,by decide⟩,⟨1,by decide⟩⟩,⟨2,by decide⟩⟩
    | ⟨6,_⟩ => ⟨⟨⟨1,by decide⟩,⟨0,by decide⟩⟩,⟨0,by decide⟩⟩
    | ⟨7,_⟩ => ⟨⟨⟨1,by decide⟩,⟨1,by decide⟩⟩,⟨0,by decide⟩⟩
    | ⟨8,_⟩ => ⟨⟨⟨1,by decide⟩,⟨2,by decide⟩⟩,⟨0,by decide⟩⟩
    | ⟨n+9,h⟩ => absurd h (by omega)
  invFun := fun q =>
    match q with
    | ⟨⟨⟨0,_⟩,⟨0,_⟩⟩,⟨0,_⟩⟩ => 0
    | ⟨⟨⟨0,_⟩,⟨0,_⟩⟩,⟨1,_⟩⟩ => 1
    | ⟨⟨⟨0,_⟩,⟨0,_⟩⟩,⟨2,_⟩⟩ => 2
    | ⟨⟨⟨0,_⟩,⟨1,_⟩⟩,⟨0,_⟩⟩ => 3
    | ⟨⟨⟨0,_⟩,⟨1,_⟩⟩,⟨1,_⟩⟩ => 4
    | ⟨⟨⟨0,_⟩,⟨1,_⟩⟩,⟨2,_⟩⟩ => 5
    | ⟨⟨⟨1,_⟩,⟨0,_⟩⟩,⟨0,_⟩⟩ => 6
    | ⟨⟨⟨1,_⟩,⟨1,_⟩⟩,⟨0,_⟩⟩ => 7
    | ⟨⟨⟨1,_⟩,⟨2,_⟩⟩,⟨0,_⟩⟩ => 8
  left_inv := by decide
  right_inv := by decide

/-- **The slot equation** `pack231 w q.1.1 q.1.2 q.2 = w (fin9EquivFlatIdx231.symm q)` (`rfl` per
slot). -/
theorem hpack231 (w : Fin 9 → ℝ) (q : FlatIdx M231) :
    pack231 w q.1.1 q.1.2 q.2 = w (fin9EquivFlatIdx231.symm q) := by
  obtain ⟨⟨s, i⟩, j⟩ := q
  fin_cases s <;> fin_cases i <;> fin_cases j <;> rfl

/-- **`pack231` is measure-preserving** (the reshape-MP at `fin9EquivFlatIdx231`). -/
theorem measurePreserving_pack231 :
    MeasurePreserving pack231 (volume : Measure (Fin 9 → ℝ)) (volume : Measure (Params M231)) :=
  measurePreserving_paramsPack_of_flatIdxEquiv M231 fin9EquivFlatIdx231 pack231 hpack231

/-- **`Q231 = paramsEquivFlat ∘ pack231` is measure-preserving** (the linear outer reshape). -/
theorem measurePreserving_Q231 :
    MeasurePreserving (fun w : Fin 9 → ℝ => paramsEquivFlat M231 (pack231 w))
      (volume : Measure (Fin 9 → ℝ)) volume :=
  (measurePreserving_paramsEquivFlat M231).comp measurePreserving_pack231

/-- **The radial blow-up** `R231 = pivotBlowupOn {6,7} 6`: slot `6 = z` fixed (pivot), slot `7 ↦
z·h1`,
all else spectators. `det = z^{card−1} = z¹` (`active.card = 2`). -/
noncomputable def R231 : (Fin 9 → ℝ) → (Fin 9 → ℝ) := pivotBlowupOn ({6, 7} : Finset (Fin 9)) 6

/-- **`R231` as an explicit vector** `(a00..a12, z, z·h1, sb)` (slot `7` scaled by the pivot `z`). -/
theorem R231_apply (u : Fin 9 → ℝ) :
    R231 u = ![u 0, u 1, u 2, u 3, u 4, u 5, u 6, u 6 * u 7, u 8] := by
  funext i; fin_cases i <;> simp [R231, pivotBlowupOn, Matrix.cons_val]

/-- **The z-free rational shear** `shear231`: subtract `Λ₀·sb` from the two kept slots `6, 7` (reads
only the A0 coords `0..5` (via `lam231`) and `sb = w 8`); all else fixed. The pole `{det P₁ = 0}` is
confined to the `lam231` coefficient. -/
noncomputable def shear231 (w : Fin 9 → ℝ) : Fin 9 → ℝ :=
  fun i =>
    if i = 6 then w 6 - lam231 w 0 * w 8
    else if i = 7 then w 7 - lam231 w 1 * w 8
    else w i

/-- `shear231 w k = w k` for `k ∈ {0,1,2,3,4,5,8}` (the non-kept slots; both `if`s miss). -/
theorem shear231_spectator (w : Fin 9 → ℝ) {k : Fin 9} (h6 : k ≠ 6) (h7 : k ≠ 7) :
    shear231 w k = w k := by simp only [shear231, if_neg h6, if_neg h7]

/-- `shear231 w 6 = w 6 − Λ₀₀·w8`, `shear231 w 7 = w 7 − Λ₀₁·w8` (the two kept slots). -/
theorem shear231_kept (w : Fin 9 → ℝ) :
    shear231 w 6 = w 6 - lam231 w 0 * w 8 ∧ shear231 w 7 = w 7 - lam231 w 1 * w 8 := by
  refine ⟨?_, ?_⟩
  · simp only [shear231, if_true, reduceIte]
  · simp only [shear231, show (7 : Fin 9) = 6 ↔ False from by decide, if_false, if_true,
      reduceIte]

/-- **The factorization** `chartParams231 u = pack231 (shear231 (R231 u))`: `R231` produces
`(…, z, z·h1, sb)`; `shear231` subtracts `Λ₀·sb` giving `(…, z−Λ₀₀sb, z·h1−Λ₀₁sb, sb)`; `pack231`
reshapes into `A⁰`, `A¹ = chartA1_231`. -/

theorem chartParams231_eq_pack_shear_R (u : Fin 9 → ℝ) :
    chartParams231 u = pack231 (shear231 (R231 u)) := by
  -- `lam231 (R231 u) i = lam231 u i` (lam231 reads only coords 0..5, which R231 fixes)
  have hlam : ∀ i, lam231 (R231 u) i = lam231 u i := by
    intro i; simp only [lam231, R231_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val]
  -- spectator readouts: `shear231 (R231 u) k = (R231 u) k = u k` for `k ∈ {0..5}`
  have hs : ∀ k : Fin 9, k ≠ 6 → k ≠ 7 → shear231 (R231 u) k = (R231 u) k :=
    fun k h6 h7 => shear231_spectator (R231 u) h6 h7
  obtain ⟨hk6, hk7⟩ := shear231_kept (R231 u)
  funext s
  fin_cases s
  · show chartA0_231 u = (pack231 (shear231 (R231 u))) 0
    have hp : (pack231 (shear231 (R231 u))) 0
        = (!![(shear231 (R231 u)) 0, (shear231 (R231 u)) 1, (shear231 (R231 u)) 2;
            (shear231 (R231 u)) 3, (shear231 (R231 u)) 4, (shear231 (R231 u)) 5]
          : Matrix (Fin 2) (Fin 3) ℝ) := rfl
    rw [hp]
    rw [hs 0 (by decide) (by decide), hs 1 (by decide) (by decide), hs 2 (by decide) (by decide),
      hs 3 (by decide) (by decide), hs 4 (by decide) (by decide), hs 5 (by decide) (by decide)]
    funext i j
    fin_cases i <;> fin_cases j <;>
      simp [chartA0_231, R231_apply, Matrix.cons_val]
  · show chartA1_231 u = (pack231 (shear231 (R231 u))) 1
    have hp : (pack231 (shear231 (R231 u))) 1
        = (!![(shear231 (R231 u)) 6; (shear231 (R231 u)) 7; (shear231 (R231 u)) 8]
          : Matrix (Fin 3) (Fin 1) ℝ) := rfl
    rw [hp, hk6, hk7, hs 8 (by decide) (by decide), hlam 0, hlam 1]
    funext i j
    fin_cases i <;> fin_cases j <;>
      simp [chartA1_231, R231_apply, Matrix.cons_val] <;> ring

/-! ### `shear231` is a global measure-preserving measurable bijection (route b)

`shear231` is the identity on coords `{0..5, 8}` and translates coords `6, 7` by `−Λ₀·sb` (a
MEASURABLE function of the others). The totalized inverse adds them back; both directions are
measurable bijections (the `lam231` coefficient totalizes off the pole, and the pole is null). MP via
the explicit measurable inverse + the global-bijection skew-product (the two translations commute —
neither modified coord is read by either shift, both reading only `{0..5, 8}`). -/

/-- **The inverse** `shear231Inv`: add `Λ₀·sb` back to coords `6, 7`. -/
noncomputable def shear231Inv (v : Fin 9 → ℝ) : Fin 9 → ℝ :=
  fun i =>
    if i = 6 then v 6 + lam231 v 0 * v 8
    else if i = 7 then v 7 + lam231 v 1 * v 8
    else v i

/-- `lam231` reads only coords `0..5`; `shear231`/`shear231Inv` fix those, so `lam231` is invariant. -/
theorem lam231_shear231 (u : Fin 9 → ℝ) (i : Fin 2) : lam231 (shear231 u) i = lam231 u i := by
  have e : ∀ k : Fin 9, k ≠ 6 → k ≠ 7 → shear231 u k = u k :=
    fun k h6 h7 => shear231_spectator u h6 h7
  simp only [lam231, e 0 (by decide) (by decide), e 1 (by decide) (by decide),
    e 2 (by decide) (by decide), e 3 (by decide) (by decide), e 4 (by decide) (by decide),
    e 5 (by decide) (by decide)]

theorem lam231_shear231Inv (u : Fin 9 → ℝ) (i : Fin 2) :
    lam231 (shear231Inv u) i = lam231 u i := by
  have e : ∀ k : Fin 9, k ≠ 6 → k ≠ 7 → shear231Inv u k = u k := by
    intro k h6 h7; simp only [shear231Inv, if_neg h6, if_neg h7]
  simp only [lam231, e 0 (by decide) (by decide), e 1 (by decide) (by decide),
    e 2 (by decide) (by decide), e 3 (by decide) (by decide), e 4 (by decide) (by decide),
    e 5 (by decide) (by decide)]

theorem shear231_leftInv (u : Fin 9 → ℝ) : shear231Inv (shear231 u) = u := by
  funext i
  have hspec : ∀ k : Fin 9, k ≠ 6 → k ≠ 7 → shear231 u k = u k :=
    fun k h6 h7 => shear231_spectator u h6 h7
  obtain ⟨h6, h7⟩ := shear231_kept u
  -- the kept coords `6,7`: add back `Λ₀·sb` (`lam231` invariant under `shear231`, `sb = u 8` fixed)
  rcases eq_or_ne i 6 with rfl | hi6
  · show shear231Inv (shear231 u) 6 = u 6
    simp only [shear231Inv, if_true, reduceIte, h6, lam231_shear231,
      hspec 8 (by decide) (by decide)]; ring
  rcases eq_or_ne i 7 with rfl | hi7
  · show shear231Inv (shear231 u) 7 = u 7
    simp only [shear231Inv, show (7:Fin 9)=6 ↔ False from by decide, if_false, if_true, reduceIte,
      h7, lam231_shear231, hspec 8 (by decide) (by decide)]; ring
  · show shear231Inv (shear231 u) i = u i
    simp only [shear231Inv, if_neg hi6, if_neg hi7, hspec i hi6 hi7]

theorem shear231_rightInv (v : Fin 9 → ℝ) : shear231 (shear231Inv v) = v := by
  funext i
  have hspec : ∀ k : Fin 9, k ≠ 6 → k ≠ 7 → shear231Inv v k = v k := by
    intro k h6 h7; simp only [shear231Inv, if_neg h6, if_neg h7]
  have h6 : shear231Inv v 6 = v 6 + lam231 v 0 * v 8 := by
    simp only [shear231Inv, if_true, reduceIte]
  have h7 : shear231Inv v 7 = v 7 + lam231 v 1 * v 8 := by
    simp only [shear231Inv, show (7:Fin 9)=6 ↔ False from by decide, if_false, if_true, reduceIte]
  rcases eq_or_ne i 6 with rfl | hi6
  · show shear231 (shear231Inv v) 6 = v 6
    simp only [shear231, if_true, reduceIte, h6, lam231_shear231Inv, hspec 8 (by decide) (by decide)]
    ring
  rcases eq_or_ne i 7 with rfl | hi7
  · show shear231 (shear231Inv v) 7 = v 7
    simp only [shear231, show (7:Fin 9)=6 ↔ False from by decide, if_false, if_true, reduceIte,
      h7, lam231_shear231Inv, hspec 8 (by decide) (by decide)]; ring
  · show shear231 (shear231Inv v) i = v i
    simp only [shear231, if_neg hi6, if_neg hi7, hspec i hi6 hi7]

/-- `lam231 w 0` and `lam231 w 1` are GLOBALLY the explicit rational expressions (`(P₁ᵀP₁)⁻¹P₁ᵀP₂`
unfolded via the `2×2` `inv_def`/`adjugate_fin_two`/`det_fin_two`; the `⁻¹` is the totalized real
inverse). -/
theorem lam231_explicit (w : Fin 9 → ℝ) :
    lam231 w 0 = (w 0 * w 4 - w 1 * w 3)⁻¹ * (-(w 1 * w 5) + w 2 * w 4)
      ∧ lam231 w 1 = (w 0 * w 4 - w 1 * w 3)⁻¹ * (w 0 * w 5 - w 2 * w 3) := by
  -- `P₁ᵀP₁` as an explicit `!![…]` (so `adjugate_fin_two`/`det_fin_two` fire)
  have hG : (!![w 0, w 1; w 3, w 4] : Matrix (Fin 2) (Fin 2) ℝ).transpose * !![w 0, w 1; w 3, w 4]
      = !![w 0 ^ 2 + w 3 ^ 2, w 0 * w 1 + w 3 * w 4; w 0 * w 1 + w 3 * w 4, w 1 ^ 2 + w 4 ^ 2] := by
    funext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply] <;> ring
  have hdet : (!![w 0 ^ 2 + w 3 ^ 2, w 0 * w 1 + w 3 * w 4;
      w 0 * w 1 + w 3 * w 4, w 1 ^ 2 + w 4 ^ 2] : Matrix (Fin 2) (Fin 2) ℝ).det
      = (w 0 * w 4 - w 1 * w 3) ^ 2 := by rw [Matrix.det_fin_two_of]; ring
  constructor <;>
  · simp only [lam231, hG, Matrix.mul_apply, Fin.sum_univ_two, Matrix.inv_def,
      Ring.inverse_eq_inv', Matrix.adjugate_fin_two_of, hdet, Matrix.smul_apply,
      Matrix.transpose_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.head_fin_const, Matrix.of_apply, Matrix.cons_val,
      Matrix.cons_val_fin_one, Matrix.empty_val', smul_eq_mul]
    rw [show (w 0 * w 4 - w 1 * w 3) ^ 2 = (w 0 * w 4 - w 1 * w 3) * (w 0 * w 4 - w 1 * w 3) from by
      ring, mul_inv]
    -- unconditional: cancel ONE `det⁻¹` against the `det` factor in the numerator (split at det=0)
    rcases eq_or_ne (w 0 * w 4 - w 1 * w 3) 0 with hz | hz
    · rw [hz]; simp
    · field_simp
      ring

/-- `lam231 w i` is a measurable function of `w` (the explicit rational in coords `0..5`). -/
theorem lam231_measurable (i : Fin 2) : Measurable (fun w : Fin 9 → ℝ => lam231 w i) := by
  have hpi : ∀ k : Fin 9, Measurable (fun w : Fin 9 → ℝ => w k) := measurable_pi_apply
  fin_cases i
  · show Measurable (fun w : Fin 9 → ℝ => lam231 w 0)
    rw [funext (fun w => (lam231_explicit w).1)]
    exact Measurable.mul (Measurable.inv (Measurable.sub ((hpi 0).mul (hpi 4)) ((hpi 1).mul (hpi 3))))
      (Measurable.add (Measurable.neg ((hpi 1).mul (hpi 5))) ((hpi 2).mul (hpi 4)))
  · show Measurable (fun w : Fin 9 → ℝ => lam231 w 1)
    rw [funext (fun w => (lam231_explicit w).2)]
    exact Measurable.mul (Measurable.inv (Measurable.sub ((hpi 0).mul (hpi 4)) ((hpi 1).mul (hpi 3))))
      (Measurable.sub ((hpi 0).mul (hpi 5)) ((hpi 2).mul (hpi 3)))

theorem shear231_measurable : Measurable shear231 := by
  apply measurable_pi_iff.2; intro i
  rcases eq_or_ne i 6 with rfl | hi6
  · simp only [shear231, if_true, reduceIte]
    exact (measurable_pi_apply 6).sub ((lam231_measurable 0).mul (measurable_pi_apply 8))
  rcases eq_or_ne i 7 with rfl | hi7
  · simp only [shear231, show (7:Fin 9)=6 ↔ False from by decide, if_false, if_true, reduceIte]
    exact (measurable_pi_apply 7).sub ((lam231_measurable 1).mul (measurable_pi_apply 8))
  · simp only [shear231, if_neg hi6, if_neg hi7]; exact measurable_pi_apply i

theorem shear231Inv_measurable : Measurable shear231Inv := by
  apply measurable_pi_iff.2; intro i
  rcases eq_or_ne i 6 with rfl | hi6
  · simp only [shear231Inv, if_true, reduceIte]
    exact (measurable_pi_apply 6).add ((lam231_measurable 0).mul (measurable_pi_apply 8))
  rcases eq_or_ne i 7 with rfl | hi7
  · simp only [shear231Inv, show (7:Fin 9)=6 ↔ False from by decide, if_false, if_true, reduceIte]
    exact (measurable_pi_apply 7).add ((lam231_measurable 1).mul (measurable_pi_apply 8))
  · simp only [shear231Inv, if_neg hi6, if_neg hi7]; exact measurable_pi_apply i

/-- **`shear231` as a measurable equivalence** (the global bijection). -/
noncomputable def shear231ME : (Fin 9 → ℝ) ≃ᵐ (Fin 9 → ℝ) where
  toFun := shear231
  invFun := shear231Inv
  left_inv := shear231_leftInv
  right_inv := shear231_rightInv
  measurable_toFun := shear231_measurable
  measurable_invFun := shear231Inv_measurable

/-! ### `shear231` is measure-preserving (Codex `shear231-mp`, Option B: single 2-core split)

Reindex `Fin 9 → ℝ` as `(reg=coord 0) × ((core=coords 6,7) × (spec=coords 1,2,3,4,5,8))`, then the
`coreShear_measurable 1 2 6` skew-product translates the `Fin 2` core by the measurable shift
`−Λ₀·sb`. Peels: `Fin 9` peel `0`; on the `Fin 8` remainder peel `5` (orig coord `6`); on the `Fin 7`
remainder peel `5` (orig coord `7`). -/

/-- The `Fin 8 → ℝ ≃ᵐ (Fin 2 → ℝ) × (Fin 6 → ℝ)` peel pulling the core coords `6,7` (after coord `0`
was already removed; in `Fin 8` they sit at indices `5,6`). -/
noncomputable def coreSpec231 :
    (Fin 8 → ℝ) ≃ᵐ (Fin 2 → ℝ) × (Fin 6 → ℝ) :=
  (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 8 => ℝ) 5).trans
    (((MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ)
      ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin 7 => ℝ) 5).trans
        (MeasurableEquiv.prodCongr
          (MeasurableEquiv.funUnique (Fin 1) ℝ).symm
          (MeasurableEquiv.refl (Fin 6 → ℝ))))).trans
    (((MeasurableEquiv.prodAssoc :
        (ℝ × (Fin 1 → ℝ)) × (Fin 6 → ℝ) ≃ᵐ
          ℝ × ((Fin 1 → ℝ) × (Fin 6 → ℝ))).symm).trans
      (MeasurableEquiv.prodCongr
        (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 2 => ℝ) 0).symm
        (MeasurableEquiv.refl (Fin 6 → ℝ))))))

/-- The full reindex `Fin 9 → ℝ ≃ᵐ (reg) × (core × spec)`. -/
noncomputable def split231 :
    (Fin 9 → ℝ) ≃ᵐ (Fin 1 → ℝ) × ((Fin 2 → ℝ) × (Fin 6 → ℝ)) :=
  (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 9 => ℝ) 0).trans
    (MeasurableEquiv.prodCongr
      (MeasurableEquiv.funUnique (Fin 1) ℝ).symm
      coreSpec231)

theorem measurePreserving_coreSpec231 :
    MeasurePreserving (coreSpec231 : (Fin 8 → ℝ) → _) volume volume := by
  unfold coreSpec231
  refine (volume_preserving_piFinSuccAbove (fun _ : Fin 8 => ℝ) 5).trans ?_
  have hstep1 : MeasurePreserving
      ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin 7 => ℝ) 5).trans
        (MeasurableEquiv.prodCongr (MeasurableEquiv.funUnique (Fin 1) ℝ).symm
          (MeasurableEquiv.refl (Fin 6 → ℝ))))
      (volume : Measure (Fin 7 → ℝ)) volume := by
    refine (volume_preserving_piFinSuccAbove (fun _ : Fin 7 => ℝ) 5).trans ?_
    exact MeasurePreserving.prod
      (volume_preserving_funUnique (Fin 1) ℝ).symm
      (MeasurePreserving.id (volume : Measure (Fin 6 → ℝ)))
  refine (MeasurePreserving.prod (MeasurePreserving.id (volume : Measure ℝ)) hstep1).trans ?_
  refine ((volume_preserving_prodAssoc (α₁ := ℝ) (β₁ := Fin 1 → ℝ) (γ₁ := Fin 6 → ℝ)).symm
      MeasurableEquiv.prodAssoc).trans ?_
  exact MeasurePreserving.prod
    (volume_preserving_piFinSuccAbove (fun _ : Fin 2 => ℝ) 0).symm
    (MeasurePreserving.id (volume : Measure (Fin 6 → ℝ)))

theorem measurePreserving_split231 :
    MeasurePreserving (split231 : (Fin 9 → ℝ) → _) volume volume := by
  unfold split231
  refine (volume_preserving_piFinSuccAbove (fun _ : Fin 9 => ℝ) 0).trans ?_
  exact MeasurePreserving.prod
    (volume_preserving_funUnique (Fin 1) ℝ).symm
    measurePreserving_coreSpec231

/-- Reconstruct the coords `{0..5, 8}` (with `0` in slots `6,7`) from the split base `(reg, spec)`,
so `lam231 (base231 q) = lam231 (orig)` (lam231 reads only coords `0..5`). -/
noncomputable def base231 (q : (Fin 1 → ℝ) × (Fin 6 → ℝ)) : Fin 9 → ℝ :=
  ![q.1 0, q.2 0, q.2 1, q.2 2, q.2 3, q.2 4, 0, 0, q.2 5]

/-- The `Fin 2` core shift `−Λ₀·sb` as a function of the split base. -/
noncomputable def shift231 :
    (Fin 1 → ℝ) × (Fin 6 → ℝ) → (Fin 2 → ℝ) :=
  fun q i => - lam231 (base231 q) i * q.2 5

theorem base231_measurable : Measurable base231 := by
  apply measurable_pi_iff.2; intro i
  have hf : Measurable (fun x : (Fin 1 → ℝ) × (Fin 6 → ℝ) => x.1 0) :=
    (measurable_pi_apply 0).comp measurable_fst
  have hs : ∀ k : Fin 6, Measurable (fun x : (Fin 1 → ℝ) × (Fin 6 → ℝ) => x.2 k) :=
    fun k => (measurable_pi_apply k).comp measurable_snd
  fin_cases i <;>
    simp only [base231, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.head_fin_const, Matrix.cons_val, Matrix.cons_val_fin_one,
      Matrix.empty_val', Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three,
      Matrix.cons_val_four]
  · exact hf
  · exact hs 0
  · exact hs 1
  · exact hs 2
  · exact hs 3
  · exact hs 4
  · exact measurable_const
  · exact measurable_const
  · exact hs 5

theorem shift231_measurable : Measurable shift231 := by
  apply measurable_pi_iff.2; intro i
  unfold shift231
  exact ((lam231_measurable i).comp base231_measurable).neg.mul
    ((measurable_pi_apply 5).comp measurable_snd)

set_option maxHeartbeats 1000000 in
theorem split231_shear231 (u : Fin 9 → ℝ) :
    split231 (shear231 u)
      = (fun q : (Fin 1 → ℝ) × ((Fin 2 → ℝ) × (Fin 6 → ℝ)) =>
          (q.1, (q.2.1 + shift231 (q.1, q.2.2), q.2.2))) (split231 u) := by
  apply Prod.ext
  · funext k
    fin_cases k
    simp [split231, coreSpec231, shear231, MeasurableEquiv.piFinSuccAbove,
      MeasurableEquiv.funUnique, MeasurableEquiv.prodCongr, MeasurableEquiv.prodAssoc,
      Fin.insertNthEquiv, Fin.removeNth, Fin.succAbove]
  apply Prod.ext
  · -- core = coords 6,7, shifted by `−Λ₀·sb`
    funext k
    fin_cases k <;>
      simp [split231, coreSpec231, shear231, shift231, base231, lam231,
        MeasurableEquiv.piFinSuccAbove, MeasurableEquiv.funUnique,
        MeasurableEquiv.prodCongr, MeasurableEquiv.prodAssoc,
        Fin.insertNthEquiv, Fin.removeNth, Fin.succAbove, Fin.tail] <;>
      ring
  · -- spec = coords 1,2,3,4,5,8 (unchanged)
    funext k
    fin_cases k <;>
      simp [split231, coreSpec231, shear231, MeasurableEquiv.piFinSuccAbove,
        MeasurableEquiv.funUnique, MeasurableEquiv.prodCongr, MeasurableEquiv.prodAssoc,
        Fin.insertNthEquiv, Fin.removeNth, Fin.succAbove, Fin.tail]

theorem shear231_eq_conj (u : Fin 9 → ℝ) :
    shear231 u = split231.symm
      ((fun q : (Fin 1 → ℝ) × ((Fin 2 → ℝ) × (Fin 6 → ℝ)) =>
          (q.1, (q.2.1 + shift231 (q.1, q.2.2), q.2.2))) (split231 u)) := by
  rw [← split231_shear231, MeasurableEquiv.symm_apply_apply]

theorem measurePreserving_shear231 :
    MeasurePreserving shear231 (volume : Measure (Fin 9 → ℝ)) volume := by
  have hcore :=
    measurePreserving_coreShear_measurable 1 2 6 shift231 shift231_measurable
  have hconj : MeasurePreserving
      (split231.symm ∘
        (fun q : (Fin 1 → ℝ) × ((Fin 2 → ℝ) × (Fin 6 → ℝ)) =>
          (q.1, (q.2.1 + shift231 (q.1, q.2.2), q.2.2))) ∘
        split231)
      volume volume :=
    (measurePreserving_split231.symm split231).comp
      (hcore.comp measurePreserving_split231)
  refine hconj.congr shear231_measurable ?_
  filter_upwards with u
  exact (shear231_eq_conj u).symm

/-! ### `ψ231 = Q231 ∘ shear231` (measure-preserving + measurable embedding) and `φ = ψ ∘ R` -/

/-- **The MP part** `ψ231 = paramsEquivFlat ∘ pack231 ∘ shear231` (the rational shear ∘ linear reshape;
NO radial). -/
noncomputable def psi231 (w : Fin 9 → ℝ) : Fin (flatDim M231) → ℝ :=
  paramsEquivFlat M231 (pack231 (shear231 w))

/-- **`φ231sm = ψ231 ∘ R231`** (the radial-then-shear factorization, through `paramsEquivFlat`). -/
theorem phi231sm_eq_psi_R (u : Fin 9 → ℝ) : phi231sm u = psi231 (R231 u) := by
  rw [phi231sm, psi231, chartParams231_eq_pack_shear_R]

theorem measurePreserving_psi231 :
    MeasurePreserving psi231 (volume : Measure (Fin 9 → ℝ)) volume := by
  have hmeas : Measurable psi231 := by
    have : psi231 = (fun w : Fin 9 → ℝ => paramsEquivFlat M231 (pack231 w)) ∘ shear231 :=
      funext (fun w => rfl)
    rw [this]; exact measurePreserving_Q231.measurable.comp shear231_measurable
  refine (measurePreserving_Q231.comp measurePreserving_shear231).congr hmeas ?_
  filter_upwards with u; rfl

/-- **`ψ231` packaged as a measurable equivalence** `shear231ME ≫ (flatEquivOf).symm ≫
paramsEquivFlat` (`pack231 = (flatEquivOf …).symm`; codomain `Fin (flatDim M231) → ℝ` defeq
`Fin 9 → ℝ`). -/
noncomputable def psi231ME : (Fin 9 → ℝ) ≃ᵐ (Fin (flatDim M231) → ℝ) :=
  shear231ME.trans
    (((flatEquivOf M231 fin9EquivFlatIdx231).symm).trans (paramsEquivFlat M231))

theorem psi231ME_eq (u : Fin 9 → ℝ) : psi231ME u = psi231 u := by
  rw [psi231ME, psi231]
  show paramsEquivFlat M231 ((flatEquivOf M231 fin9EquivFlatIdx231).symm (shear231 u)) = _
  congr 1
  funext s i j
  exact (flatEquivOf_symm_coord M231 fin9EquivFlatIdx231 (shear231 u) ⟨⟨s, i⟩, j⟩).trans
    (hpack231 (shear231 u) ⟨⟨s, i⟩, j⟩).symm

theorem measurableEmbedding_psi231 : MeasurableEmbedding psi231 := by
  have h : psi231 = ⇑psi231ME := funext (fun u => (psi231ME_eq u).symm)
  rw [h]; exact psi231ME.measurableEmbedding

/-! ### The radial-blow-up certificates (`R231`'s fderiv / injOn / |det| = |u 6|¹) -/

/-- The fderiv carrier `D231 u = pivotBlowupOnDeriv {6,7} 6 u` (the radial-blow-up arrow map). -/
noncomputable def D231 (u : Fin 9 → ℝ) : (Fin 9 → ℝ) →L[ℝ] (Fin 9 → ℝ) :=
  pivotBlowupOnDeriv ({6, 7} : Finset (Fin 9)) 6 u

theorem R231_hasFDerivWithinAt (S : Set (Fin 9 → ℝ)) (u : Fin 9 → ℝ) :
    HasFDerivWithinAt R231 (D231 u) S u :=
  pivotBlowupOn_hasFDerivWithinAt _ _ S u

/-- `|det (D231 u)| = |u 6|¹` (`active = {6,7}`, `card = 2`; `pivotBlowupOnDeriv_det`). -/
theorem D231_abs_det (u : Fin 9 → ℝ) : |(D231 u).det| = |u 6| ^ 1 := by
  rw [D231, pivotBlowupOnDeriv_det ({6, 7} : Finset (Fin 9)) 6 (by decide),
    show ({6, 7} : Finset (Fin 9)).card - 1 = 1 from by decide, abs_pow]

/-- `R231` is injective off `{u 6 = 0}` (`pivotBlowupOn_injOn`). -/
theorem R231_injOn (S : Set (Fin 9 → ℝ)) :
    Set.InjOn R231 (S \ {x | x 6 = 0}) := pivotBlowupOn_injOn _ _ S

/-! ### The bounded source sub-box `subBox231` + containment

`subBox231 δ`: `u0,u4 ∈ [δ/2, δ]` (the kept `2×2` block diagonal — keeps `det P₁` and `U` bounded
away from `0`), `u1,u2,u3,u5,u7,u8 ∈ [−δ/8, δ/8]` (small off-diagonal), `u6 = z ∈ (0, δ)` (the binding
radial axis, weight `|u6|¹`). On it `det P₁ ≠ 0` (so the rate `z²·U` holds) and `U ≥ (δ/2 − δ²/64)²`. -/
def subBox231 (δ : ℝ) : Set (Fin 9 → ℝ) :=
  {u | u 0 ∈ Set.Icc (δ/2) δ ∧ u 1 ∈ Set.Icc (-(δ/8)) (δ/8) ∧ u 2 ∈ Set.Icc (-(δ/8)) (δ/8) ∧
    u 3 ∈ Set.Icc (-(δ/8)) (δ/8) ∧ u 4 ∈ Set.Icc (δ/2) δ ∧ u 5 ∈ Set.Icc (-(δ/8)) (δ/8) ∧
    u 6 ∈ Set.Ioo (0:ℝ) δ ∧ u 7 ∈ Set.Icc (-(δ/8)) (δ/8) ∧ u 8 ∈ Set.Icc (-(δ/8)) (δ/8)}

theorem measurableSet_subBox231 (δ : ℝ) : MeasurableSet (subBox231 δ) := by
  unfold subBox231
  refine MeasurableSet.inter (measurableSet_preimage (measurable_pi_apply 0) measurableSet_Icc) ?_
  refine MeasurableSet.inter (measurableSet_preimage (measurable_pi_apply 1) measurableSet_Icc) ?_
  refine MeasurableSet.inter (measurableSet_preimage (measurable_pi_apply 2) measurableSet_Icc) ?_
  refine MeasurableSet.inter (measurableSet_preimage (measurable_pi_apply 3) measurableSet_Icc) ?_
  refine MeasurableSet.inter (measurableSet_preimage (measurable_pi_apply 4) measurableSet_Icc) ?_
  refine MeasurableSet.inter (measurableSet_preimage (measurable_pi_apply 5) measurableSet_Icc) ?_
  refine MeasurableSet.inter (measurableSet_preimage (measurable_pi_apply 6) measurableSet_Ioo) ?_
  exact MeasurableSet.inter (measurableSet_preimage (measurable_pi_apply 7) measurableSet_Icc)
    (measurableSet_preimage (measurable_pi_apply 8) measurableSet_Icc)

/-- `det P₁ = u0·u4 − u1·u3 ≠ 0` on `subBox231 δ` (`δ > 0`): `u0,u4 ≥ δ/2`, `|u1|,|u3| ≤ δ/8`, so
`det ≥ δ²/4 − δ²/64 > 0`. -/
theorem subBox231_det_ne {δ : ℝ} (hδ : 0 < δ) {u : Fin 9 → ℝ} (hu : u ∈ subBox231 δ) :
    (P1_231 u).det ≠ 0 := by
  obtain ⟨h0, h1, _, h3, h4, _, _, _, _⟩ := hu
  simp only [Set.mem_Icc] at h0 h1 h3 h4
  rw [P1_231, Matrix.det_fin_two_of]
  have hδ8 : 0 < δ / 8 := by linarith
  have hdet : u 0 * u 4 - u 1 * u 3 > 0 := by
    nlinarith [h0.1, h0.2, h4.1, h4.2, h1.1, h1.2, h3.1, h3.2, mul_nonneg (le_of_lt hδ8) (le_of_lt hδ8),
      sq_nonneg (u 1 - u 3), sq_nonneg (u 1 + u 3)]
  exact ne_of_gt hdet

/-- `det P₁ ≥ δ²/8` on `subBox231 δ` (a quantitative lower bound, for the `Λ₀` entry bound). -/
theorem subBox231_det_ge {δ : ℝ} (hδ : 0 < δ) {u : Fin 9 → ℝ} (hu : u ∈ subBox231 δ) :
    δ ^ 2 / 8 ≤ (P1_231 u).det := by
  obtain ⟨h0, h1, _, h3, h4, _, _, _, _⟩ := hu
  simp only [Set.mem_Icc] at h0 h1 h3 h4
  rw [P1_231, Matrix.det_fin_two_of]
  nlinarith [h0.1, h0.2, h4.1, h4.2, h1.1, h1.2, h3.1, h3.2, sq_nonneg (u 1 - u 3),
    sq_nonneg (u 1 + u 3), mul_pos hδ hδ]

/-- `|lam231 u i| ≤ 9/8` on `subBox231 δ` (`δ > 0`): `|lam231| = |det|⁻¹·|num| ≤ (8/δ²)·(9δ²/64)`. The
`det` here is `P₁ᵀP₁`'s det `= (det P₁)²` ≥ `(δ²/8)²`... using the `lam231_explicit` form with `det P₁`
in the denominator and the small-coord numerator. -/
theorem subBox231_lam_bound {δ : ℝ} (hδ : 0 < δ) {u : Fin 9 → ℝ} (hu : u ∈ subBox231 δ)
    (i : Fin 2) : |lam231 u i| ≤ 9 / 8 := by
  have hdg := subBox231_det_ge hδ hu
  rw [P1_231, Matrix.det_fin_two_of] at hdg
  obtain ⟨h0, h1, h2, h3, h4, h5, _, _, _⟩ := hu
  simp only [Set.mem_Icc] at h0 h1 h2 h3 h4 h5
  have hden : (0:ℝ) < u 0 * u 4 - u 1 * u 3 := by linarith [hdg, div_pos (by positivity : (0:ℝ) < δ^2) (by norm_num : (0:ℝ) < 8)]
  -- the explicit numerator bounds: |−u1u5+u2u4| and |u0u5−u2u3| each ≤ 9δ²/64
  fin_cases i
  · show |lam231 u 0| ≤ 9 / 8
    rw [(lam231_explicit u).1, abs_mul, abs_inv]
    have hnum : |(-(u 1 * u 5) + u 2 * u 4)| ≤ 9 * δ ^ 2 / 64 := by
      have h15 : |u 1 * u 5| ≤ δ/8 * (δ/8) := by
        rw [abs_mul]; exact mul_le_mul (abs_le.mpr ⟨h1.1, h1.2⟩) (abs_le.mpr ⟨h5.1, h5.2⟩)
          (abs_nonneg _) (by linarith)
      have h24 : |u 2 * u 4| ≤ δ/8 * δ := by
        rw [abs_mul]; exact mul_le_mul (abs_le.mpr ⟨h2.1, h2.2⟩) (by rw [abs_of_nonneg (by linarith)]; exact h4.2)
          (abs_nonneg _) (by linarith)
      calc |(-(u 1 * u 5) + u 2 * u 4)| = |u 2 * u 4 - u 1 * u 5| := by rw [show -(u 1 * u 5) + u 2 * u 4 = u 2 * u 4 - u 1 * u 5 from by ring]
        _ ≤ |u 2 * u 4| + |u 1 * u 5| := abs_sub _ _
        _ ≤ δ/8 * δ + δ/8 * (δ/8) := by linarith
        _ = 9 * δ ^ 2 / 64 := by ring
    rw [abs_of_pos hden, inv_mul_le_iff₀ hden]
    calc |(-(u 1 * u 5) + u 2 * u 4)| ≤ 9 * δ ^ 2 / 64 := hnum
      _ ≤ (u 0 * u 4 - u 1 * u 3) * (9 / 8) := by nlinarith [hdg]
  · show |lam231 u 1| ≤ 9 / 8
    rw [(lam231_explicit u).2, abs_mul, abs_inv]
    have hnum : |(u 0 * u 5 - u 2 * u 3)| ≤ 9 * δ ^ 2 / 64 := by
      have h05 : |u 0 * u 5| ≤ δ * (δ/8) := by
        rw [abs_mul]; exact mul_le_mul (by rw [abs_of_nonneg (by linarith)]; exact h0.2)
          (abs_le.mpr ⟨h5.1, h5.2⟩) (abs_nonneg _) (by linarith)
      have h23 : |u 2 * u 3| ≤ δ/8 * (δ/8) := by
        rw [abs_mul]; exact mul_le_mul (abs_le.mpr ⟨h2.1, h2.2⟩) (abs_le.mpr ⟨h3.1, h3.2⟩)
          (abs_nonneg _) (by linarith)
      calc |(u 0 * u 5 - u 2 * u 3)| ≤ |u 0 * u 5| + |u 2 * u 3| := abs_sub _ _
        _ ≤ δ * (δ/8) + δ/8 * (δ/8) := by linarith
        _ = 9 * δ ^ 2 / 64 := by ring
    rw [abs_of_pos hden, inv_mul_le_iff₀ hden]
    calc |(u 0 * u 5 - u 2 * u 3)| ≤ 9 * δ ^ 2 / 64 := hnum
      _ ≤ (u 0 * u 4 - u 1 * u 3) * (9 / 8) := by nlinarith [hdg]

/-- **Each flat coord of `phi231sm u`** is a matrix entry of `chartParams231 u` (`rfl` — the
`paramsEquivFlat`/`Fintype.equivFin` slot readout). -/
theorem phi231sm_entry (u : Fin 9 → ℝ) (i : Fin (flatDim M231)) :
    phi231sm u i = (chartParams231 u)
      ((Fintype.equivFin (FlatIdx M231)).symm i).1.1
      ((Fintype.equivFin (FlatIdx M231)).symm i).1.2
      ((Fintype.equivFin (FlatIdx M231)).symm i).2 := rfl

/-- **Every matrix entry of `chartParams231 u` is `≤ 2δ` on `subBox231 δ`** (`0 < δ ≤ 1`). A⁰ entries
are coords `u0..u5` (`≤ δ`); A¹ entries are `z − Λ₀₀·sb` (`≤ δ + (9/8)(δ/8)`), `z·h1 − Λ₀₁·sb`
(`z·h1 ≤ δ/8` for `δ ≤ 1`), `sb` (`≤ δ/8`). -/
theorem chartParams231_entry_bound {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) {u : Fin 9 → ℝ}
    (hu : u ∈ subBox231 δ) (s : Fin 2) (i : Fin (M231 s.castSucc)) (j : Fin (M231 s.succ)) :
    |(chartParams231 u) s i j| ≤ 2 * δ := by
  have hlam0 := subBox231_lam_bound hδ hu 0
  have hlam1 := subBox231_lam_bound hδ hu 1
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩ := hu
  simp only [Set.mem_Icc] at h0 h1 h2 h3 h4 h5 h7 h8
  simp only [Set.mem_Ioo] at h6
  -- coord bounds
  have b0 : |u 0| ≤ δ := abs_le.mpr ⟨by linarith, h0.2⟩
  have b1 : |u 1| ≤ δ := abs_le.mpr ⟨by linarith, by linarith⟩
  have b2 : |u 2| ≤ δ := abs_le.mpr ⟨by linarith, by linarith⟩
  have b3 : |u 3| ≤ δ := abs_le.mpr ⟨by linarith, by linarith⟩
  have b4 : |u 4| ≤ δ := abs_le.mpr ⟨by linarith, h4.2⟩
  have b5 : |u 5| ≤ δ := abs_le.mpr ⟨by linarith, by linarith⟩
  have b6 : |u 6| ≤ δ := abs_le.mpr ⟨by linarith, le_of_lt h6.2⟩
  have b8 : |u 8| ≤ δ/8 := abs_le.mpr ⟨h8.1, h8.2⟩
  have b7 : |u 7| ≤ δ/8 := abs_le.mpr ⟨h7.1, h7.2⟩
  -- the two nontrivial A¹ entries
  have hA10 : |u 6 - lam231 u 0 * u 8| ≤ 2 * δ := by
    have : |lam231 u 0 * u 8| ≤ 9/8 * (δ/8) := by
      rw [abs_mul]; exact mul_le_mul hlam0 b8 (abs_nonneg _) (by norm_num)
    calc |u 6 - lam231 u 0 * u 8| ≤ |u 6| + |lam231 u 0 * u 8| := abs_sub _ _
      _ ≤ δ + 9/8 * (δ/8) := by linarith
      _ ≤ 2 * δ := by linarith
  have hA11 : |u 6 * u 7 - lam231 u 1 * u 8| ≤ 2 * δ := by
    have hzh : |u 6 * u 7| ≤ δ * (δ/8) := by
      rw [abs_mul]; exact mul_le_mul b6 b7 (abs_nonneg _) (by linarith)
    have hls : |lam231 u 1 * u 8| ≤ 9/8 * (δ/8) := by
      rw [abs_mul]; exact mul_le_mul hlam1 b8 (abs_nonneg _) (by norm_num)
    calc |u 6 * u 7 - lam231 u 1 * u 8| ≤ |u 6 * u 7| + |lam231 u 1 * u 8| := abs_sub _ _
      _ ≤ δ * (δ/8) + 9/8 * (δ/8) := by linarith
      _ ≤ 2 * δ := by nlinarith [hδ, hδ1]
  have hsimp : ∀ e : ℝ, |e| ≤ δ → |e| ≤ 2 * δ := fun e h => by linarith
  fin_cases s
  · fin_cases i <;> fin_cases j
    · show |chartA0_231 u 0 0| ≤ 2 * δ
      simp only [chartA0_231, Matrix.cons_val', Matrix.cons_val_zero, Matrix.head_cons,
        Matrix.of_apply, Matrix.cons_val, Matrix.empty_val', Matrix.cons_val_fin_one]
      exact hsimp _ b0
    · show |chartA0_231 u 0 1| ≤ 2 * δ
      simp only [chartA0_231, Matrix.cons_val', Matrix.cons_val_one, Matrix.cons_val_zero,
        Matrix.head_cons, Matrix.of_apply, Matrix.cons_val, Matrix.empty_val',
        Matrix.cons_val_fin_one]
      exact hsimp _ b1
    · show |chartA0_231 u 0 2| ≤ 2 * δ
      simp only [chartA0_231, Matrix.cons_val', Matrix.cons_val_two, Matrix.tail_cons,
        Matrix.head_cons, Matrix.of_apply, Matrix.cons_val, Matrix.empty_val',
        Matrix.cons_val_fin_one]
      exact hsimp _ b2
    · show |chartA0_231 u 1 0| ≤ 2 * δ
      simp only [chartA0_231, Matrix.cons_val', Matrix.cons_val_one, Matrix.cons_val_zero,
        Matrix.head_cons, Matrix.head_fin_const, Matrix.of_apply, Matrix.cons_val,
        Matrix.empty_val', Matrix.cons_val_fin_one]
      exact hsimp _ b3
    · show |chartA0_231 u 1 1| ≤ 2 * δ
      simp only [chartA0_231, Matrix.cons_val', Matrix.cons_val_one, Matrix.head_cons,
        Matrix.head_fin_const, Matrix.of_apply, Matrix.cons_val, Matrix.empty_val',
        Matrix.cons_val_fin_one]
      exact hsimp _ b4
    · show |chartA0_231 u 1 2| ≤ 2 * δ
      simp only [chartA0_231, Matrix.cons_val', Matrix.cons_val_two, Matrix.tail_cons,
        Matrix.cons_val_one, Matrix.head_cons, Matrix.head_fin_const, Matrix.of_apply,
        Matrix.cons_val, Matrix.empty_val', Matrix.cons_val_fin_one]
      exact hsimp _ b5
  · fin_cases i <;> fin_cases j
    · show |chartA1_231 u 0 0| ≤ 2 * δ
      simpa only [chartA1_231, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val,
        Matrix.cons_val_fin_one] using hA10
    · show |chartA1_231 u 1 0| ≤ 2 * δ
      simpa only [chartA1_231, Matrix.of_apply, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val, Matrix.cons_val_fin_one] using hA11
    · show |chartA1_231 u 2 0| ≤ 2 * δ
      simp only [chartA1_231, Matrix.cons_val', Matrix.cons_val_two, Matrix.tail_cons,
        Matrix.head_cons, Matrix.of_apply, Matrix.cons_val, Matrix.empty_val',
        Matrix.cons_val_fin_one]
      have b8' : |u 8| ≤ δ := by linarith [b8]
      exact hsimp _ b8'

/-- **Containment** `subBox231 δ ⊆ phi231sm⁻¹(cubeBox 9 (2δ))` (`0 < δ ≤ 1`): each flat coord is a
matrix entry, `≤ 2δ` on the box. -/
theorem subBox231_subset_preimage {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    subBox231 δ ⊆ phi231sm ⁻¹' (cubeBox (flatDim M231) (2 * δ)) := by
  intro u hu
  rw [Set.mem_preimage, cubeBox, Set.mem_pi]
  intro i _
  rw [Set.mem_Icc, ← abs_le, phi231sm_entry]
  exact chartParams231_entry_bound hδ hδ1 hu _ _ _

/-! ### The WEIGHTED divergence on `subBox231` (the radial `|u6|¹` absorbed into the z-axis) -/

/-- `Uval231` is measurable (polynomial in coords `0,1,3,4,7`). -/
theorem Uval231_measurable : Measurable Uval231 := by
  unfold Uval231
  have hpi : ∀ k : Fin 9, Measurable (fun w : Fin 9 → ℝ => w k) := measurable_pi_apply
  exact (((hpi 0).add ((hpi 1).mul (hpi 7))).pow_const 2).add
    (((hpi 3).add ((hpi 4).mul (hpi 7))).pow_const 2)

/-- `Uval231 (insertNth 6 x y)` as an explicit polynomial in `y` (coords `0,1,3,4,7` are
`y 0, y 1, y 3, y 4, y 6` — the `succAbove 6`-preimages; coord `6 = x` is unread). -/
theorem Uval231_insertNth_6_eq (x : ℝ) (y : Fin 8 → ℝ) :
    Uval231 (Fin.insertNth 6 x y) = (y 0 + y 1 * y 6) ^ 2 + (y 3 + y 4 * y 6) ^ 2 := by
  unfold Uval231
  rw [show (0 : Fin 9) = Fin.succAbove 6 0 from by decide,
    show (1 : Fin 9) = Fin.succAbove 6 1 from by decide,
    show (3 : Fin 9) = Fin.succAbove 6 3 from by decide,
    show (4 : Fin 9) = Fin.succAbove 6 4 from by decide,
    show (7 : Fin 9) = Fin.succAbove 6 6 from by decide]
  simp only [Fin.insertNth_apply_succAbove]

/-- `Uval231` does not read coord `6`: `Uval231 (insertNth 6 x y)` is independent of `x`. -/
theorem Uval231_insertNth_6 (x : ℝ) (y : Fin 8 → ℝ) :
    Uval231 (Fin.insertNth 6 x y) = Uval231 (Fin.insertNth 6 (0:ℝ) y) := by
  rw [Uval231_insertNth_6_eq, Uval231_insertNth_6_eq]

/-- `fun y => Uval231 (insertNth 6 0 y)` is measurable. -/
theorem Uval231_insertNth_6_measurable :
    Measurable (fun y : Fin 8 → ℝ => Uval231 (Fin.insertNth 6 (0:ℝ) y)) := by
  have : (fun y : Fin 8 → ℝ => Uval231 (Fin.insertNth 6 (0:ℝ) y))
      = fun y => (y 0 + y 1 * y 6) ^ 2 + (y 3 + y 4 * y 6) ^ 2 :=
    funext (fun y => Uval231_insertNth_6_eq 0 y)
  rw [this]
  have hpi : ∀ k : Fin 8, Measurable (fun y : Fin 8 → ℝ => y k) := measurable_pi_apply
  exact (((hpi 0).add ((hpi 1).mul (hpi 6))).pow_const 2).add
    (((hpi 3).add ((hpi 4).mul (hpi 6))).pow_const 2)

/-- `U = Uval231 u > 0` on `subBox231 δ` (`δ > 0`): `U ≥ (u0+u1·u7)² ≥ (δ/2 − δ²/64)² > 0`. -/
theorem subBox231_U_pos {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) {u : Fin 9 → ℝ}
    (hu : u ∈ subBox231 δ) : 0 < Uval231 u := by
  obtain ⟨h0, h1, _, _, _, _, _, h7, _⟩ := hu
  simp only [Set.mem_Icc] at h0 h1 h7
  have hkey : 0 < u 0 + u 1 * u 7 := by
    nlinarith [h0.1, h0.2, h1.1, h1.2, h7.1, h7.2, mul_pos hδ hδ]
  have : 0 < (u 0 + u 1 * u 7) ^ 2 := by positivity
  unfold Uval231; nlinarith [sq_nonneg (u 3 + u 4 * u 7), this]

/-- `subBox231 δ` as a `univ.pi` of per-axis intervals (for the `volume_pi`/`piFinSuccAbove` peel). -/
theorem subBox231_eq_pi (δ : ℝ) :
    subBox231 δ = Set.univ.pi
      (fun i : Fin 9 => if i = 6 then Set.Ioo (0:ℝ) δ
        else if i = 0 ∨ i = 4 then Set.Icc (δ/2) δ else Set.Icc (-(δ/8)) (δ/8)) := by
  ext u
  simp only [subBox231, Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, true_implies]
  constructor
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩ i
    fin_cases i <;> simp_all
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      [have := h 0; have := h 1; have := h 2; have := h 3; have := h 4; have := h 5; have := h 6;
        have := h 7; have := h 8] <;> simp_all

/-- **The weighted divergence on `subBox231`** `∫_{S} |u6|¹·(|loss∘φ|)^{−c'} = ⊤` for `0 < δ ≤ 1`,
`c' ≥ 1`. On `S` the rate `loss∘φ = (u6)²·U` (`det P₁ ≠ 0`), so the integrand
`= |u6|^{1−2c'}·U^{−c'}`; peel the z-axis (index 6) — the z-factor `∫_{(0,δ)} |u6|^{1−2c'} = ⊤`
(`1−2c' ≤ −1`), the rest (`U^{−c'}` over the positive-measure rest box) is positive-finite. -/
theorem subBox231_diverges {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) {c' : ℝ} (hc' : (1:ℝ) ≤ c') :
    ∫⁻ u in subBox231 δ,
      ENNReal.ofReal (|u 6| ^ (1:ℕ)) * ENNReal.ofReal (|routeMCore M231 (phi231sm u)| ^ (-c')) = ⊤ := by
  -- rewrite the integrand to `|u6|^{1−2c'} * U^{−c'}` on `S` (the rate + weight absorbed)
  have hrw : ∀ u ∈ subBox231 δ,
      ENNReal.ofReal (|u 6| ^ (1:ℕ)) * ENNReal.ofReal (|routeMCore M231 (phi231sm u)| ^ (-c'))
        = ENNReal.ofReal (|u 6| ^ (1 - 2*c')) * ENNReal.ofReal (Uval231 u ^ (-c')) := by
    intro u hu
    have hdne := subBox231_det_ne hδ hu
    have hUpos := subBox231_U_pos hδ hδ1 hu
    rw [routeMCore_phi231sm_offpole u hdne]
    have h6pos : 0 < u 6 := by obtain ⟨_,_,_,_,_,_,h6,_,_⟩ := hu; exact (Set.mem_Ioo.mp h6).1
    have h6abs : (0:ℝ) < |u 6| := by rw [abs_pos]; exact ne_of_gt h6pos
    -- combine to a single `ofReal` on each side, then real-rpow algebra
    rw [pow_one, ← ENNReal.ofReal_mul (le_of_lt h6abs),
      ← ENNReal.ofReal_mul (Real.rpow_nonneg (abs_nonneg (u 6)) _)]
    congr 1
    rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ (u 6)^2 * Uval231 u),
      show (u 6)^2 * Uval231 u = |u 6|^2 * Uval231 u by rw [sq_abs],
      Real.mul_rpow (by positivity) (le_of_lt hUpos),
      ← Real.rpow_natCast |u 6| 2, ← Real.rpow_mul (abs_nonneg _)]
    -- now `|u6| * (|u6|^(2·−c') * U^(−c')) = |u6|^(1−2c') * U^(−c')`
    rw [← mul_assoc, show |u 6| * |u 6| ^ (((2:ℕ):ℝ) * -c') = |u 6| ^ (1 - 2*c') by
      rw [show (1 - 2*c') = (1:ℝ) + ((2:ℕ):ℝ) * -c' by push_cast; ring,
        Real.rpow_add h6abs, Real.rpow_one]]
  rw [setLIntegral_congr_fun (measurableSet_subBox231 δ) (fun u hu => hrw u hu)]
  rw [subBox231_eq_pi]
  -- peel the z-axis (index 6)
  set ee := MeasurableEquiv.piFinSuccAbove (fun _ : Fin 9 => ℝ) 6 with hee
  have hmpS : MeasurePreserving ee.symm (volume : Measure (ℝ × (Fin 8 → ℝ))) volume := by
    have h := (volume_preserving_piFinSuccAbove (fun _ : Fin 9 => ℝ) 6).symm
    rwa [show (volume : Measure (ℝ × (Fin 8 → ℝ))) = (volume : Measure ℝ).prod volume from
      Measure.volume_eq_prod _ _] at h
  have hsymapp : ∀ x (y : Fin 8 → ℝ), ee.symm (x, y) = Fin.insertNth 6 x y :=
    fun x y => by rw [hee, MeasurableEquiv.piFinSuccAbove_symm_apply]; exact List.ofFn_inj.mp rfl
  set restSet : Set (Fin 8 → ℝ) := Set.univ.pi
    (fun k : Fin 8 => if (Fin.succAbove 6 k) = (0 : Fin 9) ∨ (Fin.succAbove 6 k) = (4 : Fin 9)
      then Set.Icc (δ/2) δ else Set.Icc (-(δ/8)) (δ/8)) with hrestSet
  have hpre : ee.symm ⁻¹' (Set.univ.pi (fun i : Fin 9 => if i = 6 then Set.Ioo (0:ℝ) δ
        else if i = 0 ∨ i = 4 then Set.Icc (δ/2) δ else Set.Icc (-(δ/8)) (δ/8)))
      = (Set.Ioo (0:ℝ) δ) ×ˢ restSet := by
    ext p; obtain ⟨x, y⟩ := p
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_prod, hsymapp,
      hrestSet]
    constructor
    · intro hall
      refine ⟨?_, fun k => ?_⟩
      · have := hall 6; rwa [Fin.insertNth_apply_same, if_pos rfl] at this
      · have := hall (Fin.succAbove 6 k); rw [Fin.insertNth_apply_succAbove] at this
        rwa [if_neg (Fin.succAbove_ne 6 k)] at this
    · rintro ⟨h0, hrest⟩ j
      rcases Fin.eq_self_or_eq_succAbove 6 j with rfl | ⟨k, rfl⟩
      · rwa [Fin.insertNth_apply_same, if_pos rfl]
      · rw [Fin.insertNth_apply_succAbove, if_neg (Fin.succAbove_ne 6 k)]; exact hrest k
  have htrans := hmpS.setLIntegral_comp_preimage_emb (MeasurableEquiv.measurableEmbedding _)
    (fun u : Fin 9 → ℝ => ENNReal.ofReal (|u 6| ^ (1 - 2*c')) * ENNReal.ofReal (Uval231 u ^ (-c')))
    (Set.univ.pi (fun i : Fin 9 => if i = 6 then Set.Ioo (0:ℝ) δ
        else if i = 0 ∨ i = 4 then Set.Icc (δ/2) δ else Set.Icc (-(δ/8)) (δ/8)))
  rw [hpre] at htrans
  rw [← htrans]
  -- factor the integrand under `ee.symm`: z-part `|x|^{1−2c'}`, rest-part `U(insertNth 6 x y)^{−c'}`
  have hfac : ∀ x (y : Fin 8 → ℝ),
      ENNReal.ofReal (|ee.symm (x, y) 6| ^ (1 - 2*c')) * ENNReal.ofReal (Uval231 (ee.symm (x, y)) ^ (-c'))
        = ENNReal.ofReal (|x| ^ (1 - 2*c'))
          * ENNReal.ofReal (Uval231 (Fin.insertNth 6 x y) ^ (-c')) := by
    intro x y
    have e6 : ee.symm (x, y) 6 = x := by rw [hsymapp, Fin.insertNth_apply_same]
    rw [e6, hsymapp]
  -- `U(insertNth 6 x y)` is independent of `x`
  simp_rw [hfac, Uval231_insertNth_6]
  rw [show (volume : Measure (ℝ × (Fin 8 → ℝ))) = (volume : Measure ℝ).prod volume from
    Measure.volume_eq_prod _ _]
  have hUmeas : Measurable (fun y : Fin 8 → ℝ => ENNReal.ofReal (Uval231 (Fin.insertNth 6 (0:ℝ) y) ^ (-c'))) := by
    have he : (fun y : Fin 8 → ℝ => ENNReal.ofReal (Uval231 (Fin.insertNth 6 (0:ℝ) y) ^ (-c')))
        = fun y => ENNReal.ofReal (((y 0 + y 1 * y 6) ^ 2 + (y 3 + y 4 * y 6) ^ 2) ^ (-c')) :=
      funext (fun y => by rw [Uval231_insertNth_6_eq])
    rw [he]; fun_prop
  rw [setLIntegral_prod _ (by
    apply Measurable.aemeasurable
    exact (by fun_prop : Measurable (fun p : ℝ × (Fin 8 → ℝ) =>
        ENNReal.ofReal (|p.1| ^ (1 - 2*c')))).mul (hUmeas.comp measurable_snd))]
  have hinner : ∀ x, (∫⁻ y in restSet, ENNReal.ofReal (|x| ^ (1 - 2*c'))
      * ENNReal.ofReal (Uval231 (Fin.insertNth 6 (0:ℝ) y) ^ (-c')) ∂(volume : Measure (Fin 8 → ℝ)))
      = ENNReal.ofReal (|x| ^ (1 - 2*c')) * (∫⁻ y in restSet,
        ENNReal.ofReal (Uval231 (Fin.insertNth 6 (0:ℝ) y) ^ (-c')) ∂(volume : Measure (Fin 8 → ℝ))) :=
    fun x => lintegral_const_mul _ hUmeas
  simp only [hinner]
  rw [lintegral_mul_const _ (by fun_prop : Measurable (fun x : ℝ => ENNReal.ofReal (|x| ^ (1 - 2*c'))))]
  -- z-factor over (0,δ) = ⊤ (exp 1−2c' ≤ −1), rest factor > 0
  rw [abs_rpow_lintegral_Ioo_eq_top _ δ hδ (by linarith)]
  refine ENNReal.top_mul (ne_of_gt ?_)
  -- the rest factor is positive: `U^{−c'} > 0` on the positive-measure rest box
  rw [hrestSet, setLIntegral_pos_iff hUmeas]
  have hbox : 0 < (volume : Measure (Fin 8 → ℝ)) (Set.univ.pi
      (fun k : Fin 8 => if (Fin.succAbove 6 k) = (0 : Fin 9) ∨ (Fin.succAbove 6 k) = (4 : Fin 9)
        then Set.Icc (δ/2) δ else Set.Icc (-(δ/8)) (δ/8))) := by
    rw [volume_pi_pi]
    refine CanonicallyOrderedAdd.prod_pos.mpr (fun k _ => ?_)
    by_cases hk : (Fin.succAbove 6 k) = (0 : Fin 9) ∨ (Fin.succAbove 6 k) = (4 : Fin 9)
    · rw [if_pos hk, Real.volume_Icc, ENNReal.ofReal_pos]; linarith
    · rw [if_neg hk, Real.volume_Icc, ENNReal.ofReal_pos]; linarith
  apply lt_of_lt_of_le hbox
  apply measure_mono
  intro y hy
  refine ⟨?_, hy⟩
  rw [Function.mem_support, ne_eq, ENNReal.ofReal_eq_zero, not_le]
  refine Real.rpow_pos_of_pos ?_ _
  -- `U(insertNth 6 0 y) > 0` since `insertNth 6 0 y ∈ subBox231 δ` shifted; use the U-pos bound
  -- on the reconstructed point (coords 0,4 in [δ/2,δ], others small)
  have hmem : Fin.insertNth 6 (δ/2) y ∈ subBox231 δ := by
    simp only [Set.mem_pi, Set.mem_univ, true_implies, hrestSet] at hy
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [show (0:Fin 9) = Fin.succAbove 6 0 from by decide, Fin.insertNth_apply_succAbove]
      have := hy 0; rwa [show (Fin.succAbove 6 (0:Fin 8) = (0:Fin 9)) from by decide,
        if_pos (Or.inl rfl)] at this
    · rw [show (1:Fin 9) = Fin.succAbove 6 1 from by decide, Fin.insertNth_apply_succAbove]
      have := hy 1; rwa [if_neg (by decide)] at this
    · rw [show (2:Fin 9) = Fin.succAbove 6 2 from by decide, Fin.insertNth_apply_succAbove]
      have := hy 2; rwa [if_neg (by decide)] at this
    · rw [show (3:Fin 9) = Fin.succAbove 6 3 from by decide, Fin.insertNth_apply_succAbove]
      have := hy 3; rwa [if_neg (by decide)] at this
    · rw [show (4:Fin 9) = Fin.succAbove 6 4 from by decide, Fin.insertNth_apply_succAbove]
      have := hy 4; rwa [show (Fin.succAbove 6 (4:Fin 8) = (4:Fin 9)) from by decide,
        if_pos (Or.inr rfl)] at this
    · rw [show (5:Fin 9) = Fin.succAbove 6 5 from by decide, Fin.insertNth_apply_succAbove]
      have := hy 5; rwa [if_neg (by decide)] at this
    · rw [Fin.insertNth_apply_same]; exact Set.mem_Ioo.mpr ⟨by linarith, by linarith⟩
    · rw [show (7:Fin 9) = Fin.succAbove 6 6 from by decide, Fin.insertNth_apply_succAbove]
      have := hy 6; rwa [if_neg (by decide)] at this
    · rw [show (8:Fin 9) = Fin.succAbove 6 7 from by decide, Fin.insertNth_apply_succAbove]
      have := hy 7; rwa [if_neg (by decide)] at this
  rw [show Uval231 (Fin.insertNth 6 (0:ℝ) y) = Uval231 (Fin.insertNth 6 (δ/2) y) from
    (Uval231_insertNth_6 0 y).trans (Uval231_insertNth_6 (δ/2) y).symm]
  exact subBox231_U_pos hδ hδ1 hmem

/-! ### The `(2,3,1)` smeared achiever box-divergence atom (route b, the radial-MP assembly) -/

/-- `cubeBox` is monotone in the radius. -/
theorem cubeBox_mono {N : ℕ} {a b : ℝ} (hab : a ≤ b) : cubeBox N a ⊆ cubeBox N b := by
  intro x hx i _
  have := hx i (Set.mem_univ i)
  rw [Set.mem_Icc] at this ⊢
  exact ⟨by linarith [this.1], by linarith [this.2]⟩

/-- **The `(2,3,1)` smeared box-divergence** — `∫⁻_{cubeBox 9 ε} |routeMCore M231|^{−c'} = ⊤` for `c'`
at-or-above `½·minAdm M231 = 1`, every `ε > 0`. The first `minAdm ≥ 2` boundary-SMEARED atom,
discharged via the reusable RADIAL-MP-final lemma `routeMCore_box_diverges_of_RadialMPChart` (route b):
`φ = ψ ∘ R`, `ψ = Q231 ∘ shear231` (MP + measurable embedding), `R = R231` (the radial blow-up, the
sole Jacobian carrier, `|det| = |u 6|¹`), fed the bounded-away weighted source `subBox231 δ`. -/
theorem routeM231sm_box_diverges (c' : NNReal) (hc' : (minAdm M231 : ℝ≥0∞) / 2 ≤ (c' : ℝ≥0∞))
    (ε : ℝ) (hε : 0 < ε) :
    ∫⁻ x in cubeBox (routeMAmbient M231) ε,
      ENNReal.ofReal (|routeMCore M231 x| ^ (-(c' : ℝ))) = ⊤ := by
  -- `1 ≤ c'` from `minAdm M231 = 2`
  have hc'1 : (1:ℝ) ≤ (c' : ℝ) := by
    have h : (minAdm M231 : ℝ≥0∞) / 2 = 1 := by
      rw [minAdm_M231, show ((2:ℕ):ℝ≥0∞) = 2 from by norm_num, ENNReal.div_self (by norm_num) (by norm_num)]
    rw [h] at hc'
    rwa [show (1:ℝ≥0∞) = ((1:NNReal):ℝ≥0∞) by norm_num, ENNReal.coe_le_coe, ← NNReal.coe_le_coe,
      NNReal.coe_one] at hc'
  set δ : ℝ := min (ε/2) 1 with hδdef
  have hδ : 0 < δ := lt_min (by linarith) (by norm_num)
  have hδ1 : δ ≤ 1 := min_le_right _ _
  have h2δε : 2 * δ ≤ ε := by
    have : δ ≤ ε/2 := min_le_left _ _; linarith
  refine routeMCore_box_diverges_of_RadialMPChart M231 psi231 R231 D231
    (⟨6, by decide⟩ : Fin (routeMAmbient M231)) 1
    measurePreserving_psi231 measurableEmbedding_psi231 (c' : ℝ) ε
    ⟨subBox231 δ, measurableSet_subBox231 δ, ?_, ?_, ?_, ?_, ?_⟩
  · -- containment: `subBox231 δ ⊆ (ψ∘R)⁻¹(cubeBox 9 ε)` (= `phi231sm⁻¹`)
    intro u hu
    rw [Set.mem_preimage, ← phi231sm_eq_psi_R]
    exact cubeBox_mono h2δε (subBox231_subset_preimage hδ hδ1 hu)
  · -- `R231` fderiv on `subBox231 δ`
    exact fun u _ => R231_hasFDerivWithinAt _ u
  · -- `R231` injective on `subBox231 δ` (`u6 ∈ (0,δ)` so `u6 ≠ 0`)
    have hsub : subBox231 δ ⊆ subBox231 δ \ {x | x 6 = 0} := by
      intro u hu
      refine ⟨hu, ?_⟩
      obtain ⟨_,_,_,_,_,_,h6,_,_⟩ := hu
      simp only [Set.mem_setOf_eq]; exact ne_of_gt (Set.mem_Ioo.mp h6).1
    exact (R231_injOn (subBox231 δ)).mono hsub
  · -- `|det (D231 u)| = |u 6|¹`
    exact fun u _ => D231_abs_det u
  · -- the weighted divergence `∫_S |u6|¹·(loss∘ψ∘R)^{−c'} = ⊤`
    have heq : ∀ u, routeMCore M231 (psi231 (R231 u)) = routeMCore M231 (phi231sm u) :=
      fun u => by rw [phi231sm_eq_psi_R]
    simp only [heq]
    exact subBox231_diverges hδ hδ1 hc'1

end DLNFibre.DLN.RLCT
