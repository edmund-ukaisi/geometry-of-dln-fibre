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

/-! ### Residual: the `(2,3,1)` rate + MP-factorization + weighted `hsrc` + atom (multi-pass)

LANDED (sorry-free): the chart `phi231sm` (radial × rational shear), and the load-bearing **shear
cancellation `P1_lam231`** (`P₁·Λ₀ = P₂` off `det P₁ ≠ 0`, via `(P₁ᵀP₁)⁻¹P₁ᵀ = P₁⁻¹` for invertible
square `P₁`) — the 2×2 analog of `(1,2,1)`'s scalar `b/a` cancellation, the conceptually-hard
algebraic
piece. The reusable `routeMCore_box_diverges_of_RadialMPChart` (the `minAdm ≥ 2` assembly) is banked
in `RouteM121Smeared`.

RESIDUAL (the bounded `(2,3,1)` finish, reusing `routeMCore_box_diverges_of_RadialMPChart`):
1. **Rate** `routeMCore_phi231sm_offpole = z²·U` off `det P₁ ≠ 0`: the product entry `(A⁰·A¹)(i,0) =
   z·(a_{i0}+a_{i1}·h1)` (the `sb`-shear cancels via `P1_lam231`); `U =
   (a00+a01·h1)²+(a10+a11·h1)²`.
   (Opaque-index plumbing: `i : Fin (M231 0)` vs `Fin 2` — the `lean/CLAUDE.md` `have`+`exact`
   kernel.)
2. **MP factorization `φ = ψ ∘ R`**: `R = pivotBlowupOn {z-slot, h1-slot} z` (radial, det `|z|¹`,
   polynomial); `ψ = Q231 ∘ shear231` (MP + measurable embedding) — the `(1,2,1)`
   `split121`/`shear121ME`
   pattern at `Fin 9` (a bigger `piFinSuccAbove` peel, same structure).
3. **Weighted `hsrc`**: `S = subBox231 δ` (bounded away from `det P₁ = 0`); `∫_S |z|¹·(z²U)^{−c} =
⊤`
   via the z-axis `abs_rpow_lintegral_Ioo_eq_top` at exp `minAdm−1−2c = 1−2c ≤ −1` (the radial
   Jacobian
   absorbed); containment `S ⊆ φ⁻¹(cubeBox)` via the flat-entry bound.
4. **The atom** `routeM231sm_box_diverges := routeMCore_box_diverges_of_RadialMPChart M231 ψ R …
hsrc`;
   `#print axioms` expect `[propext, Classical.choice, Quot.sound]` (S2-free, like `(1,2,1)`). -/

end DLNFibre.DLN.RLCT
