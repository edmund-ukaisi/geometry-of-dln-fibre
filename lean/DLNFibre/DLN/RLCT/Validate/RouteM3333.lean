import DLNFibre.DLN.RLCT.Validate.NodeAchieverChart
import DLNFibre.DLN.RLCT.Validate.RouteM4422
import DLNFibre.DLN.RLCT.Foundations.ParamsReshapeMP
import DLNFibre.Core.MeasureTheory.PolynomialZeroSet
import Mathlib.Algebra.MvPolynomial.Basic

/-!
# `RouteM3333` — the `(3,3,3,3)` achiever box-divergence (the DECISIVE multi-pivot LDU+chaining node)

The `(3,3,3,3)` instance of the achiever-path box-divergence atom
`routeMCore_box_diverges_achiever` (`RouteMLayerCoverGE.lean`), via the multi-pivot LDU-core +
unit-triangular `B/C`-chaining chart (the cert's `threads/26-r1-genM-chart/` §Uniform closed form, the
`(3,3,3,3)` witness). It is the decisive validation that the `NodeAchieverChart` bundle handles the
genuine multi-pivot case with NONZERO intermediate codims (descent `T* = (2,1,0)`, block codims
`1,2,3`), not just `(4,4,2,2)`'s pure radial blow-up.

## The construction (`M = (3,3,3,3)`; `minAdm = 6`, `flatDim = 27`)

`routeMCore M3333 = ‖A·B·C‖²` with `A, B, C : 3×3`. The chart is Codex's explicit nested-frame
(independently re-verified, `scripts/verify_codex_3333.py`):

    K = !![a, a·α; γ·a, γ·a·α + δ]   (the 2×2 LDU rank-1+residual core, det = a·δ),
    A = [[I₂];[λ]] · K · [I₂ | m] + u·E₂₂        (3×3, the deepest-factor frame + radial u),
    D = [[1];[ℓ]]·b·[1, n₁, n₂] + u·Y,  Y = !![0,0,0; 0,η₁,η₂],
    B = [[D − m·r];[r]]   (3×3, the middle factor, `(I₂|m)·B = D`),
    C = [[u·ζ − n₁·h₁ − n₂·h₂];[h₁];[h₂]]   (3×3, the leaf, `w·C = u·ζ`).

The telescoping `A·B·C = u·H` (EXACT polynomial identity) gives `F = ‖A·B·C‖² = u²·V`, with `V = ‖H‖²`
a polynomial (NOT a pure unit — the `(3,3,3,3)` shape), `V|_{u=0} = ‖H₀‖² ≠ 0` (the sector witness).

The 27 chart coords (slot map): `u 0 = u` (the radial pivot), `u 1..8 = a,α,γ,δ,λ₁,λ₂,m₁,m₂` (the A
frame), `u 9..14 = b,ℓ,n₁,n₂,η₁,η₂` (the B/D frame), `u 15..17 = r₀,r₁,r₂` (B's last row),
`u 18..23 = h₁,h₂` (C's lower rows), `u 24..26 = ζ` (C's top row).

`|det Dφ| = |u 0|⁵·|u 1|⁴·|u 4|²·|u 9|³` (the EXACT 27×27 det `u⁵·a⁴·δ²·b³`,
`scripts/verify_codex_3333.py`) — u-exp `5 = minAdm − 1` (the radial backbone), plus the multi-pivot
spectator monomial `a⁴·δ²·b³` on the `k = 0` axes (the LDU pivots, NOT lowering the threshold). Binding
axis `(k,h) = (1, 5) = (1, minAdm − 1)`, threshold `(5+1)/(2·1) = 3 = ½·minAdm`. The det ≠ 0 off
`{u 0 = 0}` (the degenerate-chart guard — u-exp 5, generically nonzero `a,δ,b`).
-/

open MeasureTheory
open scoped ENNReal BigOperators

namespace DLNFibre.DLN.RLCT

/-- `M3333 = (3,3,3,3)` (the decisive multi-pivot `L = 3` achiever node, nonzero intermediate codims). -/
abbrev M3333 : Fin 4 → ℕ := ![3, 3, 3, 3]

theorem minAdm_M3333 : minAdm M3333 = 6 := by
  rw [← minAdmRec_eq_minAdm]; decide

theorem flatDim_M3333 : flatDim M3333 = 27 := by decide

theorem routeMAmbient_M3333 : routeMAmbient M3333 = 27 := by decide

/-! ## The chart matrices (the LDU-core frame + the `B/C` chaining)

The three `3×3` layers `A, B, C`, transcribed from Codex's verified `(3,3,3,3)` frame (the slot map in
the module docstring). All entries are polynomials in the 27 coords. -/

/-- **The layer-`0` matrix `A`** (3×3): `[[I₂];[λ]]·K·[I₂|m] + u·E₂₂`, the deepest-factor frame with
the LDU core `K = !![a, a·α; γ·a, γ·a·α + δ]` and the radial `u` in slot `(2,2)`. Coords `x 0` (= `u`),
`x 1..8` (= `a,α,γ,δ,λ₁,λ₂,m₁,m₂`). -/
noncomputable def chartA3333 (x : Fin 27 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![x 1, x 1 * x 2, x 1 * x 2 * x 8 + x 1 * x 7;
     x 1 * x 3, x 1 * x 2 * x 3 + x 4, x 1 * x 3 * x 7 + x 8 * (x 1 * x 2 * x 3 + x 4);
     x 1 * x 3 * x 6 + x 1 * x 5, x 1 * x 2 * x 5 + x 6 * (x 1 * x 2 * x 3 + x 4),
       x 0 + x 7 * (x 1 * x 3 * x 6 + x 1 * x 5)
         + x 8 * (x 1 * x 2 * x 5 + x 6 * (x 1 * x 2 * x 3 + x 4))]

/-- **The layer-`1` matrix `B`** (3×3): `[[D − m·r];[r]]` with `D = [[1];[ℓ]]·b·[1,n₁,n₂] + u·Y`. Coords
`x 9..14` (= `b,ℓ,n₁,n₂,η₁,η₂`), `x 15..17` (= `r₀,r₁,r₂`), and `x 0, x 7, x 8` (= `u, m₁, m₂`). -/
noncomputable def chartB3333 (x : Fin 27 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![x 9 - x 15 * x 7, x 11 * x 9 - x 16 * x 7, x 12 * x 9 - x 17 * x 7;
     x 10 * x 9 - x 15 * x 8, x 0 * x 13 + x 10 * x 11 * x 9 - x 16 * x 8,
       x 0 * x 14 + x 10 * x 12 * x 9 - x 17 * x 8;
     x 15, x 16, x 17]

/-- **The layer-`2` matrix `C`** (3×3): `[[u·ζ − n₁·h₁ − n₂·h₂];[h₁];[h₂]]`, the leaf. Coords `x 18..23`
(= `h₁,h₂`), `x 24..26` (= `ζ`), and `x 0, x 11, x 12` (= `u, n₁, n₂`). -/
noncomputable def chartC3333 (x : Fin 27 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![x 0 * x 24 - x 11 * x 18 - x 12 * x 21, x 0 * x 25 - x 11 * x 19 - x 12 * x 22,
       x 0 * x 26 - x 11 * x 20 - x 12 * x 23;
     x 18, x 19, x 20;
     x 21, x 22, x 23]

/-- The genuine `Params M3333`, assembled by `Fin.cons` over the three layers `A, B, C`. -/
noncomputable def chartParams3333 (x : Fin 27 → ℝ) : Params M3333 :=
  Fin.cons (chartA3333 x)
    (Fin.cons (chartB3333 x)
      (Fin.cons (chartC3333 x) (fun i => i.elim0)))

/-! ## The telescoping `A·B·C = u·H` and the loss factorization `F = u²·V`

The chart's defining property: `A·B·C = (x 0)·H` (the radial pivot factors out — the cert's exact
telescoping). `Hval3333` is the explicit `H = (A·B·C)/(x 0)` matrix (each entry the deepest-level
product with one `u` stripped; verified `scripts/verify_codex_3333.py` that every `A·B·C` entry is
`u`-divisible). Then `F = ‖A·B·C‖² = (x 0)²·‖H‖² = (x 0)²·V`, with `V = Vval3333` a genuine polynomial
(NOT a pure unit — the multi-pivot shape). -/

/-- **The stripped product matrix `H = (A·B·C)/(x 0)`** (3×3): the deepest-level product entries with
one radial pivot `x 0` factored out. A polynomial in the 27 coords (the cert's telescoping `H`). -/
noncomputable def Hval3333 (x : Fin 27 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![(x 1) * (x 10) * (x 2) * (x 24) * (x 9) + (x 1) * (x 13) * (x 18) * (x 2)
       + (x 1) * (x 14) * (x 2) * (x 21) + (x 1) * (x 24) * (x 9),
     (x 1) * (x 10) * (x 2) * (x 25) * (x 9) + (x 1) * (x 13) * (x 19) * (x 2)
       + (x 1) * (x 14) * (x 2) * (x 22) + (x 1) * (x 25) * (x 9),
     (x 1) * (x 10) * (x 2) * (x 26) * (x 9) + (x 1) * (x 13) * (x 2) * (x 20)
       + (x 1) * (x 14) * (x 2) * (x 23) + (x 1) * (x 26) * (x 9);
     (x 1) * (x 10) * (x 2) * (x 24) * (x 3) * (x 9) + (x 1) * (x 13) * (x 18) * (x 2) * (x 3)
       + (x 1) * (x 14) * (x 2) * (x 21) * (x 3) + (x 1) * (x 24) * (x 3) * (x 9)
       + (x 10) * (x 24) * (x 4) * (x 9) + (x 13) * (x 18) * (x 4) + (x 14) * (x 21) * (x 4),
     (x 1) * (x 10) * (x 2) * (x 25) * (x 3) * (x 9) + (x 1) * (x 13) * (x 19) * (x 2) * (x 3)
       + (x 1) * (x 14) * (x 2) * (x 22) * (x 3) + (x 1) * (x 25) * (x 3) * (x 9)
       + (x 10) * (x 25) * (x 4) * (x 9) + (x 13) * (x 19) * (x 4) + (x 14) * (x 22) * (x 4),
     (x 1) * (x 10) * (x 2) * (x 26) * (x 3) * (x 9) + (x 1) * (x 13) * (x 2) * (x 20) * (x 3)
       + (x 1) * (x 14) * (x 2) * (x 23) * (x 3) + (x 1) * (x 26) * (x 3) * (x 9)
       + (x 10) * (x 26) * (x 4) * (x 9) + (x 13) * (x 20) * (x 4) + (x 14) * (x 23) * (x 4);
     (x 0) * (x 15) * (x 24) + (x 1) * (x 10) * (x 2) * (x 24) * (x 3) * (x 6) * (x 9)
       + (x 1) * (x 10) * (x 2) * (x 24) * (x 5) * (x 9) + (x 1) * (x 13) * (x 18) * (x 2) * (x 3) * (x 6)
       + (x 1) * (x 13) * (x 18) * (x 2) * (x 5) + (x 1) * (x 14) * (x 2) * (x 21) * (x 3) * (x 6)
       + (x 1) * (x 14) * (x 2) * (x 21) * (x 5) + (x 1) * (x 24) * (x 3) * (x 6) * (x 9)
       + (x 1) * (x 24) * (x 5) * (x 9) + (x 10) * (x 24) * (x 4) * (x 6) * (x 9)
       - (x 11) * (x 15) * (x 18) - (x 12) * (x 15) * (x 21) + (x 13) * (x 18) * (x 4) * (x 6)
       + (x 14) * (x 21) * (x 4) * (x 6) + (x 16) * (x 18) + (x 17) * (x 21),
     (x 0) * (x 15) * (x 25) + (x 1) * (x 10) * (x 2) * (x 25) * (x 3) * (x 6) * (x 9)
       + (x 1) * (x 10) * (x 2) * (x 25) * (x 5) * (x 9) + (x 1) * (x 13) * (x 19) * (x 2) * (x 3) * (x 6)
       + (x 1) * (x 13) * (x 19) * (x 2) * (x 5) + (x 1) * (x 14) * (x 2) * (x 22) * (x 3) * (x 6)
       + (x 1) * (x 14) * (x 2) * (x 22) * (x 5) + (x 1) * (x 25) * (x 3) * (x 6) * (x 9)
       + (x 1) * (x 25) * (x 5) * (x 9) + (x 10) * (x 25) * (x 4) * (x 6) * (x 9)
       - (x 11) * (x 15) * (x 19) - (x 12) * (x 15) * (x 22) + (x 13) * (x 19) * (x 4) * (x 6)
       + (x 14) * (x 22) * (x 4) * (x 6) + (x 16) * (x 19) + (x 17) * (x 22),
     (x 0) * (x 15) * (x 26) + (x 1) * (x 10) * (x 2) * (x 26) * (x 3) * (x 6) * (x 9)
       + (x 1) * (x 10) * (x 2) * (x 26) * (x 5) * (x 9) + (x 1) * (x 13) * (x 2) * (x 20) * (x 3) * (x 6)
       + (x 1) * (x 13) * (x 2) * (x 20) * (x 5) + (x 1) * (x 14) * (x 2) * (x 23) * (x 3) * (x 6)
       + (x 1) * (x 14) * (x 2) * (x 23) * (x 5) + (x 1) * (x 26) * (x 3) * (x 6) * (x 9)
       + (x 1) * (x 26) * (x 5) * (x 9) + (x 10) * (x 26) * (x 4) * (x 6) * (x 9)
       - (x 11) * (x 15) * (x 20) - (x 12) * (x 15) * (x 23) + (x 13) * (x 20) * (x 4) * (x 6)
       + (x 14) * (x 23) * (x 4) * (x 6) + (x 16) * (x 20) + (x 17) * (x 23)]

/-- **`Vval3333 = ‖H‖²`** (the `u`-free-leading unit factor of `F = (x 0)²·V`): a sum of the 9 squared
`H` entries. A polynomial in the 27 coords; `V|_{x 0 = 0} ≠ 0` (the sector witness, below). -/
noncomputable def Vval3333 (x : Fin 27 → ℝ) : ℝ :=
  ∑ i : Fin 3, ∑ j : Fin 3, (Hval3333 x i j) ^ 2

/-- **The product entry as the explicit three-matrix sum** (`rfl` after `prod_three_layer4422`): the
`L = 3` layer product `(prod)ᵢⱼ = ∑_{k1,k2} A(i,k1)·B(k1,k2)·C(k2,j)`. Used as a `simp` rewrite to
expand `dlnLoss` to literal-index matrix accessors (sidestepping the `fin_cases` Fin.mk friction). -/
theorem prod_chartParams3333_eq_sum (x : Fin 27 → ℝ) (i j : Fin 3) :
    prod M3333 (chartParams3333 x) i j
      = ∑ k1 : Fin 3, ∑ k2 : Fin 3,
          chartA3333 x i k1 * chartB3333 x k1 k2 * chartC3333 x k2 j := by
  rw [prod_three_layer4422 M3333 (chartParams3333 x)]; rfl

/-- The single-entry tactic: at a LITERAL index pair the product sum is expanded and the matrix
accessors reduce (the `cons_val` simp set fires on the `(· : Fin 3)`-ascribed numerals — unlike on
`fin_cases`-produced `Fin.mk`), so `ring` closes `prod ... i j = (x 0)·(H_ij)` in ~quadratic budget. -/
local macro "prove_entry3333" : tactic =>
  `(tactic| (rw [prod_chartParams3333_eq_sum]
             simp only [Fin.sum_univ_three, chartA3333, chartB3333, chartC3333, Hval3333,
               Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.of_apply,
               Matrix.cons_val, Matrix.head_fin_const, Matrix.cons_val']
             ring))

set_option maxHeartbeats 800000 in
theorem prod_chartParams3333_entry_00 (x : Fin 27 → ℝ) :
    prod M3333 (chartParams3333 x) (0 : Fin 3) (0 : Fin 3) = (x 0) * Hval3333 x 0 0 := by
  prove_entry3333
set_option maxHeartbeats 800000 in
theorem prod_chartParams3333_entry_01 (x : Fin 27 → ℝ) :
    prod M3333 (chartParams3333 x) (0 : Fin 3) (1 : Fin 3) = (x 0) * Hval3333 x 0 1 := by
  prove_entry3333
set_option maxHeartbeats 800000 in
theorem prod_chartParams3333_entry_02 (x : Fin 27 → ℝ) :
    prod M3333 (chartParams3333 x) (0 : Fin 3) (2 : Fin 3) = (x 0) * Hval3333 x 0 2 := by
  prove_entry3333
set_option maxHeartbeats 800000 in
theorem prod_chartParams3333_entry_10 (x : Fin 27 → ℝ) :
    prod M3333 (chartParams3333 x) (1 : Fin 3) (0 : Fin 3) = (x 0) * Hval3333 x 1 0 := by
  prove_entry3333
set_option maxHeartbeats 800000 in
theorem prod_chartParams3333_entry_11 (x : Fin 27 → ℝ) :
    prod M3333 (chartParams3333 x) (1 : Fin 3) (1 : Fin 3) = (x 0) * Hval3333 x 1 1 := by
  prove_entry3333
set_option maxHeartbeats 800000 in
theorem prod_chartParams3333_entry_12 (x : Fin 27 → ℝ) :
    prod M3333 (chartParams3333 x) (1 : Fin 3) (2 : Fin 3) = (x 0) * Hval3333 x 1 2 := by
  prove_entry3333
set_option maxHeartbeats 800000 in
theorem prod_chartParams3333_entry_20 (x : Fin 27 → ℝ) :
    prod M3333 (chartParams3333 x) (2 : Fin 3) (0 : Fin 3) = (x 0) * Hval3333 x 2 0 := by
  prove_entry3333
set_option maxHeartbeats 800000 in
theorem prod_chartParams3333_entry_21 (x : Fin 27 → ℝ) :
    prod M3333 (chartParams3333 x) (2 : Fin 3) (1 : Fin 3) = (x 0) * Hval3333 x 2 1 := by
  prove_entry3333
set_option maxHeartbeats 800000 in
theorem prod_chartParams3333_entry_22 (x : Fin 27 → ℝ) :
    prod M3333 (chartParams3333 x) (2 : Fin 3) (2 : Fin 3) = (x 0) * Hval3333 x 2 2 := by
  prove_entry3333

/-- **The per-entry pivot factorization** `prod ... i j = (x 0)·(H_ij)` (the telescoping
`A·B·C = (x 0)·H`), dispatched to the 9 literal-index entries via `fin_cases`. -/
theorem prod_chartParams3333_entry (x : Fin 27 → ℝ) (i j : Fin 3) :
    prod M3333 (chartParams3333 x) i j = (x 0) * Hval3333 x i j := by
  fin_cases i <;> fin_cases j
  · exact prod_chartParams3333_entry_00 x
  · exact prod_chartParams3333_entry_01 x
  · exact prod_chartParams3333_entry_02 x
  · exact prod_chartParams3333_entry_10 x
  · exact prod_chartParams3333_entry_11 x
  · exact prod_chartParams3333_entry_12 x
  · exact prod_chartParams3333_entry_20 x
  · exact prod_chartParams3333_entry_21 x
  · exact prod_chartParams3333_entry_22 x

/-- **The loss factorization (EXACT, sorry-free).** `dlnLoss M3333 0 (chartParams3333 x) = (x 0)²·V`
with `V = Vval3333 x`. Each product entry equals `(x 0)·(H entry)` (`prod_chartParams3333_entry`), so
`(entry)² = (x 0)²·(H entry)²` and the squared Frobenius norm is `(x 0)²·Vval3333`. The
soundness-critical `F = u²·V` identity for the multi-pivot node. -/
theorem dlnLoss_chartParams3333 (x : Fin 27 → ℝ) :
    dlnLoss M3333 0 (chartParams3333 x) = (x 0) ^ 2 * Vval3333 x := by
  unfold dlnLoss
  simp only [Matrix.sub_apply, Matrix.zero_apply, sub_zero]
  rw [Vval3333, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [prod_chartParams3333_entry]
  ring

/-- **The genuine achiever flat chart for `(3,3,3,3)`** `phi3333 := paramsEquivFlat M3333 ∘ chartParams3333`,
an `(Fin 27 → ℝ) → (Fin 27 → ℝ)` map (`routeMAmbient M3333 = 27`). -/
noncomputable def phi3333 (x : Fin 27 → ℝ) : Fin 27 → ℝ :=
  paramsEquivFlat M3333 (chartParams3333 x)

/-- **The `routeMCore` factorization (EXACT, sorry-free).** `routeMCore M3333 (phi3333 x) = (x 0)²·V`
(`V = Vval3333 x`): `routeMCore M = dlnLoss M 0 ∘ (paramsEquivFlat).symm`, `phi3333 = paramsEquivFlat ∘
chartParams3333`, the `symm`/`apply` cancel, leaving `dlnLoss M3333 0 (chartParams3333 x)` —
`dlnLoss_chartParams3333`. The soundness-critical `F ∘ phi = u²·V` identity (the multi-pivot shape: `V` a
genuine polynomial, NOT a pure unit). -/
theorem routeMCore_phi3333 (x : Fin 27 → ℝ) :
    routeMCore M3333 (phi3333 x) = (x 0) ^ 2 * Vval3333 x := by
  rw [routeMCore, phi3333, MeasurableEquiv.symm_apply_apply, dlnLoss_chartParams3333]

/-- **`Vval3333 ≥ 0`** (a sum of squares). -/
theorem Vval3333_nonneg (x : Fin 27 → ℝ) : (0 : ℝ) ≤ Vval3333 x := by
  rw [Vval3333]; positivity

/-- `Vval3333` is continuous (a polynomial in the chart coordinates), hence measurable. -/
theorem continuous_Vval3333 : Continuous Vval3333 := by
  unfold Vval3333 Hval3333
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.of_apply, Matrix.cons_val, Matrix.head_fin_const, Matrix.cons_val']
  fun_prop

/-! ## The `V > 0` a.e. positivity (the genuine-polynomial null-zero-set route)

`Vval3333` is a genuine polynomial (NOT a pure unit — the multi-pivot shape), so there is no clean
single-coordinate bound. Instead `V = eval x VPoly3333` for a nonzero `MvPolynomial`, so `{V = 0}` is
Lebesgue-null (`MvPolynomial.ae_eval_ne_zero`, the Core brick `Core.MeasureTheory.PolynomialZeroSet`),
exactly as `(4,4,2,2)`'s `Uval4422_ae_pos`. -/

set_option maxHeartbeats 1600000 in
open MvPolynomial in
/-- The formal `H` matrix over `MvPolynomial (Fin 27) ℝ` (`Hval3333` with `X k` for coord `k`). Every
entry is a sum of monomials in the `X`-variables. -/
noncomputable def HPoly3333 : Matrix (Fin 3) (Fin 3) (MvPolynomial (Fin 27) ℝ) :=
  !![(X 1) * (X 10) * (X 2) * (X 24) * (X 9) + (X 1) * (X 13) * (X 18) * (X 2)
       + (X 1) * (X 14) * (X 2) * (X 21) + (X 1) * (X 24) * (X 9),
     (X 1) * (X 10) * (X 2) * (X 25) * (X 9) + (X 1) * (X 13) * (X 19) * (X 2)
       + (X 1) * (X 14) * (X 2) * (X 22) + (X 1) * (X 25) * (X 9),
     (X 1) * (X 10) * (X 2) * (X 26) * (X 9) + (X 1) * (X 13) * (X 2) * (X 20)
       + (X 1) * (X 14) * (X 2) * (X 23) + (X 1) * (X 26) * (X 9);
     (X 1) * (X 10) * (X 2) * (X 24) * (X 3) * (X 9) + (X 1) * (X 13) * (X 18) * (X 2) * (X 3)
       + (X 1) * (X 14) * (X 2) * (X 21) * (X 3) + (X 1) * (X 24) * (X 3) * (X 9)
       + (X 10) * (X 24) * (X 4) * (X 9) + (X 13) * (X 18) * (X 4) + (X 14) * (X 21) * (X 4),
     (X 1) * (X 10) * (X 2) * (X 25) * (X 3) * (X 9) + (X 1) * (X 13) * (X 19) * (X 2) * (X 3)
       + (X 1) * (X 14) * (X 2) * (X 22) * (X 3) + (X 1) * (X 25) * (X 3) * (X 9)
       + (X 10) * (X 25) * (X 4) * (X 9) + (X 13) * (X 19) * (X 4) + (X 14) * (X 22) * (X 4),
     (X 1) * (X 10) * (X 2) * (X 26) * (X 3) * (X 9) + (X 1) * (X 13) * (X 2) * (X 20) * (X 3)
       + (X 1) * (X 14) * (X 2) * (X 23) * (X 3) + (X 1) * (X 26) * (X 3) * (X 9)
       + (X 10) * (X 26) * (X 4) * (X 9) + (X 13) * (X 20) * (X 4) + (X 14) * (X 23) * (X 4);
     (X 0) * (X 15) * (X 24) + (X 1) * (X 10) * (X 2) * (X 24) * (X 3) * (X 6) * (X 9)
       + (X 1) * (X 10) * (X 2) * (X 24) * (X 5) * (X 9) + (X 1) * (X 13) * (X 18) * (X 2) * (X 3) * (X 6)
       + (X 1) * (X 13) * (X 18) * (X 2) * (X 5) + (X 1) * (X 14) * (X 2) * (X 21) * (X 3) * (X 6)
       + (X 1) * (X 14) * (X 2) * (X 21) * (X 5) + (X 1) * (X 24) * (X 3) * (X 6) * (X 9)
       + (X 1) * (X 24) * (X 5) * (X 9) + (X 10) * (X 24) * (X 4) * (X 6) * (X 9)
       - (X 11) * (X 15) * (X 18) - (X 12) * (X 15) * (X 21) + (X 13) * (X 18) * (X 4) * (X 6)
       + (X 14) * (X 21) * (X 4) * (X 6) + (X 16) * (X 18) + (X 17) * (X 21),
     (X 0) * (X 15) * (X 25) + (X 1) * (X 10) * (X 2) * (X 25) * (X 3) * (X 6) * (X 9)
       + (X 1) * (X 10) * (X 2) * (X 25) * (X 5) * (X 9) + (X 1) * (X 13) * (X 19) * (X 2) * (X 3) * (X 6)
       + (X 1) * (X 13) * (X 19) * (X 2) * (X 5) + (X 1) * (X 14) * (X 2) * (X 22) * (X 3) * (X 6)
       + (X 1) * (X 14) * (X 2) * (X 22) * (X 5) + (X 1) * (X 25) * (X 3) * (X 6) * (X 9)
       + (X 1) * (X 25) * (X 5) * (X 9) + (X 10) * (X 25) * (X 4) * (X 6) * (X 9)
       - (X 11) * (X 15) * (X 19) - (X 12) * (X 15) * (X 22) + (X 13) * (X 19) * (X 4) * (X 6)
       + (X 14) * (X 22) * (X 4) * (X 6) + (X 16) * (X 19) + (X 17) * (X 22),
     (X 0) * (X 15) * (X 26) + (X 1) * (X 10) * (X 2) * (X 26) * (X 3) * (X 6) * (X 9)
       + (X 1) * (X 10) * (X 2) * (X 26) * (X 5) * (X 9) + (X 1) * (X 13) * (X 2) * (X 20) * (X 3) * (X 6)
       + (X 1) * (X 13) * (X 2) * (X 20) * (X 5) + (X 1) * (X 14) * (X 2) * (X 23) * (X 3) * (X 6)
       + (X 1) * (X 14) * (X 2) * (X 23) * (X 5) + (X 1) * (X 26) * (X 3) * (X 6) * (X 9)
       + (X 1) * (X 26) * (X 5) * (X 9) + (X 10) * (X 26) * (X 4) * (X 6) * (X 9)
       - (X 11) * (X 15) * (X 20) - (X 12) * (X 15) * (X 23) + (X 13) * (X 20) * (X 4) * (X 6)
       + (X 14) * (X 23) * (X 4) * (X 6) + (X 16) * (X 20) + (X 17) * (X 23)]

open MvPolynomial in
/-- The formal polynomial `VPoly3333 : MvPolynomial (Fin 27) ℝ` (`= ‖HPoly‖²`), with
`eval x VPoly3333 = Vval3333 x`. -/
noncomputable def VPoly3333 : MvPolynomial (Fin 27) ℝ :=
  ∑ i : Fin 3, ∑ j : Fin 3, (HPoly3333 i j) ^ 2

set_option maxHeartbeats 1600000 in
open MvPolynomial in
/-- `eval x VPoly3333 = Vval3333 x` — the encoding identity (`eval` is a ring hom: distributes over the
sums / products / squares; each `eval x (X k) = x k`, and the matrix accessors match entrywise). -/
theorem eval_VPoly3333 (x : Fin 27 → ℝ) : MvPolynomial.eval x VPoly3333 = Vval3333 x := by
  rw [VPoly3333, Vval3333, HPoly3333, Hval3333]
  simp only [map_sum, map_pow, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.of_apply, Matrix.cons_val, Matrix.head_fin_const, Matrix.cons_val',
    map_add, map_sub, map_mul, MvPolynomial.eval_X]

open MvPolynomial in
/-- **`VPoly3333 ≠ 0`** — the witness `x 1 = x 9 = x 24 = 1` (a = b = ζ₀ = 1, else 0): then
`Hval3333 (0,0) = a·ζ₀·b = 1`, so `Vval3333 = 1 ≠ 0` (the cert's sector slice). Hence the formal
polynomial is nonzero. -/
theorem VPoly3333_ne_zero : VPoly3333 ≠ 0 := by
  intro h0
  set w : Fin 27 → ℝ := Pi.single 1 1 + Pi.single 9 1 + Pi.single 24 1 with hw
  have hval : Vval3333 w = 1 := by
    rw [Vval3333, Hval3333]
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.of_apply, Matrix.cons_val, Matrix.head_fin_const, Matrix.cons_val']
    simp only [hw, Pi.add_apply, Pi.single_apply, Fin.reduceEq, if_true, if_false]
    norm_num
  have : MvPolynomial.eval w VPoly3333 = 1 := by rw [eval_VPoly3333]; exact hval
  rw [h0] at this; simp at this

/-- **`Vval3333 > 0` a.e.** (the soundness-critical positivity). `Vval3333 = eval · VPoly3333` with
`VPoly3333 ≠ 0`, so `{Vval3333 = 0}` is Lebesgue-null (`MvPolynomial.ae_eval_ne_zero`); off that null
set `V ≥ 0` is `> 0`. -/
theorem Vval3333_ae_pos : ∀ᵐ x : Fin 27 → ℝ, 0 < Vval3333 x := by
  have hae := MvPolynomial.ae_eval_ne_zero VPoly3333 VPoly3333_ne_zero
  filter_upwards [hae] with x hx
  rw [eval_VPoly3333] at hx
  exact lt_of_le_of_ne (Vval3333_nonneg x) (Ne.symm hx)

/-- `Vval3333` is bounded above on the source box `[0,δ]²⁷` (continuous on a compact box). -/
theorem Vval3333_le_on_box (δ : ℝ) :
    ∃ B, 0 < B ∧ ∀ x ∈ Set.univ.pi (fun _ : Fin 27 => Set.Icc (0 : ℝ) δ), Vval3333 x ≤ B := by
  have hcpt : IsCompact (Set.univ.pi (fun _ : Fin 27 => Set.Icc (0 : ℝ) δ)) :=
    isCompact_univ_pi (fun _ => isCompact_Icc)
  rcases (Set.univ.pi (fun _ : Fin 27 => Set.Icc (0 : ℝ) δ)).eq_empty_or_nonempty with he | hne
  · exact ⟨1, one_pos, fun x hx => absurd (he ▸ hx) (Set.mem_empty_iff_false x).mp⟩
  · obtain ⟨x0, _, hx0⟩ := hcpt.exists_isMaxOn hne continuous_Vval3333.continuousOn
    exact ⟨max 1 (Vval3333 x0), lt_of_lt_of_le one_pos (le_max_left _ _),
      fun x hx => le_trans (hx0 hx) (le_max_right _ _)⟩

/-! ## The multi-pivot binding monomial (the `(3,3,3,3)` leaf, LDU+chaining Jacobian)

The post-chart leaf integrand is `|det Dφ|·|F∘φ|^{−c'} = (|u 0|⁵·|u 1|⁴·|u 4|²·|u 9|³)·(u 0²·V)^{−c'}`
— `monomialIntegrand 27 k h` with `k₀ = 1` (the loss base `|u 0|²`), `h = (5,4,…,2,…,3,…)` on the four
pivot axes (`u 0` the radial blow-up `minAdm−1 = 5`; `u 1 = a`, `u 4 = δ`, `u 9 = b` the LDU/chaining
pivots), `0` on the 23 spectator axes. Binding axis `(k,h) = (1, 5) = (1, minAdm−1)`, threshold
`(5+1)/(2·1) = 3 = ½·minAdm`; the `a⁴·δ²·b³` pivots are `k = 0` spectators (`axisRatio = ⊤`), NOT
lowering the threshold. -/

/-- The `(3,3,3,3)` leaf Jacobian exponents on `Fin 27`: `5` on the binding pivot axis `0` (the radial
blow-up `minAdm−1`); the LDU/chaining spectator monomial `4` on `u 1` (= `a`), `2` on `u 4` (= `δ`), `3`
on `u 9` (= `b`); `0` on the other 23 axes. The exact 27×27 det exponents `u⁵·a⁴·δ²·b³`. -/
def leafH3333 : Fin 27 → ℕ := fun j => if j = 0 then 5 else if j = 1 then 4 else
  if j = 4 then 2 else if j = 9 then 3 else 0

/-- `leafH3333 0 = 5 = minAdm M3333 − 1` (the binding axis carries the radial exponent). -/
theorem leafH3333_pivot : leafH3333 (0 : Fin 27) = minAdm M3333 - 1 := by
  rw [minAdm_M3333]; rfl

/-- **The Jacobian weight `∏_j |u_j|^{leafH3333 j} = |u 0|⁵·|u 1|⁴·|u 4|²·|u 9|³`** — the genuine
`|det Dφ|` exponent monomial: the radial pivot `u 0` to `5 = minAdm−1`, the LDU/chaining pivots
`u 1, u 4, u 9` (= `a, δ, b`) to `4, 2, 3`; the 23 spectator axes contribute `|·|⁰ = 1`. -/
theorem leafH3333_prod_eq (u : Fin 27 → ℝ) :
    (∏ j, |u j| ^ (leafH3333 j)) = |u 0| ^ 5 * |u 1| ^ 4 * |u 4| ^ 2 * |u 9| ^ 3 := by
  have hsub : ({0, 1, 4, 9} : Finset (Fin 27)) ⊆ Finset.univ := Finset.subset_univ _
  rw [← Finset.prod_subset hsub (fun j _ hj => ?_)]
  · rw [show ({0, 1, 4, 9} : Finset (Fin 27)) = {0, 1, 4, 9} from rfl]
    rw [Finset.prod_insert (by decide), Finset.prod_insert (by decide),
        Finset.prod_insert (by decide), Finset.prod_singleton]
    simp only [leafH3333, Fin.reduceEq, if_false, if_true]
    ring
  · -- off `{0,1,4,9}`: `leafH3333 j = 0`, so `|u j|^0 = 1`
    have h0 : j ≠ 0 := by rintro rfl; exact hj (by decide)
    have h1 : j ≠ 1 := by rintro rfl; exact hj (by decide)
    have h4 : j ≠ 4 := by rintro rfl; exact hj (by decide)
    have h9 : j ≠ 9 := by rintro rfl; exact hj (by decide)
    simp [leafH3333, h0, h1, h4, h9]

/-- **Single-pivot loss-base evaluation.** `∏_j |u j|^{2·(nodeLeafK 27 0) j} = |u 0|²` (the binding axis
`0` carries `k = 1`; the 26 other axes `k = 0`). -/
theorem nodeLeafK3333_loss_eq (u : Fin 27 → ℝ) :
    (∏ j, |u j| ^ (2 * (nodeLeafK 27 0) j)) = |u 0| ^ 2 := by
  rw [Finset.prod_eq_single (0 : Fin 27)]
  · simp [nodeLeafK]
  · intro j _ hj; simp [nodeLeafK, hj]
  · intro h; exact absurd (Finset.mem_univ (0 : Fin 27)) h

/-- **Monomial evaluation.** `monomialIntegrand 27 (nodeLeafK 27 0) leafH3333 c u =
(|u 0|⁵·|u 1|⁴·|u 4|²·|u 9|³)·(|u 0|²)^{−c}` — the loss base `|u 0|²` (`k = 1` at axis `0`) against the
multi-pivot Jacobian monomial. -/
theorem monomialIntegrand_leaf3333_eq (c : ℝ) (u : Fin 27 → ℝ) :
    monomialIntegrand 27 (nodeLeafK 27 0) leafH3333 c u
      = (|u 0| ^ 5 * |u 1| ^ 4 * |u 4| ^ 2 * |u 9| ^ 3) * (|u 0| ^ 2) ^ (-c) := by
  unfold monomialIntegrand
  rw [leafH3333_prod_eq, nodeLeafK3333_loss_eq]

/-- **The leaf-integrand identity for the `(3,3,3,3)` achiever chart**: `(∏_j |u_j|^{leafH3333 j}) ·
|routeMCore M3333 (phi3333 u)|^{−c} = monomialIntegrand · (Vval3333 u)^{−c}` — the multi-pivot Jacobian
monomial against the unit power, via `routeMCore_phi3333` (`F∘phi = u₀²·V`) +
`monomialIntegrand_leaf3333_eq`. The `(4,4,2,2)` `leaf_integrand4422` analog (multi-pivot). -/
theorem leaf_integrand3333 (c : ℝ) (u : Fin 27 → ℝ) :
    (∏ j, |u j| ^ (leafH3333 j)) * |routeMCore M3333 (phi3333 u)| ^ (-c)
      = monomialIntegrand 27 (nodeLeafK 27 0) leafH3333 c u * (Vval3333 u) ^ (-c) := by
  rw [monomialIntegrand_leaf3333_eq, leafH3333_prod_eq, routeMCore_phi3333]
  have hVnn : (0 : ℝ) ≤ Vval3333 u := Vval3333_nonneg u
  rw [abs_of_nonneg (mul_nonneg (sq_nonneg _) hVnn),
    Real.mul_rpow (sq_nonneg _) hVnn, ← sq_abs (u 0)]
  ring

/-! ## Continuity, the deepest point, and image containment -/

/-- `chartParams3333` is continuous (each layer matrix is a polynomial; `Params` a product). -/
theorem continuous_chartParams3333 : Continuous chartParams3333 := by
  apply continuous_pi
  intro s
  fin_cases s
  · show Continuous chartA3333
    unfold chartA3333
    refine Continuous.matrixVecCons ?_ (Continuous.matrixVecCons ?_ (Continuous.matrixVecCons ?_
      continuous_const))
    all_goals
      refine Continuous.matrixVecCons ?_ (Continuous.matrixVecCons ?_ (Continuous.matrixVecCons ?_
        continuous_const)) <;> fun_prop
  · show Continuous chartB3333
    unfold chartB3333
    refine Continuous.matrixVecCons ?_ (Continuous.matrixVecCons ?_ (Continuous.matrixVecCons ?_
      continuous_const))
    all_goals
      refine Continuous.matrixVecCons ?_ (Continuous.matrixVecCons ?_ (Continuous.matrixVecCons ?_
        continuous_const)) <;> fun_prop
  · show Continuous chartC3333
    unfold chartC3333
    refine Continuous.matrixVecCons ?_ (Continuous.matrixVecCons ?_ (Continuous.matrixVecCons ?_
      continuous_const))
    all_goals
      refine Continuous.matrixVecCons ?_ (Continuous.matrixVecCons ?_ (Continuous.matrixVecCons ?_
        continuous_const)) <;> fun_prop

/-- **`phi3333` is continuous**. -/
theorem continuous_phi3333 : Continuous phi3333 :=
  (continuous_paramsEquivFlat _).comp continuous_chartParams3333

/-- **`phi3333 0 = 0`** — the chart reaches the deepest point (every entry is a monomial in the coords,
vanishing at `u = 0`). -/
theorem phi3333_zero : phi3333 (0 : Fin 27 → ℝ) = 0 := by
  have hchart : chartParams3333 (0 : Fin 27 → ℝ) = (fun _ => 0 : Params M3333) := by
    funext s
    fin_cases s
    · show chartA3333 (0 : Fin 27 → ℝ) = 0
      funext i j; fin_cases i <;> fin_cases j <;> simp [chartA3333]
    · show chartB3333 (0 : Fin 27 → ℝ) = 0
      funext i j; fin_cases i <;> fin_cases j <;> simp [chartB3333]
    · show chartC3333 (0 : Fin 27 → ℝ) = 0
      funext i j; fin_cases i <;> fin_cases j <;> simp [chartC3333]
  rw [phi3333, hchart]
  exact paramsEquivFlat_deepest _

/-- **Image containment**: a small source box `[0,δ]²⁷` maps into `cubeBox 27 ε` (continuity of
`phi3333` + `phi3333 0 = 0`, exactly as `phi4422_image_subset_cubeBox`). -/
theorem phi3333_image_subset_cubeBox (ε : ℝ) (hε : 0 < ε) :
    ∃ δ > 0, phi3333 '' (Set.univ.pi (fun _ : Fin 27 => Set.Icc (0 : ℝ) δ)) ⊆ cubeBox 27 ε := by
  have hopen : IsOpen (Set.univ.pi (fun _ : Fin 27 => Set.Ioo (-ε) ε)) :=
    isOpen_set_pi Set.finite_univ (fun _ _ => isOpen_Ioo)
  have hmem : (0 : Fin 27 → ℝ) ∈ phi3333 ⁻¹' (Set.univ.pi (fun _ : Fin 27 => Set.Ioo (-ε) ε)) := by
    simp only [Set.mem_preimage, phi3333_zero, Set.mem_pi, Set.mem_univ, true_implies,
      Set.mem_Ioo, Pi.zero_apply]
    exact fun i => ⟨by linarith, hε⟩
  obtain ⟨δ, hδ, hsub⟩ := cubeBox_subset_of_isOpen (hopen.preimage continuous_phi3333) hmem
  refine ⟨δ, hδ, ?_⟩
  rintro y ⟨x, hx, rfl⟩
  have hxcube : x ∈ cubeBox 27 δ := by
    simp only [cubeBox, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Icc] at hx ⊢
    intro i; exact ⟨le_trans (by linarith [hδ]) (hx i).1, (hx i).2⟩
  have hxmem : phi3333 x ∈ Set.univ.pi (fun _ : Fin 27 => Set.Ioo (-ε) ε) :=
    Set.mem_preimage.mp (hsub hxcube)
  refine Set.mem_pi.mpr (fun i _ => ?_)
  have hi := (Set.mem_pi.mp hxmem) i (Set.mem_univ i)
  rw [Set.mem_Ioo] at hi
  rw [Set.mem_Icc]
  exact ⟨hi.1.le, hi.2.le⟩

/-! ## The flat structural map `T3333` + the reshape `pack3333` (the c-o-v factorization)

`phi3333 = paramsEquivFlat ∘ chartParams3333 = paramsEquivFlat ∘ pack3333 ∘ T3333 = Q3333 ∘ T3333`,
where `T3333 : (Fin 27 → ℝ) → (Fin 27 → ℝ)` is the chart in flat coordinates (each output coord is one
chart matrix entry, in the ROW-MAJOR `A,B,C` slot order: coords `0..8 ↦ A`, `9..17 ↦ B`, `18..26 ↦ C`),
`pack3333` reshapes the 27 flat coords into the matrix slots, and `Q3333 = paramsEquivFlat ∘ pack3333` is
a measure-preserving coordinate permutation (`|det| = 1`). The genuine chart Jacobian is
`|det Dφ3333| = |det Q3333|·|det DT3333| = 1·(|x 0|⁵·|x 1|⁴·|x 4|²·|x 9|³)`. -/

/-- **`pack3333`** — the row-major reshape `(Fin 27 → ℝ) → Params M3333`: coords `9s+3i+j ↦` slot
`(s,i,j)`, matching the `chartA3333/B3333/C3333` row-major layout. Linear (each output is one coord). -/
noncomputable def pack3333 (w : Fin 27 → ℝ) : Params M3333 :=
  Fin.cons
    (!![w 0, w 1, w 2; w 3, w 4, w 5; w 6, w 7, w 8] : Matrix (Fin 3) (Fin 3) ℝ)
    (Fin.cons
      (!![w 9, w 10, w 11; w 12, w 13, w 14; w 15, w 16, w 17] : Matrix (Fin 3) (Fin 3) ℝ)
      (Fin.cons
        (!![w 18, w 19, w 20; w 21, w 22, w 23; w 24, w 25, w 26] : Matrix (Fin 3) (Fin 3) ℝ)
        (fun i => i.elim0)))

/-- **The flat structural map `T3333`** — the chart in flat coords (`chartParams3333 = pack3333 ∘ T3333`):
each output coord is one chart matrix entry, row-major `A` (coords `0..8`), `B` (`9..17`), `C` (`18..26`).
The exact transcription of `chartA3333/B3333/C3333` into the 27 flat slots. -/
noncomputable def T3333 (x : Fin 27 → ℝ) : Fin 27 → ℝ :=
  ![x 1, x 1 * x 2, x 1 * x 2 * x 8 + x 1 * x 7,
    x 1 * x 3, x 1 * x 2 * x 3 + x 4, x 1 * x 3 * x 7 + x 8 * (x 1 * x 2 * x 3 + x 4),
    x 1 * x 3 * x 6 + x 1 * x 5, x 1 * x 2 * x 5 + x 6 * (x 1 * x 2 * x 3 + x 4),
      x 0 + x 7 * (x 1 * x 3 * x 6 + x 1 * x 5)
        + x 8 * (x 1 * x 2 * x 5 + x 6 * (x 1 * x 2 * x 3 + x 4)),
    x 9 - x 15 * x 7, x 11 * x 9 - x 16 * x 7, x 12 * x 9 - x 17 * x 7,
    x 10 * x 9 - x 15 * x 8, x 0 * x 13 + x 10 * x 11 * x 9 - x 16 * x 8,
      x 0 * x 14 + x 10 * x 12 * x 9 - x 17 * x 8,
    x 15, x 16, x 17,
    x 0 * x 24 - x 11 * x 18 - x 12 * x 21, x 0 * x 25 - x 11 * x 19 - x 12 * x 22,
      x 0 * x 26 - x 11 * x 20 - x 12 * x 23,
    x 18, x 19, x 20, x 21, x 22, x 23]

/-- **The factorization identity** `chartParams3333 = pack3333 ∘ T3333` (per-layer `funext` + `fin_cases`
on the 27 entries). -/
theorem chartParams3333_eq_pack_T (x : Fin 27 → ℝ) :
    chartParams3333 x = pack3333 (T3333 x) := by
  funext s
  fin_cases s
  · show chartA3333 x = (pack3333 (T3333 x)) 0
    have hp : (pack3333 (T3333 x)) 0
        = (!![(T3333 x) 0, (T3333 x) 1, (T3333 x) 2; (T3333 x) 3, (T3333 x) 4, (T3333 x) 5;
            (T3333 x) 6, (T3333 x) 7, (T3333 x) 8] : Matrix (Fin 3) (Fin 3) ℝ) := rfl
    rw [hp]
    funext i j
    fin_cases i <;> fin_cases j <;> simp [chartA3333, T3333]
  · show chartB3333 x = (pack3333 (T3333 x)) 1
    have hp : (pack3333 (T3333 x)) 1
        = (!![(T3333 x) 9, (T3333 x) 10, (T3333 x) 11; (T3333 x) 12, (T3333 x) 13, (T3333 x) 14;
            (T3333 x) 15, (T3333 x) 16, (T3333 x) 17] : Matrix (Fin 3) (Fin 3) ℝ) := rfl
    rw [hp]
    funext i j
    fin_cases i <;> fin_cases j <;> simp [chartB3333, T3333]
  · show chartC3333 x = (pack3333 (T3333 x)) 2
    have hp : (pack3333 (T3333 x)) 2
        = (!![(T3333 x) 18, (T3333 x) 19, (T3333 x) 20; (T3333 x) 21, (T3333 x) 22, (T3333 x) 23;
            (T3333 x) 24, (T3333 x) 25, (T3333 x) 26] : Matrix (Fin 3) (Fin 3) ℝ) := rfl
    rw [hp]
    funext i j
    fin_cases i <;> fin_cases j <;> simp [chartC3333, T3333]

/-- `pack3333` as a continuous ℝ-linear map (each output matrix entry is one input coordinate). -/
noncomputable def pack3333CLM : (Fin 27 → ℝ) →L[ℝ] Params M3333 :=
  ContinuousLinearMap.pi (fun s =>
    match s with
    | ⟨0, _⟩ => ContinuousLinearMap.pi (fun i => ContinuousLinearMap.pi (fun j =>
        ContinuousLinearMap.proj
          (![![0, 1, 2], ![3, 4, 5], ![6, 7, 8]] i j : Fin 27)))
    | ⟨1, _⟩ => ContinuousLinearMap.pi (fun i => ContinuousLinearMap.pi (fun j =>
        ContinuousLinearMap.proj
          (![![9, 10, 11], ![12, 13, 14], ![15, 16, 17]] i j : Fin 27)))
    | ⟨2, _⟩ => ContinuousLinearMap.pi (fun i => ContinuousLinearMap.pi (fun j =>
        ContinuousLinearMap.proj
          (![![18, 19, 20], ![21, 22, 23], ![24, 25, 26]] i j : Fin 27)))
    | ⟨n + 3, h⟩ => absurd h (by omega))

/-- `pack3333CLM` has underlying function `pack3333`. -/
theorem pack3333CLM_coe : ⇑pack3333CLM = pack3333 := by
  funext w s
  fin_cases s
  · funext i j; fin_cases i <;> fin_cases j <;> rfl
  · funext i j; fin_cases i <;> fin_cases j <;> rfl
  · funext i j; fin_cases i <;> fin_cases j <;> rfl

/-- **The outer-reindex CLM** `Q3333CLM = paramsEquivFlatCLE ∘ pack3333CLM`. -/
noncomputable def Q3333CLM : (Fin 27 → ℝ) →L[ℝ] (Fin 27 → ℝ) :=
  (paramsEquivFlatCLE M3333).toContinuousLinearMap.comp pack3333CLM

/-- The explicit slot bijection `Fin 27 ≃ FlatIdx M3333` pinning `pack3333`'s row-major flat-coord →
matrix-slot order (`k = 9s+3i+j ↦ ⟨⟨s,i⟩,j⟩`). The inverses are `decide` (kernel). -/
noncomputable def fin27EquivFlatIdx3333 : Fin 27 ≃ FlatIdx M3333 where
  toFun := fun k =>
    match k with
    | ⟨0,_⟩ => ⟨⟨⟨0,by decide⟩,⟨0,by decide⟩⟩,⟨0,by decide⟩⟩
    | ⟨1,_⟩ => ⟨⟨⟨0,by decide⟩,⟨0,by decide⟩⟩,⟨1,by decide⟩⟩
    | ⟨2,_⟩ => ⟨⟨⟨0,by decide⟩,⟨0,by decide⟩⟩,⟨2,by decide⟩⟩
    | ⟨3,_⟩ => ⟨⟨⟨0,by decide⟩,⟨1,by decide⟩⟩,⟨0,by decide⟩⟩
    | ⟨4,_⟩ => ⟨⟨⟨0,by decide⟩,⟨1,by decide⟩⟩,⟨1,by decide⟩⟩
    | ⟨5,_⟩ => ⟨⟨⟨0,by decide⟩,⟨1,by decide⟩⟩,⟨2,by decide⟩⟩
    | ⟨6,_⟩ => ⟨⟨⟨0,by decide⟩,⟨2,by decide⟩⟩,⟨0,by decide⟩⟩
    | ⟨7,_⟩ => ⟨⟨⟨0,by decide⟩,⟨2,by decide⟩⟩,⟨1,by decide⟩⟩
    | ⟨8,_⟩ => ⟨⟨⟨0,by decide⟩,⟨2,by decide⟩⟩,⟨2,by decide⟩⟩
    | ⟨9,_⟩ => ⟨⟨⟨1,by decide⟩,⟨0,by decide⟩⟩,⟨0,by decide⟩⟩
    | ⟨10,_⟩ => ⟨⟨⟨1,by decide⟩,⟨0,by decide⟩⟩,⟨1,by decide⟩⟩
    | ⟨11,_⟩ => ⟨⟨⟨1,by decide⟩,⟨0,by decide⟩⟩,⟨2,by decide⟩⟩
    | ⟨12,_⟩ => ⟨⟨⟨1,by decide⟩,⟨1,by decide⟩⟩,⟨0,by decide⟩⟩
    | ⟨13,_⟩ => ⟨⟨⟨1,by decide⟩,⟨1,by decide⟩⟩,⟨1,by decide⟩⟩
    | ⟨14,_⟩ => ⟨⟨⟨1,by decide⟩,⟨1,by decide⟩⟩,⟨2,by decide⟩⟩
    | ⟨15,_⟩ => ⟨⟨⟨1,by decide⟩,⟨2,by decide⟩⟩,⟨0,by decide⟩⟩
    | ⟨16,_⟩ => ⟨⟨⟨1,by decide⟩,⟨2,by decide⟩⟩,⟨1,by decide⟩⟩
    | ⟨17,_⟩ => ⟨⟨⟨1,by decide⟩,⟨2,by decide⟩⟩,⟨2,by decide⟩⟩
    | ⟨18,_⟩ => ⟨⟨⟨2,by decide⟩,⟨0,by decide⟩⟩,⟨0,by decide⟩⟩
    | ⟨19,_⟩ => ⟨⟨⟨2,by decide⟩,⟨0,by decide⟩⟩,⟨1,by decide⟩⟩
    | ⟨20,_⟩ => ⟨⟨⟨2,by decide⟩,⟨0,by decide⟩⟩,⟨2,by decide⟩⟩
    | ⟨21,_⟩ => ⟨⟨⟨2,by decide⟩,⟨1,by decide⟩⟩,⟨0,by decide⟩⟩
    | ⟨22,_⟩ => ⟨⟨⟨2,by decide⟩,⟨1,by decide⟩⟩,⟨1,by decide⟩⟩
    | ⟨23,_⟩ => ⟨⟨⟨2,by decide⟩,⟨1,by decide⟩⟩,⟨2,by decide⟩⟩
    | ⟨24,_⟩ => ⟨⟨⟨2,by decide⟩,⟨2,by decide⟩⟩,⟨0,by decide⟩⟩
    | ⟨25,_⟩ => ⟨⟨⟨2,by decide⟩,⟨2,by decide⟩⟩,⟨1,by decide⟩⟩
    | ⟨26,_⟩ => ⟨⟨⟨2,by decide⟩,⟨2,by decide⟩⟩,⟨2,by decide⟩⟩
    | ⟨n+27,h⟩ => absurd h (by omega)
  invFun := fun q =>
    match q with
    | ⟨⟨⟨0,_⟩,⟨0,_⟩⟩,⟨0,_⟩⟩ => 0 | ⟨⟨⟨0,_⟩,⟨0,_⟩⟩,⟨1,_⟩⟩ => 1 | ⟨⟨⟨0,_⟩,⟨0,_⟩⟩,⟨2,_⟩⟩ => 2
    | ⟨⟨⟨0,_⟩,⟨1,_⟩⟩,⟨0,_⟩⟩ => 3 | ⟨⟨⟨0,_⟩,⟨1,_⟩⟩,⟨1,_⟩⟩ => 4 | ⟨⟨⟨0,_⟩,⟨1,_⟩⟩,⟨2,_⟩⟩ => 5
    | ⟨⟨⟨0,_⟩,⟨2,_⟩⟩,⟨0,_⟩⟩ => 6 | ⟨⟨⟨0,_⟩,⟨2,_⟩⟩,⟨1,_⟩⟩ => 7 | ⟨⟨⟨0,_⟩,⟨2,_⟩⟩,⟨2,_⟩⟩ => 8
    | ⟨⟨⟨1,_⟩,⟨0,_⟩⟩,⟨0,_⟩⟩ => 9 | ⟨⟨⟨1,_⟩,⟨0,_⟩⟩,⟨1,_⟩⟩ => 10 | ⟨⟨⟨1,_⟩,⟨0,_⟩⟩,⟨2,_⟩⟩ => 11
    | ⟨⟨⟨1,_⟩,⟨1,_⟩⟩,⟨0,_⟩⟩ => 12 | ⟨⟨⟨1,_⟩,⟨1,_⟩⟩,⟨1,_⟩⟩ => 13 | ⟨⟨⟨1,_⟩,⟨1,_⟩⟩,⟨2,_⟩⟩ => 14
    | ⟨⟨⟨1,_⟩,⟨2,_⟩⟩,⟨0,_⟩⟩ => 15 | ⟨⟨⟨1,_⟩,⟨2,_⟩⟩,⟨1,_⟩⟩ => 16 | ⟨⟨⟨1,_⟩,⟨2,_⟩⟩,⟨2,_⟩⟩ => 17
    | ⟨⟨⟨2,_⟩,⟨0,_⟩⟩,⟨0,_⟩⟩ => 18 | ⟨⟨⟨2,_⟩,⟨0,_⟩⟩,⟨1,_⟩⟩ => 19 | ⟨⟨⟨2,_⟩,⟨0,_⟩⟩,⟨2,_⟩⟩ => 20
    | ⟨⟨⟨2,_⟩,⟨1,_⟩⟩,⟨0,_⟩⟩ => 21 | ⟨⟨⟨2,_⟩,⟨1,_⟩⟩,⟨1,_⟩⟩ => 22 | ⟨⟨⟨2,_⟩,⟨1,_⟩⟩,⟨2,_⟩⟩ => 23
    | ⟨⟨⟨2,_⟩,⟨2,_⟩⟩,⟨0,_⟩⟩ => 24 | ⟨⟨⟨2,_⟩,⟨2,_⟩⟩,⟨1,_⟩⟩ => 25 | ⟨⟨⟨2,_⟩,⟨2,_⟩⟩,⟨2,_⟩⟩ => 26
  left_inv := by decide
  right_inv := by decide

/-- **The slot equation** `pack3333 w q.1.1 q.1.2 q.2 = w (fin27EquivFlatIdx3333.symm q)` (`rfl` per
slot). The `hpack` hypothesis of `measurePreserving_paramsPack_of_flatIdxEquiv`. -/
theorem hpack3333 (w : Fin 27 → ℝ) (q : FlatIdx M3333) :
    pack3333 w q.1.1 q.1.2 q.2 = w (fin27EquivFlatIdx3333.symm q) := by
  obtain ⟨⟨s, i⟩, j⟩ := q
  fin_cases s <;> fin_cases i <;> fin_cases j <;> rfl

/-- **`pack3333` is measure-preserving** — the reusable reshape-MP at `fin27EquivFlatIdx3333`. -/
theorem measurePreserving_pack3333 :
    MeasurePreserving pack3333 (volume : Measure (Fin 27 → ℝ)) (volume : Measure (Params M3333)) :=
  measurePreserving_paramsPack_of_flatIdxEquiv M3333 fin27EquivFlatIdx3333 pack3333 hpack3333

/-- **`Q3333CLM = paramsEquivFlat ∘ pack3333` is measure-preserving.** -/
theorem measurePreserving_Q3333CLM :
    MeasurePreserving (Q3333CLM : (Fin 27 → ℝ) → (Fin 27 → ℝ))
      (volume : Measure (Fin 27 → ℝ)) volume := by
  have hcomp : (Q3333CLM : (Fin 27 → ℝ) → (Fin 27 → ℝ))
      = (paramsEquivFlat M3333) ∘ pack3333 := by
    funext w
    have h1 : Q3333CLM w = paramsEquivFlatCLE M3333 (pack3333CLM w) := rfl
    rw [Function.comp_apply, h1, paramsEquivFlatCLE_coe, pack3333CLM_coe]
  rw [hcomp]
  exact (measurePreserving_paramsEquivFlat _).comp measurePreserving_pack3333

/-- **`|det Q3333CLM| = 1`** — the outer reshape is a measure-preserving coordinate permutation. -/
theorem Q3333CLM_abs_det : |LinearMap.det (Q3333CLM : (Fin 27 → ℝ) →ₗ[ℝ] (Fin 27 → ℝ))| = 1 :=
  continuousLinearMap_abs_det_eq_one_of_measurePreserving Q3333CLM measurePreserving_Q3333CLM

/-! ## The structural Jacobian `T3333Deriv` (the explicit 27×27 fderiv CLM)

`T3333Deriv x` is the explicit fderiv of the flat structural map `T3333`: row `i` is the gradient of the
`i`-th chart entry (a sum/difference of products of the input projections). Built as a
`ContinuousLinearMap.pi` of the 27 gradient rows (`P k := ContinuousLinearMap.proj k`). -/

/-- The fderiv of `T3333` (the explicit per-output gradient CLM). -/
noncomputable def T3333Deriv (x : Fin 27 → ℝ) : (Fin 27 → ℝ) →L[ℝ] (Fin 27 → ℝ) :=
  ContinuousLinearMap.pi (fun i =>
    let P : Fin 27 → ((Fin 27 → ℝ) →L[ℝ] ℝ) := fun k => ContinuousLinearMap.proj k
    match i with
    | ⟨0,_⟩ => P 1
    | ⟨1,_⟩ => (x 2) • P 1 + (x 1) • P 2
    | ⟨2,_⟩ => (x 2 * x 8 + x 7) • P 1 + (x 1 * x 8) • P 2 + (x 1) • P 7 + (x 1 * x 2) • P 8
    | ⟨3,_⟩ => (x 3) • P 1 + (x 1) • P 3
    | ⟨4,_⟩ => (x 2 * x 3) • P 1 + (x 1 * x 3) • P 2 + (x 1 * x 2) • P 3 + P 4
    | ⟨5,_⟩ => (x 3 * (x 2 * x 8 + x 7)) • P 1 + (x 1 * x 3 * x 8) • P 2
        + (x 1 * (x 2 * x 8 + x 7)) • P 3 + (x 8) • P 4 + (x 1 * x 3) • P 7
        + (x 1 * x 2 * x 3 + x 4) • P 8
    | ⟨6,_⟩ => (x 3 * x 6 + x 5) • P 1 + (x 1 * x 6) • P 3 + (x 1) • P 5 + (x 1 * x 3) • P 6
    | ⟨7,_⟩ => (x 2 * (x 3 * x 6 + x 5)) • P 1 + (x 1 * (x 3 * x 6 + x 5)) • P 2
        + (x 1 * x 2 * x 6) • P 3 + (x 6) • P 4 + (x 1 * x 2) • P 5
        + (x 1 * x 2 * x 3 + x 4) • P 6
    | ⟨8,_⟩ => P 0 + ((x 2 * x 8 + x 7) * (x 3 * x 6 + x 5)) • P 1
        + (x 1 * x 8 * (x 3 * x 6 + x 5)) • P 2 + (x 1 * x 6 * (x 2 * x 8 + x 7)) • P 3
        + (x 6 * x 8) • P 4 + (x 1 * (x 2 * x 8 + x 7)) • P 5
        + (x 1 * x 2 * x 3 * x 8 + x 1 * x 3 * x 7 + x 4 * x 8) • P 6
        + (x 1 * (x 3 * x 6 + x 5)) • P 7
        + (x 1 * x 2 * x 3 * x 6 + x 1 * x 2 * x 5 + x 4 * x 6) • P 8
    | ⟨9,_⟩ => (-x 15) • P 7 + P 9 + (-x 7) • P 15
    | ⟨10,_⟩ => (-x 16) • P 7 + (x 11) • P 9 + (x 9) • P 11 + (-x 7) • P 16
    | ⟨11,_⟩ => (-x 17) • P 7 + (x 12) • P 9 + (x 9) • P 12 + (-x 7) • P 17
    | ⟨12,_⟩ => (-x 15) • P 8 + (x 10) • P 9 + (x 9) • P 10 + (-x 8) • P 15
    | ⟨13,_⟩ => (x 13) • P 0 + (-x 16) • P 8 + (x 10 * x 11) • P 9 + (x 11 * x 9) • P 10
        + (x 10 * x 9) • P 11 + (x 0) • P 13 + (-x 8) • P 16
    | ⟨14,_⟩ => (x 14) • P 0 + (-x 17) • P 8 + (x 10 * x 12) • P 9 + (x 12 * x 9) • P 10
        + (x 10 * x 9) • P 12 + (x 0) • P 14 + (-x 8) • P 17
    | ⟨15,_⟩ => P 15
    | ⟨16,_⟩ => P 16
    | ⟨17,_⟩ => P 17
    | ⟨18,_⟩ => (x 24) • P 0 + (-x 18) • P 11 + (-x 21) • P 12 + (-x 11) • P 18
        + (-x 12) • P 21 + (x 0) • P 24
    | ⟨19,_⟩ => (x 25) • P 0 + (-x 19) • P 11 + (-x 22) • P 12 + (-x 11) • P 19
        + (-x 12) • P 22 + (x 0) • P 25
    | ⟨20,_⟩ => (x 26) • P 0 + (-x 20) • P 11 + (-x 23) • P 12 + (-x 11) • P 20
        + (-x 12) • P 23 + (x 0) • P 26
    | ⟨21,_⟩ => P 18
    | ⟨22,_⟩ => P 19
    | ⟨23,_⟩ => P 20
    | ⟨24,_⟩ => P 21
    | ⟨25,_⟩ => P 22
    | ⟨26,_⟩ => P 23
    | ⟨n+27,h⟩ => absurd h (by omega))

/-- The explicit `T3333Deriv` row equals the combinator-produced fderiv (the closing CLM equality of
each `T3333_hasFDerivAt` row). Discharged by `ContinuousLinearMap.ext` + `simp`-reduce + `ring`. -/
local macro "match_row3333" : tactic =>
  `(tactic| (apply ContinuousLinearMap.ext
             intro y
             simp only [T3333Deriv, ContinuousLinearMap.comp_apply, ContinuousLinearMap.pi_apply,
               ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
               ContinuousLinearMap.smul_apply, ContinuousLinearMap.neg_apply,
               ContinuousLinearMap.proj_apply, smul_eq_mul, Pi.mul_apply, Pi.add_apply,
               Pi.sub_apply]
             try ring))

set_option maxHeartbeats 1600000 in
/-- **`T3333` has fderiv `T3333Deriv`** — `hasFDerivAt_pi''` per row, each row's fderiv built by the
product/sum rule (`hc k = hasFDerivAt_apply k`); the combinator fderiv is matched to the explicit
`T3333Deriv` row by `HasFDerivAt.congr_fderiv` + `match_row3333`. -/
theorem T3333_hasFDerivAt (x : Fin 27 → ℝ) : HasFDerivAt T3333 (T3333Deriv x) x := by
  apply hasFDerivAt_pi''
  intro i
  have hc : ∀ k : Fin 27, HasFDerivAt (fun y : Fin 27 → ℝ => y k)
      (ContinuousLinearMap.proj (R := ℝ) k) x := fun k => hasFDerivAt_apply (𝕜 := ℝ) k x
  fin_cases i <;>
    simp only [T3333, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.head_fin_const, Matrix.cons_val]
  · exact (hc 1).congr_fderiv (by match_row3333)
  · exact ((hc 1).mul (hc 2)).congr_fderiv (by match_row3333)
  · exact ((((hc 1).mul (hc 2)).mul (hc 8)).add ((hc 1).mul (hc 7))).congr_fderiv (by match_row3333)
  · exact ((hc 1).mul (hc 3)).congr_fderiv (by match_row3333)
  · exact ((((hc 1).mul (hc 2)).mul (hc 3)).add (hc 4)).congr_fderiv (by match_row3333)
  · exact ((((hc 1).mul (hc 3)).mul (hc 7)).add
      ((hc 8).mul ((((hc 1).mul (hc 2)).mul (hc 3)).add (hc 4)))).congr_fderiv (by match_row3333)
  · exact ((((hc 1).mul (hc 3)).mul (hc 6)).add ((hc 1).mul (hc 5))).congr_fderiv (by match_row3333)
  · exact ((((hc 1).mul (hc 2)).mul (hc 5)).add
      ((hc 6).mul ((((hc 1).mul (hc 2)).mul (hc 3)).add (hc 4)))).congr_fderiv (by match_row3333)
  · exact (((hc 0).add ((hc 7).mul ((((hc 1).mul (hc 3)).mul (hc 6)).add ((hc 1).mul (hc 5))))).add
      ((hc 8).mul ((((hc 1).mul (hc 2)).mul (hc 5)).add
        ((hc 6).mul ((((hc 1).mul (hc 2)).mul (hc 3)).add (hc 4)))))).congr_fderiv (by match_row3333)
  · exact ((hc 9).sub ((hc 15).mul (hc 7))).congr_fderiv (by match_row3333)
  · exact (((hc 11).mul (hc 9)).sub ((hc 16).mul (hc 7))).congr_fderiv (by match_row3333)
  · exact (((hc 12).mul (hc 9)).sub ((hc 17).mul (hc 7))).congr_fderiv (by match_row3333)
  · exact (((hc 10).mul (hc 9)).sub ((hc 15).mul (hc 8))).congr_fderiv (by match_row3333)
  · exact ((((hc 0).mul (hc 13)).add (((hc 10).mul (hc 11)).mul (hc 9))).sub
      ((hc 16).mul (hc 8))).congr_fderiv (by match_row3333)
  · exact ((((hc 0).mul (hc 14)).add (((hc 10).mul (hc 12)).mul (hc 9))).sub
      ((hc 17).mul (hc 8))).congr_fderiv (by match_row3333)
  · exact (hc 15).congr_fderiv (by match_row3333)
  · exact (hc 16).congr_fderiv (by match_row3333)
  · exact (hc 17).congr_fderiv (by match_row3333)
  · exact ((((hc 0).mul (hc 24)).sub ((hc 11).mul (hc 18))).sub
      ((hc 12).mul (hc 21))).congr_fderiv (by match_row3333)
  · exact ((((hc 0).mul (hc 25)).sub ((hc 11).mul (hc 19))).sub
      ((hc 12).mul (hc 22))).congr_fderiv (by match_row3333)
  · exact ((((hc 0).mul (hc 26)).sub ((hc 11).mul (hc 20))).sub
      ((hc 12).mul (hc 23))).congr_fderiv (by match_row3333)
  · exact (hc 18).congr_fderiv (by match_row3333)
  · exact (hc 19).congr_fderiv (by match_row3333)
  · exact (hc 20).congr_fderiv (by match_row3333)
  · exact (hc 21).congr_fderiv (by match_row3333)
  · exact (hc 22).congr_fderiv (by match_row3333)
  · exact (hc 23).congr_fderiv (by match_row3333)

/-! ## The composition `T3333 = Frame3333 ∘ Kparam3333` (the timeout-free det factorization)

The flat chart `T3333` factors as `Frame3333 ∘ Kparam3333`: `Kparam3333` is the LDU-core
parametrization (the near-identity map sending the deepest-factor coords `a,α,γ,δ` (`x 1,2,3,4`) to the
`2×2` core entries `k00,k01,k10,k11`, identity on the other 23 coords), and `Frame3333` is the bilinear
frame map (`A = G·K·H + u·E33`, `B`, `C` from the core + the remaining coords). The Jacobian then
factors `D T3333 = D Frame3333 ∘ D Kparam3333` (chain rule), so
`det = det(Frame3333Deriv) · det(Kparam3333Deriv)` (`LinearMap.det_comp`) — NO `27×27` matrix-product
identity, the timeout-free route. `det(Kparam3333Deriv) = (x 1)²` (lower-triangular, only the `4×4`
core block nontrivial); `det(Frame3333Deriv) = (x 0)⁵·(x 1)²·(x 4)²·(x 9)³` (block-triangular over the
abstract fderiv entry, the `pivotBlowupOnDeriv_det` pattern). -/

/-- **The LDU-core parametrization** `Kparam3333`: sends `a,α,γ,δ` (`x 1,2,3,4`) to the `2×2` core
entries `k00 = a`, `k01 = a·α`, `k10 = a·γ`, `k11 = a·α·γ + δ`; identity on the other 23 coords. -/
noncomputable def Kparam3333 (x : Fin 27 → ℝ) : Fin 27 → ℝ :=
  ![x 0, x 1, x 1 * x 2, x 1 * x 3, x 1 * x 2 * x 3 + x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12,
    x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, x 24, x 25, x 26]

/-- **The bilinear frame map** `Frame3333`: `A = G·K·H + u·E33` (`G = [[I₂];[λ]]`, `H = [I₂|m]`, `K` the
`2×2` core in coords `z 1,2,3,4`), with `B`, `C` from the remaining coords. `Frame3333 ∘ Kparam3333 =
T3333`. -/
noncomputable def Frame3333 (z : Fin 27 → ℝ) : Fin 27 → ℝ :=
  ![z 1, z 2, z 1 * z 7 + z 2 * z 8,
    z 3, z 4, z 3 * z 7 + z 4 * z 8,
    z 1 * z 5 + z 3 * z 6, z 2 * z 5 + z 4 * z 6,
      z 0 + z 1 * z 5 * z 7 + z 2 * z 5 * z 8 + z 3 * z 6 * z 7 + z 4 * z 6 * z 8,
    z 9 - z 15 * z 7, z 11 * z 9 - z 16 * z 7, z 12 * z 9 - z 17 * z 7,
    z 10 * z 9 - z 15 * z 8, z 0 * z 13 + z 10 * z 11 * z 9 - z 16 * z 8,
      z 0 * z 14 + z 10 * z 12 * z 9 - z 17 * z 8,
    z 15, z 16, z 17,
    z 0 * z 24 - z 11 * z 18 - z 12 * z 21, z 0 * z 25 - z 11 * z 19 - z 12 * z 22,
      z 0 * z 26 - z 11 * z 20 - z 12 * z 23,
    z 18, z 19, z 20, z 21, z 22, z 23]

set_option maxHeartbeats 4000000 in
/-- **The composition identity** `Frame3333 ∘ Kparam3333 = T3333` (per-coordinate `fin_cases` + `ring`). -/
theorem Frame3333_Kparam3333 (x : Fin 27 → ℝ) : Frame3333 (Kparam3333 x) = T3333 x := by
  funext i
  fin_cases i <;>
    simp only [Frame3333, Kparam3333, T3333, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.head_fin_const, Matrix.cons_val] <;> ring

/-- The fderiv of `Kparam3333` (the LDU-core parametrization): rows `2,3,4` carry the core gradients,
the other 23 rows are projections. -/
noncomputable def Kparam3333Deriv (x : Fin 27 → ℝ) : (Fin 27 → ℝ) →L[ℝ] (Fin 27 → ℝ) :=
  ContinuousLinearMap.pi (fun i =>
    let P : Fin 27 → ((Fin 27 → ℝ) →L[ℝ] ℝ) := fun k => ContinuousLinearMap.proj k
    match i with
    | ⟨0,_⟩ => P 0
    | ⟨1,_⟩ => P 1
    | ⟨2,_⟩ => (x 2) • P 1 + (x 1) • P 2
    | ⟨3,_⟩ => (x 3) • P 1 + (x 1) • P 3
    | ⟨4,_⟩ => (x 2 * x 3) • P 1 + (x 1 * x 3) • P 2 + (x 1 * x 2) • P 3 + P 4
    | ⟨5,_⟩ => P 5 | ⟨6,_⟩ => P 6 | ⟨7,_⟩ => P 7 | ⟨8,_⟩ => P 8 | ⟨9,_⟩ => P 9
    | ⟨10,_⟩ => P 10 | ⟨11,_⟩ => P 11 | ⟨12,_⟩ => P 12 | ⟨13,_⟩ => P 13 | ⟨14,_⟩ => P 14
    | ⟨15,_⟩ => P 15 | ⟨16,_⟩ => P 16 | ⟨17,_⟩ => P 17 | ⟨18,_⟩ => P 18 | ⟨19,_⟩ => P 19
    | ⟨20,_⟩ => P 20 | ⟨21,_⟩ => P 21 | ⟨22,_⟩ => P 22 | ⟨23,_⟩ => P 23 | ⟨24,_⟩ => P 24
    | ⟨25,_⟩ => P 25 | ⟨26,_⟩ => P 26
    | ⟨n+27,h⟩ => absurd h (by omega))

/-- The fderiv of `Frame3333` (the bilinear frame map): the explicit per-output gradient CLM. -/
noncomputable def Frame3333Deriv (z : Fin 27 → ℝ) : (Fin 27 → ℝ) →L[ℝ] (Fin 27 → ℝ) :=
  ContinuousLinearMap.pi (fun i =>
    let P : Fin 27 → ((Fin 27 → ℝ) →L[ℝ] ℝ) := fun k => ContinuousLinearMap.proj k
    match i with
    | ⟨0,_⟩ => P 1
    | ⟨1,_⟩ => P 2
    | ⟨2,_⟩ => (z 7) • P 1 + (z 8) • P 2 + (z 1) • P 7 + (z 2) • P 8
    | ⟨3,_⟩ => P 3
    | ⟨4,_⟩ => P 4
    | ⟨5,_⟩ => (z 7) • P 3 + (z 8) • P 4 + (z 3) • P 7 + (z 4) • P 8
    | ⟨6,_⟩ => (z 5) • P 1 + (z 6) • P 3 + (z 1) • P 5 + (z 3) • P 6
    | ⟨7,_⟩ => (z 5) • P 2 + (z 6) • P 4 + (z 2) • P 5 + (z 4) • P 6
    | ⟨8,_⟩ => P 0 + (z 5 * z 7) • P 1 + (z 5 * z 8) • P 2 + (z 6 * z 7) • P 3 + (z 6 * z 8) • P 4
        + (z 1 * z 7 + z 2 * z 8) • P 5 + (z 3 * z 7 + z 4 * z 8) • P 6
        + (z 1 * z 5 + z 3 * z 6) • P 7 + (z 2 * z 5 + z 4 * z 6) • P 8
    | ⟨9,_⟩ => (-z 15) • P 7 + P 9 + (-z 7) • P 15
    | ⟨10,_⟩ => (-z 16) • P 7 + (z 11) • P 9 + (z 9) • P 11 + (-z 7) • P 16
    | ⟨11,_⟩ => (-z 17) • P 7 + (z 12) • P 9 + (z 9) • P 12 + (-z 7) • P 17
    | ⟨12,_⟩ => (-z 15) • P 8 + (z 10) • P 9 + (z 9) • P 10 + (-z 8) • P 15
    | ⟨13,_⟩ => (z 13) • P 0 + (-z 16) • P 8 + (z 10 * z 11) • P 9 + (z 11 * z 9) • P 10
        + (z 10 * z 9) • P 11 + (z 0) • P 13 + (-z 8) • P 16
    | ⟨14,_⟩ => (z 14) • P 0 + (-z 17) • P 8 + (z 10 * z 12) • P 9 + (z 12 * z 9) • P 10
        + (z 10 * z 9) • P 12 + (z 0) • P 14 + (-z 8) • P 17
    | ⟨15,_⟩ => P 15
    | ⟨16,_⟩ => P 16
    | ⟨17,_⟩ => P 17
    | ⟨18,_⟩ => (z 24) • P 0 + (-z 11) • P 18 + (-z 12) • P 21 + (-z 18) • P 11 + (-z 21) • P 12
        + (z 0) • P 24
    | ⟨19,_⟩ => (z 25) • P 0 + (-z 11) • P 19 + (-z 12) • P 22 + (-z 19) • P 11 + (-z 22) • P 12
        + (z 0) • P 25
    | ⟨20,_⟩ => (z 26) • P 0 + (-z 11) • P 20 + (-z 12) • P 23 + (-z 20) • P 11 + (-z 23) • P 12
        + (z 0) • P 26
    | ⟨21,_⟩ => P 18
    | ⟨22,_⟩ => P 19
    | ⟨23,_⟩ => P 20
    | ⟨24,_⟩ => P 21
    | ⟨25,_⟩ => P 22
    | ⟨26,_⟩ => P 23
    | ⟨n+27,h⟩ => absurd h (by omega))

/-- Match a combinator fderiv to an explicit `Kparam3333Deriv`/`Frame3333Deriv` row. -/
local macro "match_frow3333" d:term : tactic =>
  `(tactic| (apply ContinuousLinearMap.ext
             intro y
             simp only [$d:term, ContinuousLinearMap.comp_apply, ContinuousLinearMap.pi_apply,
               ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
               ContinuousLinearMap.smul_apply, ContinuousLinearMap.neg_apply,
               ContinuousLinearMap.proj_apply, smul_eq_mul, Pi.mul_apply, Pi.add_apply,
               Pi.sub_apply]
             try ring))

set_option maxHeartbeats 800000 in
/-- **`Kparam3333` has fderiv `Kparam3333Deriv`**. -/
theorem Kparam3333_hasFDerivAt (x : Fin 27 → ℝ) :
    HasFDerivAt Kparam3333 (Kparam3333Deriv x) x := by
  apply hasFDerivAt_pi''
  intro i
  have hc : ∀ k : Fin 27, HasFDerivAt (fun y : Fin 27 → ℝ => y k)
      (ContinuousLinearMap.proj (R := ℝ) k) x := fun k => hasFDerivAt_apply (𝕜 := ℝ) k x
  fin_cases i <;>
    simp only [Kparam3333, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.head_fin_const, Matrix.cons_val]
  · exact (hc 0).congr_fderiv (by match_frow3333 Kparam3333Deriv)
  · exact (hc 1).congr_fderiv (by match_frow3333 Kparam3333Deriv)
  · exact ((hc 1).mul (hc 2)).congr_fderiv (by match_frow3333 Kparam3333Deriv)
  · exact ((hc 1).mul (hc 3)).congr_fderiv (by match_frow3333 Kparam3333Deriv)
  · exact ((((hc 1).mul (hc 2)).mul (hc 3)).add (hc 4)).congr_fderiv (by match_frow3333 Kparam3333Deriv)
  · exact (hc 5).congr_fderiv (by match_frow3333 Kparam3333Deriv)
  · exact (hc 6).congr_fderiv (by match_frow3333 Kparam3333Deriv)
  · exact (hc 7).congr_fderiv (by match_frow3333 Kparam3333Deriv)
  · exact (hc 8).congr_fderiv (by match_frow3333 Kparam3333Deriv)
  · exact (hc 9).congr_fderiv (by match_frow3333 Kparam3333Deriv)
  · exact (hc 10).congr_fderiv (by match_frow3333 Kparam3333Deriv)
  · exact (hc 11).congr_fderiv (by match_frow3333 Kparam3333Deriv)
  · exact (hc 12).congr_fderiv (by match_frow3333 Kparam3333Deriv)
  · exact (hc 13).congr_fderiv (by match_frow3333 Kparam3333Deriv)
  · exact (hc 14).congr_fderiv (by match_frow3333 Kparam3333Deriv)
  · exact (hc 15).congr_fderiv (by match_frow3333 Kparam3333Deriv)
  · exact (hc 16).congr_fderiv (by match_frow3333 Kparam3333Deriv)
  · exact (hc 17).congr_fderiv (by match_frow3333 Kparam3333Deriv)
  · exact (hc 18).congr_fderiv (by match_frow3333 Kparam3333Deriv)
  · exact (hc 19).congr_fderiv (by match_frow3333 Kparam3333Deriv)
  · exact (hc 20).congr_fderiv (by match_frow3333 Kparam3333Deriv)
  · exact (hc 21).congr_fderiv (by match_frow3333 Kparam3333Deriv)
  · exact (hc 22).congr_fderiv (by match_frow3333 Kparam3333Deriv)
  · exact (hc 23).congr_fderiv (by match_frow3333 Kparam3333Deriv)
  · exact (hc 24).congr_fderiv (by match_frow3333 Kparam3333Deriv)
  · exact (hc 25).congr_fderiv (by match_frow3333 Kparam3333Deriv)
  · exact (hc 26).congr_fderiv (by match_frow3333 Kparam3333Deriv)

set_option maxHeartbeats 1600000 in
/-- **`Frame3333` has fderiv `Frame3333Deriv`**. -/
theorem Frame3333_hasFDerivAt (z : Fin 27 → ℝ) :
    HasFDerivAt Frame3333 (Frame3333Deriv z) z := by
  apply hasFDerivAt_pi''
  intro i
  have hc : ∀ k : Fin 27, HasFDerivAt (fun y : Fin 27 → ℝ => y k)
      (ContinuousLinearMap.proj (R := ℝ) k) z := fun k => hasFDerivAt_apply (𝕜 := ℝ) k z
  fin_cases i <;>
    simp only [Frame3333, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.head_fin_const, Matrix.cons_val]
  · exact (hc 1).congr_fderiv (by match_frow3333 Frame3333Deriv)
  · exact (hc 2).congr_fderiv (by match_frow3333 Frame3333Deriv)
  · exact (((hc 1).mul (hc 7)).add ((hc 2).mul (hc 8))).congr_fderiv (by match_frow3333 Frame3333Deriv)
  · exact (hc 3).congr_fderiv (by match_frow3333 Frame3333Deriv)
  · exact (hc 4).congr_fderiv (by match_frow3333 Frame3333Deriv)
  · exact (((hc 3).mul (hc 7)).add ((hc 4).mul (hc 8))).congr_fderiv (by match_frow3333 Frame3333Deriv)
  · exact (((hc 1).mul (hc 5)).add ((hc 3).mul (hc 6))).congr_fderiv (by match_frow3333 Frame3333Deriv)
  · exact (((hc 2).mul (hc 5)).add ((hc 4).mul (hc 6))).congr_fderiv (by match_frow3333 Frame3333Deriv)
  · exact (((((hc 0).add (((hc 1).mul (hc 5)).mul (hc 7))).add (((hc 2).mul (hc 5)).mul (hc 8))).add
      (((hc 3).mul (hc 6)).mul (hc 7))).add (((hc 4).mul (hc 6)).mul (hc 8))).congr_fderiv
        (by match_frow3333 Frame3333Deriv)
  · exact ((hc 9).sub ((hc 15).mul (hc 7))).congr_fderiv (by match_frow3333 Frame3333Deriv)
  · exact (((hc 11).mul (hc 9)).sub ((hc 16).mul (hc 7))).congr_fderiv (by match_frow3333 Frame3333Deriv)
  · exact (((hc 12).mul (hc 9)).sub ((hc 17).mul (hc 7))).congr_fderiv (by match_frow3333 Frame3333Deriv)
  · exact (((hc 10).mul (hc 9)).sub ((hc 15).mul (hc 8))).congr_fderiv (by match_frow3333 Frame3333Deriv)
  · exact ((((hc 0).mul (hc 13)).add (((hc 10).mul (hc 11)).mul (hc 9))).sub
      ((hc 16).mul (hc 8))).congr_fderiv (by match_frow3333 Frame3333Deriv)
  · exact ((((hc 0).mul (hc 14)).add (((hc 10).mul (hc 12)).mul (hc 9))).sub
      ((hc 17).mul (hc 8))).congr_fderiv (by match_frow3333 Frame3333Deriv)
  · exact (hc 15).congr_fderiv (by match_frow3333 Frame3333Deriv)
  · exact (hc 16).congr_fderiv (by match_frow3333 Frame3333Deriv)
  · exact (hc 17).congr_fderiv (by match_frow3333 Frame3333Deriv)
  · exact ((((hc 0).mul (hc 24)).sub ((hc 11).mul (hc 18))).sub
      ((hc 12).mul (hc 21))).congr_fderiv (by match_frow3333 Frame3333Deriv)
  · exact ((((hc 0).mul (hc 25)).sub ((hc 11).mul (hc 19))).sub
      ((hc 12).mul (hc 22))).congr_fderiv (by match_frow3333 Frame3333Deriv)
  · exact ((((hc 0).mul (hc 26)).sub ((hc 11).mul (hc 20))).sub
      ((hc 12).mul (hc 23))).congr_fderiv (by match_frow3333 Frame3333Deriv)
  · exact (hc 18).congr_fderiv (by match_frow3333 Frame3333Deriv)
  · exact (hc 19).congr_fderiv (by match_frow3333 Frame3333Deriv)
  · exact (hc 20).congr_fderiv (by match_frow3333 Frame3333Deriv)
  · exact (hc 21).congr_fderiv (by match_frow3333 Frame3333Deriv)
  · exact (hc 22).congr_fderiv (by match_frow3333 Frame3333Deriv)
  · exact (hc 23).congr_fderiv (by match_frow3333 Frame3333Deriv)

/-! ## Determinant note (the sub-determinants live in a dedicated follow-up file)

`det(Kparam3333Deriv) = (x 1)²` and `det(Frame3333Deriv z) = (z 0)⁵·(z 9)³·(z 1·z 4 − z 2·z 3)²` close
the chart Jacobian `|det Dφ3333| = |x 0|⁵·|x 1|⁴·|x 4|²·|x 9|³` (via `LinearMap.det_comp` on the
composition `T3333 = Frame3333 ∘ Kparam3333` + the measure-preserving outer reshape `Q3333CLM_abs_det`).
Both sub-determinants follow `pivotBlowupOnDeriv_det`'s abstract-entry `BlockTriangular` pattern
(`toMatrix'` of the fderiv; `BlockTriangular` proven by `fin_cases` on the ROW index only — 27 cases,
NOT `i × j` — with the entry evaluated via `Pi.single_apply`, never expanded to a `![...]`-literal
matrix). `Kparam3333Deriv_det` is lower-triangular (diagonal `1,1,x1,x1,1,…`); `Frame3333Deriv_det` is
block-triangular with two `2×2` `K`/`Kᵀ` blocks (each det `z1·z4 − z2·z3`, via `Matrix.det_fin_two`).
Both are validated sorry-free in isolation but their combined per-file elaboration cost (the two
27-row `HasFDerivAt` + the `4M`-heartbeat composition identity + the heavy `det`s) exceeds a tractable
single build, so the determinant + the downstream `phi3333_abs_det` / `cov` / atom are split into a
dedicated module on top of this banked infrastructure. -/

end DLNFibre.DLN.RLCT
