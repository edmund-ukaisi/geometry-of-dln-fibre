import DLNFibre.DLN.RLCT.Validate.NodeAchieverChart
import DLNFibre.DLN.RLCT.Validate.RouteMLayerCoverGEL2
import DLNFibre.DLN.RLCT.Foundations.ParamsReshapeMP
import DLNFibre.Core.MeasureTheory.PolynomialZeroSet
import Mathlib.Algebra.MvPolynomial.Basic

/-!
# `RouteM4422` — the `(4,4,2,2)` achiever box-divergence (pure radial blow-up of the deepest factor)

The `(4,4,2,2)` instance of the achiever-path box-divergence atom
`routeMCore_box_diverges_achiever` (`RouteMLayerCoverGE.lean`), via a PURE radial blow-up of the
deepest `2×2` factor — the cleanest `L = 3` node (leaf-only codims `0,0,4`, the cert's
`threads/26-r1-genM-chart/` order-(a) witness). It constructs a `NodeAchieverChart M4422` and
discharges the atom for `M = (4,4,2,2)` through the M-agnostic assembly
`routeMCore_box_diverges_of_nodeChart`.

## The construction (`M = (4,4,2,2)`; `minAdm = 4`, `flatDim = 28`)

`routeMCore M4422 = ‖A0·A1·A2‖²` with `A0 : 4×4`, `A1 : 4×2`, `A2 : 2×2` (the 4×2 product). The
achiever center is `{A2 = 0}` — codim `4 = minAdm`, ENTIRELY from the deepest factor (`A0, A1` are
full-rank clean, codim `0` each). The chart blows up that codim-`4` center radially by ONE pivot
`u 0`:

    A2 = u₀ · M2bar,   M2bar = !![1, u 1; u 2, u 3]   (pivot u₀, the 3 angular coords u 1,u 2,u 3),
    A0, A1 free,
    A0·A1·A2 = u₀ · (A0·A1·M2bar),   so   F = ‖A0·A1·A2‖² = u₀² · U,
    U = ‖A0·A1·M2bar‖²   (u₀-free).

`|det Dφ| = |u 0|³ = |u 0|^{minAdm−1}` (a codim-`4` radial blow-up: radial-coord exponent `= codim − 1`,
`pivotBlowupOnDeriv_det` at `active.card = 4`). NO Schur shear and NO `b = aβ` substitution — the
descent codims are `0,0,4`, so the chart is a SINGLE `pivotBlowupOn` of the 4 deepest-factor coords.
Binding axis `(k,h) = (1, 3) = (1, minAdm−1)`, threshold `(3+1)/(2·1) = 2 = ½·minAdm`. At `c' = 2`
the leaf exponent on `u 0` is `3 − 2·1·2 = −1` (the sharp `∫ u₀⁻¹ = ⊤`).

The `U > 0` a.e. (the soundness-critical positivity field) is the genuine-polynomial null-zero-set
route: `U = eval · UPoly4422` for a nonzero `MvPolynomial`, so `{U = 0}` is Lebesgue-null
(`MvPolynomial.ae_eval_ne_zero`, the Core brick) — no clean single-coordinate bound exists (every
product entry is bilinear in `A0, A1`), unlike `(3,3,4)`'s `U ≥ a²`.

Verified EXACT in flat coordinates (`threads/26-r1-genM-chart/scripts/genM_genuine_4422.py`: `F = u₀²·U`,
`det = u₀³`, the radial coord exponent `= minAdm − 1`).
-/

open MeasureTheory
open scoped ENNReal BigOperators

namespace DLNFibre.DLN.RLCT

/-- `M4422 = (4,4,2,2)` (the cleanest `L = 3` achiever node, leaf-only codims). -/
abbrev M4422 : Fin 4 → ℕ := ![4, 4, 2, 2]

theorem minAdm_M4422 : minAdm M4422 = 4 := by
  rw [← minAdmRec_eq_minAdm]; decide

theorem flatDim_M4422 : flatDim M4422 = 28 := by decide

theorem routeMAmbient_M4422 : routeMAmbient M4422 = 28 := by decide

/-! ## The 3-layer product entry form -/

/-- **The `L = 3` layer-product entry form** `(prod M A) i j = ∑_{k1} ∑_{k2} A₀(i,k1)·A₁(k1,k2)·A₂(k2,j)`
— the explicit three-matrix product `A⁽⁰⁾·A⁽¹⁾·A⁽²⁾`. The general-`M` `L = 3` lift of
`prod_two_layer334` (same `prodAux` dependent-`Fin`-cast closer, one extra `mul_apply` level). -/
theorem prod_three_layer4422 (M : Fin 4 → ℕ) (A : Params M) (i : Fin (M 0)) (j : Fin (M 3)) :
    prod M A i j = ∑ k1 : Fin (M 1), ∑ k2 : Fin (M 2), A 0 i k1 * A 1 k1 k2 * A 2 k2 j := by
  unfold prod
  simp only [prodAux, Matrix.mul_apply, eq_mpr_eq_cast]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun k2 _ => ?_)
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl (fun k1 _ => ?_)
  congr 2
  convert congrFun (congrFun (Matrix.one_mul (cast (by rfl) (cast (by rfl) (A 0)))) i) k1 using 2

/-! ## The chart matrices (pure radial blow-up of the deepest factor) -/

/-- **The layer-`0` matrix `A⁽⁰⁾`** (4×4, free): coords `u 4 … u 19` in row-major. -/
noncomputable def chartA0_4422 (u : Fin 28 → ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![u 4, u 5, u 6, u 7;
     u 8, u 9, u 10, u 11;
     u 12, u 13, u 14, u 15;
     u 16, u 17, u 18, u 19]

/-- **The layer-`1` matrix `A⁽¹⁾`** (4×2, free): coords `u 20 … u 27` in row-major. -/
noncomputable def chartA1_4422 (u : Fin 28 → ℝ) : Matrix (Fin 4) (Fin 2) ℝ :=
  !![u 20, u 21; u 22, u 23; u 24, u 25; u 26, u 27]

/-- **The layer-`2` matrix `A⁽²⁾`** (2×2): the radial blow-up `A2 = u₀ · !![1, u 1; u 2, u 3]` of the
deepest factor. Pivot `u 0`; the 3 angular coords `u 1, u 2, u 3`. -/
noncomputable def chartA2_4422 (u : Fin 28 → ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![u 0, u 0 * u 1; u 0 * u 2, u 0 * u 3]

/-- The genuine `Params M4422`, assembled by `Fin.cons` over the three layers. -/
noncomputable def chartParams4422 (u : Fin 28 → ℝ) : Params M4422 :=
  Fin.cons (chartA0_4422 u)
    (Fin.cons (chartA1_4422 u)
      (Fin.cons (chartA2_4422 u) (fun i => i.elim0)))

/-- The post-blow-up unit factor `U = ‖A0·A1·M2bar‖²` (the `u₀`-free factor of `F = u₀²·U`), written in
the `prod_three_layer4422` entry shape with `M2bar = !![1, u 1; u 2, u 3]` (the deepest factor with the
pivot `u₀` stripped). A polynomial in the 27 angular/free coords. -/
noncomputable def Uval4422 (u : Fin 28 → ℝ) : ℝ :=
  ∑ i : Fin 4, ∑ j : Fin 2,
    (∑ k1 : Fin 4, ∑ k2 : Fin 2,
      chartA0_4422 u i k1 * chartA1_4422 u k1 k2
        * (!![1, u 1; u 2, u 3] : Matrix (Fin 2) (Fin 2) ℝ) k2 j) ^ 2

/-- **The deepest-factor entrywise pivot** `A2(k2,j) = u 0 · M2bar(k2,j)` (the radial blow-up: each
of the 4 deepest-factor entries carries one `u 0`). -/
theorem chartA2_4422_eq (u : Fin 28 → ℝ) (k2 j : Fin 2) :
    chartA2_4422 u k2 j = u 0 * (!![1, u 1; u 2, u 3] : Matrix (Fin 2) (Fin 2) ℝ) k2 j := by
  fin_cases k2 <;> fin_cases j <;> simp [chartA2_4422] <;> ring

set_option maxHeartbeats 800000 in
/-- **The per-entry pivot factorization.** Each product entry of the chart factors as
`u 0 · (the un-blown entry)`: the deepest factor `A2 = u₀·M2bar` contributes one `u 0` per entry. -/
theorem prod_chartParams4422_entry (u : Fin 28 → ℝ) (i : Fin 4) (j : Fin 2) :
    prod M4422 (chartParams4422 u) i j
      = u 0 * (∑ k1 : Fin 4, ∑ k2 : Fin 2,
          chartA0_4422 u i k1 * chartA1_4422 u k1 k2
            * (!![1, u 1; u 2, u 3] : Matrix (Fin 2) (Fin 2) ℝ) k2 j) := by
  rw [prod_three_layer4422 M4422 (chartParams4422 u) i j, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k1 _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k2 _ => ?_)
  have hA0 : (chartParams4422 u) 0 = chartA0_4422 u := rfl
  have hA1 : (chartParams4422 u) 1 = chartA1_4422 u := rfl
  have hA2 : (chartParams4422 u) 2 = chartA2_4422 u := rfl
  rw [hA0, hA1, hA2, chartA2_4422_eq]
  ring

/-- **The loss factorization (EXACT, sorry-free).** `dlnLoss M4422 0 (chartParams4422 u) = (u 0)² · U`
with `U = Uval4422 u` (the `u₀`-free unit). Each of the 8 product entries equals `u₀ · (un-blown
entry)` (`prod_chartParams4422_entry`), so `(entry)² = u₀² · (un-blown entry)²` and the squared
Frobenius norm is `u₀² · Uval4422`. The soundness-critical `F = u²·U` identity. -/
theorem dlnLoss_chartParams4422 (u : Fin 28 → ℝ) :
    dlnLoss M4422 0 (chartParams4422 u) = (u 0) ^ 2 * Uval4422 u := by
  unfold dlnLoss
  simp only [Matrix.sub_apply, Matrix.zero_apply, sub_zero]
  rw [Uval4422, Finset.mul_sum]
  -- the outer sum is over `Fin (M4422 0) = Fin 4`; inner over `Fin (M4422 3) = Fin 2` (defeq)
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [prod_chartParams4422_entry]
  ring

/-- **The genuine achiever flat chart for `(4,4,2,2)`** `phi4422 := paramsEquivFlat M4422 ∘ chartParams4422`,
an `(Fin 28 → ℝ) → (Fin 28 → ℝ)` map (`routeMAmbient M4422 = 28`). -/
noncomputable def phi4422 (u : Fin 28 → ℝ) : Fin 28 → ℝ :=
  paramsEquivFlat M4422 (chartParams4422 u)

/-- **The `routeMCore` factorization (EXACT, sorry-free).** `routeMCore M4422 (phi4422 u) = (u 0)² · U`
(`U = Uval4422 u`): since `routeMCore M = dlnLoss M 0 ∘ (paramsEquivFlat).symm` and `phi4422 =
paramsEquivFlat ∘ chartParams4422`, the `symm`/`apply` cancel, leaving `dlnLoss M4422 0 (chartParams4422 u)`
— discharged by `dlnLoss_chartParams4422` (the banked exact algebra). The soundness-critical
`F ∘ phi = u²·U` identity. -/
theorem routeMCore_phi4422 (u : Fin 28 → ℝ) :
    routeMCore M4422 (phi4422 u) = (u 0) ^ 2 * Uval4422 u := by
  rw [routeMCore, phi4422, MeasurableEquiv.symm_apply_apply, dlnLoss_chartParams4422]

/-- **`Uval4422 ≥ 0`** (a sum of squares). -/
theorem Uval4422_nonneg (u : Fin 28 → ℝ) : (0 : ℝ) ≤ Uval4422 u := by
  rw [Uval4422]
  positivity

/-- **`routeMCore M4422 (phi4422 u) ≥ 0`** (the loss is a sum of squares). -/
theorem routeMCore_phi4422_nonneg (u : Fin 28 → ℝ) :
    0 ≤ routeMCore M4422 (phi4422 u) := by
  rw [routeMCore]; exact dlnLoss_nonneg _ _ _

/-- `Uval4422` is continuous (a polynomial in the chart coordinates), hence measurable. -/
theorem continuous_Uval4422 : Continuous Uval4422 := by
  unfold Uval4422 chartA0_4422 chartA1_4422
  simp only [Fin.sum_univ_four, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.of_apply, Matrix.cons_val, Matrix.head_fin_const, Matrix.cons_val']
  fun_prop

/-! ## The `U > 0` a.e. positivity (the genuine-polynomial null-zero-set route)

Every product entry of `A0·A1·M2bar` is bilinear in the free `A0, A1` coords, so there is NO clean
single-coordinate lower bound `U ≥ (coord)²` (the `(3,3,4)` trick). Instead `U = eval u UPoly4422`
for a nonzero `MvPolynomial`, so `{U = 0}` is Lebesgue-null (`MvPolynomial.ae_eval_ne_zero`, the Core
brick `Core.MeasureTheory.PolynomialZeroSet`). The chart is left UNCHANGED (no extra shear). -/

open MvPolynomial in
/-- The formal polynomial `UPoly4422 : MvPolynomial (Fin 28) ℝ` with `eval u UPoly4422 = Uval4422 u`:
the `Uval4422` expression with `X k` for coord `k` and the deepest factor `M2bar = !![C 1, X 1; X 2, X 3]`
(the pivot `u₀` stripped). The `A0, A1` entries are `X`-variables; only `M2bar(0,0)` is the constant
`C 1`. -/
noncomputable def UPoly4422 : MvPolynomial (Fin 28) ℝ :=
  ∑ i : Fin 4, ∑ j : Fin 2,
    (∑ k1 : Fin 4, ∑ k2 : Fin 2,
      (!![X 4, X 5, X 6, X 7; X 8, X 9, X 10, X 11; X 12, X 13, X 14, X 15; X 16, X 17, X 18, X 19]
          : Matrix (Fin 4) (Fin 4) (MvPolynomial (Fin 28) ℝ)) i k1
        * (!![X 20, X 21; X 22, X 23; X 24, X 25; X 26, X 27]
          : Matrix (Fin 4) (Fin 2) (MvPolynomial (Fin 28) ℝ)) k1 k2
        * (!![C 1, X 1; X 2, X 3] : Matrix (Fin 2) (Fin 2) (MvPolynomial (Fin 28) ℝ)) k2 j) ^ 2

open MvPolynomial in
/-- `eval u UPoly4422 = Uval4422 u` — the encoding identity (`eval` is a ring hom: distributes over the
sums / products / squares; each `eval u (X k) = u k`, `eval u (C 1) = 1`, and the matrix accessors
match `chartA0_4422`/`chartA1_4422`/`M2bar` entrywise). -/
theorem eval_UPoly4422 (u : Fin 28 → ℝ) : MvPolynomial.eval u UPoly4422 = Uval4422 u := by
  rw [UPoly4422, Uval4422, chartA0_4422, chartA1_4422]
  simp only [map_sum, map_pow, map_mul]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  refine congrArg (· ^ 2) (Finset.sum_congr rfl (fun k1 _ => Finset.sum_congr rfl (fun k2 _ => ?_)))
  -- match the three matrix accessors entrywise under `eval u`
  fin_cases i <;> fin_cases k1 <;> fin_cases k2 <;> fin_cases j <;>
    simp [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.of_apply,
      Matrix.cons_val, Matrix.head_fin_const, Matrix.cons_val', MvPolynomial.eval_X,
      MvPolynomial.eval_C]

open MvPolynomial in
/-- **`UPoly4422 ≠ 0`** — the witness `u₀-free` point `A0 = I₄`, `A1 = !![1,0;0,1;0,0;0,0]`,
`M2bar = !![1,0;0,1]` (i.e. `u 1 = u 2 = u 3 = 0`): then `A0·A1·M2bar = !![1,0;0,1;0,0;0,0]`, so
`Uval4422 = 1² + 1² = 2 ≠ 0` (the cert's slice). Hence the formal polynomial is nonzero. -/
theorem UPoly4422_ne_zero : UPoly4422 ≠ 0 := by
  intro h0
  -- the witness coordinate vector (`M2bar = I₂` needs `u 3 = 1`, `u 1 = u 2 = 0`; `A0 = I₄` at coords
  -- 4,9,14,19; `A1 = !![1,0;0,1;0,0;0,0]` at coords 20,23) — `Pi.single` form so each accessor
  -- reduces by `Pi.single_apply` + decidable `Fin` equality. Then `A0·A1·M2bar = !![1,0;0,1;0,0;0,0]`,
  -- `U = 1² + 1² = 2` (the cert's slice).
  set w : Fin 28 → ℝ :=
    Pi.single 3 1 + Pi.single 4 1 + Pi.single 9 1 + Pi.single 14 1 + Pi.single 19 1
      + Pi.single 20 1 + Pi.single 23 1 with hw
  have hval : Uval4422 w = 2 := by
    rw [Uval4422, chartA0_4422, chartA1_4422]
    simp only [Fin.sum_univ_four, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.of_apply, Matrix.cons_val, Matrix.head_fin_const, Matrix.cons_val']
    simp only [hw, Pi.add_apply, Pi.single_apply, Fin.reduceEq, if_true, if_false]
    norm_num
  have : MvPolynomial.eval w UPoly4422 = 2 := by rw [eval_UPoly4422]; exact hval
  rw [h0] at this; simp at this

/-- **`Uval4422 > 0` a.e.** (the soundness-critical positivity). `Uval4422 = eval · UPoly4422` with
`UPoly4422 ≠ 0`, so `{Uval4422 = 0}` is Lebesgue-null (`MvPolynomial.ae_eval_ne_zero`); off that null
set `U ≥ 0` is `> 0`. -/
theorem Uval4422_ae_pos : ∀ᵐ u : Fin 28 → ℝ, 0 < Uval4422 u := by
  have hae := MvPolynomial.ae_eval_ne_zero UPoly4422 UPoly4422_ne_zero
  filter_upwards [hae] with u hu
  rw [eval_UPoly4422] at hu
  exact lt_of_le_of_ne (Uval4422_nonneg u) (Ne.symm hu)

/-! ## The single-axis binding monomial (the `(4,4,2,2)` leaf, pure radial blow-up)

The post-chart leaf integrand is `|det Dφ|·|F∘φ|^{−c'} = |u₀|³·(u₀²·U)^{−c'}` — `monomialIntegrand 28 k h`
with `k₀ = 1` (the loss base `u₀²`), `h₀ = 3` (the radial blow-up `|u₀|³ = |u₀|^{minAdm−1}`), `0` on the
27 spectator axes. NO spectator monomial (a PURE radial blow-up — no Schur shear / `b = aβ`). Binding
axis `(k,h) = (1, 3) = (1, minAdm−1)`, threshold `(3+1)/(2·1) = 2 = ½·minAdm`. -/

/-- The `(4,4,2,2)` leaf Jacobian exponents on `Fin 28` (`= Fin (routeMAmbient M4422)` defeq): `h = 3`
on the binding pivot axis `0` (the radial blow-up determinant `|u 0|³ = |u 0|^{minAdm−1}`); `0` on the
27 spectator axes (the PURE radial blow-up has NO spectator monomial). -/
def leafH4422 : Fin 28 → ℕ := fun j => if j = 0 then 3 else 0

/-- `leafH4422 0 = 3 = minAdm M4422 − 1` (the binding axis carries the radial exponent). -/
theorem leafH4422_pivot : leafH4422 (0 : Fin 28) = minAdm M4422 - 1 := by
  rw [minAdm_M4422]; rfl

/-- **The Jacobian weight `∏_j |u_j|^{leafH4422 j} = |u 0|³`** — the genuine `|det Dφ|` of the pure
radial blow-up (the pivot exceptional divisor `³`); the 27 spectator axes contribute `|·|⁰ = 1`. -/
theorem leafH4422_prod_eq (u : Fin 28 → ℝ) :
    (∏ j, |u j| ^ (leafH4422 j)) = |u 0| ^ 3 := by
  rw [Finset.prod_eq_single (0 : Fin 28)]
  · simp [leafH4422]
  · intro j _ hj; simp [leafH4422, hj]
  · intro h; exact absurd (Finset.mem_univ (0 : Fin 28)) h

/-- **Single-axis monomial evaluation.** `monomialIntegrand 28 (nodeLeafK 28 0) leafH4422 c u =
|u 0|³ · (|u 0|²)^{−c}` — the loss base `|u 0|²` (`k = 1` at axis `0`) against the pure radial Jacobian
`|u 0|³`. The 27 spectator axes contribute `1`. -/
theorem monomialIntegrand_leaf4422_eq (c : ℝ) (u : Fin 28 → ℝ) :
    monomialIntegrand 28 (nodeLeafK 28 0) leafH4422 c u
      = (|u 0| ^ 3) * (|u 0| ^ 2) ^ (-c) := by
  unfold monomialIntegrand
  rw [leafH4422_prod_eq]
  congr 1
  rw [Finset.prod_eq_single (0 : Fin 28)]
  · simp [nodeLeafK]
  · intro j _ hj; simp [nodeLeafK, hj]
  · intro h; exact absurd (Finset.mem_univ (0 : Fin 28)) h

/-- **The leaf-integrand identity for the `(4,4,2,2)` achiever chart**: `(∏_j |u_j|^{leafH4422 j}) ·
|routeMCore M4422 (phi4422 u)|^{−c} = monomialIntegrand · (Uval4422 u)^{−c}` — the pure radial Jacobian
`|u 0|³` against the unit power. Via `routeMCore_phi4422` (`F∘phi = u₀²·U`) +
`monomialIntegrand_leaf4422_eq`. The M-agnostic `leaf_integrand334` analog. -/
theorem leaf_integrand4422 (c : ℝ) (u : Fin 28 → ℝ) :
    (∏ j, |u j| ^ (leafH4422 j)) * |routeMCore M4422 (phi4422 u)| ^ (-c)
      = monomialIntegrand 28 (nodeLeafK 28 0) leafH4422 c u * (Uval4422 u) ^ (-c) := by
  rw [monomialIntegrand_leaf4422_eq, leafH4422_prod_eq, routeMCore_phi4422]
  have hUnn : (0 : ℝ) ≤ Uval4422 u := Uval4422_nonneg u
  rw [abs_of_nonneg (mul_nonneg (sq_nonneg _) hUnn),
    Real.mul_rpow (sq_nonneg _) hUnn, ← sq_abs (u 0)]
  ring

/-! ## The radial blow-up reshape + the chart Jacobian determinant `|det Dφ| = |u 0|³`

`phi4422 = paramsEquivFlat ∘ chartParams4422 = paramsEquivFlat ∘ pack4422 ∘ pb4422 = Q4422 ∘ pb4422`,
where `pb4422 = pivotBlowupOn {0,1,2,3} 0` is the PURE radial blow-up of the 4 deepest-factor coords
(det `u₀³ = u₀^{minAdm−1}`, `pivotBlowupOnDeriv_det` at `active.card = 4`), `pack4422` reshapes the 28
flat coords into the matrix slots, and `Q4422 = paramsEquivFlat ∘ pack4422` is a measure-preserving
coordinate permutation (`|det| = 1`). NO Schur shear — the cleanest `L ≥ 3` det. -/

/-- **The `(4,4,2,2)` radial blow-up** `pb4422 = pivotBlowupOn {0,1,2,3} 0`: blow up the 4 deepest-factor
coords (the `A2` entries) by the pivot `u 0`. `det = u₀³ = u₀^{minAdm−1}` (a codim-`4` center). -/
noncomputable def pb4422 : (Fin 28 → ℝ) → (Fin 28 → ℝ) :=
  pivotBlowupOn ({0, 1, 2, 3} : Finset (Fin 28)) 0

/-- **`pb4422` as an explicit vector** (per-coordinate `if`-reduction by `decide`). -/
theorem pb4422_apply (u : Fin 28 → ℝ) :
    pb4422 u = ![u 0, u 0 * u 1, u 0 * u 2, u 0 * u 3, u 4, u 5, u 6, u 7, u 8, u 9, u 10, u 11,
      u 12, u 13, u 14, u 15, u 16, u 17, u 18, u 19, u 20, u 21, u 22, u 23, u 24, u 25, u 26,
      u 27] := by
  funext i
  fin_cases i <;> simp [pb4422, pivotBlowupOn, Matrix.cons_val]

/-- **`pack4422`** — the reshape `(Fin 28 → ℝ) → Params M4422` sending the 28 flat coords (in the chart
slot order: coords `0..3` ↦ `A2`, `4..19` ↦ `A0`, `20..27` ↦ `A1`) to the matrix entries, matching
`chartParams4422`'s output layout. Linear (each output entry is one input coord). -/
noncomputable def pack4422 (w : Fin 28 → ℝ) : Params M4422 :=
  Fin.cons
    (!![w 4, w 5, w 6, w 7; w 8, w 9, w 10, w 11; w 12, w 13, w 14, w 15; w 16, w 17, w 18, w 19]
      : Matrix (Fin 4) (Fin 4) ℝ)
    (Fin.cons
      (!![w 20, w 21; w 22, w 23; w 24, w 25; w 26, w 27] : Matrix (Fin 4) (Fin 2) ℝ)
      (Fin.cons
        (!![w 0, w 1; w 2, w 3] : Matrix (Fin 2) (Fin 2) ℝ)
        (fun i => i.elim0)))

/-- **The factorization identity** `chartParams4422 = pack4422 ∘ pb4422` (the load-bearing diffeo
factorization; per-layer `funext` + `fin_cases` + `ring` on the 28 entries). -/
theorem chartParams4422_eq_pack_pb (u : Fin 28 → ℝ) :
    chartParams4422 u = pack4422 (pb4422 u) := by
  funext s
  fin_cases s
  · show chartA0_4422 u = (pack4422 (pb4422 u)) 0
    have hp : (pack4422 (pb4422 u)) 0
        = (!![(pb4422 u) 4, (pb4422 u) 5, (pb4422 u) 6, (pb4422 u) 7;
            (pb4422 u) 8, (pb4422 u) 9, (pb4422 u) 10, (pb4422 u) 11;
            (pb4422 u) 12, (pb4422 u) 13, (pb4422 u) 14, (pb4422 u) 15;
            (pb4422 u) 16, (pb4422 u) 17, (pb4422 u) 18, (pb4422 u) 19]
          : Matrix (Fin 4) (Fin 4) ℝ) := rfl
    rw [hp, pb4422_apply]
    funext i j
    fin_cases i <;> fin_cases j <;> simp [chartA0_4422]
  · show chartA1_4422 u = (pack4422 (pb4422 u)) 1
    have hp : (pack4422 (pb4422 u)) 1
        = (!![(pb4422 u) 20, (pb4422 u) 21; (pb4422 u) 22, (pb4422 u) 23;
            (pb4422 u) 24, (pb4422 u) 25; (pb4422 u) 26, (pb4422 u) 27]
          : Matrix (Fin 4) (Fin 2) ℝ) := rfl
    rw [hp, pb4422_apply]
    funext i j
    fin_cases i <;> fin_cases j <;> simp [chartA1_4422]
  · show chartA2_4422 u = (pack4422 (pb4422 u)) 2
    have hp : (pack4422 (pb4422 u)) 2
        = (!![(pb4422 u) 0, (pb4422 u) 1; (pb4422 u) 2, (pb4422 u) 3]
          : Matrix (Fin 2) (Fin 2) ℝ) := rfl
    rw [hp, pb4422_apply]
    funext i j
    fin_cases i <;> fin_cases j <;> simp [chartA2_4422]

/-- **The reusable radial-blow-up determinant** `|det D(pivotBlowupOn active p)| = |x p|^{active.card−1}`
— a pure radial blow-up of a codim-`active.card` linear center has radial-coord Jacobian exponent
`active.card − 1` (`pivotBlowupOnDeriv_det`). For a codim-`minAdm` achiever center the exponent is
`minAdm − 1`. The depth-independent backbone of the achiever Jacobian (the `(4,4,2,2)` `det = u₀³` is
the `active.card = minAdm = 4` instance). -/
theorem pivotBlowupOn_abs_det {N : ℕ} (active : Finset (Fin N)) (p : Fin N) (hp : p ∈ active)
    (x : Fin N → ℝ) :
    |(pivotBlowupOnDeriv active p x).det| = |x p| ^ (active.card - 1) := by
  rw [pivotBlowupOnDeriv_det active p hp, abs_pow]

/-- **The `(4,4,2,2)` chart fderiv** `phi4422Deriv u = Q4422CLM ∘L pb4422Deriv u`. First the pieces:
`pb4422` has fderiv `pivotBlowupOnDeriv {0,1,2,3} 0`, det `u₀³`. -/
theorem pb4422_hasFDerivAt (u : Fin 28 → ℝ) :
    HasFDerivAt pb4422 (pivotBlowupOnDeriv ({0, 1, 2, 3} : Finset (Fin 28)) 0 u) u :=
  hasFDerivWithinAt_univ.mp (pivotBlowupOn_hasFDerivWithinAt _ _ Set.univ u)

/-- **The radial-blow-up determinant for `(4,4,2,2)`** `|det D(pb4422)| = |u 0|³ = |u 0|^{minAdm−1}`
(the codim-`4` center; `active.card = 4`). -/
theorem pb4422_abs_det (u : Fin 28 → ℝ) :
    |(pivotBlowupOnDeriv ({0, 1, 2, 3} : Finset (Fin 28)) 0 u).det| = |u 0| ^ 3 := by
  rw [pivotBlowupOn_abs_det _ _ (by decide)]
  norm_num [show ({0, 1, 2, 3} : Finset (Fin 28)).card = 4 from by decide]

/-! ## The outer reindex `Q4422 = paramsEquivFlat ∘ pack4422` (measure-preserving, `|det| = 1`) -/

/-- `pack4422` as a continuous ℝ-linear map (each output matrix entry is one input coordinate). -/
noncomputable def pack4422CLM : (Fin 28 → ℝ) →L[ℝ] Params M4422 :=
  ContinuousLinearMap.pi (fun s =>
    match s with
    | ⟨0, _⟩ => ContinuousLinearMap.pi (fun i => ContinuousLinearMap.pi (fun j =>
        ContinuousLinearMap.proj
          (![![4, 5, 6, 7], ![8, 9, 10, 11], ![12, 13, 14, 15], ![16, 17, 18, 19]] i j : Fin 28)))
    | ⟨1, _⟩ => ContinuousLinearMap.pi (fun i => ContinuousLinearMap.pi (fun j =>
        ContinuousLinearMap.proj
          (![![20, 21], ![22, 23], ![24, 25], ![26, 27]] i j : Fin 28)))
    | ⟨2, _⟩ => ContinuousLinearMap.pi (fun i => ContinuousLinearMap.pi (fun j =>
        ContinuousLinearMap.proj
          (![![0, 1], ![2, 3]] i j : Fin 28)))
    | ⟨n + 3, h⟩ => absurd h (by omega))

/-- `pack4422CLM` has underlying function `pack4422`. -/
theorem pack4422CLM_coe : ⇑pack4422CLM = pack4422 := by
  funext w s
  fin_cases s
  · funext i j; fin_cases i <;> fin_cases j <;> rfl
  · funext i j; fin_cases i <;> fin_cases j <;> rfl
  · funext i j; fin_cases i <;> fin_cases j <;> rfl

/-- **The outer-reindex CLM** `Q4422CLM = paramsEquivFlatCLE ∘ pack4422CLM`. -/
noncomputable def Q4422CLM : (Fin 28 → ℝ) →L[ℝ] (Fin 28 → ℝ) :=
  (paramsEquivFlatCLE M4422).toContinuousLinearMap.comp pack4422CLM

/-- The explicit slot bijection `Fin 28 ≃ FlatIdx M4422` pinning `pack4422`'s flat-coord → matrix-slot
order. The `toFun`/`invFun` are the explicit slot tables; the inverses are `decide` (kernel). -/
noncomputable def fin28EquivFlatIdx4422 : Fin 28 ≃ FlatIdx M4422 where
  toFun := fun k =>
    match k with
    | ⟨0,_⟩ => ⟨⟨⟨2,by decide⟩,⟨0,by decide⟩⟩,⟨0,by decide⟩⟩
    | ⟨1,_⟩ => ⟨⟨⟨2,by decide⟩,⟨0,by decide⟩⟩,⟨1,by decide⟩⟩
    | ⟨2,_⟩ => ⟨⟨⟨2,by decide⟩,⟨1,by decide⟩⟩,⟨0,by decide⟩⟩
    | ⟨3,_⟩ => ⟨⟨⟨2,by decide⟩,⟨1,by decide⟩⟩,⟨1,by decide⟩⟩
    | ⟨4,_⟩ => ⟨⟨⟨0,by decide⟩,⟨0,by decide⟩⟩,⟨0,by decide⟩⟩
    | ⟨5,_⟩ => ⟨⟨⟨0,by decide⟩,⟨0,by decide⟩⟩,⟨1,by decide⟩⟩
    | ⟨6,_⟩ => ⟨⟨⟨0,by decide⟩,⟨0,by decide⟩⟩,⟨2,by decide⟩⟩
    | ⟨7,_⟩ => ⟨⟨⟨0,by decide⟩,⟨0,by decide⟩⟩,⟨3,by decide⟩⟩
    | ⟨8,_⟩ => ⟨⟨⟨0,by decide⟩,⟨1,by decide⟩⟩,⟨0,by decide⟩⟩
    | ⟨9,_⟩ => ⟨⟨⟨0,by decide⟩,⟨1,by decide⟩⟩,⟨1,by decide⟩⟩
    | ⟨10,_⟩ => ⟨⟨⟨0,by decide⟩,⟨1,by decide⟩⟩,⟨2,by decide⟩⟩
    | ⟨11,_⟩ => ⟨⟨⟨0,by decide⟩,⟨1,by decide⟩⟩,⟨3,by decide⟩⟩
    | ⟨12,_⟩ => ⟨⟨⟨0,by decide⟩,⟨2,by decide⟩⟩,⟨0,by decide⟩⟩
    | ⟨13,_⟩ => ⟨⟨⟨0,by decide⟩,⟨2,by decide⟩⟩,⟨1,by decide⟩⟩
    | ⟨14,_⟩ => ⟨⟨⟨0,by decide⟩,⟨2,by decide⟩⟩,⟨2,by decide⟩⟩
    | ⟨15,_⟩ => ⟨⟨⟨0,by decide⟩,⟨2,by decide⟩⟩,⟨3,by decide⟩⟩
    | ⟨16,_⟩ => ⟨⟨⟨0,by decide⟩,⟨3,by decide⟩⟩,⟨0,by decide⟩⟩
    | ⟨17,_⟩ => ⟨⟨⟨0,by decide⟩,⟨3,by decide⟩⟩,⟨1,by decide⟩⟩
    | ⟨18,_⟩ => ⟨⟨⟨0,by decide⟩,⟨3,by decide⟩⟩,⟨2,by decide⟩⟩
    | ⟨19,_⟩ => ⟨⟨⟨0,by decide⟩,⟨3,by decide⟩⟩,⟨3,by decide⟩⟩
    | ⟨20,_⟩ => ⟨⟨⟨1,by decide⟩,⟨0,by decide⟩⟩,⟨0,by decide⟩⟩
    | ⟨21,_⟩ => ⟨⟨⟨1,by decide⟩,⟨0,by decide⟩⟩,⟨1,by decide⟩⟩
    | ⟨22,_⟩ => ⟨⟨⟨1,by decide⟩,⟨1,by decide⟩⟩,⟨0,by decide⟩⟩
    | ⟨23,_⟩ => ⟨⟨⟨1,by decide⟩,⟨1,by decide⟩⟩,⟨1,by decide⟩⟩
    | ⟨24,_⟩ => ⟨⟨⟨1,by decide⟩,⟨2,by decide⟩⟩,⟨0,by decide⟩⟩
    | ⟨25,_⟩ => ⟨⟨⟨1,by decide⟩,⟨2,by decide⟩⟩,⟨1,by decide⟩⟩
    | ⟨26,_⟩ => ⟨⟨⟨1,by decide⟩,⟨3,by decide⟩⟩,⟨0,by decide⟩⟩
    | ⟨27,_⟩ => ⟨⟨⟨1,by decide⟩,⟨3,by decide⟩⟩,⟨1,by decide⟩⟩
    | ⟨n+28,h⟩ => absurd h (by omega)
  invFun := fun q =>
    match q with
    | ⟨⟨⟨2,_⟩,⟨0,_⟩⟩,⟨0,_⟩⟩ => 0 | ⟨⟨⟨2,_⟩,⟨0,_⟩⟩,⟨1,_⟩⟩ => 1
    | ⟨⟨⟨2,_⟩,⟨1,_⟩⟩,⟨0,_⟩⟩ => 2 | ⟨⟨⟨2,_⟩,⟨1,_⟩⟩,⟨1,_⟩⟩ => 3
    | ⟨⟨⟨0,_⟩,⟨0,_⟩⟩,⟨0,_⟩⟩ => 4 | ⟨⟨⟨0,_⟩,⟨0,_⟩⟩,⟨1,_⟩⟩ => 5
    | ⟨⟨⟨0,_⟩,⟨0,_⟩⟩,⟨2,_⟩⟩ => 6 | ⟨⟨⟨0,_⟩,⟨0,_⟩⟩,⟨3,_⟩⟩ => 7
    | ⟨⟨⟨0,_⟩,⟨1,_⟩⟩,⟨0,_⟩⟩ => 8 | ⟨⟨⟨0,_⟩,⟨1,_⟩⟩,⟨1,_⟩⟩ => 9
    | ⟨⟨⟨0,_⟩,⟨1,_⟩⟩,⟨2,_⟩⟩ => 10 | ⟨⟨⟨0,_⟩,⟨1,_⟩⟩,⟨3,_⟩⟩ => 11
    | ⟨⟨⟨0,_⟩,⟨2,_⟩⟩,⟨0,_⟩⟩ => 12 | ⟨⟨⟨0,_⟩,⟨2,_⟩⟩,⟨1,_⟩⟩ => 13
    | ⟨⟨⟨0,_⟩,⟨2,_⟩⟩,⟨2,_⟩⟩ => 14 | ⟨⟨⟨0,_⟩,⟨2,_⟩⟩,⟨3,_⟩⟩ => 15
    | ⟨⟨⟨0,_⟩,⟨3,_⟩⟩,⟨0,_⟩⟩ => 16 | ⟨⟨⟨0,_⟩,⟨3,_⟩⟩,⟨1,_⟩⟩ => 17
    | ⟨⟨⟨0,_⟩,⟨3,_⟩⟩,⟨2,_⟩⟩ => 18 | ⟨⟨⟨0,_⟩,⟨3,_⟩⟩,⟨3,_⟩⟩ => 19
    | ⟨⟨⟨1,_⟩,⟨0,_⟩⟩,⟨0,_⟩⟩ => 20 | ⟨⟨⟨1,_⟩,⟨0,_⟩⟩,⟨1,_⟩⟩ => 21
    | ⟨⟨⟨1,_⟩,⟨1,_⟩⟩,⟨0,_⟩⟩ => 22 | ⟨⟨⟨1,_⟩,⟨1,_⟩⟩,⟨1,_⟩⟩ => 23
    | ⟨⟨⟨1,_⟩,⟨2,_⟩⟩,⟨0,_⟩⟩ => 24 | ⟨⟨⟨1,_⟩,⟨2,_⟩⟩,⟨1,_⟩⟩ => 25
    | ⟨⟨⟨1,_⟩,⟨3,_⟩⟩,⟨0,_⟩⟩ => 26 | ⟨⟨⟨1,_⟩,⟨3,_⟩⟩,⟨1,_⟩⟩ => 27
  left_inv := by decide
  right_inv := by decide

/-- **The slot equation** `pack4422 w q.1.1 q.1.2 q.2 = w (fin28EquivFlatIdx4422.symm q)` (`rfl` per
slot). The `hpack` hypothesis of `measurePreserving_paramsPack_of_flatIdxEquiv`. -/
theorem hpack4422 (w : Fin 28 → ℝ) (q : FlatIdx M4422) :
    pack4422 w q.1.1 q.1.2 q.2 = w (fin28EquivFlatIdx4422.symm q) := by
  obtain ⟨⟨s, i⟩, j⟩ := q
  fin_cases s <;> fin_cases i <;> fin_cases j <;> rfl

/-- **`pack4422` is measure-preserving** — the reusable reshape-MP at `fin28EquivFlatIdx4422`. -/
theorem measurePreserving_pack4422 :
    MeasurePreserving pack4422 (volume : Measure (Fin 28 → ℝ)) (volume : Measure (Params M4422)) :=
  measurePreserving_paramsPack_of_flatIdxEquiv M4422 fin28EquivFlatIdx4422 pack4422 hpack4422

/-- **`Q4422CLM = paramsEquivFlat ∘ pack4422` is measure-preserving.** -/
theorem measurePreserving_Q4422CLM :
    MeasurePreserving (Q4422CLM : (Fin 28 → ℝ) → (Fin 28 → ℝ))
      (volume : Measure (Fin 28 → ℝ)) volume := by
  have hcomp : (Q4422CLM : (Fin 28 → ℝ) → (Fin 28 → ℝ))
      = (paramsEquivFlat M4422) ∘ pack4422 := by
    funext w
    have h1 : Q4422CLM w = paramsEquivFlatCLE M4422 (pack4422CLM w) := rfl
    rw [Function.comp_apply, h1, paramsEquivFlatCLE_coe, pack4422CLM_coe]
  rw [hcomp]
  exact (measurePreserving_paramsEquivFlat _).comp measurePreserving_pack4422

/-- **`|det Q4422CLM| = 1`** — the outer reshape is a measure-preserving coordinate permutation. -/
theorem Q4422CLM_abs_det : |LinearMap.det (Q4422CLM : (Fin 28 → ℝ) →ₗ[ℝ] (Fin 28 → ℝ))| = 1 :=
  continuousLinearMap_abs_det_eq_one_of_measurePreserving Q4422CLM measurePreserving_Q4422CLM

/-! ## The chart fderiv `phi4422` + the structural determinant `|det Dφ| = |u 0|³` -/

/-- `pack4422` (linear) has constant fderiv `pack4422CLM`. -/
theorem pack4422_hasFDerivAt (w : Fin 28 → ℝ) : HasFDerivAt pack4422 pack4422CLM w := by
  have h : HasFDerivAt (⇑pack4422CLM) pack4422CLM w := pack4422CLM.hasFDerivAt
  exact h.congr_of_eventuallyEq (by filter_upwards with v; rw [pack4422CLM_coe])

/-- **The `(4,4,2,2)` chart fderiv** `phi4422Deriv u = Q4422CLM ∘L pb4422Deriv u`. -/
noncomputable def phi4422Deriv (u : Fin 28 → ℝ) : (Fin 28 → ℝ) →L[ℝ] (Fin 28 → ℝ) :=
  Q4422CLM.comp (pivotBlowupOnDeriv ({0, 1, 2, 3} : Finset (Fin 28)) 0 u)

/-- **`phi4422` has fderiv `phi4422Deriv`** — the chain rule for `phi4422 = paramsEquivFlat ∘ pack4422 ∘
pb4422` (`= Q4422 ∘ pb4422`). -/
theorem phi4422_hasFDerivAt (u : Fin 28 → ℝ) : HasFDerivAt phi4422 (phi4422Deriv u) u := by
  have hchart : HasFDerivAt chartParams4422 (pack4422CLM.comp
      (pivotBlowupOnDeriv ({0, 1, 2, 3} : Finset (Fin 28)) 0 u)) u := by
    have hcomp : HasFDerivAt (fun v => pack4422 (pb4422 v))
        (pack4422CLM.comp (pivotBlowupOnDeriv ({0, 1, 2, 3} : Finset (Fin 28)) 0 u)) u :=
      (pack4422_hasFDerivAt (pb4422 u)).comp u (pb4422_hasFDerivAt u)
    exact hcomp.congr_of_eventuallyEq (by filter_upwards with v; rw [chartParams4422_eq_pack_pb])
  have hflat : HasFDerivAt (paramsEquivFlat M4422)
      ((paramsEquivFlatCLE M4422).toContinuousLinearMap) (chartParams4422 u) :=
    hasFDerivAt_paramsEquivFlat _ _
  have : HasFDerivAt (fun u => paramsEquivFlat M4422 (chartParams4422 u))
      (((paramsEquivFlatCLE M4422).toContinuousLinearMap).comp
        (pack4422CLM.comp (pivotBlowupOnDeriv ({0, 1, 2, 3} : Finset (Fin 28)) 0 u))) u :=
    hflat.comp u hchart
  rw [phi4422Deriv, Q4422CLM]
  exact this

/-- **The genuine chart Jacobian determinant** `|det Dφ4422| = |u 0|³ = |u 0|^{minAdm−1}` — the
soundness-critical weight matching `leafH4422`. `phi4422Deriv = Q4422CLM ∘ pb4422Deriv` has
`|det| = |det Q4422CLM| · |det pb4422Deriv| = 1 · |u 0|³` (`Q4422CLM_abs_det` + `pb4422_abs_det`). -/
theorem phi4422_abs_det (u : Fin 28 → ℝ) :
    |(phi4422Deriv u).det| = |u 0| ^ 3 := by
  rw [phi4422Deriv, ContinuousLinearMap.det, ContinuousLinearMap.coe_comp, LinearMap.det_comp,
    abs_mul, Q4422CLM_abs_det, one_mul, ← ContinuousLinearMap.det, pb4422_abs_det]

/-- `phi4422` is differentiable (a composite of the polynomial `chartParams4422` and the linear
`paramsEquivFlat`). -/
theorem differentiable_phi4422 : Differentiable ℝ phi4422 :=
  fun u => (phi4422_hasFDerivAt u).differentiableAt

/-! ## Injectivity off `{u 0 = 0}`, continuity, image containment -/

/-- **`chartParams4422` is injective off `{u 0 = 0}`** (the radial center; null). From the matrix
equalities every coord is recovered: spectators `A0, A1` directly; the pivot `u 0` from `A2(0,0)`; then
`u 1, u 2, u 3` via `÷ u 0` (`u 0 ≠ 0`). -/
theorem chartParams4422_injOn :
    Set.InjOn chartParams4422 {u : Fin 28 → ℝ | u 0 ≠ 0} := by
  rintro u hu0 v hv0 huv
  simp only [Set.mem_setOf_eq] at hu0 hv0
  have hA0 : chartA0_4422 u = chartA0_4422 v := congrFun huv 0
  have hA1 : chartA1_4422 u = chartA1_4422 v := congrFun huv 1
  have hA2 : chartA2_4422 u = chartA2_4422 v := congrFun huv 2
  have eA0 := fun i j => congrFun (congrFun hA0 i) j
  have eA1 := fun i j => congrFun (congrFun hA1 i) j
  have eA2 := fun i j => congrFun (congrFun hA2 i) j
  -- A0 spectators (coords 4..19)
  have h4 : u 4 = v 4 := by have := eA0 0 0; simpa [chartA0_4422] using this
  have h5 : u 5 = v 5 := by have := eA0 0 1; simpa [chartA0_4422] using this
  have h6 : u 6 = v 6 := by have := eA0 0 2; simpa [chartA0_4422] using this
  have h7 : u 7 = v 7 := by have := eA0 0 3; simpa [chartA0_4422] using this
  have h8 : u 8 = v 8 := by have := eA0 1 0; simpa [chartA0_4422] using this
  have h9 : u 9 = v 9 := by have := eA0 1 1; simpa [chartA0_4422] using this
  have h10 : u 10 = v 10 := by have := eA0 1 2; simpa [chartA0_4422] using this
  have h11 : u 11 = v 11 := by have := eA0 1 3; simpa [chartA0_4422] using this
  have h12 : u 12 = v 12 := by have := eA0 2 0; simpa [chartA0_4422] using this
  have h13 : u 13 = v 13 := by have := eA0 2 1; simpa [chartA0_4422] using this
  have h14 : u 14 = v 14 := by have := eA0 2 2; simpa [chartA0_4422] using this
  have h15 : u 15 = v 15 := by have := eA0 2 3; simpa [chartA0_4422] using this
  have h16 : u 16 = v 16 := by have := eA0 3 0; simpa [chartA0_4422] using this
  have h17 : u 17 = v 17 := by have := eA0 3 1; simpa [chartA0_4422] using this
  have h18 : u 18 = v 18 := by have := eA0 3 2; simpa [chartA0_4422] using this
  have h19 : u 19 = v 19 := by have := eA0 3 3; simpa [chartA0_4422] using this
  -- A1 spectators (coords 20..27)
  have h20 : u 20 = v 20 := by have := eA1 0 0; simpa [chartA1_4422] using this
  have h21 : u 21 = v 21 := by have := eA1 0 1; simpa [chartA1_4422] using this
  have h22 : u 22 = v 22 := by have := eA1 1 0; simpa [chartA1_4422] using this
  have h23 : u 23 = v 23 := by have := eA1 1 1; simpa [chartA1_4422] using this
  have h24 : u 24 = v 24 := by have := eA1 2 0; simpa [chartA1_4422] using this
  have h25 : u 25 = v 25 := by have := eA1 2 1; simpa [chartA1_4422] using this
  have h26 : u 26 = v 26 := by have := eA1 3 0; simpa [chartA1_4422] using this
  have h27 : u 27 = v 27 := by have := eA1 3 1; simpa [chartA1_4422] using this
  -- pivot u 0 from A2(0,0) (no division)
  have h0 : u 0 = v 0 := by have := eA2 0 0; simpa [chartA2_4422] using this
  -- u 1, u 2, u 3 via ÷ u 0 (A2(0,1) = u 0·u 1, etc.)
  have h1 : u 1 = v 1 := by
    have he := eA2 0 1; simp only [chartA2_4422, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.of_apply, Matrix.cons_val] at he
    rw [h0] at he; exact mul_left_cancel₀ hv0 he
  have h2 : u 2 = v 2 := by
    have he := eA2 1 0; simp only [chartA2_4422, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.of_apply, Matrix.cons_val] at he
    rw [h0] at he; exact mul_left_cancel₀ hv0 he
  have h3 : u 3 = v 3 := by
    have he := eA2 1 1; simp only [chartA2_4422, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.of_apply, Matrix.cons_val] at he
    rw [h0] at he; exact mul_left_cancel₀ hv0 he
  funext j; fin_cases j <;>
    first
    | exact h0 | exact h1 | exact h2 | exact h3 | exact h4 | exact h5 | exact h6 | exact h7
    | exact h8 | exact h9 | exact h10 | exact h11 | exact h12 | exact h13 | exact h14 | exact h15
    | exact h16 | exact h17 | exact h18 | exact h19 | exact h20 | exact h21 | exact h22 | exact h23
    | exact h24 | exact h25 | exact h26 | exact h27

/-- **`phi4422` is injective off `{u 0 = 0}`** (`paramsEquivFlat` a bijection ∘ `chartParams4422_injOn`). -/
theorem phi4422_injOn : Set.InjOn phi4422 {u : Fin 28 → ℝ | u 0 ≠ 0} := by
  intro u hu v hv huv
  exact chartParams4422_injOn hu hv ((paramsEquivFlat M4422).injective huv)

/-- `chartParams4422` is continuous (each layer matrix is a polynomial; `Params` a product). -/
theorem continuous_chartParams4422 : Continuous chartParams4422 := by
  apply continuous_pi
  intro s
  fin_cases s
  · show Continuous chartA0_4422
    unfold chartA0_4422
    refine Continuous.matrixVecCons ?_ (Continuous.matrixVecCons ?_ (Continuous.matrixVecCons ?_
      (Continuous.matrixVecCons ?_ continuous_const)))
    all_goals
      refine Continuous.matrixVecCons ?_ (Continuous.matrixVecCons ?_ (Continuous.matrixVecCons ?_
        (Continuous.matrixVecCons ?_ continuous_const))) <;> fun_prop
  · show Continuous chartA1_4422
    unfold chartA1_4422
    refine Continuous.matrixVecCons ?_ (Continuous.matrixVecCons ?_ (Continuous.matrixVecCons ?_
      (Continuous.matrixVecCons ?_ continuous_const)))
    all_goals
      refine Continuous.matrixVecCons ?_ (Continuous.matrixVecCons ?_ continuous_const) <;> fun_prop
  · show Continuous chartA2_4422
    unfold chartA2_4422
    refine Continuous.matrixVecCons ?_ (Continuous.matrixVecCons ?_ continuous_const)
    all_goals
      refine Continuous.matrixVecCons ?_ (Continuous.matrixVecCons ?_ continuous_const) <;> fun_prop

/-- **`phi4422` is continuous**. -/
theorem continuous_phi4422 : Continuous phi4422 :=
  (continuous_paramsEquivFlat _).comp continuous_chartParams4422

/-- **`phi4422 0 = 0`** — the chart reaches the deepest point (every entry is a monomial in the coords,
vanishing at `u = 0`). -/
theorem phi4422_zero : phi4422 (0 : Fin 28 → ℝ) = 0 := by
  have hchart : chartParams4422 (0 : Fin 28 → ℝ) = (fun _ => 0 : Params M4422) := by
    funext s
    fin_cases s
    · show chartA0_4422 (0 : Fin 28 → ℝ) = 0
      funext i j; fin_cases i <;> fin_cases j <;> simp [chartA0_4422]
    · show chartA1_4422 (0 : Fin 28 → ℝ) = 0
      funext i j; fin_cases i <;> fin_cases j <;> simp [chartA1_4422]
    · show chartA2_4422 (0 : Fin 28 → ℝ) = 0
      funext i j; fin_cases i <;> fin_cases j <;> simp [chartA2_4422]
  rw [phi4422, hchart]
  exact paramsEquivFlat_deepest _

/-- **Image containment**: a small source box `[0,δ]²⁸` maps into `cubeBox 28 ε` (continuity of
`phi4422` + `phi4422 0 = 0`, exactly as `phi334_image_subset_cubeBox`). -/
theorem phi4422_image_subset_cubeBox (ε : ℝ) (hε : 0 < ε) :
    ∃ δ > 0, phi4422 '' (Set.univ.pi (fun _ : Fin 28 => Set.Icc (0 : ℝ) δ)) ⊆ cubeBox 28 ε := by
  have hopen : IsOpen (Set.univ.pi (fun _ : Fin 28 => Set.Ioo (-ε) ε)) :=
    isOpen_set_pi Set.finite_univ (fun _ _ => isOpen_Ioo)
  have hmem : (0 : Fin 28 → ℝ) ∈ phi4422 ⁻¹' (Set.univ.pi (fun _ : Fin 28 => Set.Ioo (-ε) ε)) := by
    simp only [Set.mem_preimage, phi4422_zero, Set.mem_pi, Set.mem_univ, true_implies,
      Set.mem_Ioo, Pi.zero_apply]
    exact fun i => ⟨by linarith, hε⟩
  obtain ⟨δ, hδ, hsub⟩ := cubeBox_subset_of_isOpen (hopen.preimage continuous_phi4422) hmem
  refine ⟨δ, hδ, ?_⟩
  rintro y ⟨x, hx, rfl⟩
  have hxcube : x ∈ cubeBox 28 δ := by
    simp only [cubeBox, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Icc] at hx ⊢
    intro i; exact ⟨le_trans (by linarith [hδ]) (hx i).1, (hx i).2⟩
  have hxmem : phi4422 x ∈ Set.univ.pi (fun _ : Fin 28 => Set.Ioo (-ε) ε) :=
    Set.mem_preimage.mp (hsub hxcube)
  refine Set.mem_pi.mpr (fun i _ => ?_)
  have hi := (Set.mem_pi.mp hxmem) i (Set.mem_univ i)
  rw [Set.mem_Ioo] at hi
  rw [Set.mem_Icc]
  exact ⟨hi.1.le, hi.2.le⟩

/-! ## The genuine geometric change-of-variables for `phi4422` (the `cov` field)

`phi4422` is `InjOn` off `{u 0 = 0}` (`phi4422_injOn`), C¹ (`phi4422_hasFDerivAt`), with structural
determinant `|det Dφ| = |u 0|³` (`phi4422_abs_det`). The c-o-v runs directly on `V \ {u 0 = 0}` — a
PURE radial blow-up needs NO second null-slice (unlike `(3,3,4)`'s `{u 1 = 0}` from the `b = aβ`
factor). -/
theorem phi4422_cov (V : Set (Fin 28 → ℝ)) (hV : MeasurableSet V) (g : (Fin 28 → ℝ) → ℝ≥0∞) :
    ∫⁻ x in phi4422 '' (V \ {x | x 0 = 0}), g x
      = ∫⁻ u in V \ {x | x 0 = 0}, ENNReal.ofReal (∏ j, |u j| ^ (leafH4422 j)) * g (phi4422 u) := by
  set S := V \ {x : Fin 28 → ℝ | x 0 = 0} with hS
  have hSmeas : MeasurableSet S :=
    hV.diff (measurableSet_eq_fun (measurable_pi_apply 0) measurable_const)
  have hcov : ∫⁻ x in phi4422 '' S, g x
      = ∫⁻ u in S, ENNReal.ofReal |(phi4422Deriv u).det| * g (phi4422 u) := by
    refine lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hSmeas
      (fun x _ => (phi4422_hasFDerivAt x).hasFDerivWithinAt) ?_ g
    intro x hx y hy hxy
    exact phi4422_injOn hx.2 hy.2 hxy
  rw [hcov]
  refine setLIntegral_congr_fun hSmeas (fun u _ => ?_)
  rw [phi4422_abs_det, leafH4422_prod_eq]

/-- `Uval4422` is bounded above on the source box `[0,δ]²⁸` (continuous on a compact box). -/
theorem Uval4422_le_on_box (δ : ℝ) :
    ∃ B, 0 < B ∧ ∀ u ∈ Set.univ.pi (fun _ : Fin 28 => Set.Icc (0 : ℝ) δ), Uval4422 u ≤ B := by
  have hcpt : IsCompact (Set.univ.pi (fun _ : Fin 28 => Set.Icc (0 : ℝ) δ)) :=
    isCompact_univ_pi (fun _ => isCompact_Icc)
  rcases (Set.univ.pi (fun _ : Fin 28 => Set.Icc (0 : ℝ) δ)).eq_empty_or_nonempty with he | hne
  · exact ⟨1, one_pos, fun u hu => absurd (he ▸ hu) (Set.mem_empty_iff_false u).mp⟩
  · obtain ⟨u0, _, hu0⟩ := hcpt.exists_isMaxOn hne continuous_Uval4422.continuousOn
    exact ⟨max 1 (Uval4422 u0), lt_of_lt_of_le one_pos (le_max_left _ _),
      fun u hu => le_trans (hu0 hu) (le_max_right _ _)⟩

/-! ## The `NodeAchieverChart M4422` instance + the atom discharge -/

/-- **The `(4,4,2,2)` achiever chart bundle** (`phi = phi4422` the pure radial blow-up of the deepest
factor, binding axis `0`, unit `Uval4422`, the radial Jacobian `|u 0|³`).

The chart is the cleanest `L ≥ 3` node — a SINGLE `pivotBlowupOn` of the 4 deepest-factor coords, no
Schur shear (descent codims `0,0,4`). The factorization `F∘phi4422 = u₀²·U` (`routeMCore_phi4422`), the
threshold `2 = ½·minAdm` (`leafH4422_pivot` + the structure's `nodeChart_thresholdLe`), the
leaf-integrand (`leaf_integrand4422`), the `U > 0` a.e. (`Uval4422_ae_pos`, the genuine-polynomial
null-zero-set route), the image containment (`phi4422_image_subset_cubeBox`), and the genuine c-o-v
(`phi4422_cov`, with the structural determinant `|det Dφ| = |u 0|³` = `pivotBlowupOn_abs_det` at
`active.card = minAdm = 4`) are all banked sorry-free. The `det ≠ 0` off `{u 0 = 0}` (the degenerate-chart
guard) holds genuinely (`|det Dφ| = |u 0|³ ≠ 0` for `u 0 ≠ 0`; `phi4422_injOn`). -/
noncomputable def nodeChart4422 : NodeAchieverChart M4422 where
  hpos := by rw [minAdm_M4422]; norm_num
  phi := phi4422
  p := (0 : Fin 28)
  leafH := leafH4422
  leafH_pivot := leafH4422_pivot
  Ufun := Uval4422
  Ubound := fun δ => by
    obtain ⟨B, hB0, hBle⟩ := Uval4422_le_on_box δ
    refine ⟨B, hB0, hBle, ?_⟩
    -- `0 < Uval4422` a.e. on the box (the global a.e.-positivity, restricted)
    exact ae_restrict_of_ae Uval4422_ae_pos
  Umeas := continuous_Uval4422.measurable
  leaf_integrand := leaf_integrand4422
  cov := phi4422_cov
  image_subset := phi4422_image_subset_cubeBox

/-- **The `(4,4,2,2)` achiever box-divergence** — `∫⁻_{cubeBox 28 ε} |routeMCore M4422|^{−c'} = ⊤` for
`c'` at-or-above the achiever threshold `2 = ½·minAdm M4422`, every `ε > 0`. This is the atom
`routeMCore_box_diverges_achiever` discharged for `M = (4,4,2,2)`, via the chart bundle `nodeChart4422`
fed through the M-agnostic assembly `routeMCore_box_diverges_of_nodeChart`. The cleanest `L = 3` node
(pure radial blow-up of the deepest factor).

The soundness-critical content is banked sorry-free: the EXACT factorization `routeMCore M4422 (phi4422 u)
= (u 0)²·U` (`routeMCore_phi4422`, off the verified-exact `dlnLoss_chartParams4422`), the genuine
structural determinant `|det Dφ| = |u 0|³` (`phi4422_abs_det`, `pivotBlowupOn_abs_det` at
`minAdm = active.card = 4` ∘ the measure-preserving outer reshape `Q4422CLM_abs_det`), the `U > 0` a.e.
(`Uval4422_ae_pos`), the binding-monomial threshold `2` (`leafH4422_pivot` + `nodeChart_thresholdLe`),
and the divergence assembly (feeding the single cited leaf atom `monomial_rlct` via
`monomialIntegrand_lintegral_box_eq_top`). -/
theorem routeM4422_box_diverges (c' : NNReal) (hc' : (minAdm M4422 : ℝ≥0∞) / 2 ≤ (c' : ℝ≥0∞))
    (ε : ℝ) (hε : 0 < ε) :
    ∫⁻ x in cubeBox (routeMAmbient M4422) ε,
      ENNReal.ofReal (|routeMCore M4422 x| ^ (-(c' : ℝ))) = ⊤ :=
  routeMCore_box_diverges_of_nodeChart M4422 nodeChart4422 c' hc' ε hε

/-- **`routeMCore_box_diverges_achiever` for `M = (4,4,2,2)`** — the atom (`RouteMLayerCoverGE.lean`)
discharged at the binding `L = 3` node `(4,4,2,2)`, stated in the atom's own shape (the
`(minAdm M : ℝ≥0∞)/2 ≤ c'` premise). The instance, NOT the general-`M` atom (which needs the uniform
`φ_M`, designed separately). -/
theorem routeMCore_box_diverges_achiever_4422 (c' : NNReal)
    (hc' : (minAdm M4422 : ℝ≥0∞) / 2 ≤ (c' : ℝ≥0∞)) (ε : ℝ) (hε : 0 < ε) :
    ∫⁻ x in cubeBox (routeMAmbient M4422) ε,
      ENNReal.ofReal (|routeMCore M4422 x| ^ (-(c' : ℝ))) = ⊤ :=
  routeM4422_box_diverges c' hc' ε hε

/-- **The `(4,4,2,2)` cross-check** (the cert's order-(a) witness): `minAdm = 4`, binding axis
`(k,h) = (1,3)`, threshold `2 = ½·minAdm`; at `c' = 2` the leaf exponent on `u 0` is `3 − 2·1·2 = −1`
(the sharp `∫ u₀⁻¹ = ⊤`). The box integral diverges at `c' = 2` (and above), every `ε > 0`. -/
theorem routeM4422_box_diverges_at_two (ε : ℝ) (hε : 0 < ε) :
    ∫⁻ x in cubeBox (routeMAmbient M4422) ε,
      ENNReal.ofReal (|routeMCore M4422 x| ^ (-(2 : ℝ))) = ⊤ := by
  have hle : (minAdm M4422 : ℝ≥0∞) / 2 ≤ ((2 : NNReal) : ℝ≥0∞) := by
    rw [minAdm_M4422]
    rw [show ((4 : ℕ) : ℝ≥0∞) = 2 * 2 by norm_num,
      ENNReal.mul_div_cancel_right (by norm_num) (by norm_num)]
    norm_num
  have h := routeM4422_box_diverges 2 hle ε hε
  rwa [show ((2 : NNReal) : ℝ) = (2 : ℝ) by norm_num] at h

end DLNFibre.DLN.RLCT
