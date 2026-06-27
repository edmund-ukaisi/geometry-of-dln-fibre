import DLNFibre.DLN.RLCT.Validate.NodeAchieverChart
import DLNFibre.DLN.RLCT.Foundations.ParamsReshapeMP
import DLNFibre.Core.MeasureTheory.PolynomialZeroSet
import Mathlib.Algebra.MvPolynomial.Basic

/-!
# `RouteM221` — the `(2,2,1)` achiever box-divergence (the layered validate-small for the option-(C) chart)

The smallest genuinely-layered achiever node, `M = (2,2,1)`, built END-TO-END through the general
machinery the option-(C) certificate prescribes (`threads/36-genM-jacobian-det/certificate-{decoder-fix,
achiever-path}.md`). It discharges the achiever-path box-divergence atom
`routeMCore_box_diverges_achiever` (`RouteMLayerCoverGE.lean`) for `M = (2,2,1)` by constructing a
`NodeAchieverChart M221` and feeding it through the M-agnostic assembly
`routeMCore_box_diverges_of_nodeChart`.

## The construction (`M = (2,2,1)`; `minAdm = 2`, `flatDim = 6`)

`routeMCore M221 = ‖A0·A1‖²` with `A0 : 2×2` (layer 0), `A1 : 2×1` (layer 1); the product `A0·A1`
is `2×1`. The achiever center has codim `minAdm = 2` (`minAdm(2,2,1) = min_t[(2−t)² + t·1] = 2`, at
`t = 1`). The option-(C) chart blows up that codim-`2` center radially by ONE pivot `u 0`, placing the
two radial-active coords in the deepest factor `A1` (the `§4b` validated shape):

    A1 = !![u 0; u 0 · u 1]     (deepest factor: entry (0,0)=u₀ scales the FIXED 1, entry (1,0)=u₀·u₁ active),
    A0 = !![u 2, u 3; u 4, u 5]  (free spectators),
    A0·A1 = u₀ · (A0 · !![1; u 1]),  so  F = ‖A0·A1‖² = u₀² · U,  U = ‖A0·!![1; u 1]‖² (u₀-free).

`|det Dφ| = |u 0|¹ = |u 0|^{minAdm−1}` (a codim-`2` radial blow-up: `pivotBlowupOnDeriv_det` at
`active.card = minAdm = 2`). Binding axis `(k,h) = (1, 1) = (1, minAdm−1)`, threshold
`(1+1)/(2·1) = 1 = ½·minAdm`. At `c' = 1` the leaf exponent on `u 0` is `1 − 2·1·1 = −1` (the sharp
`∫ u₀⁻¹ = ⊤`).

This is the `(4,4,2,2)` pure-radial spine (`RouteM4422`) on the smallest LAYERED node (`L = 2`,
nontrivial `A0·A1` matrix product), exercising BOTH the RATE field (`leaf_integrand`) and the DET field
(`cov`) through the general option-(C) bricks: `pivotBlowupOn` (radial), the measure-preserving
`pack` via `measurePreserving_paramsPack_of_flatIdxEquiv` with a genuine `Fin 6 ≃ FlatIdx M221`, the
linear reshape `Q221CLM` (`|det| = 1`), and the genuine-polynomial `U > 0` a.e. route.

Verified EXACT in flat coordinates (sympy, certificate §4b): `F = u₀²·U`, `det Dφ = u₀` so
`|det| = |u₀|¹ = |u₀|^{minAdm−1}`, and `U` matches the certificate's `U` exactly.
-/

open MeasureTheory
open scoped ENNReal BigOperators

namespace DLNFibre.DLN.RLCT

/-- `M221 = (2,2,1)` (the smallest genuinely-layered achiever node). -/
abbrev M221 : Fin 3 → ℕ := ![2, 2, 1]

theorem minAdm_M221 : minAdm M221 = 2 := by
  rw [← minAdmRec_eq_minAdm]; decide

theorem flatDim_M221 : flatDim M221 = 6 := by decide

theorem routeMAmbient_M221 : routeMAmbient M221 = 6 := by decide

/-! ## The 2-layer product entry form -/

/-- **The `L = 2` layer-product entry form** `(prod M A) i j = ∑_{k1} A₀(i,k1)·A₁(k1,j)` — the explicit
two-matrix product `A⁽⁰⁾·A⁽¹⁾` (the general-`M` `L = 2` form; one `mul_apply` level over the dependent
`prodAux` cast closer, mirroring `prod_three_layer4422`). -/
theorem prod_two_layer221 (M : Fin 3 → ℕ) (A : Params M) (i : Fin (M 0)) (j : Fin (M 2)) :
    prod M A i j = ∑ k1 : Fin (M 1), A 0 i k1 * A 1 k1 j := by
  unfold prod
  simp only [prodAux, Matrix.mul_apply, eq_mpr_eq_cast]
  refine Finset.sum_congr rfl (fun k1 _ => ?_)
  congr 2
  convert congrFun (congrFun (Matrix.one_mul (cast (by rfl) (cast (by rfl) (A 0)))) i) k1 using 2

/-! ## The chart matrices (radial blow-up of the deepest factor) -/

/-- **The layer-`0` matrix `A⁽⁰⁾`** (2×2, free spectators): coords `u 2, u 3, u 4, u 5` in row-major. -/
noncomputable def chartA0_221 (u : Fin 6 → ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![u 2, u 3; u 4, u 5]

/-- **The layer-`1` matrix `A⁽¹⁾`** (2×1): the radial blow-up `A1 = !![u₀; u₀·u₁]` of the deepest
factor. Pivot `u 0` (scaling the fixed `1` of the residual direction); the 1 angular coord `u 1`. -/
noncomputable def chartA1_221 (u : Fin 6 → ℝ) : Matrix (Fin 2) (Fin 1) ℝ :=
  !![u 0; u 0 * u 1]

/-- The genuine `Params M221`, assembled by `Fin.cons` over the two layers. -/
noncomputable def chartParams221 (u : Fin 6 → ℝ) : Params M221 :=
  Fin.cons (chartA0_221 u)
    (Fin.cons (chartA1_221 u) (fun i => i.elim0))

/-- The post-blow-up unit factor `U = ‖A0·M1bar‖²` (the `u₀`-free factor of `F = u₀²·U`), written in
the `prod_two_layer221` entry shape with `M1bar = !![1; u 1]` (the deepest factor with the pivot `u₀`
stripped). A polynomial in the 5 angular/free coords. -/
noncomputable def Uval221 (u : Fin 6 → ℝ) : ℝ :=
  ∑ i : Fin 2, ∑ j : Fin 1,
    (∑ k1 : Fin 2,
      chartA0_221 u i k1 * (!![1; u 1] : Matrix (Fin 2) (Fin 1) ℝ) k1 j) ^ 2

/-- **The deepest-factor entrywise pivot** `A1(k1,j) = u 0 · M1bar(k1,j)` (the radial blow-up: each of
the 2 deepest-factor entries carries one `u 0`). -/
theorem chartA1_221_eq (u : Fin 6 → ℝ) (k1 : Fin 2) (j : Fin 1) :
    chartA1_221 u k1 j = u 0 * (!![1; u 1] : Matrix (Fin 2) (Fin 1) ℝ) k1 j := by
  fin_cases k1 <;> fin_cases j <;> simp [chartA1_221]

/-- **The per-entry pivot factorization.** Each product entry of the chart factors as
`u 0 · (the un-blown entry)`: the deepest factor `A1 = u₀·M1bar` contributes one `u 0` per entry. -/
theorem prod_chartParams221_entry (u : Fin 6 → ℝ) (i : Fin 2) (j : Fin 1) :
    prod M221 (chartParams221 u) i j
      = u 0 * (∑ k1 : Fin 2,
          chartA0_221 u i k1 * (!![1; u 1] : Matrix (Fin 2) (Fin 1) ℝ) k1 j) := by
  rw [prod_two_layer221 M221 (chartParams221 u) i j, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k1 _ => ?_)
  have hA0 : (chartParams221 u) 0 = chartA0_221 u := rfl
  have hA1 : (chartParams221 u) 1 = chartA1_221 u := rfl
  rw [hA0, hA1, chartA1_221_eq]
  ring

/-- **The loss factorization (EXACT, sorry-free).** `dlnLoss M221 0 (chartParams221 u) = (u 0)² · U`
with `U = Uval221 u` (the `u₀`-free unit). Each of the 2 product entries equals `u₀ · (un-blown
entry)` (`prod_chartParams221_entry`), so `(entry)² = u₀² · (un-blown entry)²` and the squared
Frobenius norm is `u₀² · Uval221`. The soundness-critical `F = u²·U` identity. -/
theorem dlnLoss_chartParams221 (u : Fin 6 → ℝ) :
    dlnLoss M221 0 (chartParams221 u) = (u 0) ^ 2 * Uval221 u := by
  unfold dlnLoss
  simp only [Matrix.sub_apply, Matrix.zero_apply, sub_zero]
  rw [Uval221, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [prod_chartParams221_entry]
  ring

/-- **The genuine achiever flat chart for `(2,2,1)`** `phi221 := paramsEquivFlat M221 ∘ chartParams221`,
an `(Fin 6 → ℝ) → (Fin 6 → ℝ)` map (`routeMAmbient M221 = 6`). -/
noncomputable def phi221 (u : Fin 6 → ℝ) : Fin 6 → ℝ :=
  paramsEquivFlat M221 (chartParams221 u)

/-- **The `routeMCore` factorization (EXACT, sorry-free).** `routeMCore M221 (phi221 u) = (u 0)² · U`
(`U = Uval221 u`): `routeMCore M = dlnLoss M 0 ∘ (paramsEquivFlat).symm`, `phi221 = paramsEquivFlat ∘
chartParams221`, the `symm`/`apply` cancel, leaving `dlnLoss M221 0 (chartParams221 u)` —
`dlnLoss_chartParams221`. The soundness-critical `F ∘ phi = u²·U` identity. -/
theorem routeMCore_phi221 (u : Fin 6 → ℝ) :
    routeMCore M221 (phi221 u) = (u 0) ^ 2 * Uval221 u := by
  rw [routeMCore, phi221, MeasurableEquiv.symm_apply_apply, dlnLoss_chartParams221]

/-- **`Uval221 ≥ 0`** (a sum of squares). -/
theorem Uval221_nonneg (u : Fin 6 → ℝ) : (0 : ℝ) ≤ Uval221 u := by
  rw [Uval221]; positivity

/-- `Uval221` is continuous (a polynomial in the chart coordinates), hence measurable. -/
theorem continuous_Uval221 : Continuous Uval221 := by
  unfold Uval221 chartA0_221
  simp only [Fin.sum_univ_two, Fin.sum_univ_one, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.of_apply, Matrix.cons_val, Matrix.head_fin_const, Matrix.cons_val']
  fun_prop

/-! ## The `U > 0` a.e. positivity (the genuine-polynomial null-zero-set route)

Every product entry of `A0·M1bar` is bilinear in the free `A0` coords and `u 1`, so there is NO clean
single-coordinate lower bound. `U = eval u UPoly221` for a nonzero `MvPolynomial`, so `{U = 0}` is
Lebesgue-null (`MvPolynomial.ae_eval_ne_zero`, the Core brick). -/

open MvPolynomial in
/-- The formal polynomial `UPoly221 : MvPolynomial (Fin 6) ℝ` with `eval u UPoly221 = Uval221 u`: the
`Uval221` expression with `X k` for coord `k` and the deepest factor `M1bar = !![C 1; X 1]` (the pivot
`u₀` stripped). -/
noncomputable def UPoly221 : MvPolynomial (Fin 6) ℝ :=
  ∑ i : Fin 2, ∑ j : Fin 1,
    (∑ k1 : Fin 2,
      (!![X 2, X 3; X 4, X 5] : Matrix (Fin 2) (Fin 2) (MvPolynomial (Fin 6) ℝ)) i k1
        * (!![C 1; X 1] : Matrix (Fin 2) (Fin 1) (MvPolynomial (Fin 6) ℝ)) k1 j) ^ 2

open MvPolynomial in
/-- `eval u UPoly221 = Uval221 u` — the encoding identity (`eval` a ring hom: distributes over sums /
products / squares; `eval u (X k) = u k`, `eval u (C 1) = 1`; the matrix accessors match
`chartA0_221`/`M1bar` entrywise). -/
theorem eval_UPoly221 (u : Fin 6 → ℝ) : MvPolynomial.eval u UPoly221 = Uval221 u := by
  rw [UPoly221, Uval221, chartA0_221]
  simp only [map_sum, map_pow, map_mul]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  refine congrArg (· ^ 2) (Finset.sum_congr rfl (fun k1 _ => ?_))
  fin_cases i <;> fin_cases k1 <;> fin_cases j <;>
    simp [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.of_apply,
      Matrix.cons_val, Matrix.head_fin_const, Matrix.cons_val', MvPolynomial.eval_X,
      MvPolynomial.eval_C]

open MvPolynomial in
/-- **`UPoly221 ≠ 0`** — the witness `u₀-free` point `A0 = I₂` (coords `u 2 = u 5 = 1`, `u 3 = u 4 = 0`),
`M1bar = !![1; 0]` (i.e. `u 1 = 0`): then `A0·M1bar = !![1; 0]`, so `Uval221 = 1² + 0² = 1 ≠ 0`. Hence
the formal polynomial is nonzero. -/
theorem UPoly221_ne_zero : UPoly221 ≠ 0 := by
  intro h0
  set w : Fin 6 → ℝ := Pi.single 2 1 + Pi.single 5 1 with hw
  have hval : Uval221 w = 1 := by
    rw [Uval221, chartA0_221]
    simp only [Fin.sum_univ_two, Fin.sum_univ_one, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.of_apply, Matrix.cons_val, Matrix.head_fin_const, Matrix.cons_val']
    simp only [hw, Pi.add_apply, Pi.single_apply, Fin.reduceEq, if_true, if_false]
    norm_num
  have : MvPolynomial.eval w UPoly221 = 1 := by rw [eval_UPoly221]; exact hval
  rw [h0] at this; simp at this

/-- **`Uval221 > 0` a.e.** (the soundness-critical positivity). `Uval221 = eval · UPoly221` with
`UPoly221 ≠ 0`, so `{Uval221 = 0}` is Lebesgue-null (`MvPolynomial.ae_eval_ne_zero`); off that null set
`U ≥ 0` is `> 0`. -/
theorem Uval221_ae_pos : ∀ᵐ u : Fin 6 → ℝ, 0 < Uval221 u := by
  have hae := MvPolynomial.ae_eval_ne_zero UPoly221 UPoly221_ne_zero
  filter_upwards [hae] with u hu
  rw [eval_UPoly221] at hu
  exact lt_of_le_of_ne (Uval221_nonneg u) (Ne.symm hu)

/-! ## The single-axis binding monomial (the `(2,2,1)` leaf, radial blow-up) -/

/-- The `(2,2,1)` leaf Jacobian exponents on `Fin 6` (`= Fin (routeMAmbient M221)` defeq): `h = 1`
on the binding pivot axis `0` (the radial blow-up determinant `|u 0|¹ = |u 0|^{minAdm−1}`); `0` on the
5 spectator axes (the radial blow-up has NO spectator monomial — both blown-up coords sit at the pivot
exponent). -/
def leafH221 : Fin 6 → ℕ := fun j => if j = 0 then 1 else 0

/-- `leafH221 0 = 1 = minAdm M221 − 1` (the binding axis carries the radial exponent). -/
theorem leafH221_pivot : leafH221 (0 : Fin 6) = minAdm M221 - 1 := by
  rw [minAdm_M221]; rfl

/-- **The Jacobian weight `∏_j |u_j|^{leafH221 j} = |u 0|¹`** — the genuine `|det Dφ|` of the radial
blow-up (the pivot exceptional divisor `¹`); the 5 spectator axes contribute `|·|⁰ = 1`. -/
theorem leafH221_prod_eq (u : Fin 6 → ℝ) :
    (∏ j, |u j| ^ (leafH221 j)) = |u 0| ^ 1 := by
  rw [Finset.prod_eq_single (0 : Fin 6)]
  · simp [leafH221]
  · intro j _ hj; simp [leafH221, hj]
  · intro h; exact absurd (Finset.mem_univ (0 : Fin 6)) h

/-- **Single-axis monomial evaluation.** `monomialIntegrand 6 (nodeLeafK 6 0) leafH221 c u =
|u 0|¹ · (|u 0|²)^{−c}` — the loss base `|u 0|²` (`k = 1` at axis `0`) against the radial Jacobian
`|u 0|¹`. The 5 spectator axes contribute `1`. -/
theorem monomialIntegrand_leaf221_eq (c : ℝ) (u : Fin 6 → ℝ) :
    monomialIntegrand 6 (nodeLeafK 6 0) leafH221 c u
      = (|u 0| ^ 1) * (|u 0| ^ 2) ^ (-c) := by
  unfold monomialIntegrand
  rw [leafH221_prod_eq]
  congr 1
  rw [Finset.prod_eq_single (0 : Fin 6)]
  · simp [nodeLeafK]
  · intro j _ hj; simp [nodeLeafK, hj]
  · intro h; exact absurd (Finset.mem_univ (0 : Fin 6)) h

/-- **The leaf-integrand identity for the `(2,2,1)` achiever chart**: `(∏_j |u_j|^{leafH221 j}) ·
|routeMCore M221 (phi221 u)|^{−c} = monomialIntegrand · (Uval221 u)^{−c}` — the radial Jacobian
`|u 0|¹` against the unit power. Via `routeMCore_phi221` (`F∘phi = u₀²·U`) +
`monomialIntegrand_leaf221_eq`. -/
theorem leaf_integrand221 (c : ℝ) (u : Fin 6 → ℝ) :
    (∏ j, |u j| ^ (leafH221 j)) * |routeMCore M221 (phi221 u)| ^ (-c)
      = monomialIntegrand 6 (nodeLeafK 6 0) leafH221 c u * (Uval221 u) ^ (-c) := by
  rw [monomialIntegrand_leaf221_eq, leafH221_prod_eq, routeMCore_phi221]
  have hUnn : (0 : ℝ) ≤ Uval221 u := Uval221_nonneg u
  rw [abs_of_nonneg (mul_nonneg (sq_nonneg _) hUnn),
    Real.mul_rpow (sq_nonneg _) hUnn, ← sq_abs (u 0)]
  ring

/-! ## The radial blow-up reshape + the chart Jacobian determinant `|det Dφ| = |u 0|¹`

`phi221 = paramsEquivFlat ∘ chartParams221 = paramsEquivFlat ∘ pack221 ∘ pb221 = Q221 ∘ pb221`, where
`pb221 = pivotBlowupOn {0,1} 0` is the radial blow-up of the 2 deepest-factor coords (det
`u₀¹ = u₀^{minAdm−1}`, `pivotBlowupOnDeriv_det` at `active.card = 2`), `pack221` reshapes the 6 flat
coords into the matrix slots, and `Q221 = paramsEquivFlat ∘ pack221` is measure-preserving (`|det| = 1`). -/

/-- **The `(2,2,1)` radial blow-up** `pb221 = pivotBlowupOn {0,1} 0`: blow up the 2 deepest-factor coords
(the `A1` entries) by the pivot `u 0`. `det = u₀¹ = u₀^{minAdm−1}` (a codim-`2` center). -/
noncomputable def pb221 : (Fin 6 → ℝ) → (Fin 6 → ℝ) :=
  pivotBlowupOn ({0, 1} : Finset (Fin 6)) 0

/-- **`pb221` as an explicit vector** (per-coordinate `if`-reduction). -/
theorem pb221_apply (u : Fin 6 → ℝ) :
    pb221 u = ![u 0, u 0 * u 1, u 2, u 3, u 4, u 5] := by
  funext i
  fin_cases i <;> simp [pb221, pivotBlowupOn, Matrix.cons_val]

/-- **`pack221`** — the reshape `(Fin 6 → ℝ) → Params M221` sending the 6 flat coords (in the chart slot
order: coords `0,1` ↦ `A1`, `2,3,4,5` ↦ `A0`) to the matrix entries, matching `chartParams221`'s output
layout. Linear (each output entry is one input coord). -/
noncomputable def pack221 (w : Fin 6 → ℝ) : Params M221 :=
  Fin.cons
    (!![w 2, w 3; w 4, w 5] : Matrix (Fin 2) (Fin 2) ℝ)
    (Fin.cons
      (!![w 0; w 1] : Matrix (Fin 2) (Fin 1) ℝ)
      (fun i => i.elim0))

/-- **The factorization identity** `chartParams221 = pack221 ∘ pb221` (the load-bearing diffeo
factorization; per-layer `funext` + `fin_cases` on the 6 entries). -/
theorem chartParams221_eq_pack_pb (u : Fin 6 → ℝ) :
    chartParams221 u = pack221 (pb221 u) := by
  funext s
  fin_cases s
  · show chartA0_221 u = (pack221 (pb221 u)) 0
    have hp : (pack221 (pb221 u)) 0
        = (!![(pb221 u) 2, (pb221 u) 3; (pb221 u) 4, (pb221 u) 5] : Matrix (Fin 2) (Fin 2) ℝ) := rfl
    rw [hp, pb221_apply]
    funext i j
    fin_cases i <;> fin_cases j <;> simp [chartA0_221]
  · show chartA1_221 u = (pack221 (pb221 u)) 1
    have hp : (pack221 (pb221 u)) 1
        = (!![(pb221 u) 0; (pb221 u) 1] : Matrix (Fin 2) (Fin 1) ℝ) := rfl
    rw [hp, pb221_apply]
    funext i j
    fin_cases i <;> fin_cases j <;> simp [chartA1_221]

/-- **The radial-blow-up determinant for `(2,2,1)`** `|det D(pb221)| = |u 0|¹ = |u 0|^{minAdm−1}`
(the codim-`2` center; `active.card = 2`). -/
theorem pb221_abs_det (u : Fin 6 → ℝ) :
    |(pivotBlowupOnDeriv ({0, 1} : Finset (Fin 6)) 0 u).det| = |u 0| ^ 1 := by
  rw [show |(pivotBlowupOnDeriv ({0, 1} : Finset (Fin 6)) 0 u).det|
        = |u 0| ^ (({0, 1} : Finset (Fin 6)).card - 1) by
    rw [pivotBlowupOnDeriv_det _ _ (by decide), abs_pow]]
  norm_num [show ({0, 1} : Finset (Fin 6)).card = 2 from by decide]

/-! ## The outer reindex `Q221 = paramsEquivFlat ∘ pack221` (measure-preserving, `|det| = 1`) -/

/-- `pack221` as a continuous ℝ-linear map (each output matrix entry is one input coordinate). -/
noncomputable def pack221CLM : (Fin 6 → ℝ) →L[ℝ] Params M221 :=
  ContinuousLinearMap.pi (fun s =>
    match s with
    | ⟨0, _⟩ => ContinuousLinearMap.pi (fun i => ContinuousLinearMap.pi (fun j =>
        ContinuousLinearMap.proj
          (![![2, 3], ![4, 5]] i j : Fin 6)))
    | ⟨1, _⟩ => ContinuousLinearMap.pi (fun i => ContinuousLinearMap.pi (fun j =>
        ContinuousLinearMap.proj
          (![![0], ![1]] i j : Fin 6)))
    | ⟨n + 2, h⟩ => absurd h (by omega))

/-- `pack221CLM` has underlying function `pack221`. -/
theorem pack221CLM_coe : ⇑pack221CLM = pack221 := by
  funext w s
  fin_cases s
  · funext i j; fin_cases i <;> fin_cases j <;> rfl
  · funext i j; fin_cases i <;> fin_cases j <;> rfl

/-- **The outer-reindex CLM** `Q221CLM = paramsEquivFlatCLE ∘ pack221CLM`. -/
noncomputable def Q221CLM : (Fin 6 → ℝ) →L[ℝ] (Fin 6 → ℝ) :=
  (paramsEquivFlatCLE M221).toContinuousLinearMap.comp pack221CLM

/-- The explicit slot bijection `Fin 6 ≃ FlatIdx M221` pinning `pack221`'s flat-coord → matrix-slot
order: coords `0,1` ↦ layer-`1` (`A1`) entries `(1,0,0)`,`(1,1,0)`; coords `2,3,4,5` ↦ layer-`0`
(`A0`) entries in row-major. A GENUINE `Equiv` (`left_inv`/`right_inv` by `decide`) — NO dead slots
(every flat coord lands in exactly one matrix entry, the guard against the decoder dead-slot bug). -/
noncomputable def fin6EquivFlatIdx221 : Fin 6 ≃ FlatIdx M221 where
  toFun := fun k =>
    match k with
    | ⟨0,_⟩ => ⟨⟨⟨1,by decide⟩,⟨0,by decide⟩⟩,⟨0,by decide⟩⟩
    | ⟨1,_⟩ => ⟨⟨⟨1,by decide⟩,⟨1,by decide⟩⟩,⟨0,by decide⟩⟩
    | ⟨2,_⟩ => ⟨⟨⟨0,by decide⟩,⟨0,by decide⟩⟩,⟨0,by decide⟩⟩
    | ⟨3,_⟩ => ⟨⟨⟨0,by decide⟩,⟨0,by decide⟩⟩,⟨1,by decide⟩⟩
    | ⟨4,_⟩ => ⟨⟨⟨0,by decide⟩,⟨1,by decide⟩⟩,⟨0,by decide⟩⟩
    | ⟨5,_⟩ => ⟨⟨⟨0,by decide⟩,⟨1,by decide⟩⟩,⟨1,by decide⟩⟩
    | ⟨n+6,h⟩ => absurd h (by omega)
  invFun := fun q =>
    match q with
    | ⟨⟨⟨1,_⟩,⟨0,_⟩⟩,⟨0,_⟩⟩ => 0
    | ⟨⟨⟨1,_⟩,⟨1,_⟩⟩,⟨0,_⟩⟩ => 1
    | ⟨⟨⟨0,_⟩,⟨0,_⟩⟩,⟨0,_⟩⟩ => 2
    | ⟨⟨⟨0,_⟩,⟨0,_⟩⟩,⟨1,_⟩⟩ => 3
    | ⟨⟨⟨0,_⟩,⟨1,_⟩⟩,⟨0,_⟩⟩ => 4
    | ⟨⟨⟨0,_⟩,⟨1,_⟩⟩,⟨1,_⟩⟩ => 5
  left_inv := by decide
  right_inv := by decide

/-- **The slot equation** `pack221 w q.1.1 q.1.2 q.2 = w (fin6EquivFlatIdx221.symm q)` (`rfl` per slot).
The `hpack` hypothesis of `measurePreserving_paramsPack_of_flatIdxEquiv`. -/
theorem hpack221 (w : Fin 6 → ℝ) (q : FlatIdx M221) :
    pack221 w q.1.1 q.1.2 q.2 = w (fin6EquivFlatIdx221.symm q) := by
  obtain ⟨⟨s, i⟩, j⟩ := q
  fin_cases s <;> fin_cases i <;> fin_cases j <;> rfl

/-- **`pack221` is measure-preserving** — the reusable reshape-MP at `fin6EquivFlatIdx221`. -/
theorem measurePreserving_pack221 :
    MeasurePreserving pack221 (volume : Measure (Fin 6 → ℝ)) (volume : Measure (Params M221)) :=
  measurePreserving_paramsPack_of_flatIdxEquiv M221 fin6EquivFlatIdx221 pack221 hpack221

/-- **`Q221CLM = paramsEquivFlat ∘ pack221` is measure-preserving.** -/
theorem measurePreserving_Q221CLM :
    MeasurePreserving (Q221CLM : (Fin 6 → ℝ) → (Fin 6 → ℝ))
      (volume : Measure (Fin 6 → ℝ)) volume := by
  have hcomp : (Q221CLM : (Fin 6 → ℝ) → (Fin 6 → ℝ))
      = (paramsEquivFlat M221) ∘ pack221 := by
    funext w
    have h1 : Q221CLM w = paramsEquivFlatCLE M221 (pack221CLM w) := rfl
    rw [Function.comp_apply, h1, paramsEquivFlatCLE_coe, pack221CLM_coe]
  rw [hcomp]
  exact (measurePreserving_paramsEquivFlat _).comp measurePreserving_pack221

/-- **`|det Q221CLM| = 1`** — the outer reshape is a measure-preserving coordinate permutation. -/
theorem Q221CLM_abs_det : |LinearMap.det (Q221CLM : (Fin 6 → ℝ) →ₗ[ℝ] (Fin 6 → ℝ))| = 1 :=
  continuousLinearMap_abs_det_eq_one_of_measurePreserving Q221CLM measurePreserving_Q221CLM

/-! ## The chart fderiv `phi221` + the structural determinant `|det Dφ| = |u 0|¹` -/

/-- **`pb221` has fderiv `pivotBlowupOnDeriv {0,1} 0`**. -/
theorem pb221_hasFDerivAt (u : Fin 6 → ℝ) :
    HasFDerivAt pb221 (pivotBlowupOnDeriv ({0, 1} : Finset (Fin 6)) 0 u) u :=
  hasFDerivWithinAt_univ.mp (pivotBlowupOn_hasFDerivWithinAt _ _ Set.univ u)

/-- `pack221` (linear) has constant fderiv `pack221CLM`. -/
theorem pack221_hasFDerivAt (w : Fin 6 → ℝ) : HasFDerivAt pack221 pack221CLM w := by
  have h : HasFDerivAt (⇑pack221CLM) pack221CLM w := pack221CLM.hasFDerivAt
  exact h.congr_of_eventuallyEq (by filter_upwards with v; rw [pack221CLM_coe])

/-- **The `(2,2,1)` chart fderiv** `phi221Deriv u = Q221CLM ∘L pb221Deriv u`. -/
noncomputable def phi221Deriv (u : Fin 6 → ℝ) : (Fin 6 → ℝ) →L[ℝ] (Fin 6 → ℝ) :=
  Q221CLM.comp (pivotBlowupOnDeriv ({0, 1} : Finset (Fin 6)) 0 u)

/-- **`phi221` has fderiv `phi221Deriv`** — the chain rule for `phi221 = paramsEquivFlat ∘ pack221 ∘
pb221` (`= Q221 ∘ pb221`). -/
theorem phi221_hasFDerivAt (u : Fin 6 → ℝ) : HasFDerivAt phi221 (phi221Deriv u) u := by
  have hchart : HasFDerivAt chartParams221 (pack221CLM.comp
      (pivotBlowupOnDeriv ({0, 1} : Finset (Fin 6)) 0 u)) u := by
    have hcomp : HasFDerivAt (fun v => pack221 (pb221 v))
        (pack221CLM.comp (pivotBlowupOnDeriv ({0, 1} : Finset (Fin 6)) 0 u)) u :=
      (pack221_hasFDerivAt (pb221 u)).comp u (pb221_hasFDerivAt u)
    exact hcomp.congr_of_eventuallyEq (by filter_upwards with v; rw [chartParams221_eq_pack_pb])
  have hflat : HasFDerivAt (paramsEquivFlat M221)
      ((paramsEquivFlatCLE M221).toContinuousLinearMap) (chartParams221 u) :=
    hasFDerivAt_paramsEquivFlat _ _
  have : HasFDerivAt (fun u => paramsEquivFlat M221 (chartParams221 u))
      (((paramsEquivFlatCLE M221).toContinuousLinearMap).comp
        (pack221CLM.comp (pivotBlowupOnDeriv ({0, 1} : Finset (Fin 6)) 0 u))) u :=
    hflat.comp u hchart
  rw [phi221Deriv, Q221CLM]
  exact this

/-- **The genuine chart Jacobian determinant** `|det Dφ221| = |u 0|¹ = |u 0|^{minAdm−1}` — the
soundness-critical weight matching `leafH221`. `phi221Deriv = Q221CLM ∘ pb221Deriv` has
`|det| = |det Q221CLM| · |det pb221Deriv| = 1 · |u 0|¹`. -/
theorem phi221_abs_det (u : Fin 6 → ℝ) :
    |(phi221Deriv u).det| = |u 0| ^ 1 := by
  rw [phi221Deriv, ContinuousLinearMap.det, ContinuousLinearMap.coe_comp, LinearMap.det_comp,
    abs_mul, Q221CLM_abs_det, one_mul, ← ContinuousLinearMap.det, pb221_abs_det]

/-! ## Injectivity off `{u 0 = 0}`, continuity, image containment -/

/-- **`chartParams221` is injective off `{u 0 = 0}`** (the radial center; null). Spectators `A0`
directly; pivot `u 0` from `A1(0,0)`; then `u 1` via `÷ u 0` (`u 0 ≠ 0`). -/
theorem chartParams221_injOn :
    Set.InjOn chartParams221 {u : Fin 6 → ℝ | u 0 ≠ 0} := by
  rintro u hu0 v hv0 huv
  simp only [Set.mem_setOf_eq] at hu0 hv0
  have hA0 : chartA0_221 u = chartA0_221 v := congrFun huv 0
  have hA1 : chartA1_221 u = chartA1_221 v := congrFun huv 1
  have eA0 := fun i j => congrFun (congrFun hA0 i) j
  have eA1 := fun i j => congrFun (congrFun hA1 i) j
  -- A0 spectators (coords 2..5)
  have h2 : u 2 = v 2 := by have := eA0 0 0; simpa [chartA0_221] using this
  have h3 : u 3 = v 3 := by have := eA0 0 1; simpa [chartA0_221] using this
  have h4 : u 4 = v 4 := by have := eA0 1 0; simpa [chartA0_221] using this
  have h5 : u 5 = v 5 := by have := eA0 1 1; simpa [chartA0_221] using this
  -- pivot u 0 from A1(0,0) (no division)
  have h0 : u 0 = v 0 := by have := eA1 0 0; simpa [chartA1_221] using this
  -- u 1 via ÷ u 0 (A1(1,0) = u 0·u 1)
  have h1 : u 1 = v 1 := by
    have he := eA1 1 0; simp only [chartA1_221, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.of_apply] at he
    rw [h0] at he; exact mul_left_cancel₀ hv0 he
  funext j; fin_cases j <;>
    first | exact h0 | exact h1 | exact h2 | exact h3 | exact h4 | exact h5

/-- **`phi221` is injective off `{u 0 = 0}`** (`paramsEquivFlat` a bijection ∘
`chartParams221_injOn`). -/
theorem phi221_injOn : Set.InjOn phi221 {u : Fin 6 → ℝ | u 0 ≠ 0} := by
  intro u hu v hv huv
  exact chartParams221_injOn hu hv ((paramsEquivFlat M221).injective huv)

/-- `chartParams221` is continuous (each layer matrix is a polynomial; `Params` a product). -/
theorem continuous_chartParams221 : Continuous chartParams221 := by
  apply continuous_pi
  intro s
  fin_cases s
  · change Continuous chartA0_221
    unfold chartA0_221
    refine Continuous.matrixVecCons ?_ (Continuous.matrixVecCons ?_ continuous_const)
    all_goals
      refine Continuous.matrixVecCons ?_ (Continuous.matrixVecCons ?_ continuous_const) <;>
        fun_prop
  · change Continuous chartA1_221
    unfold chartA1_221
    refine Continuous.matrixVecCons ?_ (Continuous.matrixVecCons ?_ continuous_const) <;>
      (refine Continuous.matrixVecCons ?_ continuous_const <;> fun_prop)

/-- **`phi221` is continuous**. -/
theorem continuous_phi221 : Continuous phi221 :=
  (continuous_paramsEquivFlat _).comp continuous_chartParams221

/-- **`phi221 0 = 0`** — the chart reaches the deepest point (every entry is a monomial in the
coords, vanishing at `u = 0`). -/
theorem phi221_zero : phi221 (0 : Fin 6 → ℝ) = 0 := by
  have hchart : chartParams221 (0 : Fin 6 → ℝ) = (fun _ => 0 : Params M221) := by
    funext s
    fin_cases s
    · change chartA0_221 (0 : Fin 6 → ℝ) = 0
      funext i j; fin_cases i <;> fin_cases j <;> simp [chartA0_221]
    · change chartA1_221 (0 : Fin 6 → ℝ) = 0
      funext i j; fin_cases i <;> fin_cases j <;> simp [chartA1_221]
  rw [phi221, hchart]
  exact paramsEquivFlat_deepest _

/-- **Image containment**: a small source box `[0,δ]⁶` maps into `cubeBox 6 ε` (continuity of
`phi221` + `phi221 0 = 0`). -/
theorem phi221_image_subset_cubeBox (ε : ℝ) (hε : 0 < ε) :
    ∃ δ > 0, phi221 '' (Set.univ.pi (fun _ : Fin 6 => Set.Icc (0 : ℝ) δ)) ⊆ cubeBox 6 ε := by
  have hopen : IsOpen (Set.univ.pi (fun _ : Fin 6 => Set.Ioo (-ε) ε)) :=
    isOpen_set_pi Set.finite_univ (fun _ _ => isOpen_Ioo)
  have hmem : (0 : Fin 6 → ℝ) ∈ phi221 ⁻¹' (Set.univ.pi (fun _ : Fin 6 => Set.Ioo (-ε) ε)) := by
    simp only [Set.mem_preimage, phi221_zero, Set.mem_pi, Set.mem_univ, true_implies,
      Set.mem_Ioo, Pi.zero_apply]
    exact fun i => ⟨by linarith, hε⟩
  obtain ⟨δ, hδ, hsub⟩ := cubeBox_subset_of_isOpen (hopen.preimage continuous_phi221) hmem
  refine ⟨δ, hδ, ?_⟩
  rintro y ⟨x, hx, rfl⟩
  have hxcube : x ∈ cubeBox 6 δ := by
    simp only [cubeBox, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Icc] at hx ⊢
    intro i; exact ⟨le_trans (by linarith [hδ]) (hx i).1, (hx i).2⟩
  have hxmem : phi221 x ∈ Set.univ.pi (fun _ : Fin 6 => Set.Ioo (-ε) ε) :=
    Set.mem_preimage.mp (hsub hxcube)
  refine Set.mem_pi.mpr (fun i _ => ?_)
  have hi := (Set.mem_pi.mp hxmem) i (Set.mem_univ i)
  rw [Set.mem_Ioo] at hi
  rw [Set.mem_Icc]
  exact ⟨hi.1.le, hi.2.le⟩

/-! ## The genuine geometric change-of-variables for `phi221` (the `cov` field)

`phi221` is `InjOn` off `{u 0 = 0}` (`phi221_injOn`), C¹ (`phi221_hasFDerivAt`), with structural
determinant `|det Dφ| = |u 0|¹` (`phi221_abs_det`). The c-o-v runs directly on `V \ {u 0 = 0}` — a
radial blow-up needs NO second null-slice (the deepest factor carries the whole `u₀`). -/
theorem phi221_cov (V : Set (Fin 6 → ℝ)) (hV : MeasurableSet V) (g : (Fin 6 → ℝ) → ℝ≥0∞) :
    ∫⁻ x in phi221 '' (V \ {x | x 0 = 0}), g x
      = ∫⁻ u in V \ {x | x 0 = 0}, ENNReal.ofReal (∏ j, |u j| ^ (leafH221 j)) * g (phi221 u) := by
  set S := V \ {x : Fin 6 → ℝ | x 0 = 0} with hS
  have hSmeas : MeasurableSet S :=
    hV.diff (measurableSet_eq_fun (measurable_pi_apply 0) measurable_const)
  have hcov : ∫⁻ x in phi221 '' S, g x
      = ∫⁻ u in S, ENNReal.ofReal |(phi221Deriv u).det| * g (phi221 u) := by
    refine lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hSmeas
      (fun x _ => (phi221_hasFDerivAt x).hasFDerivWithinAt) ?_ g
    intro x hx y hy hxy
    exact phi221_injOn hx.2 hy.2 hxy
  rw [hcov]
  refine setLIntegral_congr_fun hSmeas (fun u _ => ?_)
  rw [phi221_abs_det, leafH221_prod_eq]

/-- `Uval221` is bounded above on the source box `[0,δ]⁶` (continuous on a compact box). -/
theorem Uval221_le_on_box (δ : ℝ) :
    ∃ B, 0 < B ∧ ∀ u ∈ Set.univ.pi (fun _ : Fin 6 => Set.Icc (0 : ℝ) δ), Uval221 u ≤ B := by
  have hcpt : IsCompact (Set.univ.pi (fun _ : Fin 6 => Set.Icc (0 : ℝ) δ)) :=
    isCompact_univ_pi (fun _ => isCompact_Icc)
  rcases (Set.univ.pi (fun _ : Fin 6 => Set.Icc (0 : ℝ) δ)).eq_empty_or_nonempty with he | hne
  · exact ⟨1, one_pos, fun u hu => absurd (he ▸ hu) (Set.mem_empty_iff_false u).mp⟩
  · obtain ⟨u0, _, hu0⟩ := hcpt.exists_isMaxOn hne continuous_Uval221.continuousOn
    exact ⟨max 1 (Uval221 u0), lt_of_lt_of_le one_pos (le_max_left _ _),
      fun u hu => le_trans (hu0 hu) (le_max_right _ _)⟩

/-! ## The `NodeAchieverChart M221` instance + the atom discharge -/

/-- **The `(2,2,1)` achiever chart bundle** — the layered validate-small for the option-(C)
construction, built end-to-end through the general machinery (`pivotBlowupOn` radial, the
measure-preserving `pack` via `measurePreserving_paramsPack_of_flatIdxEquiv`, the linear reshape
`Q221CLM`, the genuine-polynomial `U > 0` a.e.). Binding axis `0`, unit `Uval221`, the radial Jacobian
`|u 0|¹ = |u 0|^{minAdm−1}`. All fields banked sorry-free. -/
noncomputable def nodeChart221 : NodeAchieverChart M221 where
  hpos := by rw [minAdm_M221]; norm_num
  phi := phi221
  p := (0 : Fin 6)
  leafH := leafH221
  leafH_pivot := leafH221_pivot
  Ufun := Uval221
  Ubound := fun δ => by
    obtain ⟨B, hB0, hBle⟩ := Uval221_le_on_box δ
    refine ⟨B, hB0, hBle, ?_⟩
    exact ae_restrict_of_ae Uval221_ae_pos
  Umeas := continuous_Uval221.measurable
  leaf_integrand := leaf_integrand221
  cov := phi221_cov
  image_subset := phi221_image_subset_cubeBox

/-- **The `(2,2,1)` achiever box-divergence** — `∫⁻_{cubeBox 6 ε} |routeMCore M221|^{−c'} = ⊤` for
`c'` at-or-above the achiever threshold `1 = ½·minAdm M221`, every `ε > 0`. The atom
`routeMCore_box_diverges_achiever` discharged for `M = (2,2,1)`, via the chart bundle `nodeChart221`
fed through the M-agnostic assembly `routeMCore_box_diverges_of_nodeChart`. The smallest genuinely-
layered node (`L = 2`, nontrivial `A0·A1` matrix product), built through the option-(C) bricks. -/
theorem routeM221_box_diverges (c' : NNReal) (hc' : (minAdm M221 : ℝ≥0∞) / 2 ≤ (c' : ℝ≥0∞))
    (ε : ℝ) (hε : 0 < ε) :
    ∫⁻ x in cubeBox (routeMAmbient M221) ε,
      ENNReal.ofReal (|routeMCore M221 x| ^ (-(c' : ℝ))) = ⊤ :=
  routeMCore_box_diverges_of_nodeChart M221 nodeChart221 c' hc' ε hε

/-- **`routeMCore_box_diverges_achiever` for `M = (2,2,1)`** — the atom (`RouteMLayerCoverGE.lean`)
discharged at the layered validate-small node `(2,2,1)`, in the atom's own shape. The instance, NOT
the general-`M` atom (which needs the uniform `φ_M`, designed separately). -/
theorem routeMCore_box_diverges_achiever_221 (c' : NNReal)
    (hc' : (minAdm M221 : ℝ≥0∞) / 2 ≤ (c' : ℝ≥0∞)) (ε : ℝ) (hε : 0 < ε) :
    ∫⁻ x in cubeBox (routeMAmbient M221) ε,
      ENNReal.ofReal (|routeMCore M221 x| ^ (-(c' : ℝ))) = ⊤ :=
  routeM221_box_diverges c' hc' ε hε

/-- **The `(2,2,1)` cross-check**: `minAdm = 2`, binding axis `(k,h) = (1,1)`, threshold
`1 = ½·minAdm`; at `c' = 1` the leaf exponent on `u 0` is `1 − 2·1·1 = −1` (the sharp `∫ u₀⁻¹ = ⊤`).
The box integral diverges at `c' = 1` (and above), every `ε > 0`. -/
theorem routeM221_box_diverges_at_one (ε : ℝ) (hε : 0 < ε) :
    ∫⁻ x in cubeBox (routeMAmbient M221) ε,
      ENNReal.ofReal (|routeMCore M221 x| ^ (-(1 : ℝ))) = ⊤ := by
  have hle : (minAdm M221 : ℝ≥0∞) / 2 ≤ ((1 : NNReal) : ℝ≥0∞) := by
    rw [minAdm_M221]
    rw [ENNReal.div_le_iff (by norm_num) (by norm_num)]
    norm_num
  have h := routeM221_box_diverges 1 hle ε hε
  rwa [show ((1 : NNReal) : ℝ) = (1 : ℝ) by norm_num] at h

end DLNFibre.DLN.RLCT
