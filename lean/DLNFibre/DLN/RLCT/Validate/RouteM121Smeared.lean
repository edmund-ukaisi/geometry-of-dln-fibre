import DLNFibre.DLN.RLCT.Validate.NodeAchieverChart
import DLNFibre.DLN.RLCT.Validate.RouteM221
import DLNFibre.DLN.RLCT.Validate.Case222Resolution
import DLNFibre.DLN.RLCT.Foundations.CoreShearMP
import DLNFibre.DLN.RLCT.Foundations.ParamsReshapeMP
import DLNFibre.Core.MeasureTheory.PolynomialZeroSet
import Mathlib.Algebra.MvPolynomial.Basic

/-!
# `RouteM121Smeared` — the BOUNDARY-SMEARED achiever box-divergence VALIDATE-SMALL `(1,2,1)`

The smallest boundary-SMEARED node `M = (1,2,1)` (`L = 2`, `r = Text(L) = 1`, `c = M_L = 1`,
`m1 = M_{L−1} = 2`, `s = m1 − r = 1`, `minAdm = r·c = 1`, `flatDim = 4`) — the validate-small for
the
RATIONAL single-pivot chart `φ_sm` (`certificate-genM-smeared.md`), built on the **a.e.
`leaf_integrand`** core (option (i), landed in `NodeAchieverChart`).

**Why the a.e. core is needed (the wall it resolves).** The rate `F∘φ = z²·U` holds ONLY off the
rational pole `{a = 0}` (Lean totalizes `b/a = b·0⁻¹ = 0`, so ON the pole `A⁰·A¹ = b·sb ≠ 0`,
witnessed
nonzero by `dlnLoss_chartParams121_pole_pos`). The original POINTWISE (`∀ u`) `leaf_integrand`
could not
be met; the box-divergence atom is intrinsically an a.e./lintegral property, so the a.e. field
(`∀ᵐ u`) is the faithful form — supplied here off the null pole by `leaf_integrand121_ae`.

## The chart (`certificate-genM-smeared.md` §2, specialized to `(1,2,1)`)
Coords `(a, b, z, sb) : Fin 4 → ℝ`. The front product `P = A⁽⁰⁾ = [a, b]` (`1×2`); `P₁ = [a]`,
`P₂ = [b]`; the rational routing `Λ₀ = (P₁ᵀP₁)⁻¹P₁ᵀP₂ = b/a`. The deepest factor
`A⁽¹⁾ = [z·H̄ − Λ₀·S_bot ; S_bot] = [z − (b/a)·sb ; sb]` (`2×1`, `H̄(0,0) = 1`). Then

    A⁽⁰⁾·A⁽¹⁾ = a·(z − (b/a)·sb) + b·sb = a·z   ⟹   F = ‖A⁽⁰⁾·A⁽¹⁾‖² = a²·z² = z²·U,  U = a².

`U = a²` is a POLYNOMIAL (the rational `b/a` cancels out of `F`). `minAdm = 1`, so the radial det is
`|z|^{minAdm−1} = |z|⁰ = 1`: `(1,2,1)` exercises the rational SHEAR (NOT the radial blow-up — the
next
validate-small `(2,3,1)` / `(1,3,2)` has `minAdm ≥ 2`).

## The pole + the `cov` split (`N0 = {a = 0}`)
`φ_sm` is RATIONAL: `Λ₀ = b/a` is undefined on the pole `N0 := {a = 0}` (the front Gram minor
`P₁ᵀP₁ = a² = 0`), a Lebesgue-null hypersurface NOT inside the radial-pivot locus `{z = 0}`. Two
fields
see the pole: `leaf_integrand` (resolved by the a.e. core, `leaf_integrand121_ae`) and `cov`. The
`cov`
runs the `phi334_cov` TWO-SLICE split: c-o-v on `s \ N0` (φ_sm C¹/InjOn/`|det| = 1` there), then add
back `s ∩ N0` — RHS null (`leafH121 ≡ 0`, weight `1`; `N0` null); LHS image-null via the FRONT-block
identity (`φ_sm '' (s∩N0) ⊆ {a-flat-coord = 0}`, a target null hypersurface — NOT Luzin-N).

Codex (xhigh, decorrelated, `codex/smeared-leafintegrand-{prompt,answer}.md`) confirmed the a.e.
core
(option (i)) as the faithful fix; the controller approved it. -/

open MeasureTheory
open scoped ENNReal BigOperators

namespace DLNFibre.DLN.RLCT

/-- `M121 = (1,2,1)` (the smallest boundary-smeared achiever node). -/
abbrev M121 : Fin 3 → ℕ := ![1, 2, 1]

theorem minAdm_M121 : minAdm M121 = 1 := by
  rw [← minAdmRec_eq_minAdm]; decide

theorem flatDim_M121 : flatDim M121 = 4 := by decide

theorem routeMAmbient_M121 : routeMAmbient M121 = 4 := by decide

/-! ## The chart matrices (rational single-pivot, `certificate-genM-smeared.md` §2)

Coords `(u 0, u 1, u 2, u 3) = (a, b, z, sb)`. Layer 0 `A⁰ = [a, b]` (`1×2`, the front product `P`);
layer 1 `A¹ = [z − (b/a)·sb ; sb]` (`2×1`, the rational shear). The pivot axis is `z = u 2`. -/

/-- **The layer-`0` matrix `A⁽⁰⁾`** (`1×2`): the front product `P = [a, b]` (free generic). -/
noncomputable def chartA0_121 (u : Fin 4 → ℝ) : Matrix (Fin 1) (Fin 2) ℝ :=
  !![u 0, u 1]

/-- **The layer-`1` matrix `A⁽¹⁾`** (`2×1`): the rational shear `[z − (b/a)·sb ; sb]`. The top row
absorbs the routing `Λ₀ = b/a` (RATIONAL — undefined on the pole `{u 0 = 0}`); the bottom row is the
free residual `sb`. -/
noncomputable def chartA1_121 (u : Fin 4 → ℝ) : Matrix (Fin 2) (Fin 1) ℝ :=
  !![u 2 - (u 1 / u 0) * u 3; u 3]

/-- The genuine `Params M121`, assembled by `Fin.cons` over the two layers. -/
noncomputable def chartParams121 (u : Fin 4 → ℝ) : Params M121 :=
  Fin.cons (chartA0_121 u)
    (Fin.cons (chartA1_121 u) (fun i => i.elim0))

/-- **The chart in flat coordinates** `phi121sm := paramsEquivFlat M121 ∘ chartParams121` (codomain
`Fin (flatDim M121) → ℝ = Fin 4 → ℝ`, matching the `NodeAchieverChart` field type). -/
noncomputable def phi121sm (u : Fin 4 → ℝ) : Fin (flatDim M121) → ℝ :=
  paramsEquivFlat M121 (chartParams121 u)

/-! ## The rate `F∘φ = z²·U` — holds OFF the pole `{a=0}`, FAILS at it (the `leaf_integrand` wall)

The single product entry telescopes: `A⁰·A¹ = a·(z − (b/a)·sb) + b·sb`. For `a ≠ 0` the `b·sb` terms
cancel, leaving `a·z`, so `F = (a·z)² = z²·a²` (`U = a²`). AT `a = 0`, Lean's `b/a = b·0⁻¹ = 0`, so
`A¹` top `= z` and `A⁰·A¹ = b·sb` — the rate `F = z²·a² = 0` FAILS whenever `b·sb ≠ 0`.

This off-pole-only rate is the crux of the handback: `NodeAchieverChart.leaf_integrand` demands the
rate `∀ u` (the assembly rewrites the integrand POINTWISE on all of `[0,δ]^N`), and the rational
chart
cannot meet it — the pole `{a=0}` is a positive-loss slice the field cannot see. The pole witness
below
is at a CONCRETE point (avoids the opaque-width `Fin (M121 k)` plumbing). -/

/-- **The single product entry** `A⁰·A¹ = a·(z − (b/a)·sb) + b·sb` (the only entry: `M121 0 = M121 2
= 1`). Indices given explicitly — the opaque widths `M121 0`/`M121 2` admit no literal reduction;
any
index is the unique one. -/
theorem prod_chartParams121_entry (u : Fin 4 → ℝ)
    (i : Fin (M121 0)) (j : Fin (M121 2)) :
    prod M121 (chartParams121 u) i j
      = u 0 * (u 2 - (u 1 / u 0) * u 3) + u 1 * u 3 := by
  obtain rfl : i = ⟨0, by decide⟩ := Fin.ext (by have h := i.isLt; have : M121 0 = 1 := rfl; omega)
  obtain rfl : j = ⟨0, by decide⟩ := Fin.ext (by have h := j.isLt; have : M121 2 = 1 := rfl; omega)
  rw [prod_two_layer221 M121 (chartParams121 u) ⟨0, by decide⟩ ⟨0, by decide⟩]
  have hA0 : (chartParams121 u) 0 = chartA0_121 u := rfl
  have hA1 : (chartParams121 u) 1 = chartA1_121 u := rfl
  rw [hA0, hA1]
  -- the inner sum is over `Fin (M121 1)`, defeq `Fin 2`; force the literal type then collapse
  change (∑ k1 : Fin 2, chartA0_121 u ⟨0, by decide⟩ k1 * chartA1_121 u k1 ⟨0, by decide⟩) = _
  rw [Fin.sum_univ_two, chartA0_121, chartA1_121]
  simp only [show (⟨0, by decide⟩ : Fin 2) = 0 from rfl, show (⟨1, by decide⟩ : Fin 2) = 1 from rfl,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_fin_one,
    Matrix.cons_val', Matrix.head_fin_const, Matrix.of_apply, Matrix.cons_val, Fin.isValue]

/-- **The off-pole rate** `dlnLoss M121 0 (chartParams121 u) = z²·a²` for `a ≠ 0`: the `b·sb` shear
cancels (`a·(b/a) = b`), leaving `A⁰·A¹ = a·z`, so the squared single entry is `a²·z²`. -/
theorem dlnLoss_chartParams121_offpole (u : Fin 4 → ℝ) (ha : u 0 ≠ 0) :
    dlnLoss M121 0 (chartParams121 u) = (u 2) ^ 2 * (u 0) ^ 2 := by
  have hcard0 : (Finset.univ : Finset (Fin (M121 0))).card = 1 := by
    rw [Finset.card_univ, Fintype.card_fin]; rfl
  have hcard2 : (Finset.univ : Finset (Fin (M121 2))).card = 1 := by
    rw [Finset.card_univ, Fintype.card_fin]; rfl
  unfold dlnLoss
  -- replace each entry by the constant `(u 0 * u 2)^2`, then sum a constant over the 1×1 grid
  have hconst : ∀ (i : Fin (M121 0)) (j : Fin (M121 2)),
      ((prod M121 (chartParams121 u) - 0) i j) ^ 2 = (u 0 * u 2) ^ 2 := by
    intro i j
    have h0 : ((0 : Matrix (Fin (M121 0)) (Fin (M121 (Fin.last 2))) ℝ)) i j = 0 :=
      Matrix.zero_apply i j
    rw [Matrix.sub_apply, h0, sub_zero, prod_chartParams121_entry]
    have heq : u 0 * (u 2 - (u 1 / u 0) * u 3) + u 1 * u 3 = u 0 * u 2 := by field_simp; ring
    rw [heq]
  calc ∑ i, ∑ j, ((prod M121 (chartParams121 u) - 0) i j) ^ 2
      = ∑ _i : Fin (M121 0), ∑ _j : Fin (M121 2), (u 0 * u 2) ^ 2 := by
        refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => hconst i j))
    _ = (u 2) ^ 2 * (u 0) ^ 2 := by
        rw [Finset.sum_const, Finset.sum_const, hcard0, hcard2]; ring

/-- **The pole-slice loss is positive** at `u = (0,1,7,1)` (on `{a=0}`, `z=7≠0`): `A⁰·A¹ = 0·7 + 1·1
= 1`, so `dlnLoss = 1 ≠ 0 = z²·a²`. The explicit obstruction to the `∀ u` `leaf_integrand` field —
on
`{a=0}` the loss is positive, which no `z²·U = z²·a² = 0` factorization can match. -/
theorem dlnLoss_chartParams121_pole_pos :
    dlnLoss M121 0 (chartParams121 ![0, 1, 7, 1]) = 1 := by
  have hcard0 : (Finset.univ : Finset (Fin (M121 0))).card = 1 := by
    rw [Finset.card_univ, Fintype.card_fin]; rfl
  have hcard2 : (Finset.univ : Finset (Fin (M121 2))).card = 1 := by
    rw [Finset.card_univ, Fintype.card_fin]; rfl
  unfold dlnLoss
  have hconst : ∀ (i : Fin (M121 0)) (j : Fin (M121 2)),
      ((prod M121 (chartParams121 ![0,1,7,1]) - 0) i j) ^ 2 = (1 : ℝ) := by
    intro i j
    have h0 : ((0 : Matrix (Fin (M121 0)) (Fin (M121 (Fin.last 2))) ℝ)) i j = 0 :=
      Matrix.zero_apply i j
    rw [Matrix.sub_apply, h0, sub_zero, prod_chartParams121_entry]
    rw [show (![0,1,7,1] : Fin 4 → ℝ) 0 = 0 from rfl, show (![0,1,7,1] : Fin 4 → ℝ) 1 = 1 from rfl,
      show (![0,1,7,1] : Fin 4 → ℝ) 2 = 7 from rfl, show (![0,1,7,1] : Fin 4 → ℝ) 3 = 1 from rfl]
    norm_num
  calc ∑ i, ∑ j, ((prod M121 (chartParams121 ![0,1,7,1]) - 0) i j) ^ 2
      = ∑ _i : Fin (M121 0), ∑ _j : Fin (M121 2), (1 : ℝ) := by
        refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => hconst i j))
    _ = 1 := by rw [Finset.sum_const, Finset.sum_const, hcard0, hcard2]; ring

/-! ## The `routeMCore` rate (off-pole) + the a.e. `leaf_integrand`

`routeMCore M121 = dlnLoss M121 0 ∘ (paramsEquivFlat).symm`, and `phi121sm = paramsEquivFlat ∘
chartParams121`, so the `symm`/`apply` cancel and `routeMCore M121 (phi121sm u) = dlnLoss M121 0
(chartParams121 u)` — `= (u 2)²·(u 0)²` off the pole (`dlnLoss_chartParams121_offpole`). With the
a.e.
`leaf_integrand` field (the option-(i) core), only this OFF-POLE rate is needed: `{u 0 = 0}` is
null. -/

/-- **The `routeMCore` rate, off the pole** `routeMCore M121 (phi121sm u) = (u 2)²·(u 0)²` for
`u 0 ≠ 0`. -/
theorem routeMCore_phi121sm_offpole (u : Fin 4 → ℝ) (ha : u 0 ≠ 0) :
    routeMCore M121 (phi121sm u) = (u 2) ^ 2 * (u 0) ^ 2 := by
  rw [routeMCore, phi121sm, MeasurableEquiv.symm_apply_apply,
    dlnLoss_chartParams121_offpole u ha]

/-- The unit factor `U = a² = (u 0)²` (the `z`-free factor of `F = z²·U`). -/
noncomputable def Uval121 (u : Fin 4 → ℝ) : ℝ := (u 0) ^ 2

/-- `Uval121 ≥ 0`. -/
theorem Uval121_nonneg (u : Fin 4 → ℝ) : (0 : ℝ) ≤ Uval121 u := by unfold Uval121; positivity

/-- `Uval121` is measurable. -/
theorem Uval121_measurable : Measurable Uval121 := by
  unfold Uval121; fun_prop

/-- The leaf exponents `leafH121` — all `0` (`minAdm = 1`, so the radial exponent `minAdm − 1 = 0`;
the
chart has det `|z|⁰ = 1`, no genuine radial blow-up). -/
def leafH121 : Fin 4 → ℕ := fun _ => 0

/-- `leafH121 p = 0 = minAdm M121 − 1` at the pivot `p = z`-axis. -/
theorem leafH121_pivot : leafH121 (2 : Fin 4) = minAdm M121 - 1 := by rw [minAdm_M121]; rfl

/-- **The a.e. leaf-integrand identity** (the option-(i) field): off the null pole `{u 0 = 0}`, the
rate `routeMCore = (u 2)²·U` holds, so the det-free leaf-integrand algebra (the loss base `|u_p|²`
factors out, `leafH121 ≡ 0`) gives the identity. The pole is `volume`-null (`coordZero_null`), so
the
field holds `∀ᵐ u`. -/
theorem leaf_integrand121_ae (c : ℝ) :
    ∀ᵐ u ∂(volume : Measure (Fin 4 → ℝ)),
      (∏ j, |u j| ^ (leafH121 j)) * |routeMCore M121 (phi121sm u)| ^ (-c)
        = monomialIntegrand 4 (nodeLeafK 4 (2 : Fin 4)) leafH121 c u * (Uval121 u) ^ (-c) := by
  -- the bad set `{u 0 = 0}` is null; the identity holds on its complement
  have hpole : (volume : Measure (Fin 4 → ℝ)) {u : Fin 4 → ℝ | u 0 = 0} = 0 :=
    coordZero_null (0 : Fin 4)
  have hcompl : {u : Fin 4 → ℝ | u 0 ≠ 0} ∈ (ae (volume : Measure (Fin 4 → ℝ))) := by
    rw [mem_ae_iff]; convert hpole using 2; ext u; simp [not_not]
  filter_upwards [hcompl] with u hu
  -- off-pole: replicate `leaf_integrand_of_rate`'s algebra at this `u` (rate holds here)
  unfold monomialIntegrand
  have hloss : (∏ j, |u j| ^ (2 * (nodeLeafK 4 (2 : Fin 4)) j)) = |u 2| ^ 2 := by
    rw [Finset.prod_eq_single (2 : Fin 4)]
    · simp [nodeLeafK]
    · intro j _ hj; simp [nodeLeafK, hj]
    · intro h; exact absurd (Finset.mem_univ (2 : Fin 4)) h
  rw [hloss, routeMCore_phi121sm_offpole u hu, show Uval121 u = (u 0) ^ 2 from rfl,
    show (∏ j, |u j| ^ (leafH121 j)) = 1 by simp [leafH121]]
  rw [abs_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)),
    Real.mul_rpow (sq_nonneg _) (sq_nonneg _), ← sq_abs (u 2)]
  ring

/-! ## The `cov` split (the genuinely-new piece — the rational pole image-null)

`phi121sm = Q121 ∘ shear121`, where `shear121 (a,b,z,sb) = (a, b, z − (b/a)·sb, sb)` is the RATIONAL
shear in coordinate space (a self-map of `Fin 4 → ℝ`) and `Q121 = paramsEquivFlat ∘ pack121` is the
measure-preserving linear reshape (det ±1). Off the pole `N0 = {a = 0}` the shear is a C¹ diffeo
with
`|det| = 1` (lower-unitriangular: `∂(z−(b/a)sb)/∂z = 1`, the shear shift reads only other coords).
The
`cov` runs the two-slice split (the `phi334_cov` pattern): c-o-v on `S \ N0`, then add back `S ∩ N0`
— RHS null (`leafH121 ≡ 0` weight `1`, integrand finite, `N0` null); LHS image-null via the
FRONT-block
identity `shear121` fixes `(a,b)`, so `phi121sm '' (S ∩ N0) ⊆ {first flat coord lands `a = 0`}`. -/

/-- **The coordinate-space rational shear** `shear121 (a,b,z,sb) = (a, b, z − (b/a)·sb, sb)`. -/
noncomputable def shear121 (u : Fin 4 → ℝ) : Fin 4 → ℝ :=
  ![u 0, u 1, u 2 - (u 1 / u 0) * u 3, u 3]

/-- **The linear reshape** `pack121 : (Fin 4 → ℝ) → Params M121` (flat coords → matrix slots):
coords
`0,1` ↦ layer-`0` (`A⁰`) entries `(0,0)`,`(0,1)`; coords `2,3` ↦ layer-`1` (`A¹`) entries
`(0,0)`,`(1,0)`. Each output entry is one input coordinate. -/
noncomputable def pack121 (w : Fin 4 → ℝ) : Params M121 :=
  Fin.cons (!![w 0, w 1] : Matrix (Fin 1) (Fin 2) ℝ)
    (Fin.cons (!![w 2; w 3] : Matrix (Fin 2) (Fin 1) ℝ) (fun i => i.elim0))

/-- **The factorization** `chartParams121 u = pack121 (shear121 u)`: the shear produces the 4 flat
entries `(a, b, z−(b/a)sb, sb)`, `pack121` reshapes them into `A⁰=[a,b]`, `A¹=[z−(b/a)sb ; sb]`. -/
theorem chartParams121_eq_pack_shear (u : Fin 4 → ℝ) :
    chartParams121 u = pack121 (shear121 u) := by
  funext s
  fin_cases s
  · show chartA0_121 u = (pack121 (shear121 u)) 0
    funext i j; fin_cases i <;> fin_cases j <;> rfl
  · show chartA1_121 u = (pack121 (shear121 u)) 1
    funext i j; fin_cases i <;> fin_cases j <;> simp [chartA1_121, pack121, shear121]

/-- **`shear121` is injective off the pole `{u 0 = 0}`.** The inverse is `(a,b,z',sb) ↦
(a, b, z'+(b/a)sb, sb)`: `a,b,sb` are read directly; `z = z' + (b/a)·sb` is recovered (`a ≠ 0`). -/
theorem shear121_injOn : Set.InjOn shear121 {u : Fin 4 → ℝ | u 0 ≠ 0} := by
  rintro u hu v hv huv
  simp only [Set.mem_setOf_eq] at hu hv
  have e0 : u 0 = v 0 := by have := congrFun huv 0; simpa [shear121] using this
  have e1 : u 1 = v 1 := by have := congrFun huv 1; simpa [shear121] using this
  have e3 : u 3 = v 3 := by have := congrFun huv 3; simpa [shear121] using this
  have e2 : u 2 - (u 1 / u 0) * u 3 = v 2 - (v 1 / v 0) * v 3 := by
    have := congrFun huv 2; simpa [shear121] using this
  have e2' : u 2 = v 2 := by
    have hk : (u 1 / u 0) * u 3 = (v 1 / v 0) * v 3 := by rw [e0, e1, e3]
    have : u 2 - (u 1 / u 0) * u 3 = v 2 - (u 1 / u 0) * u 3 := by rw [e2, hk]
    linarith
  funext i; fin_cases i
  · exact e0
  · exact e1
  · exact e2'
  · exact e3

/-- The pole `{u 0 = 0}` is `volume`-null. -/
theorem pole121_null : (volume : Measure (Fin 4 → ℝ)) {u : Fin 4 → ℝ | u 0 = 0} = 0 :=
  coordZero_null (0 : Fin 4)

/-! ### The shear Jacobian off-pole: `|det| = 1` via the transvection structure

`shear121`'s fderiv off `{u 0 = 0}` is the matrix `1 + (row-2 shear)`: identity on coords `0,1,3`;
row
`2` is `e₂ + ∂₀·e₀ + ∂₁·e₁ + ∂₃·e₃` (`∂₀ = (u 1/u 0²)·u 3`, `∂₁ = −(1/u 0)·u 3`, `∂₃ = −(u 1/u 0)`).
Adding multiples of OTHER rows to row `2` of the identity is a chain of transvections
(`Matrix.det_updateRow_add_smul_self`, `i ≠ j`), each preserving `det`; so `det = det 1 = 1`. -/

/-- The shear's fderiv matrix (rows = output coord): `1` with row `2` carrying the shear shifts. -/
noncomputable def shear121DerivMat (u : Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of ![![1, 0, 0, 0], ![0, 1, 0, 0],
    ![(u 1 / (u 0)^2) * u 3, -(1 / u 0) * u 3, 1, -(u 1 / u 0)], ![0, 0, 0, 1]]

/-- `det (shear121DerivMat u) = 1`. Row `2` is `(identity row 2) + c₀·(row 0) + c₁·(row 1) +
c₃·(row 3)`
(`c₀ = u 1/u 0²·u 3`, `c₁ = −(1/u 0)·u 3`, `c₃ = −(u 1/u 0)`): the identity with multiples of OTHER
rows
added to row `2`, a chain of three transvections (`det_updateRow_add_smul_self`, distinct row
indices),
each `det`-preserving, so `det = det 1 = 1`. -/
theorem shear121DerivMat_det (u : Fin 4 → ℝ) : (shear121DerivMat u).det = 1 := by
  set c0 := u 1 / (u 0)^2 * u 3 with hc0
  set c1 := -(1 / u 0) * u 3 with hc1
  set c3 := -(u 1 / u 0) with hc3
  -- the three transvection steps from the identity, each adding `cᵢ • (row i)` to row 2
  set M1 := Matrix.updateRow (1 : Matrix (Fin 4) (Fin 4) ℝ) 2
    ((1 : Matrix (Fin 4) (Fin 4) ℝ) 2 + c0 • (1 : Matrix (Fin 4) (Fin 4) ℝ) 0) with hM1
  set M2 := Matrix.updateRow M1 2 (M1 2 + c1 • M1 1) with hM2
  set M3 := Matrix.updateRow M2 2 (M2 2 + c3 • M2 3) with hM3
  have hM1det : M1.det = 1 := by
    rw [hM1, Matrix.det_updateRow_add_smul_self _ (by decide) c0, Matrix.det_one]
  have hM2det : M2.det = 1 := by
    rw [hM2, Matrix.det_updateRow_add_smul_self _ (by decide) c1, hM1det]
  have hM3det : M3.det = 1 := by
    rw [hM3, Matrix.det_updateRow_add_smul_self _ (by decide) c3, hM2det]
  -- `shear121DerivMat u = M3` entrywise
  have hEq : shear121DerivMat u = M3 := by
    funext i j
    fin_cases i <;> fin_cases j <;>
      simp [shear121DerivMat, hM3, hM2, hM1, Matrix.updateRow_apply, Matrix.one_apply,
        Matrix.of_apply, hc0, hc1, hc3] <;> ring
  rw [hEq, hM3det]

/-! ### The shear fderiv off-pole + `phi121sm_abs_det = 1` -/

/-- The shear fderiv as the CLM of the transvection matrix `shear121DerivMat u` (so the det is the
banked `shear121DerivMat_det = 1`). -/
noncomputable def shear121Deriv (u : Fin 4 → ℝ) : (Fin 4 → ℝ) →L[ℝ] (Fin 4 → ℝ) :=
  (Matrix.toLin' (shear121DerivMat u)).toContinuousLinearMap

/-- **`|det (shear121Deriv u)| = 1`** off-pole (the chart-derivative CLM is the transvection matrix
`shear121DerivMat u`, det `1` by `shear121DerivMat_det`). -/
theorem shear121Deriv_abs_det (u : Fin 4 → ℝ) :
    |(shear121Deriv u : (Fin 4 → ℝ) →ₗ[ℝ] (Fin 4 → ℝ)).det| = 1 := by
  have h : (shear121Deriv u : (Fin 4 → ℝ) →ₗ[ℝ] (Fin 4 → ℝ)) = Matrix.toLin' (shear121DerivMat u) :=
    rfl
  rw [h, LinearMap.det_toLin', shear121DerivMat_det, abs_one]

/-! ### The `cov` field via MeasurePreserving (route (b) — NO `HasFDerivAt`)

`leafH121 ≡ 0` (minAdm = 1), so the `cov` weight `∏|u_j|^{leafH121 j} = 1` and the
change-of-variables
is exactly `MeasurePreserving.setLIntegral_comp_emb`: `phi121sm` is a measure-preserving measurable
EMBEDDING (a global measurable bijection, det 1 — the chart-deriv det records the weight is 1). NO
Jacobian, NO `HasFDerivAt`, and — since the totalized shear is a GLOBAL measurable bijection (`b/a`
is `0`
at `a = 0`, where the fiber translation is the identity) — NO pole-split either. -/

/-- **The core-shear MP with a MEASURABLE shift** (the `measurePreserving_coreShear` proof
verbatim, with
`Continuous shift` weakened to `Measurable shift` — `skew_product` needs only measurability). -/
theorem measurePreserving_coreShear_measurable (a b c : ℕ)
    (shift : (Fin a → ℝ) × (Fin c → ℝ) → (Fin b → ℝ)) (hmshift : Measurable shift) :
    MeasurePreserving
      (fun q : (Fin a → ℝ) × ((Fin b → ℝ) × (Fin c → ℝ)) =>
        (q.1, (q.2.1 + shift (q.1, q.2.2), q.2.2)))
      volume volume := by
  have hreassoc : MeasurePreserving
      (fun q : (Fin a → ℝ) × ((Fin b → ℝ) × (Fin c → ℝ)) => ((q.1, q.2.2), q.2.1))
      volume volume :=
    measurePreserving_coreReassoc a b c
  have hskew : MeasurePreserving
      (fun p : ((Fin a → ℝ) × (Fin c → ℝ)) × (Fin b → ℝ) => (p.1, p.2 + shift p.1))
      ((volume : Measure ((Fin a → ℝ) × (Fin c → ℝ))).prod volume)
      ((volume : Measure ((Fin a → ℝ) × (Fin c → ℝ))).prod volume) :=
    MeasurePreserving.skew_product
      (μa := (volume : Measure ((Fin a → ℝ) × (Fin c → ℝ)))) (μb := volume)
      (μc := (volume : Measure (Fin b → ℝ))) (μd := volume)
      (f := id) (g := fun rs core => core + shift rs)
      (MeasurePreserving.id volume)
      (measurable_snd.add (hmshift.comp measurable_fst))
      (ae_of_all _ (fun rs =>
        (measurePreserving_add_right (volume : Measure (Fin b → ℝ)) (shift rs)).map_eq))
  have hskew' : MeasurePreserving
      (fun p : ((Fin a → ℝ) × (Fin c → ℝ)) × (Fin b → ℝ) => (p.1, p.2 + shift p.1))
      volume volume := by
    rw [show (volume : Measure (((Fin a → ℝ) × (Fin c → ℝ)) × (Fin b → ℝ)))
          = (volume : Measure ((Fin a → ℝ) × (Fin c → ℝ))).prod volume from
      Measure.volume_eq_prod _ _]
    exact hskew
  have hreassoc' : MeasurePreserving
      (fun p : ((Fin a → ℝ) × (Fin c → ℝ)) × (Fin b → ℝ) => (p.1.1, (p.2, p.1.2)))
      volume volume := by
    have hassoc : MeasurePreserving
        (fun p : ((Fin a → ℝ) × (Fin c → ℝ)) × (Fin b → ℝ) => (p.1.1, (p.1.2, p.2)))
        volume volume := by
      rw [show (volume : Measure (((Fin a → ℝ) × (Fin c → ℝ)) × (Fin b → ℝ)))
            = ((volume : Measure (Fin a → ℝ)).prod volume).prod volume from by
            rw [Measure.volume_eq_prod _ _, Measure.volume_eq_prod _ _],
        show (volume : Measure ((Fin a → ℝ) × ((Fin c → ℝ) × (Fin b → ℝ))))
            = (volume : Measure (Fin a → ℝ)).prod
                ((volume : Measure (Fin c → ℝ)).prod volume) from by
            rw [Measure.volume_eq_prod _ _, Measure.volume_eq_prod _ _]]
      exact measurePreserving_prodAssoc (volume : Measure (Fin a → ℝ)) volume volume
    have hswapinner : MeasurePreserving
        (Prod.map (id : (Fin a → ℝ) → (Fin a → ℝ))
          (Prod.swap : (Fin c → ℝ) × (Fin b → ℝ) → (Fin b → ℝ) × (Fin c → ℝ)))
        volume volume := by
      rw [show (volume : Measure ((Fin a → ℝ) × ((Fin c → ℝ) × (Fin b → ℝ))))
            = (volume : Measure (Fin a → ℝ)).prod volume from Measure.volume_eq_prod _ _,
        show (volume : Measure ((Fin a → ℝ) × ((Fin b → ℝ) × (Fin c → ℝ))))
            = (volume : Measure (Fin a → ℝ)).prod volume from Measure.volume_eq_prod _ _]
      refine (MeasurePreserving.id (volume : Measure (Fin a → ℝ))).prod ?_
      rw [show (volume : Measure ((Fin c → ℝ) × (Fin b → ℝ)))
            = (volume : Measure (Fin c → ℝ)).prod volume from Measure.volume_eq_prod _ _,
        show (volume : Measure ((Fin b → ℝ) × (Fin c → ℝ)))
            = (volume : Measure (Fin b → ℝ)).prod volume from Measure.volume_eq_prod _ _]
      exact Measure.measurePreserving_swap
    exact hswapinner.comp hassoc
  have hcomp := (hreassoc'.comp hskew').comp hreassoc
  have hfun :
      (fun q : (Fin a → ℝ) × ((Fin b → ℝ) × (Fin c → ℝ)) =>
          (q.1, (q.2.1 + shift (q.1, q.2.2), q.2.2)))
        = (fun p : ((Fin a → ℝ) × (Fin c → ℝ)) × (Fin b → ℝ) => (p.1.1, (p.2, p.1.2)))
            ∘ (fun p : ((Fin a → ℝ) × (Fin c → ℝ)) × (Fin b → ℝ) => (p.1, p.2 + shift p.1))
            ∘ (fun q : (Fin a → ℝ) × ((Fin b → ℝ) × (Fin c → ℝ)) => ((q.1, q.2.2), q.2.1)) := by
    funext q; rfl
  rw [hfun]; exact hcomp

/-! ### `Q121 = paramsEquivFlat ∘ pack121` measure-preserving (the linear outer reshape) -/

/-- The slot bijection `Fin 4 ≃ FlatIdx M121` pinning `pack121`'s flat-coord → matrix-slot order:
coords
`0,1` ↦ layer-`0` `(0,0),(0,1)`; coords `2,3` ↦ layer-`1` `(0,0),(1,0)`. A genuine `Equiv` (no dead
slots; `left_inv`/`right_inv` by `decide`). -/
noncomputable def fin4EquivFlatIdx121 : Fin 4 ≃ FlatIdx M121 where
  toFun := fun k =>
    match k with
    | ⟨0,_⟩ => ⟨⟨⟨0,by decide⟩,⟨0,by decide⟩⟩,⟨0,by decide⟩⟩
    | ⟨1,_⟩ => ⟨⟨⟨0,by decide⟩,⟨0,by decide⟩⟩,⟨1,by decide⟩⟩
    | ⟨2,_⟩ => ⟨⟨⟨1,by decide⟩,⟨0,by decide⟩⟩,⟨0,by decide⟩⟩
    | ⟨3,_⟩ => ⟨⟨⟨1,by decide⟩,⟨1,by decide⟩⟩,⟨0,by decide⟩⟩
    | ⟨n+4,h⟩ => absurd h (by omega)
  invFun := fun q =>
    match q with
    | ⟨⟨⟨0,_⟩,⟨0,_⟩⟩,⟨0,_⟩⟩ => 0
    | ⟨⟨⟨0,_⟩,⟨0,_⟩⟩,⟨1,_⟩⟩ => 1
    | ⟨⟨⟨1,_⟩,⟨0,_⟩⟩,⟨0,_⟩⟩ => 2
    | ⟨⟨⟨1,_⟩,⟨1,_⟩⟩,⟨0,_⟩⟩ => 3
  left_inv := by decide
  right_inv := by decide

/-- **The slot equation** `pack121 w q.1.1 q.1.2 q.2 = w (fin4EquivFlatIdx121.symm q)` (`rfl` per
slot). -/
theorem hpack121 (w : Fin 4 → ℝ) (q : FlatIdx M121) :
    pack121 w q.1.1 q.1.2 q.2 = w (fin4EquivFlatIdx121.symm q) := by
  obtain ⟨⟨s, i⟩, j⟩ := q
  fin_cases s <;> fin_cases i <;> fin_cases j <;> rfl

/-- **`pack121` is measure-preserving** (the reshape-MP at `fin4EquivFlatIdx121`). -/
theorem measurePreserving_pack121 :
    MeasurePreserving pack121 (volume : Measure (Fin 4 → ℝ)) (volume : Measure (Params M121)) :=
  measurePreserving_paramsPack_of_flatIdxEquiv M121 fin4EquivFlatIdx121 pack121 hpack121

/-- **`Q121 = paramsEquivFlat ∘ pack121` is measure-preserving** (the linear outer reshape). -/
theorem measurePreserving_Q121 :
    MeasurePreserving (fun w : Fin 4 → ℝ => paramsEquivFlat M121 (pack121 w))
      (volume : Measure (Fin 4 → ℝ)) volume :=
  (measurePreserving_paramsEquivFlat M121).comp measurePreserving_pack121

/-! ### `shear121` is a global measure-preserving measurable bijection (route (b))

`shear121` is `id` on coords `0,1,3` and translates coord `2` by `−(b/a)·sb` (a MEASURABLE function
of
the others). It is a GLOBAL measurable bijection (the totalized inverse `v 2 ↦ v 2 + (v 1/v 0)·v 3`
cancels even at `a = 0`, where `b/a = 0`), measure-preserving by the skew-product (the pole `{a=0}`
is
null but not even needed — the translation is a measurable bijection there too). -/

/-- **`shear121` is measure-preserving.** Direct skew-product on `Fin 4 → ℝ` reindexed as
`(reg=coord 0) × ((core=coord 2) × (spec=coords 1,3))` is the banked `coreShear_measurable` route;
here
we prove it via the explicit measurable inverse + the global-bijection MP, packaged below. -/
noncomputable def shear121Inv (v : Fin 4 → ℝ) : Fin 4 → ℝ :=
  ![v 0, v 1, v 2 + (v 1 / v 0) * v 3, v 3]

/-- `shear121` and `shear121Inv` are mutually inverse (global — `b/a` totalizes, cancels at `a=0`).
-/
theorem shear121_leftInv (u : Fin 4 → ℝ) : shear121Inv (shear121 u) = u := by
  funext i; fin_cases i <;> simp [shear121, shear121Inv] <;> ring

theorem shear121_rightInv (v : Fin 4 → ℝ) : shear121 (shear121Inv v) = v := by
  funext i; fin_cases i <;> simp [shear121, shear121Inv] <;> ring

/-- `shear121` is measurable. -/
theorem shear121_measurable : Measurable shear121 := by
  apply measurable_pi_iff.2
  intro i
  fin_cases i <;> simp only [shear121, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val, Matrix.cons_val_fin_one]
  · exact measurable_pi_apply 0
  · exact measurable_pi_apply 1
  · exact (measurable_pi_apply 2).sub
      (((measurable_pi_apply 1).div (measurable_pi_apply 0)).mul (measurable_pi_apply 3))
  · exact measurable_pi_apply 3

/-- `shear121Inv` is measurable. -/
theorem shear121Inv_measurable : Measurable shear121Inv := by
  apply measurable_pi_iff.2
  intro i
  fin_cases i <;>
    simp only [shear121Inv, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val, Matrix.cons_val_fin_one]
  · exact measurable_pi_apply 0
  · exact measurable_pi_apply 1
  · exact (measurable_pi_apply 2).add
      (((measurable_pi_apply 1).div (measurable_pi_apply 0)).mul (measurable_pi_apply 3))
  · exact measurable_pi_apply 3

/-- **`shear121` as a measurable equivalence** (the global bijection). -/
noncomputable def shear121ME : (Fin 4 → ℝ) ≃ᵐ (Fin 4 → ℝ) where
  toFun := shear121
  invFun := shear121Inv
  left_inv := shear121_leftInv
  right_inv := shear121_rightInv
  measurable_toFun := shear121_measurable
  measurable_invFun := shear121Inv_measurable

/-- The reindex `Fin 4 → ℝ ≃ᵐ (reg=coord 0) × ((core=coord 2) × (spec=coords 1,3))` (`Fin`-factor
shape, for `coreShear_measurable 1 1 2`): `piFinSuccAbove 0` pulls out coord `0`, then on the `Fin
3`
remainder `piFinSuccAbove 1` pulls out the original coord `2`; `funUnique.symm` repackages the bare
`ℝ` factors as `Fin 1 → ℝ`. -/
noncomputable def split121 : (Fin 4 → ℝ) ≃ᵐ (Fin 1 → ℝ) × ((Fin 1 → ℝ) × (Fin 2 → ℝ)) :=
  (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 4 => ℝ) 0).trans
    (MeasurableEquiv.prodCongr (MeasurableEquiv.funUnique (Fin 1) ℝ).symm
      ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 1).trans
        (MeasurableEquiv.prodCongr (MeasurableEquiv.funUnique (Fin 1) ℝ).symm
          (MeasurableEquiv.refl (Fin 2 → ℝ)))))

/-- `split121` is measure-preserving (a chain of `piFinSuccAbove`/`funUnique` volume-preservers). -/
theorem measurePreserving_split121 :
    MeasurePreserving (split121 : (Fin 4 → ℝ) → _) volume volume := by
  refine (volume_preserving_piFinSuccAbove (fun _ : Fin 4 => ℝ) 0).trans ?_
  refine MeasurePreserving.prod (volume_preserving_funUnique (Fin 1) ℝ).symm ?_
  refine (volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) 1).trans ?_
  exact MeasurePreserving.prod (volume_preserving_funUnique (Fin 1) ℝ).symm (MeasurePreserving.id _)

/-- The core-shear shift in the split coordinates: `−(b/a)·sb` (reg `= a = q.1 0`, spec `= (b, sb) =
(q.2 0, q.2 1)`). -/
noncomputable def shift121 : (Fin 1 → ℝ) × (Fin 2 → ℝ) → (Fin 1 → ℝ) :=
  fun q => fun _ => -((q.2 0) / (q.1 0)) * q.2 1

set_option maxHeartbeats 1000000 in
/-- **The FORWARD conjugation** `split121 (shear121 u) = coreShear121 (split121 u)` — both sides
apply
`split121` forward (no `.symm` reduction). The `coreShear` translates the core (coord 2) by the
shift. -/
theorem split121_shear121 (u : Fin 4 → ℝ) :
    split121 (shear121 u)
      = (fun q : (Fin 1 → ℝ) × ((Fin 1 → ℝ) × (Fin 2 → ℝ)) =>
          (q.1, (q.2.1 + shift121 (q.1, q.2.2), q.2.2))) (split121 u) := by
  have htail : ∀ (k : Fin 3), Fin.tail u k = u k.succ := fun _ => rfl
  apply Prod.ext
  · -- reg = coord 0
    funext k; fin_cases k
    simp [split121, shear121, MeasurableEquiv.piFinSuccAbove, MeasurableEquiv.funUnique,
      MeasurableEquiv.prodCongr, Fin.insertNthEquiv, Fin.removeNth, Fin.succAbove]
  apply Prod.ext
  · -- core = coord 2, shifted
    funext k; fin_cases k
    simp [split121, shear121, shift121, MeasurableEquiv.piFinSuccAbove, MeasurableEquiv.funUnique,
      MeasurableEquiv.prodCongr, Fin.insertNthEquiv, Fin.removeNth, Fin.succAbove, htail,
      Fin.succ_zero_eq_one, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val, Matrix.cons_val_fin_one]
    ring
  · -- spec = coords 1,3 (unchanged)
    funext k; fin_cases k <;>
      simp [split121, shear121, MeasurableEquiv.piFinSuccAbove, MeasurableEquiv.funUnique,
        MeasurableEquiv.prodCongr, Fin.insertNthEquiv, Fin.removeNth, Fin.succAbove, htail,
        Fin.succ_zero_eq_one]

/-- **`shear121 = split121.symm ∘ coreShear121 ∘ split121`** (pointwise) — from the forward
identity. -/
theorem shear121_eq_conj (u : Fin 4 → ℝ) :
    shear121 u = split121.symm
      ((fun q : (Fin 1 → ℝ) × ((Fin 1 → ℝ) × (Fin 2 → ℝ)) =>
          (q.1, (q.2.1 + shift121 (q.1, q.2.2), q.2.2))) (split121 u)) := by
  rw [← split121_shear121, MeasurableEquiv.symm_apply_apply]

/-- **`shear121` is measure-preserving** (conjugate the banked `coreShear_measurable` by
`split121`). -/
theorem measurePreserving_shear121 :
    MeasurePreserving shear121 (volume : Measure (Fin 4 → ℝ)) volume := by
  have hcore := measurePreserving_coreShear_measurable 1 1 2 shift121
    (by unfold shift121; fun_prop)
  have hconj : MeasurePreserving
      (split121.symm ∘ (fun q : (Fin 1 → ℝ) × ((Fin 1 → ℝ) × (Fin 2 → ℝ)) =>
          (q.1, (q.2.1 + shift121 (q.1, q.2.2), q.2.2))) ∘ split121)
      volume volume :=
    (measurePreserving_split121.symm split121).comp (hcore.comp measurePreserving_split121)
  refine hconj.congr shear121_measurable ?_
  filter_upwards with u
  exact (shear121_eq_conj u).symm

/-! ### `phi121sm` measure-preserving + measurable embedding, and the `cov` field -/

/-- `phi121sm = Q121 ∘ shear121` (pointwise; `chartParams121 = pack121 ∘ shear121`). -/
theorem phi121sm_eq_Q121_shear121 (u : Fin 4 → ℝ) :
    phi121sm u = paramsEquivFlat M121 (pack121 (shear121 u)) := by
  rw [phi121sm, chartParams121_eq_pack_shear]

/-- **`phi121sm` is measure-preserving** (`Q121 ∘ shear121`, both MP). -/
theorem measurePreserving_phi121sm :
    MeasurePreserving phi121sm (volume : Measure (Fin 4 → ℝ)) volume := by
  have hphimeas : Measurable phi121sm := by
    have : phi121sm = (fun w : Fin 4 → ℝ => paramsEquivFlat M121 (pack121 w)) ∘ shear121 :=
      funext (fun u => phi121sm_eq_Q121_shear121 u)
    rw [this]; exact measurePreserving_Q121.measurable.comp shear121_measurable
  refine (measurePreserving_Q121.comp measurePreserving_shear121).congr hphimeas ?_
  filter_upwards with u; exact (phi121sm_eq_Q121_shear121 u).symm

/-- **`phi121sm` packaged as a measurable equivalence** `shear121ME ≫ (flatEquivOf).symm ≫
paramsEquivFlat` (`pack121 = (flatEquivOf …).symm`, all three measurable bijections; codomain
`Fin (flatDim M121) → ℝ = Fin 4 → ℝ` defeq). -/
noncomputable def phi121smME : (Fin 4 → ℝ) ≃ᵐ (Fin (flatDim M121) → ℝ) :=
  shear121ME.trans
    (((flatEquivOf M121 fin4EquivFlatIdx121).symm).trans (paramsEquivFlat M121))

/-- `phi121smME` agrees with `phi121sm` (`pack121 = (flatEquivOf …).symm`). The codomains
`Fin (flatDim M121) → ℝ` and `Fin 4 → ℝ` are defeq. -/
theorem phi121smME_eq (u : Fin 4 → ℝ) : phi121smME u = phi121sm u := by
  rw [phi121smME, phi121sm_eq_Q121_shear121]
  show paramsEquivFlat M121 ((flatEquivOf M121 fin4EquivFlatIdx121).symm (shear121 u)) = _
  congr 1
  funext s i j
  exact (flatEquivOf_symm_coord M121 fin4EquivFlatIdx121 (shear121 u) ⟨⟨s, i⟩, j⟩).trans
    (hpack121 (shear121 u) ⟨⟨s, i⟩, j⟩).symm

/-- **`phi121sm` is a measurable embedding** (= the measurable equivalence `phi121smME`; codomain
`Fin (flatDim M121) → ℝ` defeq `Fin 4 → ℝ`). -/
theorem measurableEmbedding_phi121sm : MeasurableEmbedding phi121sm := by
  have h : phi121sm = ⇑phi121smME := funext (fun u => (phi121smME_eq u).symm)
  rw [h]; exact phi121smME.measurableEmbedding

/-- **The `cov` field for `phi121sm`** (route (b)): `leafH121 ≡ 0` ⟹ weight `1`, so the c-o-v is
exactly
`MeasurePreserving.setLIntegral_comp_emb` — no `HasFDerivAt`, no Jacobian, no pole-split. -/
theorem phi121sm_cov (V : Set (Fin 4 → ℝ)) (hV : MeasurableSet V)
    (g : (Fin (flatDim M121) → ℝ) → ℝ≥0∞) :
    ∫⁻ x in phi121sm '' (V \ {x | x 2 = 0}), g x
      = ∫⁻ u in V \ {x | x 2 = 0},
          ENNReal.ofReal (∏ j, |u j| ^ (leafH121 j)) * g (phi121sm u) := by
  have hcov := (measurePreserving_phi121sm.setLIntegral_comp_emb measurableEmbedding_phi121sm g
    (V \ {x | x 2 = 0})).symm
  rw [hcov]
  refine setLIntegral_congr_fun (hV.diff
    (measurableSet_eq_fun (measurable_pi_apply 2) measurable_const)) (fun u _ => ?_)
  simp only [leafH121, pow_zero, Finset.prod_const_one, ENNReal.ofReal_one, one_mul]

/-! ### The MP-final-step assembly (route (b), reusable — replaces `image_subset`)

The rational/MP smeared chart does NOT use image-containment (`φ_sm` is unbounded near its pole).
The
box-divergence is discharged by the MeasurePreserving change-of-variables: `∫_{cubeBox ε} g =
∫_{φ⁻¹(cubeBox ε)} g∘φ` (`setLIntegral_comp_preimage_emb`), lower-bounded by a source sub-box `S ⊆
φ⁻¹(cubeBox ε)` where the rate `z²·a²` gives the monomial divergence. The reusable shape
`routeMCore_box_diverges_of_MPChart` takes a **source certificate** `hsrc` (the
bounded-away-from-pole
sub-box `S ⊆ φ⁻¹(cubeBox)` with `∫_S (loss∘φ)^{−c} = ⊤`) — the ∀M-smeared lift (46 M) reuses it. The
banked image_subset core (`routeMCore_box_diverges_of_nodeChart`) is UNTOUCHED — the polynomial
interior/clean charts keep it (they are not MP). -/

/-- **The MP-chart box-divergence (route (b), reusable, NO `image_subset`).** Given a
measure-preserving
measurable embedding `phi` and a source certificate `hsrc` (a sub-box `S ⊆ phi⁻¹(cubeBox N ε)` on
which
the pulled-back loss already diverges), the loss box-integral over `cubeBox N ε` is `⊤`. The whole
MP
step: `∫_{cubeBox} = ∫_{phi⁻¹(cubeBox)} (loss∘phi)` ≥ `∫_S (loss∘phi)` = `⊤`. -/
theorem routeMCore_box_diverges_of_MPChart {L : ℕ} (M : Fin (L + 1) → ℕ)
    (phi : (Fin (routeMAmbient M) → ℝ) → (Fin (routeMAmbient M) → ℝ))
    (hmp : MeasurePreserving phi (volume : Measure (Fin (routeMAmbient M) → ℝ)) volume)
    (hemb : MeasurableEmbedding phi) (c' : ℝ) (ε : ℝ)
    (hsrc : ∃ S : Set (Fin (routeMAmbient M) → ℝ), MeasurableSet S ∧
      S ⊆ phi ⁻¹' (cubeBox (routeMAmbient M) ε) ∧
      (∫⁻ u in S, ENNReal.ofReal (|routeMCore M (phi u)| ^ (-c'))) = ⊤) :
    ∫⁻ x in cubeBox (routeMAmbient M) ε,
      ENNReal.ofReal (|routeMCore M x| ^ (-c')) = ⊤ := by
  obtain ⟨S, _, hSsub, hSdiv⟩ := hsrc
  set g := fun x : Fin (routeMAmbient M) → ℝ => ENNReal.ofReal (|routeMCore M x| ^ (-c')) with hg
  have hpre := hmp.setLIntegral_comp_preimage_emb hemb g (cubeBox (routeMAmbient M) ε)
  apply top_le_iff.1
  calc (⊤ : ℝ≥0∞)
      = ∫⁻ u in S, g (phi u) := hSdiv.symm
    _ ≤ ∫⁻ u in phi ⁻¹' (cubeBox (routeMAmbient M) ε), g (phi u) := lintegral_mono_set hSsub
    _ = ∫⁻ x in cubeBox (routeMAmbient M) ε, g x := hpre

/-! ### The radial-MP-chart box-divergence (route b, `minAdm ≥ 2` — radial Jacobian
`|z|^{minAdm−1}`)

For `minAdm ≥ 2` the smeared chart `φ = ψ ∘ R` has a RADIAL blow-up `R` (det `|z|^{minAdm−1} ≠ 1`,
so
`φ` is NOT measure-preserving). The reusable assembly (Codex `radial-mp-assembly`): `ψ = Q ∘ shear`
is
the measure-preserving measurable-embedding part (the rational pole confined here, NEVER
differentiated);
`R` is the polynomial radial (differentiable everywhere, the ONLY Jacobian carrier). The source
certificate `hsrc` is now WEIGHTED — `∫_S |u_p|^{minAdm−1}·(loss∘φ)^{−c} = ⊤` (the radial Jacobian
absorbed into the binding-axis divergence: exponent `minAdm−1−2c ≤ −1` from `c ≥ minAdm/2`).
`routeMCore_box_diverges_of_MPChart` is the `R = id, h = 0` special case (kept as the lighter
sibling). -/

/-- **The radial-MP-chart box-divergence (route b, reusable, `minAdm ≥ 2`).** `φ = ψ ∘ R`, `ψ`
measure-preserving + measurable embedding (the rational/MP part), `R` the radial blow-up
(`HasFDerivWithinAt`/`InjOn`/`|det| = |u_p|^{minAdm−1}` on a certified preimage source `S`), and a
WEIGHTED source-divergence `∫_S |u_p|^{h}·(loss∘ψ∘R)^{−c} = ⊤`. The c-o-v: `ψ`-preimage
(`setLIntegral_comp_preimage_emb`) + `R`-image Jacobian
(`lintegral_image_eq_lintegral_abs_det_fderiv_mul`). -/
theorem routeMCore_box_diverges_of_RadialMPChart {L : ℕ} (M : Fin (L + 1) → ℕ)
    (ψ R : (Fin (routeMAmbient M) → ℝ) → (Fin (routeMAmbient M) → ℝ))
    (D : (Fin (routeMAmbient M) → ℝ) → (Fin (routeMAmbient M) → ℝ) →L[ℝ] (Fin (routeMAmbient M) → ℝ))
    (p : Fin (routeMAmbient M)) (h : ℕ)
    (hmp : MeasurePreserving ψ (volume : Measure (Fin (routeMAmbient M) → ℝ)) volume)
    (hemb : MeasurableEmbedding ψ) (c' : ℝ) (ε : ℝ)
    (hsrc : ∃ S : Set (Fin (routeMAmbient M) → ℝ), MeasurableSet S ∧
      S ⊆ (fun u => ψ (R u)) ⁻¹' (cubeBox (routeMAmbient M) ε) ∧
      (∀ u ∈ S, HasFDerivWithinAt R (D u) S u) ∧ Set.InjOn R S ∧
      (∀ u ∈ S, |(D u).det| = |u p| ^ h) ∧
      (∫⁻ u in S, ENNReal.ofReal (|u p| ^ h)
        * ENNReal.ofReal (|routeMCore M (ψ (R u))| ^ (-c'))) = ⊤) :
    ∫⁻ x in cubeBox (routeMAmbient M) ε,
      ENNReal.ofReal (|routeMCore M x| ^ (-c')) = ⊤ := by
  obtain ⟨S, hSmeas, hSpre, hRderiv, hRinj, hRdet, hSdiv⟩ := hsrc
  set g := fun x : Fin (routeMAmbient M) → ℝ => ENNReal.ofReal (|routeMCore M x| ^ (-c')) with hg
  -- ψ-preimage c-o-v: ∫_{ψ⁻¹(cubeBox)} g∘ψ = ∫_{cubeBox} g
  have hψ : ∫⁻ y in ψ ⁻¹' (cubeBox (routeMAmbient M) ε), g (ψ y)
      = ∫⁻ x in cubeBox (routeMAmbient M) ε, g x :=
    hmp.setLIntegral_comp_preimage_emb hemb g (cubeBox (routeMAmbient M) ε)
  -- R '' S ⊆ ψ⁻¹(cubeBox) (since S ⊆ (ψ∘R)⁻¹(cubeBox))
  have hRimage : R '' S ⊆ ψ ⁻¹' (cubeBox (routeMAmbient M) ε) := by
    rintro y ⟨u, hu, rfl⟩; exact hSpre hu
  -- R-image Jacobian c-o-v on S
  have hcov : ∫⁻ y in R '' S, g (ψ y)
      = ∫⁻ u in S, ENNReal.ofReal (|u p| ^ h) * g (ψ (R u)) := by
    rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hSmeas hRderiv hRinj (fun y => g (ψ y))]
    refine setLIntegral_congr_fun hSmeas (fun u hu => ?_)
    rw [hRdet u hu]
  apply top_le_iff.1
  calc (⊤ : ℝ≥0∞)
      = ∫⁻ u in S, ENNReal.ofReal (|u p| ^ h) * g (ψ (R u)) := hSdiv.symm
    _ = ∫⁻ y in R '' S, g (ψ y) := hcov.symm
    _ ≤ ∫⁻ y in ψ ⁻¹' (cubeBox (routeMAmbient M) ε), g (ψ y) := lintegral_mono_set hRimage
    _ = ∫⁻ x in cubeBox (routeMAmbient M) ε, g x := hψ

/-! ### The `(1,2,1)` source certificate `hsrc` + the atom (the bounded finish, route b)

`S = subBox121 δ` (Codex `mp-final-step`): `a = u 0 ∈ [δ/2, δ]` (bounded away from the pole),
`b = u 1, sb = u 3 ∈ [−δ, δ]`, `z = u 2 ∈ (0, δ)`. Sub-goal 1 (containment): each flat coord of
`phi121sm u = paramsEquivFlat (chartParams121 u)` is a matrix entry (`rfl` readout), `≤ 4δ` on the
bounded-away box. Sub-goal 2 (divergence): the rate `z²·a²` + the `z`-axis monomial divergence. -/

/-- The `(1,2,1)` divergence sub-box `Pδ`. -/
def subBox121 (δ : ℝ) : Set (Fin 4 → ℝ) :=
  {u | u 0 ∈ Set.Icc (δ/2) δ ∧ u 1 ∈ Set.Icc (-δ) δ ∧ u 2 ∈ Set.Ioo (0:ℝ) δ ∧
    u 3 ∈ Set.Icc (-δ) δ}

/-- **Each flat coord of `phi121sm u` is a matrix entry of `chartParams121 u`** (`rfl` —
`paramsEquivFlat
A i = A` at the canonical slot `(Fintype.equivFin (FlatIdx M121)).symm i`). -/
theorem phi121sm_entry (u : Fin 4 → ℝ) (i : Fin (flatDim M121)) :
    phi121sm u i = (chartParams121 u)
      ((Fintype.equivFin (FlatIdx M121)).symm i).1.1
      ((Fintype.equivFin (FlatIdx M121)).symm i).1.2
      ((Fintype.equivFin (FlatIdx M121)).symm i).2 := rfl

/-- **Every matrix entry of `chartParams121 u` is `≤ 4δ` on `subBox121 δ`** (`δ > 0`). The two
layer-0
entries are `a, b`; the two layer-1 entries are `z − (b/a)·sb` (the only nontrivial one, `≤ 3δ`
since
`a ≥ δ/2`) and `sb`. -/
theorem chartParams121_entry_bound {δ : ℝ} (hδ : 0 < δ) {u : Fin 4 → ℝ} (hu : u ∈ subBox121 δ)
    (s : Fin 2) (i : Fin (M121 s.castSucc)) (j : Fin (M121 s.succ)) :
    |(chartParams121 u) s i j| ≤ 4 * δ := by
  obtain ⟨ha, hb, hz, hsb⟩ := hu
  simp only [Set.mem_Icc] at ha hb hsb
  simp only [Set.mem_Ioo] at hz
  have ha0 : (0:ℝ) < u 0 := lt_of_lt_of_le (by linarith) ha.1
  -- pin the four coord bounds
  have hba : |u 0| ≤ δ := by rw [abs_of_pos ha0]; exact ha.2
  have hbb : |u 1| ≤ δ := abs_le.mpr ⟨hb.1, hb.2⟩
  have hbz : |u 2| ≤ δ := abs_le.mpr ⟨by linarith [hz.1], le_of_lt hz.2⟩
  have hbsb : |u 3| ≤ δ := abs_le.mpr ⟨hsb.1, hsb.2⟩
  -- the shear entry bound: |z − (b/a)·sb| ≤ 3δ ≤ 4δ
  have hak : |u 1| / u 0 ≤ 2 := by
    rw [div_le_iff₀ ha0]
    calc |u 1| ≤ δ := hbb
      _ ≤ 2 * u 0 := by linarith [ha.1]
  have hbound : |u 1 / u 0 * u 3| ≤ 2 * δ := by
    rw [abs_mul, abs_div, abs_of_pos ha0]
    have := mul_le_mul hak hbsb (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 2)
    linarith [this]
  have hshear : |u 2 - u 1 / u 0 * u 3| ≤ 4 * δ := by
    have h1 : |u 2 - u 1 / u 0 * u 3| ≤ |u 2| + |u 1 / u 0 * u 3| := abs_sub _ _
    linarith [h1, hbz, hbound]
  -- each of the four entries is one of {a, b, z−(b/a)sb, sb}, all ≤ 4δ
  fin_cases s
  · fin_cases i <;> fin_cases j
    · show |chartA0_121 u 0 0| ≤ 4 * δ
      simp only [chartA0_121, Matrix.cons_val_zero, Matrix.of_apply, Matrix.cons_val]; linarith [hba]
    · show |chartA0_121 u 0 1| ≤ 4 * δ
      simp only [chartA0_121, Matrix.cons_val_one, Matrix.head_cons, Matrix.of_apply,
        Matrix.cons_val]; linarith [hbb]
  · fin_cases i <;> fin_cases j
    · show |chartA1_121 u 0 0| ≤ 4 * δ
      simpa only [chartA1_121, Matrix.cons_val_zero, Matrix.of_apply, Matrix.cons_val,
        Matrix.cons_val_fin_one] using hshear
    · show |chartA1_121 u 1 0| ≤ 4 * δ
      simp only [chartA1_121, Matrix.cons_val_one, Matrix.head_cons, Matrix.of_apply,
        Matrix.cons_val, Matrix.cons_val_fin_one]; linarith [hbsb]

/-- **Containment** `subBox121 δ ⊆ phi121sm⁻¹(cubeBox 4 (4δ))` (`δ > 0`): each flat coord is a
matrix
entry (`phi121sm_entry`), bounded by `4δ` on the box (`chartParams121_entry_bound`). -/
theorem subBox121_subset_preimage {δ : ℝ} (hδ : 0 < δ) :
    subBox121 δ ⊆ phi121sm ⁻¹' (cubeBox (flatDim M121) (4 * δ)) := by
  intro u hu
  rw [Set.mem_preimage, cubeBox, Set.mem_pi]
  intro i _
  rw [Set.mem_Icc, ← abs_le, phi121sm_entry]
  exact chartParams121_entry_bound hδ hu _ _ _

/-- `subBox121 δ` is measurable (a finite intersection of coordinate-interval preimages). -/
theorem measurableSet_subBox121 (δ : ℝ) : MeasurableSet (subBox121 δ) := by
  unfold subBox121
  refine MeasurableSet.inter (measurableSet_preimage (measurable_pi_apply 0) measurableSet_Icc) ?_
  refine MeasurableSet.inter (measurableSet_preimage (measurable_pi_apply 1) measurableSet_Icc) ?_
  exact MeasurableSet.inter (measurableSet_preimage (measurable_pi_apply 2) measurableSet_Ioo)
    (measurableSet_preimage (measurable_pi_apply 3) measurableSet_Icc)

/-! ### Sub-goal 2 — the divergence on `subBox121` (the rate `z²·a²` + the z-axis monomial)

`subBox121 δ` factors as the `univ.pi` of per-axis intervals; on it the rate `loss∘φ = z²·a²` holds
(`a ≥ δ/2 > 0`). `(z²a²)^{−c'} = |z|^{−2c'}·|a|^{−2c'}` reads only `z, a`; peel the `z`-axis (index
2)
via `piFinSuccAbove`, `setLIntegral_prod` — the `z`-factor over `(0,δ)` is `⊤`
(`abs_rpow_lintegral_Ioo_eq_top`, exp `−2c' ≤ −1` from `c' ≥ minAdm/2 = ½`), the rest
positive-finite. -/

/-- `subBox121 δ` as a `univ.pi` of per-axis intervals. -/
theorem subBox121_eq_pi (δ : ℝ) :
    subBox121 δ = Set.univ.pi
      (fun i : Fin 4 => if i = 2 then Set.Ioo (0:ℝ) δ
        else if i = 0 then Set.Icc (δ/2) δ else Set.Icc (-δ) δ) := by
  ext u
  simp only [subBox121, Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, true_implies]
  constructor
  · rintro ⟨h0, h1, h2, h3⟩ i
    fin_cases i
    · simpa using h0
    · simpa using h1
    · simpa using h2
    · simpa using h3
  · intro h
    refine ⟨?_, ?_, ?_, ?_⟩
    · have := h 0; simpa using this
    · have := h 1; simpa using this
    · have := h 2; simpa using this
    · have := h 3; simpa using this

/-- **The divergence on `subBox121`** `∫_{subBox121 δ} (|loss∘φ|)^{−c'} = ⊤` for `δ > 0`, `c' ≥ ½`.
On
`Pδ` the rate `loss∘φ = (u 2)²·(u 0)²` (`a > 0`), so the integrand is `|u 2|^{−2c'}·|u 0|^{−2c'}`;
peel
the `z`-axis (index 2) via `piFinSuccAbove`/`setLIntegral_prod` — the `z`-factor over `(0,δ)` is `⊤`
(`abs_rpow_lintegral_Ioo_eq_top`, exp `−2c' ≤ −1`), the rest positive-finite. -/
theorem subBox121_diverges {δ : ℝ} (hδ : 0 < δ) {c' : ℝ} (hc' : (1:ℝ)/2 ≤ c') :
    ∫⁻ u in subBox121 δ,
      ENNReal.ofReal (|routeMCore M121 (phi121sm u)| ^ (-c')) = ⊤ := by
  -- rewrite the integrand to the per-axis rpow product `|u 2|^{-2c'} * |u 0|^{-2c'}` on `Pδ`
  have hrw : ∀ u ∈ subBox121 δ,
      ENNReal.ofReal (|routeMCore M121 (phi121sm u)| ^ (-c'))
        = ENNReal.ofReal (|u 2| ^ (-(2*c'))) * ENNReal.ofReal (|u 0| ^ (-(2*c'))) := by
    intro u hu
    obtain ⟨ha, _, _, _⟩ := hu
    simp only [Set.mem_Icc] at ha
    have ha0 : u 0 ≠ 0 := ne_of_gt (lt_of_lt_of_le (by linarith) ha.1)
    rw [routeMCore_phi121sm_offpole u ha0]
    rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ (u 2)^2 * (u 0)^2),
      show (u 2)^2 * (u 0)^2 = |u 2|^2 * |u 0|^2 by rw [sq_abs, sq_abs]]
    rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_natCast |u 2| 2,
      ← Real.rpow_natCast |u 0| 2, ← Real.rpow_mul (abs_nonneg _), ← Real.rpow_mul (abs_nonneg _),
      ← ENNReal.ofReal_mul (by positivity)]
    congr 2 <;> push_cast <;> ring
  rw [setLIntegral_congr_fun (measurableSet_subBox121 δ) (fun u hu => hrw u hu)]
  rw [subBox121_eq_pi]
  -- peel the z-axis (index 2) via `piFinSuccAbove`
  set ee := MeasurableEquiv.piFinSuccAbove (fun _ : Fin 4 => ℝ) 2 with hee
  have hmpS : MeasurePreserving ee.symm (volume : Measure (ℝ × (Fin 3 → ℝ))) volume := by
    have h := (volume_preserving_piFinSuccAbove (fun _ : Fin 4 => ℝ) 2).symm
    rwa [show (volume : Measure (ℝ × (Fin 3 → ℝ))) = (volume : Measure ℝ).prod volume from
      Measure.volume_eq_prod _ _] at h
  have hsymapp : ∀ x (y : Fin 3 → ℝ), ee.symm (x, y) = Fin.insertNth 2 x y :=
    fun x y => by rw [hee, MeasurableEquiv.piFinSuccAbove_symm_apply]; exact List.ofFn_inj.mp rfl
  -- the box pulls back to `Ioo 0 δ ×ˢ (rest box)`
  set restSet : Set (Fin 3 → ℝ) := Set.univ.pi
    (fun k : Fin 3 => if (Fin.succAbove 2 k) = (0 : Fin 4) then Set.Icc (δ/2) δ else Set.Icc (-δ) δ)
    with hrestSet
  have hpre : ee.symm ⁻¹' (Set.univ.pi (fun i : Fin 4 => if i = 2 then Set.Ioo (0:ℝ) δ
        else if i = 0 then Set.Icc (δ/2) δ else Set.Icc (-δ) δ))
      = (Set.Ioo (0:ℝ) δ) ×ˢ restSet := by
    ext p; obtain ⟨x, y⟩ := p
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_prod, hsymapp,
      hrestSet]
    constructor
    · intro hall
      refine ⟨?_, fun k => ?_⟩
      · have := hall 2; rwa [Fin.insertNth_apply_same, if_pos rfl] at this
      · have := hall (Fin.succAbove 2 k); rw [Fin.insertNth_apply_succAbove] at this
        rwa [if_neg (Fin.succAbove_ne 2 k)] at this
    · rintro ⟨h0, hrest⟩ j
      rcases Fin.eq_self_or_eq_succAbove 2 j with rfl | ⟨k, rfl⟩
      · rwa [Fin.insertNth_apply_same, if_pos rfl]
      · rw [Fin.insertNth_apply_succAbove, if_neg (Fin.succAbove_ne 2 k)]; exact hrest k
  have htrans := hmpS.setLIntegral_comp_preimage_emb (MeasurableEquiv.measurableEmbedding _)
    (fun u : Fin 4 → ℝ => ENNReal.ofReal (|u 2| ^ (-(2*c'))) * ENNReal.ofReal (|u 0| ^ (-(2*c'))))
    (Set.univ.pi (fun i : Fin 4 => if i = 2 then Set.Ioo (0:ℝ) δ
        else if i = 0 then Set.Icc (δ/2) δ else Set.Icc (-δ) δ))
  rw [hpre] at htrans
  rw [← htrans]
  -- the integrand under `ee.symm` is `ofReal(|x|^p) * ofReal(|y₀|^p)` (a = coord 0 = succAbove 2 0)
  have hidx : Fin.succAbove (2 : Fin 4) (0 : Fin 3) = (0 : Fin 4) := by decide
  have hfac : ∀ x (y : Fin 3 → ℝ),
      ENNReal.ofReal (|ee.symm (x, y) 2| ^ (-(2*c'))) * ENNReal.ofReal (|ee.symm (x, y) 0| ^ (-(2*c')))
        = ENNReal.ofReal (|x| ^ (-(2*c'))) * ENNReal.ofReal (|y 0| ^ (-(2*c'))) := by
    intro x y
    have e2 : ee.symm (x, y) 2 = x := by rw [hsymapp, Fin.insertNth_apply_same]
    have e0 : ee.symm (x, y) 0 = y 0 := by
      rw [hsymapp, show (0 : Fin 4) = Fin.succAbove 2 0 from hidx.symm, Fin.insertNth_apply_succAbove]
    rw [e2, e0]
  simp_rw [hfac]
  rw [show (volume : Measure (ℝ × (Fin 3 → ℝ))) = (volume : Measure ℝ).prod volume from
    Measure.volume_eq_prod _ _]
  rw [setLIntegral_prod _ (by
    apply Measurable.aemeasurable
    exact ((by fun_prop : Measurable (fun p : ℝ × (Fin 3 → ℝ) => ENNReal.ofReal (|p.1| ^ (-(2*c'))))).mul
      (by fun_prop : Measurable (fun p : ℝ × (Fin 3 → ℝ) => ENNReal.ofReal (|p.2 0| ^ (-(2*c')))))))]
  have hinner : ∀ x, (∫⁻ y in restSet, ENNReal.ofReal (|x| ^ (-(2*c')))
      * ENNReal.ofReal (|y 0| ^ (-(2*c'))) ∂(volume : Measure (Fin 3 → ℝ)))
      = ENNReal.ofReal (|x| ^ (-(2*c'))) * (∫⁻ y in restSet,
        ENNReal.ofReal (|y 0| ^ (-(2*c'))) ∂(volume : Measure (Fin 3 → ℝ))) :=
    fun x => lintegral_const_mul _ (by fun_prop)
  simp only [hinner]
  rw [lintegral_mul_const _ (by fun_prop : Measurable (fun x : ℝ => ENNReal.ofReal (|x| ^ (-(2*c')))))]
  -- z-factor over (0,δ) = ⊤ (exp -2c' ≤ -1), rest factor > 0
  rw [abs_rpow_lintegral_Ioo_eq_top _ δ hδ (by linarith)]
  refine ENNReal.top_mul (ne_of_gt ?_)
  -- the rest factor is positive: integrand > 0 on the positive-measure rest box
  rw [hrestSet, setLIntegral_pos_iff (by fun_prop)]
  have hbox : 0 < (volume : Measure (Fin 3 → ℝ)) (Set.univ.pi
      (fun k : Fin 3 => if (Fin.succAbove 2 k) = (0 : Fin 4) then Set.Icc (δ/2) δ
        else Set.Icc (-δ) δ)) := by
    rw [volume_pi_pi]
    refine CanonicallyOrderedAdd.prod_pos.mpr (fun k _ => ?_)
    by_cases hk : (Fin.succAbove 2 k) = (0 : Fin 4)
    · rw [if_pos hk, Real.volume_Icc, ENNReal.ofReal_pos]; linarith
    · rw [if_neg hk, Real.volume_Icc, ENNReal.ofReal_pos]; linarith
  apply lt_of_lt_of_le hbox
  apply measure_mono
  intro y hy
  refine ⟨?_, hy⟩
  simp only [Set.mem_pi, Set.mem_univ, true_implies] at hy
  have hy0 : 0 < y 0 := by
    have := hy 0; rw [hidx, if_pos rfl, Set.mem_Icc] at this; linarith
  rw [Function.mem_support, ne_eq, ENNReal.ofReal_eq_zero, not_le]
  exact Real.rpow_pos_of_pos (by rw [abs_pos]; exact ne_of_gt hy0) _

/-! ### The `(1,2,1)` smeared achiever box-divergence atom (route b, via the MP-final lemma) -/

/-- **The `(1,2,1)` smeared box-divergence** — `∫⁻_{cubeBox 4 ε} |routeMCore M121|^{−c'} = ⊤` for
`c'`
at-or-above `½·minAdm M121 = ½`, every `ε > 0`. The atom for the smallest boundary-SMEARED node,
discharged via the reusable MP-final lemma `routeMCore_box_diverges_of_MPChart` (route b — NO
`image_subset`, NO `HasFDerivAt`) fed the source certificate `hsrc` (the bounded-away sub-box
`subBox121 (ε/4) ⊆ phi121sm⁻¹(cubeBox 4 ε)` with the rate `z²·a²` giving the monomial divergence).
-/
theorem routeM121sm_box_diverges (c' : NNReal) (hc' : (minAdm M121 : ℝ≥0∞) / 2 ≤ (c' : ℝ≥0∞))
    (ε : ℝ) (hε : 0 < ε) :
    ∫⁻ x in cubeBox (routeMAmbient M121) ε,
      ENNReal.ofReal (|routeMCore M121 x| ^ (-(c' : ℝ))) = ⊤ := by
  -- `½ ≤ c'` from `minAdm M121 = 1`
  have hc'half : (1:ℝ)/2 ≤ (c' : ℝ) := by
    have : (minAdm M121 : ℝ≥0∞) / 2 = ((1:ℝ≥0∞)) / 2 := by rw [minAdm_M121]; norm_num
    rw [this] at hc'
    have h2 : ((1:ℝ≥0∞))/2 ≤ (c' : ℝ≥0∞) := hc'
    have : (1:ℝ)/2 ≤ (c' : ℝ) := by
      rw [show ((1:ℝ≥0∞))/2 = ENNReal.ofReal (1/2) by
        rw [ENNReal.ofReal_div_of_pos (by norm_num)]; norm_num] at h2
      rwa [ENNReal.ofReal_le_iff_le_toReal (by simp), ENNReal.coe_toReal] at h2
    exact this
  refine routeMCore_box_diverges_of_MPChart M121 phi121sm measurePreserving_phi121sm
    measurableEmbedding_phi121sm (c' : ℝ) ε ⟨subBox121 (ε/4), measurableSet_subBox121 _, ?_, ?_⟩
  · -- containment: `subBox121 (ε/4) ⊆ phi121sm⁻¹(cubeBox _ ε)` (`4·(ε/4) = ε`)
    have h := subBox121_subset_preimage (by linarith : (0:ℝ) < ε/4)
    rwa [show 4 * (ε/4) = ε by ring] at h
  · exact subBox121_diverges (by linarith : (0:ℝ) < ε/4) hc'half

end DLNFibre.DLN.RLCT
