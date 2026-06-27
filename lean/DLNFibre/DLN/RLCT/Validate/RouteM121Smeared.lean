import DLNFibre.DLN.RLCT.Validate.NodeAchieverChart
import DLNFibre.DLN.RLCT.Validate.RouteM221
import DLNFibre.DLN.RLCT.Validate.Case222Resolution
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

/-- **The chart in flat coordinates** `phi121sm := paramsEquivFlat M121 ∘ chartParams121`. -/
noncomputable def phi121sm (u : Fin 4 → ℝ) : Fin 4 → ℝ :=
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

/-! ### Residual for the full `(1,2,1)` smeared instance (the `cov` split assembly)

LANDED (sorry-free, this module): the chart `phi121sm`, the off-pole rate
(`routeMCore_phi121sm_offpole`), the **a.e. `leaf_integrand`** (`leaf_integrand121_ae`, the piece
the
option-(i) a.e. core unlocks), `Uval121`/`leafH121`/`leafH121_pivot`, the shear factorization
(`chartParams121_eq_pack_shear`), `shear121_injOn` (off-pole), `pole121_null`, and the shear
Jacobian
**det `= 1`** (`shear121DerivMat_det`, via the transvection chain).

RESIDUAL (the `cov` split + `image_subset` + the instance assembly — standard but fiddly analysis):
* `shear121_hasFDerivAt` off the pole (the rational comp-`2` `z − (b/a)·sb` is C¹ for `u 0 ≠ 0`;
  fderiv = `shear121DerivMat u` by `mulVec`) → `phi121sm_hasFDerivAt` (chain with the linear
  measure-preserving `Q121 = paramsEquivFlat ∘ pack121`), giving `|det Dφ| = 1` (=
  `∏|u_j|^{leafH121 j}`).
* `phi121sm_cov` via the `phi334_cov` TWO-SLICE split: c-o-v
  (`lintegral_image_eq_lintegral_abs_det_fderiv_mul`) on `S \ N0` (`N0 = {u 0 = 0}`, where
  `phi121sm` is
  C¹/InjOn/`|det|=1`); add back `S ∩ N0` — RHS null (`leafH121≡0`, weight `1`; `N0` null); LHS
  image-null
  `volume (phi121sm '' (S ∩ N0)) = 0` via the FRONT-block-identity containment `⊆ {first flat coord
  reads `a = 0`}` (a target null hypersurface — NOT Luzin-N, which fails for the non-Lipschitz
  pole).
* then the `NodeAchieverChart M121` instance (a.e. `leaf_integrand := leaf_integrand121_ae`) +
  `routeMCore_box_diverges_of_nodeChart` discharges the atom for `(1,2,1)`.

This module establishes the wall-resolution (the a.e. core makes the smeared `leaf_integrand`
dischargeable) and banks the rate/det; the `cov`-split assembly is the bounded remaining analysis.
-/

end DLNFibre.DLN.RLCT
