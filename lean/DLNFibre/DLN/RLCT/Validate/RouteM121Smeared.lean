import DLNFibre.DLN.RLCT.Validate.NodeAchieverChart
import DLNFibre.DLN.RLCT.Validate.RouteM221
import DLNFibre.DLN.RLCT.Validate.Case222Resolution
import DLNFibre.Core.MeasureTheory.PolynomialZeroSet
import Mathlib.Algebra.MvPolynomial.Basic

/-!
# `RouteM121Smeared` — the BOUNDARY-SMEARED achiever box-divergence VALIDATE-SMALL `(1,2,1)`

The smallest boundary-SMEARED node `M = (1,2,1)` (`L = 2`, `r = Text(L) = 1`, `c = M_L = 1`,
`m1 = M_{L−1} = 2`, `s = m1 − r = 1`, `minAdm = r·c = 1`, `flatDim = 4`) — the validate-small that
PINS the precise wall in building the RATIONAL single-pivot chart `φ_sm`
(`certificate-genM-smeared.md`) into the EXISTING `NodeAchieverChart`.

**Finding (the wall, handed back): the rational chart does NOT fit the existing structure.** The
rate
`F∘φ = z²·U` holds ONLY off the rational pole `{a = 0}`, so the `leaf_integrand` field — which the
banked assembly rewrites POINTWISE `∀ u` — cannot be met. This is EARLIER than the `cov` split the
controller scoped: `leaf_integrand` breaks too. See the statement card + the bottom note.

## The chart (`certificate-genM-smeared.md` §2, specialized to `(1,2,1)`)
Coords `(a, b, z, sb) : Fin 4 → ℝ`. The front product `P = A⁽⁰⁾ = [a, b]` (`1×2`); `P₁ = [a]`,
`P₂ = [b]`; the rational routing `Λ₀ = (P₁ᵀP₁)⁻¹P₁ᵀP₂ = b/a`. The deepest factor
`A⁽¹⁾ = [z·H̄ − Λ₀·S_bot ; S_bot] = [z − (b/a)·sb ; sb]` (`2×1`, `H̄(0,0) = 1`). Then

    A⁽⁰⁾·A⁽¹⁾ = a·(z − (b/a)·sb) + b·sb = a·z   ⟹   F = ‖A⁽⁰⁾·A⁽¹⁾‖² = a²·z² = z²·U,  U = a².

`U = a²` is a POLYNOMIAL (the rational `b/a` cancels out of `F`). `minAdm = 1`, so the radial det is
`|z|^{minAdm−1} = |z|⁰ = 1`: `(1,2,1)` exercises the rational SHEAR (NOT the radial blow-up — the
next
validate-small `(2,3,1)` / `(1,3,2)` has `minAdm ≥ 2`).

## The two walls (BOTH pole-affected, the handback)
`φ_sm` is RATIONAL: `Λ₀ = b/a` is undefined on the pole `N0 := {a = 0}` (the front Gram minor
`P₁ᵀP₁ = a² = 0`), a Lebesgue-null hypersurface NOT inside the radial-pivot locus `{z = 0}`.

1. **`leaf_integrand` (∀ u) — the EARLIER wall.** The rate `F∘φ = z²·U` holds only off `N0`
   (`dlnLoss_chartParams121_offpole`); ON `N0` the loss is genuinely positive
   (`dlnLoss_chartParams121_pole_pos`: `= 1` at `(0,1,7,1)`), so no `z²·U` factorization holds
   there.
   `leaf_integrand` is rewritten POINTWISE on all of `[0,δ]^N` in the banked assembly
   `routeMCore_box_diverges_of_nodeChart`, so the rational chart cannot supply it.
2. **`cov` — the controller's scoped split.** The Mathlib all-x∈s c-o-v
   (`lintegral_image_eq_lintegral_abs_det_fderiv_mul`) fails on `s = V\{z=0}` (φ_sm
   non-differentiable
   on `N0 ⊆ s`); the split (c-o-v on `s\N0` + image-null `φ_sm '' (s∩N0) ⊆ {a-coord=0}`) repairs it.

Codex (xhigh, decorrelated, `codex/smeared-leafintegrand-{prompt,answer}.md`) confirms option (a) as
framed does NOT survive: the cheapest sound fix is an a.e. `leaf_integrand` field + an a.e. rewrite
in
the assembly (touching the banked M-agnostic core) — a controller-gated structure change.

This file PROVES the rate split (off-pole rate + on-pole positivity, the wall witness), sorry-free +
axiom-clean. It does NOT build the chart instance (blocked on the structure change). -/

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

end DLNFibre.DLN.RLCT
