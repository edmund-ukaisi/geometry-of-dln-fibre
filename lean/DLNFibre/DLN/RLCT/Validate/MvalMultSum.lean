import DLNFibre.DLN.RLCT.Foundations.Lambda
import DLNFibre.Core.CTheta
import DLNFibre.Core.CascadeAchiever

/-!
# `DLNFibre.DLN.RLCT.Validate.MvalMultSum` — the combinatorial `Mval = codimForm` bridge (#136/#146)

The geometric-headline extension: the candidate `Mval M T` (Aoyagi's RLCT-contribution value,
`Foundations/Lambda.lean`) equals the **LR quadratic codimension form** `codimForm` (Cor 3.5, `Core/CTheta`)
evaluated on the mixed difference of the **cascade rank array** `cascadeRank M T`. This is the paper's "new
content" tie — the minimal codim `minAdm = ½·…` reads as a genuine orbit codimension — at the level of the
signed ring identity.

**SCOPE (Codex-decorrelated verdict, `threads/.../codex/mval-multsum-answer.md`): this is a SIGNED RING
IDENTITY, holding for ALL `M, T` with NO admissibility.** The cascade rank `r_{a,b} = ρ_b + (M_a − ρ_a)`
(`ρ = expSurvivor`); its mixed difference `diffRank` is boundary-supported, and the `codimForm` quadruple sum
collapses to `Mval` by pure algebra (no inequalities). The GEOMETRIC reading `codimForm (diffRank r) = codim
Ō` additionally needs `diffRank r ≥ 0` (a Kostant multiplicity array exists), which is the width-monotone /
admissible hypothesis — a SEPARATE scoped corollary, NOT proved here. On a width-spike `M` the ring identity
still holds but `codimForm` is not a codimension. The name says exactly this: a signed-`Mval` identity.

The proof (Codex-mapped collapse): `diffRank (cascadeRank M T)` vanishes in the interior `1 ≤ a ≤ b < L`;
its top row is `ρ_b − ρ_{b+1}` and its right column is `q_a − q_{a−1}` (`q_a = M_a − ρ_a`, `q_0 = 0`). In
`codimForm`'s quadruple sum the first factor `m (i−1) (j−1)` forces `i = 1` (`j−1 < L`) and the second
`m u v` forces `v = L`, leaving `Σ_{u≤j} (ρ_{j−1} − ρ_j)(q_u − q_{u−1})`; the inner telescopes (`q_0 = 0`) to
`Σ_j (ρ_{j−1} − ρ_j) q_j = Mval`.
-/

open scoped BigOperators
open Finset

namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-- `ρ_a` as a plain `ℤ` value at an in-range index `a ∈ [0, L]`: `Core.expSurvivor M T` (`ρ_0 = M 0`,
`ρ_{k+1} = T_k`). Used only inside the box of `cascadeRank`. -/
noncomputable def rhoVal (M : Fin (L + 1) → ℕ) (T : Fin L → ℕ) (a : ℤ) (h : 0 ≤ a ∧ a ≤ (L : ℤ)) : ℤ :=
  (Core.expSurvivor M T ⟨a.toNat, by omega⟩ : ℤ)

/-- The **cascade rank array** `r_{a,b}` (`ℤ`-indexed). On the box `0 ≤ a, b ≤ L`: `r_{a,b} = ρ_b + (M_a −
ρ_a)`. OUTSIDE the box: `0` (the `diff` boundary convention `r(−1, ·) = 0`, `r(·, L+1) = 0`). The whole `r`
is clamped — NOT `ρ`/`q` separately (separable clamping would make `diff r ≡ 0`). `diff r` is then
boundary-supported and its `codimForm` is `Mval`. -/
noncomputable def cascadeRank (M : Fin (L + 1) → ℕ) (T : Fin L → ℕ) : ℤ → ℤ → ℤ :=
  fun a b ↦
    if ha : 0 ≤ a ∧ a ≤ (L : ℤ) then
      if hb : 0 ≤ b ∧ b ≤ (L : ℤ) then
        rhoVal M T b hb + ((M ⟨a.toNat, by omega⟩ : ℤ) - rhoVal M T a ha)
      else 0
    else 0

/-- The **mixed second difference** `(diff r)_{a,b} = r_{a,b} − r_{a−1,b} − r_{a,b+1} + r_{a−1,b+1}` — the
multiplicity array of the interval-module decomposition. `codimForm` consumes this. -/
def diffRank (r : ℤ → ℤ → ℤ) : ℤ → ℤ → ℤ :=
  fun a b ↦ r a b - r (a - 1) b - r a (b + 1) + r (a - 1) (b + 1)

/-- `cascadeRank` is `0` when the row index is out of `[0, L]` (`r(−1, ·) = 0`, the left/below boundary). -/
theorem cascadeRank_of_row_oob (M : Fin (L + 1) → ℕ) (T : Fin L → ℕ) (a b : ℤ)
    (ha : ¬ (0 ≤ a ∧ a ≤ (L : ℤ))) : cascadeRank M T a b = 0 := by
  unfold cascadeRank; rw [dif_neg ha]

/-- `cascadeRank` is `0` when the column index is out of `[0, L]` (`r(·, L+1) = 0`, the right boundary). -/
theorem cascadeRank_of_col_oob (M : Fin (L + 1) → ℕ) (T : Fin L → ℕ) (a b : ℤ)
    (hb : ¬ (0 ≤ b ∧ b ≤ (L : ℤ))) : cascadeRank M T a b = 0 := by
  unfold cascadeRank; split_ifs <;> simp_all

/-- In-box value: `cascadeRank M T a b = ρ_b + (M_a − ρ_a)` for `a, b ∈ [0, L]`. -/
theorem cascadeRank_in_box (M : Fin (L + 1) → ℕ) (T : Fin L → ℕ) (a b : ℤ)
    (ha : 0 ≤ a ∧ a ≤ (L : ℤ)) (hb : 0 ≤ b ∧ b ≤ (L : ℤ)) :
    cascadeRank M T a b = rhoVal M T b hb + ((M ⟨a.toNat, by omega⟩ : ℤ) - rhoVal M T a ha) := by
  unfold cascadeRank; rw [dif_pos ha, dif_pos hb]

/-- `rhoVal` at index `0` is `M 0` (`ρ_0 = M_0`; `expSurvivor … 0 = M 0`). -/
theorem rhoVal_zero (M : Fin (L + 1) → ℕ) (T : Fin L → ℕ) (h : 0 ≤ (0 : ℤ) ∧ (0 : ℤ) ≤ (L : ℤ)) :
    rhoVal M T 0 h = (M 0 : ℤ) := by
  unfold rhoVal
  have : (⟨(0 : ℤ).toNat, by omega⟩ : Fin (L + 1)) = 0 := by apply Fin.ext; simp
  rw [this, Core.expSurvivor_zero]

/-- `rhoVal` is proof-irrelevant in its range hypothesis (it only uses `a.toNat`). -/
theorem rhoVal_pi (M : Fin (L + 1) → ℕ) (T : Fin L → ℕ) (a : ℤ) (h h' : 0 ≤ a ∧ a ≤ (L : ℤ)) :
    rhoVal M T a h = rhoVal M T a h' := rfl

/-! ## The boundary-support of `diffRank (cascadeRank M T)`

The mixed difference of the box-clamped cascade rank is supported on the boundary of the box: zero in the
interior `1 ≤ a ≤ b < L`; the **top row** `m 0 b = ρ_b − ρ_{b+1}` (`0 ≤ b < L`); the **right column**
`m a L = q_a − q_{a−1}` (`1 ≤ a ≤ L`, `q_a = M_a − ρ_a`). In `codimForm`'s quadruple sum the first factor
`m (i−1) (j−1)` (with `j−1 < L`) is nonzero only at `i = 1` (top row) and the second `m u v` (with `u ≥ 1`)
only at `v = L` (right column). The collapse below uses exactly these.

NOTE: the boundary-support lemmas (top-row / right-col / interior-zero) are PROVEN below — the reusable
foundation. The remaining work is the `codimForm` quadruple→single-sum COLLAPSE (the one `sorry`), tracked
at #146. The plan (Codex-mapped, `threads/.../codex/mval-collapse-answer.md`), all standard Finset steps:
1. `Finset.sum_eq_single_of_mem (a := (1:ℤ))` on the outer `i`-sum: the `i ≠ 1` terms vanish (factor1
   `m (i−1) (j−1) = 0` by `diffRank_cascadeRank_interior`, since `i−1 ≥ 1` and `j−1 ≤ L−1`).
2. Inside (`i = 1`), `Finset.sum_eq_single_of_mem (a := (L:ℤ))` on the inner `v`-sum (`L ∈ Icc j L` always):
   the `v < L` terms vanish (factor2 `m u v = 0` by interior, `u ≥ 1`, `v ≤ L−1`). NO j/v swap needed.
3. Rewrite the surviving factors by `diffRank_cascadeRank_top_row` (`m 0 (j−1) = ρ_{j−1} − ρ_j`) and
   `diffRank_cascadeRank_right_col` (`m u L = q_u − q_{u−1}`).
4. Triangular reorder `Σ_{1≤u≤j≤L} → Σ_{j} Σ_{u∈Icc 1 j}` (a local `sum_sigma' + sum_nbij'` lemma);
   inner telescope `Σ_{u≤j}(q_u − q_{u−1}) = q_j` (`q_0 = 0`, via `Int.Icc_eq_finset_map` + `sum_range_sub`).
5. ℤ-Icc→`Fin L` reindex (`Int.Icc_eq_finset_map` + `Fin.sum_univ_eq_sum_range`) + `ring` per term to `Mval`. -/

/-- **Top-row support**: for `0 ≤ b` and `b + 1 ≤ L`, `diffRank (cascadeRank M T) 0 b = ρ_b − ρ_{b+1}`. The
`r(−1, ·) = 0` boundary kills two terms; the `M_0 − ρ_0 = 0` cancellation (`ρ_0 = M_0`) leaves `ρ_b − ρ_{b+1}`. -/
theorem diffRank_cascadeRank_top_row (M : Fin (L + 1) → ℕ) (T : Fin L → ℕ) (b : ℤ)
    (hb0 : 0 ≤ b) (hbL : b + 1 ≤ (L : ℤ)) :
    diffRank (cascadeRank M T) 0 b
      = rhoVal M T b ⟨hb0, by omega⟩ - rhoVal M T (b + 1) ⟨by omega, hbL⟩ := by
  have hb : (0 : ℤ) ≤ b ∧ b ≤ (L : ℤ) := ⟨hb0, by omega⟩
  have hb1 : (0 : ℤ) ≤ b + 1 ∧ b + 1 ≤ (L : ℤ) := ⟨by omega, hbL⟩
  have h0 : (0 : ℤ) ≤ (0 : ℤ) ∧ (0 : ℤ) ≤ (L : ℤ) := ⟨le_rfl, by omega⟩
  unfold diffRank
  -- r(-1, ·) = 0 (row out of box)
  rw [cascadeRank_of_row_oob M T (0 - 1) b (by omega),
      cascadeRank_of_row_oob M T (0 - 1) (b + 1) (by omega),
      cascadeRank_in_box M T 0 b h0 hb, cascadeRank_in_box M T 0 (b + 1) h0 hb1,
      rhoVal_zero M T h0]
  -- M_0 - ρ_0 = 0 cancels; left with ρ_b - ρ_{b+1}.
  have hidx : (⟨(0 : ℤ).toNat, by omega⟩ : Fin (L + 1)) = 0 := by apply Fin.ext; simp
  rw [hidx]; ring

/-- **Right-column support**: for `1 ≤ a` and `a ≤ L`, `diffRank (cascadeRank M T) a L = q_a − q_{a−1}` where
`q_x = M_x − ρ_x`. The `r(·, L+1) = 0` boundary kills two terms; the `ρ_L` row-value cancels, leaving the
`q` difference. -/
theorem diffRank_cascadeRank_right_col (M : Fin (L + 1) → ℕ) (T : Fin L → ℕ) (a : ℤ)
    (ha1 : 1 ≤ a) (haL : a ≤ (L : ℤ)) :
    diffRank (cascadeRank M T) a (L : ℤ)
      = ((M ⟨a.toNat, by omega⟩ : ℤ) - rhoVal M T a ⟨by omega, haL⟩)
        - ((M ⟨(a - 1).toNat, by omega⟩ : ℤ) - rhoVal M T (a - 1) ⟨by omega, by omega⟩) := by
  have ha : (0 : ℤ) ≤ a ∧ a ≤ (L : ℤ) := ⟨by omega, haL⟩
  have ha1' : (0 : ℤ) ≤ a - 1 ∧ a - 1 ≤ (L : ℤ) := ⟨by omega, by omega⟩
  have hL : (0 : ℤ) ≤ (L : ℤ) ∧ (L : ℤ) ≤ (L : ℤ) := ⟨by omega, le_rfl⟩
  unfold diffRank
  -- r(·, L+1) = 0 (column out of box)
  rw [cascadeRank_of_col_oob M T a ((L : ℤ) + 1) (by omega),
      cascadeRank_of_col_oob M T (a - 1) ((L : ℤ) + 1) (by omega),
      cascadeRank_in_box M T a (L : ℤ) ha hL, cascadeRank_in_box M T (a - 1) (L : ℤ) ha1' hL]
  -- the ρ_L row-values cancel; left with the q-difference.
  ring

/-- **Interior-zero support**: for `1 ≤ a ≤ L` and `0 ≤ b ≤ L−1` (all four corners in the box), the mixed
difference of the separable `r = ρ_b + q_a` vanishes — `m a b = 0`. Covers BOTH `codimForm` factors'
vanishing: factor1 `m (i−1) (j−1)` for `i ≥ 2` (`a = i−1 ≥ 1`, `b = j−1 ≤ L−1`) and factor2 `m u v` for
`v < L` (`a = u ≥ 1`, `b = v ≤ L−1`). -/
theorem diffRank_cascadeRank_interior (M : Fin (L + 1) → ℕ) (T : Fin L → ℕ) (a b : ℤ)
    (ha1 : 1 ≤ a) (haL : a ≤ (L : ℤ)) (hb0 : 0 ≤ b) (hbL : b + 1 ≤ (L : ℤ)) :
    diffRank (cascadeRank M T) a b = 0 := by
  have ha : (0 : ℤ) ≤ a ∧ a ≤ (L : ℤ) := ⟨by omega, haL⟩
  have ha1' : (0 : ℤ) ≤ a - 1 ∧ a - 1 ≤ (L : ℤ) := ⟨by omega, by omega⟩
  have hb : (0 : ℤ) ≤ b ∧ b ≤ (L : ℤ) := ⟨hb0, by omega⟩
  have hb1 : (0 : ℤ) ≤ b + 1 ∧ b + 1 ≤ (L : ℤ) := ⟨by omega, hbL⟩
  unfold diffRank
  rw [cascadeRank_in_box M T a b ha hb, cascadeRank_in_box M T (a - 1) b ha1' hb,
      cascadeRank_in_box M T a (b + 1) ha hb1, cascadeRank_in_box M T (a - 1) (b + 1) ha1' hb1]
  -- separable r = ρ_b + q_a: the mixed difference telescopes to 0.
  ring

/-- **The combinatorial bridge `Mval = codimForm (diffRank cascadeRank)`** (SIGNED ring identity, all `M T`,
no admissibility — see the file docstring). `Mval M T` equals the LR quadratic codim form on the cascade
rank array's mixed difference. The collapse: `diffRank (cascadeRank M T)` is boundary-supported (top row
`ρ_b − ρ_{b+1}`, right col `q_a − q_{a−1}`); the quadruple sum forces `i = 1 ∧ v = L`, collapsing to
`Σ_{u≤j}(ρ_{j−1}−ρ_j)(q_u−q_{u−1})`, whose inner telescopes (`q_0 = 0`) to `Σ_j(ρ_{j−1}−ρ_j)q_j = Mval`. -/
theorem Mval_eq_codimForm_diffRank_cascadeRank (M : Fin (L + 1) → ℕ) (T : Fin L → ℕ) :
    Mval M T = Core.codimForm L (diffRank (cascadeRank M T)) := by
  sorry

end DLNFibre.DLN.RLCT
