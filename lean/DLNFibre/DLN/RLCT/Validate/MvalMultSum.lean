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

/-! ## Two ℤ-`Icc` combinatorial helpers (collapse infrastructure)

A triangular reorder of a double `Icc` sum, and the ℤ-`Icc` telescope. Both are pure `Finset` facts,
network-free; they are the engine of the quadruple→single-sum collapse. -/

/-- **Triangular reorder.** For a triangle `1 ≤ u ≤ j ≤ L` summed `u`-outer, reorder to `j`-outer:
`Σ_{u∈Icc 1 L} Σ_{j∈Icc u L} F u j = Σ_{j∈Icc 1 L} Σ_{u∈Icc 1 j} F u j`. -/
theorem sum_Icc_Icc_comm_int {A : Type*} [AddCommMonoid A] (N : ℤ) (F : ℤ → ℤ → A) :
    (∑ u ∈ Finset.Icc (1 : ℤ) N, ∑ j ∈ Finset.Icc u N, F u j)
      = ∑ j ∈ Finset.Icc (1 : ℤ) N, ∑ u ∈ Finset.Icc (1 : ℤ) j, F u j := by
  rw [Finset.sum_sigma', Finset.sum_sigma']
  refine Finset.sum_nbij'
    (i := fun x ↦ (⟨x.2, x.1⟩ : Σ _ : ℤ, ℤ))
    (j := fun x ↦ (⟨x.2, x.1⟩ : Σ _ : ℤ, ℤ))
    ?_ ?_ (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) <;>
  · intro x hx
    simp only [Finset.mem_sigma, Finset.mem_Icc] at hx ⊢
    omega

/-- **ℤ-`Icc` telescope.** For `0 ≤ j`, `Σ_{u∈Icc 1 j} (q u − q (u−1)) = q j − q 0`. -/
theorem telescope_Icc_int (q : ℤ → ℤ) {j : ℤ} (hj : 0 ≤ j) :
    (∑ u ∈ Finset.Icc (1 : ℤ) j, (q u - q (u - 1))) = q j - q 0 := by
  rw [Int.Icc_eq_finset_map (1 : ℤ) j, Finset.sum_map]
  have key := Finset.sum_range_sub (fun n : ℕ => q ((n : ℤ))) (j + 1 - 1).toNat
  -- the mapped summand `q (n+1) - q ((n+1)-1)` equals `q (n+1) - q n`
  have hsum :
      ∑ n ∈ Finset.range (j + 1 - 1).toNat,
          (q (((Nat.castEmbedding.trans (addLeftEmbedding (1 : ℤ))) n : ℤ))
            - q (((Nat.castEmbedding.trans (addLeftEmbedding (1 : ℤ))) n : ℤ) - 1))
        = ∑ n ∈ Finset.range (j + 1 - 1).toNat, (q ((n : ℤ) + 1) - q (n : ℤ)) := by
      apply Finset.sum_congr rfl
      intro n _
      simp only [Function.Embedding.trans_apply, Nat.castEmbedding_apply, addLeftEmbedding_apply]
      push_cast
      ring_nf
  rw [hsum]
  -- align the cast `((n+1 : ℕ) : ℤ)` in `key`'s LHS, then evaluate via `Int.toNat_of_nonneg`.
  have key' :
      ∑ n ∈ Finset.range (j + 1 - 1).toNat, (q ((n : ℤ) + 1) - q (n : ℤ))
        = q (((j + 1 - 1).toNat : ℤ)) - q ((0 : ℕ) : ℤ) := by
    rw [← key]
    apply Finset.sum_congr rfl
    intro n _
    push_cast
    ring
  rw [key']
  have : ((j + 1 - 1).toNat : ℤ) = j := by omega
  rw [this]
  norm_num

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

/-! ## Proof-irrelevant total `ρ`/`q` (for the collapse sums)

`rhoVal`/the box value carry a range proof; the collapse sums want plain total functions of `ℤ`. `rhoT`
and `qT` are the clamped totals (`rhoT a = ρ_{a.toNat}` for `a ∈ [0,L]`, `qT a = M_a − ρ_a`), and the
support lemmas re-express through them. -/

/-- Total `ρ` on `ℤ`: `Core.expSurvivor` at the clamped index `min a.toNat L`. Agrees with `rhoVal`
on `[0, L]` (where `a.toNat ≤ L`, the clamp is inert). -/
noncomputable def rhoT (M : Fin (L + 1) → ℕ) (T : Fin L → ℕ) (a : ℤ) : ℤ :=
  (Core.expSurvivor M T ⟨min a.toNat L, by omega⟩ : ℤ)

/-- Total `q = M − ρ` on `ℤ` (clamped index). `qT 0 = 0` since `ρ_0 = M_0`. -/
noncomputable def qT (M : Fin (L + 1) → ℕ) (T : Fin L → ℕ) (a : ℤ) : ℤ :=
  (M ⟨min a.toNat L, by omega⟩ : ℤ) - rhoT M T a

/-- `rhoT` agrees with the proof-carrying `rhoVal` on `[0, L]`. -/
theorem rhoT_eq_rhoVal (M : Fin (L + 1) → ℕ) (T : Fin L → ℕ) (a : ℤ) (h : 0 ≤ a ∧ a ≤ (L : ℤ)) :
    rhoT M T a = rhoVal M T a h := by
  unfold rhoT rhoVal
  have : (⟨min a.toNat L, by omega⟩ : Fin (L + 1)) = ⟨a.toNat, by omega⟩ := by
    apply Fin.ext; simp only []; omega
  rw [this]

/-- `qT a = (M_a − ρ_a)` with `rhoVal` on `[0, L]`. -/
theorem qT_eq (M : Fin (L + 1) → ℕ) (T : Fin L → ℕ) (a : ℤ) (h : 0 ≤ a ∧ a ≤ (L : ℤ)) :
    qT M T a = (M ⟨a.toNat, by omega⟩ : ℤ) - rhoVal M T a h := by
  unfold qT
  rw [rhoT_eq_rhoVal M T a h]
  have : (⟨min a.toNat L, by omega⟩ : Fin (L + 1)) = ⟨a.toNat, by omega⟩ := by
    apply Fin.ext; simp only []; omega
  rw [this]

/-- `qT 0 = 0` (`ρ_0 = M_0`). -/
theorem qT_zero (M : Fin (L + 1) → ℕ) (T : Fin L → ℕ) : qT M T 0 = 0 := by
  rw [qT_eq M T 0 ⟨le_rfl, by positivity⟩, rhoVal_zero M T ⟨le_rfl, by positivity⟩]
  have : (⟨(0 : ℤ).toNat, by omega⟩ : Fin (L + 1)) = 0 := by apply Fin.ext; simp
  rw [this]; ring

/-- **Top-row, `rhoT` form**: `m 0 b = ρ_b − ρ_{b+1}` (`0 ≤ b`, `b+1 ≤ L`). -/
theorem diffRank_cascadeRank_top_row' (M : Fin (L + 1) → ℕ) (T : Fin L → ℕ) (b : ℤ)
    (hb0 : 0 ≤ b) (hbL : b + 1 ≤ (L : ℤ)) :
    diffRank (cascadeRank M T) 0 b = rhoT M T b - rhoT M T (b + 1) := by
  rw [diffRank_cascadeRank_top_row M T b hb0 hbL,
    rhoT_eq_rhoVal M T b ⟨hb0, by omega⟩, rhoT_eq_rhoVal M T (b + 1) ⟨by omega, hbL⟩]

/-- **Right-column, `qT` form**: `m a L = q_a − q_{a−1}` (`1 ≤ a ≤ L`). -/
theorem diffRank_cascadeRank_right_col' (M : Fin (L + 1) → ℕ) (T : Fin L → ℕ) (a : ℤ)
    (ha1 : 1 ≤ a) (haL : a ≤ (L : ℤ)) :
    diffRank (cascadeRank M T) a (L : ℤ) = qT M T a - qT M T (a - 1) := by
  rw [diffRank_cascadeRank_right_col M T a ha1 haL,
    qT_eq M T a ⟨by omega, haL⟩, qT_eq M T (a - 1) ⟨by omega, by omega⟩]

/-- `rhoT` at `k : Fin L` equals `tPrev` (`ρ_0 = M_0`, `ρ_{m+1} = T_m`). -/
theorem rhoT_fin (M : Fin (L + 1) → ℕ) (T : Fin L → ℕ) (k : Fin L) :
    rhoT M T ((k : ℤ)) = tPrev M T k := by
  unfold rhoT tPrev
  have hkz : ((k : ℤ)).toNat = k.val := by simp
  have hkL : k.val < L := k.isLt
  rcases Nat.eq_zero_or_pos k.val with hk | hk
  · -- k = 0: ρ_0 = M_0
    have hidx : (⟨min ((k : ℤ)).toNat L, by omega⟩ : Fin (L + 1)) = 0 := by
      apply Fin.ext; simp only [hkz, Fin.val_zero]; omega
    rw [hidx, Core.expSurvivor_zero, if_pos hk]
  · -- k = m+1: ρ_{m+1} = T_m
    have hsucc : (⟨min ((k : ℤ)).toNat L, by omega⟩ : Fin (L + 1))
        = (⟨k.val - 1, by omega⟩ : Fin L).succ := by
      apply Fin.ext; simp only [Fin.val_succ, hkz]; omega
    rw [hsucc, Core.expSurvivor_succ, if_neg (by omega)]

/-- `rhoT` at `k + 1` (`k : Fin L`) equals `T_k` (`ρ_{k+1} = T_k`). -/
theorem rhoT_fin_succ (M : Fin (L + 1) → ℕ) (T : Fin L → ℕ) (k : Fin L) :
    rhoT M T ((k : ℤ) + 1) = (T k : ℤ) := by
  unfold rhoT
  have hkz : ((k : ℤ) + 1).toNat = k.val + 1 := by push_cast; omega
  have hkL : k.val < L := k.isLt
  have hsucc : (⟨min ((k : ℤ) + 1).toNat L, by omega⟩ : Fin (L + 1)) = k.succ := by
    apply Fin.ext; simp only [Fin.val_succ, hkz]; omega
  rw [hsucc, Core.expSurvivor_succ]

/-- `qT` at `k + 1` (`k : Fin L`) equals `M k.succ − T k`. -/
theorem qT_fin_succ (M : Fin (L + 1) → ℕ) (T : Fin L → ℕ) (k : Fin L) :
    qT M T ((k : ℤ) + 1) = (M k.succ : ℤ) - (T k : ℤ) := by
  unfold qT
  rw [rhoT_fin_succ M T k]
  have hkz : ((k : ℤ) + 1).toNat = k.val + 1 := by push_cast; omega
  have hkL : k.val < L := k.isLt
  have hidx : (⟨min ((k : ℤ) + 1).toNat L, by omega⟩ : Fin (L + 1)) = k.succ := by
    apply Fin.ext; simp only [Fin.val_succ, hkz]; omega
  rw [hidx]

/-- **The combinatorial bridge `Mval = codimForm (diffRank cascadeRank)`** (SIGNED ring identity, all `M T`,
no admissibility — see the file docstring). `Mval M T` equals the LR quadratic codim form on the cascade
rank array's mixed difference. The collapse: `diffRank (cascadeRank M T)` is boundary-supported (top row
`ρ_b − ρ_{b+1}`, right col `q_a − q_{a−1}`); the quadruple sum forces `i = 1 ∧ v = L`, collapsing to
`Σ_{u≤j}(ρ_{j−1}−ρ_j)(q_u−q_{u−1})`, whose inner telescopes (`q_0 = 0`) to `Σ_j(ρ_{j−1}−ρ_j)q_j = Mval`. -/
theorem Mval_eq_codimForm_diffRank_cascadeRank (M : Fin (L + 1) → ℕ) (T : Fin L → ℕ) :
    Mval M T = Core.codimForm L (diffRank (cascadeRank M T)) := by
  set m := diffRank (cascadeRank M T) with hm
  rw [Core.codimForm]
  -- STAGE 1: outer `i`-sum collapses to `i = 1` (factor1 `m (i−1) (j−1) = 0`, `i ≥ 2`: interior).
  have stage1 :
      (∑ i ∈ Finset.Icc (1 : ℤ) L, ∑ u ∈ Finset.Icc i (L : ℤ), ∑ j ∈ Finset.Icc u (L : ℤ),
          ∑ v ∈ Finset.Icc j (L : ℤ), m (i - 1) (j - 1) * m u v)
        = ∑ u ∈ Finset.Icc (1 : ℤ) (L : ℤ), ∑ j ∈ Finset.Icc u (L : ℤ),
            ∑ v ∈ Finset.Icc j (L : ℤ), m 0 (j - 1) * m u v := by
    by_cases hL : (1 : ℤ) ≤ (L : ℤ)
    · rw [Finset.sum_eq_single_of_mem (a := (1 : ℤ)) (Finset.mem_Icc.2 ⟨le_rfl, hL⟩)]
      · norm_num
      · intro i hi hine
        refine Finset.sum_eq_zero (fun u hu ↦ Finset.sum_eq_zero (fun j hj ↦
          Finset.sum_eq_zero (fun v hv ↦ ?_)))
        rw [Finset.mem_Icc] at hi hu hj hv
        have hz : m (i - 1) (j - 1) = 0 := by
          rw [hm]; apply diffRank_cascadeRank_interior M T (i - 1) (j - 1) <;> omega
        rw [hz, zero_mul]
    · have : Finset.Icc (1 : ℤ) (L : ℤ) = ∅ := Finset.Icc_eq_empty (by exact_mod_cast hL)
      rw [this, Finset.sum_empty, Finset.sum_empty]
  rw [stage1]
  -- STAGE 2: inner `v`-sum collapses to `v = L` (factor2 `m u v = 0` for `v < L`, `u ≥ 1`);
  -- rewrite the two surviving factors by top-row / right-col support.
  -- The summand at `(u, j)` becomes `(ρ_{j−1} − ρ_j) · (q_u − q_{u−1})`.
  have stage2 :
      (∑ u ∈ Finset.Icc (1 : ℤ) (L : ℤ), ∑ j ∈ Finset.Icc u (L : ℤ),
          ∑ v ∈ Finset.Icc j (L : ℤ), m 0 (j - 1) * m u v)
        = ∑ u ∈ Finset.Icc (1 : ℤ) (L : ℤ), ∑ j ∈ Finset.Icc u (L : ℤ),
            (rhoT M T (j - 1) - rhoT M T j) * (qT M T u - qT M T (u - 1)) := by
    refine Finset.sum_congr rfl (fun u hu ↦ Finset.sum_congr rfl (fun j hj ↦ ?_))
    rw [Finset.mem_Icc] at hu hj
    -- inner `v`-sum: only `v = L` survives.
    rw [Finset.sum_eq_single_of_mem (a := (L : ℤ)) (Finset.mem_Icc.2 ⟨hj.2, le_rfl⟩)]
    · -- factor1 = top-row (`j − 1`), factor2 = right-col (`u`).
      rw [hm, diffRank_cascadeRank_top_row' M T (j - 1) (by omega) (by omega),
        diffRank_cascadeRank_right_col' M T u (by omega) (by omega)]
      ring_nf
    · intro v hv hvne
      rw [Finset.mem_Icc] at hv
      have hz : m u v = 0 := by
        rw [hm]; apply diffRank_cascadeRank_interior M T u v <;> omega
      rw [hz, mul_zero]
  rw [stage2]
  -- STAGE 3: triangular reorder (`u`-outer → `j`-outer), factor out the `j`-only factor,
  -- telescope the inner `u`-sum (`q_0 = 0`), then reindex to `Mval`.
  rw [sum_Icc_Icc_comm_int (L : ℤ)
        (fun u j ↦ (rhoT M T (j - 1) - rhoT M T j) * (qT M T u - qT M T (u - 1)))]
  -- factor the `j`-only factor out of the inner `u`-sum, then telescope.
  have stage3 :
      (∑ j ∈ Finset.Icc (1 : ℤ) (L : ℤ), ∑ u ∈ Finset.Icc (1 : ℤ) j,
          (rhoT M T (j - 1) - rhoT M T j) * (qT M T u - qT M T (u - 1)))
        = ∑ j ∈ Finset.Icc (1 : ℤ) (L : ℤ), (rhoT M T (j - 1) - rhoT M T j) * qT M T j := by
    refine Finset.sum_congr rfl (fun j hj ↦ ?_)
    rw [Finset.mem_Icc] at hj
    rw [← Finset.mul_sum, telescope_Icc_int (qT M T) (by omega : (0 : ℤ) ≤ j), qT_zero, sub_zero]
  rw [stage3]
  -- STAGE 4: reindex `j ∈ Icc 1 L` to `k : Fin L` (`j = k + 1`), match the `Mval` summand.
  rw [Mval]
  rw [Int.Icc_eq_finset_map (1 : ℤ) (L : ℤ), Finset.sum_map,
    show ((L : ℤ) + 1 - 1).toNat = L by omega]
  simp only [Function.Embedding.trans_apply, Nat.castEmbedding_apply, addLeftEmbedding_apply]
  rw [← Fin.sum_univ_eq_sum_range
        (fun n : ℕ ↦ (rhoT M T (((1 : ℤ) + (n : ℤ)) - 1) - rhoT M T ((1 : ℤ) + (n : ℤ)))
          * qT M T ((1 : ℤ) + (n : ℤ))) L]
  refine (Finset.sum_congr rfl (fun k _ ↦ ?_)).symm
  -- per-term: `(tPrev k − T k)(M k.succ − T k) = (ρ_k − ρ_{k+1}) · q_{k+1}`.
  rw [show (1 : ℤ) + (k : ℤ) - 1 = (k : ℤ) by ring, show (1 : ℤ) + (k : ℤ) = (k : ℤ) + 1 by ring,
    rhoT_fin M T k, rhoT_fin_succ M T k, qT_fin_succ M T k]

end DLNFibre.DLN.RLCT
