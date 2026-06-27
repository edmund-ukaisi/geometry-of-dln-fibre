import DLNFibre.DLN.RLCT.Validate.MatMulFibre
import Mathlib.Algebra.Order.Chebyshev

/-!
# `DLNFibre.DLN.RLCT.Validate.RouteMSchurAlg` — elementary `frobSq` algebra for the N2b comparison

The S2-free finite-sum inequalities the N2b two-sided Schur comparison consumes. All raw `frobSq`
(`∑ᵢⱼ Mᵢⱼ²`) — no operator norm, no normed-space transport (the Codex-recommended route ii).

* `frobSq_add_le` — `frobSq (X + Y) ≤ 2·(frobSq X + frobSq Y)` (pointwise `(a+b)² ≤ 2(a²+b²)`).
* `frobSq_rmatMul_entryBound_le` — Cauchy-Schwarz: if `|A i k| ≤ 1` then
  `frobSq (rmatMul A X) ≤ n·m·frobSq X` (`n` = contraction dim, `m` = #rows of `A`).
* `schur_key_identity` — the algebraic collapse `(R·S)_bot = A·(R·S)_top + Sc·S_bot` (`A := M21·Minv`,
  `Sc := M22 − A·M12`, `Minv` a left inverse of `M11`). This is what makes the whole `L⁻¹·diag·U⁻¹`
  block-Gauss machinery unnecessary — only the row shear `A` is needed (numerically confirmed,
  `L32a_N2b_keyident.py`, residual `< 1.6e-12` up to `r = 5`).
* `schur_abstract_comparison` — the two-sided `frobSq` comparison from the key identity + the `|A| ≤ 1`
  shear bound, with explicit uniform constants `(c₀, c₁) = (1/(2+2js), 2+2js)`.
-/

namespace DLNFibre.DLN.RLCT

open scoped BigOperators

/-- **`Fin r = Fin j ⊕ Fin (r−j)` sum split.** For `j ≤ r`, a sum over `Fin r` splits into the top
`j` block (`⟨a, _⟩`) and the bottom `r−j` block (`⟨j+a, _⟩`). The reindex bridge for the N2b blocks. -/
theorem fin_sum_block_split {r : ℕ} (j : ℕ) (hj : j ≤ r) (f : Fin r → ℝ) :
    (∑ i, f i)
      = (∑ a : Fin j, f ⟨a, lt_of_lt_of_le a.2 hj⟩)
        + ∑ a : Fin (r - j), f ⟨j + a, by omega⟩ := by
  have hsplit : r = j + (r - j) := by omega
  let e : Fin j ⊕ Fin (r - j) ≃ Fin r := finSumFinEquiv.trans (finCongr hsplit.symm)
  rw [← Equiv.sum_comp e f, Fintype.sum_sum_type]
  refine congrArg₂ (· + ·) ?_ ?_
  · refine Finset.sum_congr rfl (fun a _ => ?_); congr 1
  · refine Finset.sum_congr rfl (fun a _ => ?_); congr 1

/-- **`frobSq` block split.** For `j ≤ r`, `frobSq` over `Fin r → Fin p` splits as the top-`j`-block
`frobSq` plus the bottom-`(r−j)`-block `frobSq`. -/
theorem frobSq_fin_block_split {r p : ℕ} (j : ℕ) (hj : j ≤ r) (M : Fin r → Fin p → ℝ) :
    frobSq M
      = frobSq (fun a : Fin j => M ⟨a, lt_of_lt_of_le a.2 hj⟩)
        + frobSq (fun a : Fin (r - j) => M ⟨j + a, by omega⟩) := by
  unfold frobSq
  exact fin_sum_block_split j hj (fun i => ∑ col, (M i col) ^ 2)

/-- `frobSq (X + Y) ≤ 2·(frobSq X + frobSq Y)` — the parallelogram-style bound (`(a+b)² ≤ 2a²+2b²`). -/
theorem frobSq_add_le {m q : ℕ} (X Y : Fin m → Fin q → ℝ) :
    frobSq (fun i j => X i j + Y i j) ≤ 2 * (frobSq X + frobSq Y) := by
  unfold frobSq
  have hxy : (2 : ℝ) * ((∑ i, ∑ j, X i j ^ 2) + ∑ i, ∑ j, Y i j ^ 2)
      = ∑ i, ∑ j, (2 * (X i j) ^ 2 + 2 * (Y i j) ^ 2) := by
    rw [mul_add, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  rw [hxy]
  refine Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => ?_))
  nlinarith [sq_nonneg (X i j - Y i j)]

/-- **Cauchy-Schwarz entry bound.** If `|A i k| ≤ 1` for all `i, k`, then
`frobSq (rmatMul A X) ≤ (n·m)·frobSq X` where `A : Fin m → Fin n → ℝ`, `X : Fin n → Fin q → ℝ`. The
factor `n` is the contraction (Cauchy-Schwarz card) and `m` the number of output rows. -/
theorem frobSq_rmatMul_entryBound_le {m n q : ℕ} (A : Fin m → Fin n → ℝ) (X : Fin n → Fin q → ℝ)
    (hA : ∀ i k, |A i k| ≤ 1) :
    frobSq (rmatMul A X) ≤ ((n : ℝ) * m) * frobSq X := by
  unfold frobSq rmatMul
  -- ∑_i ∑_j (∑_k A i k · X k j)²  ≤  ∑_i ∑_j  n · ∑_k (X k j)²
  have hstep : ∀ i : Fin m, ∀ j : Fin q,
      (∑ k, A i k * X k j) ^ 2 ≤ (n : ℝ) * ∑ k, (X k j) ^ 2 := by
    intro i j
    have hcs : (∑ k, A i k * X k j) ^ 2
        ≤ ((Finset.univ : Finset (Fin n)).card : ℝ) * ∑ k, (A i k * X k j) ^ 2 :=
      sq_sum_le_card_mul_sum_sq
    calc (∑ k, A i k * X k j) ^ 2
        ≤ ((Finset.univ : Finset (Fin n)).card : ℝ) * ∑ k, (A i k * X k j) ^ 2 := hcs
      _ = (n : ℝ) * ∑ k, (A i k * X k j) ^ 2 := by rw [Finset.card_univ, Fintype.card_fin]
      _ ≤ (n : ℝ) * ∑ k, (X k j) ^ 2 := by
          refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun k _ => ?_)) (by positivity)
          rw [mul_pow]
          have hA2 : (A i k) ^ 2 ≤ 1 := by
            rw [← sq_abs]; nlinarith [hA i k, abs_nonneg (A i k)]
          nlinarith [sq_nonneg (X k j), hA2]
  -- sum the pointwise bound and re-collect (Fubini on the j,k double sum)
  calc ∑ i, ∑ j, (∑ k, A i k * X k j) ^ 2
      ≤ ∑ i : Fin m, ∑ j, (n : ℝ) * ∑ k, (X k j) ^ 2 :=
        Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hstep i j))
    _ = ∑ i : Fin m, (n : ℝ) * ∑ j, ∑ k, (X k j) ^ 2 := by
        refine Finset.sum_congr rfl (fun i _ => ?_); rw [Finset.mul_sum]
    _ = (m : ℝ) * ((n : ℝ) * ∑ j, ∑ k, (X k j) ^ 2) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ = ((n : ℝ) * m) * ∑ k, ∑ j, (X k j) ^ 2 := by rw [Finset.sum_comm]; ring

/-- **The N2b key identity (abstract).** Blocks as raw functions; `Minv` a LEFT inverse of `M11`
(`∑ᵢ Minv t i · M11 i k = δ_{tk}`). With `A := M21·Minv` (row shear) and `Sc := M22 − A·M12`, the
bottom block of `R·S` equals `A·(R·S)_top + Sc·S_bot`. The single algebraic fact that collapses the
N2b comparison (no `L⁻¹·diag·U⁻¹`, no column shear). -/
theorem schur_key_identity {j s p : ℕ}
    (M11 : Fin j → Fin j → ℝ) (M12 : Fin j → Fin s → ℝ)
    (M21 : Fin s → Fin j → ℝ) (M22 : Fin s → Fin s → ℝ)
    (Minv : Fin j → Fin j → ℝ) (Stop : Fin j → Fin p → ℝ) (Sbot : Fin s → Fin p → ℝ)
    (hinv : ∀ t k, (∑ i, Minv t i * M11 i k) = if t = k then 1 else 0)
    (a : Fin s) (col : Fin p) :
    ((∑ i, M21 a i * Stop i col) + ∑ b, M22 a b * Sbot b col)
      = (∑ i : Fin j, (rmatMul M21 Minv) a i * ((∑ k, M11 i k * Stop k col)
            + ∑ b, M12 i b * Sbot b col))
        + rmatMul (fun x y => M22 x y - rmatMul (rmatMul M21 Minv) M12 x y) Sbot a col := by
  have hpiv : ∀ k : Fin j, (∑ i, (rmatMul M21 Minv) a i * M11 i k) = M21 a k := by
    intro k
    simp only [rmatMul]
    calc (∑ i, (∑ t, M21 a t * Minv t i) * M11 i k)
        = ∑ i, ∑ t, (M21 a t * Minv t i * M11 i k) := by
          refine Finset.sum_congr rfl (fun i _ => ?_); rw [Finset.sum_mul]
      _ = ∑ t, M21 a t * (∑ i, Minv t i * M11 i k) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl (fun t _ => ?_)
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun i _ => ?_); ring
      _ = ∑ t, M21 a t * (if t = k then 1 else 0) := by
          refine Finset.sum_congr rfl (fun t _ => ?_); rw [hinv t k]
      _ = M21 a k := by simp
  have hAM12 : ∀ b : Fin s,
      rmatMul (rmatMul M21 Minv) M12 a b = ∑ i, (rmatMul M21 Minv) a i * M12 i b := by
    intro b; simp [rmatMul]
  have e1 : ∀ i : Fin j, (rmatMul M21 Minv) a i * ((∑ k, M11 i k * Stop k col)
          + ∑ b, M12 i b * Sbot b col)
      = (∑ k, (rmatMul M21 Minv) a i * M11 i k * Stop k col)
        + ∑ b, (rmatMul M21 Minv) a i * M12 i b * Sbot b col := by
    intro i; rw [mul_add, Finset.mul_sum, Finset.mul_sum]
    congr 1 <;> (refine Finset.sum_congr rfl (fun _ _ => ?_); ring)
  rw [Finset.sum_congr rfl (fun i _ => e1 i), Finset.sum_add_distrib]
  have hM11part : (∑ i : Fin j, ∑ k, (rmatMul M21 Minv) a i * M11 i k * Stop k col)
      = ∑ i, M21 a i * Stop i col := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [← Finset.sum_mul, hpiv k]
  have hM12part : (∑ i : Fin j, ∑ b, (rmatMul M21 Minv) a i * M12 i b * Sbot b col)
      = ∑ b, (rmatMul (rmatMul M21 Minv) M12) a b * Sbot b col := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [hAM12 b, ← Finset.sum_mul]
  rw [hM11part, hM12part, add_assoc]
  congr 1
  symm
  show (∑ b, (rmatMul (rmatMul M21 Minv) M12) a b * Sbot b col)
      + rmatMul (fun x y => M22 x y - rmatMul (rmatMul M21 Minv) M12 x y) Sbot a col
    = ∑ b, M22 a b * Sbot b col
  simp only [rmatMul]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun b _ => ?_); ring

/-- **The N2b two-sided comparison (abstract).** Given the key identity `gbot = A·gtop + Sch`
pointwise with `|A| ≤ 1`, the full `frobSq gtop + frobSq gbot` is two-sided-comparable to
`frobSq gtop + frobSq Sch` with the uniform constants `(c₀, c₁) = (1/(2+2js), 2+2js)`. -/
theorem schur_abstract_comparison {j s p : ℕ}
    (gtop : Fin j → Fin p → ℝ) (gbot : Fin s → Fin p → ℝ)
    (Sch : Fin s → Fin p → ℝ) (A : Fin s → Fin j → ℝ)
    (hA : ∀ a i, |A a i| ≤ 1)
    (hid : ∀ a col, gbot a col = rmatMul A gtop a col + Sch a col) :
    (1 / (2 + 2 * (j : ℝ) * s)) * (frobSq gtop + frobSq Sch)
        ≤ frobSq gtop + frobSq gbot
      ∧ frobSq gtop + frobSq gbot
        ≤ (2 + 2 * (j : ℝ) * s) * (frobSq gtop + frobSq Sch) := by
  set c : ℝ := 2 + 2 * (j : ℝ) * s with hc
  have hcpos : 0 < c := by rw [hc]; positivity
  have hAX : frobSq (rmatMul A gtop) ≤ ((j : ℝ) * s) * frobSq gtop :=
    frobSq_rmatMul_entryBound_le A gtop hA
  have hgtop0 : 0 ≤ frobSq gtop := frobSq_nonneg _
  have hSch0 : 0 ≤ frobSq Sch := frobSq_nonneg _
  have hgbot0 : 0 ≤ frobSq gbot := frobSq_nonneg _
  have hgbot_eq : gbot = fun a col => rmatMul A gtop a col + Sch a col := by
    funext a col; exact hid a col
  have hfwd : frobSq gbot ≤ 2 * (frobSq (rmatMul A gtop) + frobSq Sch) := by
    rw [hgbot_eq]; exact frobSq_add_le _ _
  have hSch_eq : Sch = fun a col => gbot a col + (-(rmatMul A gtop a col)) := by
    funext a col; rw [hid a col]; ring
  have hrev : frobSq Sch ≤ 2 * (frobSq gbot + frobSq (fun a col => -(rmatMul A gtop a col))) := by
    rw [hSch_eq]; exact frobSq_add_le _ _
  have hneg : frobSq (fun a col => -(rmatMul A gtop a col)) = frobSq (rmatMul A gtop) := by
    unfold frobSq; refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun col _ => ?_))
    ring
  rw [hneg] at hrev
  have hjs0 : (0 : ℝ) ≤ (j : ℝ) * s := by positivity
  constructor
  · rw [one_div, inv_mul_le_iff₀ hcpos, hc]
    have hrev' : frobSq Sch ≤ 2 * frobSq gbot + 2 * ((j:ℝ)*s) * frobSq gtop := by
      nlinarith [hrev, hAX, hgtop0]
    nlinarith [hrev', hgtop0, hgbot0, hjs0]
  · rw [hc]
    have hfwd' : frobSq gbot ≤ 2 * ((j:ℝ)*s) * frobSq gtop + 2 * frobSq Sch := by
      nlinarith [hfwd, hAX, hSch0, hgtop0]
    nlinarith [hfwd', hgtop0, hSch0, hjs0]

end DLNFibre.DLN.RLCT
