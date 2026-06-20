import DLNFibre.Core.RankPattern
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# `DLNFibre.Core.BoxMoveGeneration` — the box-move generation crux (L6.2b-key)

The combinatorial converse to the box-move degeneration: a pure second-difference telescope on a
nonnegative triangular integer array, decoupled from the orbit/representation engine.

For a nonnegative array `g` (the residual `r − s` of two achievable rank patterns) supported off the
half-plane (out-of-range `= 0`, i.e. `Supported N g`), and any cell `(I,J)` with `g I J > 0`, the
sum of the second difference `diff g` (`= g_{a,e} − g_{a,e+1} − g_{a−1,e} + g_{a−1,e+1}`,
`RankPattern.diff`) over the **rectangle-in-support family**
`A = {(a,e) : a ≤ I, J ≤ e, rect ⊆ supp g}` is at least `g I J`:

> **L6.2b-key (`sum_secondDiff_coveringRect_ge`).** `∑_{(a,e)∈A} diff g a e ≥ g I J`.   (★)

This is the load-bearing input to box-move existence (L6.2b): substituting `diff g = m(r) − m(s)`
(the `diff_cumul` dictionary) and `m(s) ≥ 0`, (★) forces some covering interval `[a,e]∈A` to carry
a positive multiplicity `m(r)_{[a,e]} ≥ 1`, whose rectangle lies in `supp g` — exactly the interval
the linked box move recombines.

**Proof (the telescope, Codex-cleaned over the thread-26 block argument).** For row-start `a`, the
`e`-fibre of `A` is the half-open interval `[J, q_a)` where `q_a` is the **first bad column** (least
`q ≥ J` with `g i q = 0` for some `i ∈ [a,I]`); `q_a` is nondecreasing in `a`, and the `a`-fibre is
nonempty exactly on `[α, I]` (`α` the least `a ≤ I` with column `J` positive on `[a,I]`). The inner
telescope over `[J,q_a)` collapses `diff g` to a column difference `D_a(J) − D_a(q_a)`; the outer
row telescope of `D_a(J)` gives `g I J` (`g (α−1) J = 0`), and the `D_a(q_a)` remainder is `≥ 0` by
an adjacent Abel shift (`g I q_I = 0`; at each step either `q_a = q_{a+1}` or `g a q_a = 0`).

**Typeclass.** Pure `ℤ`-combinatorics; no field, no representation theory. **Dependency rule:**
`Core` only (imports `RankPattern` for `diff` / `Supported`).
-/

namespace DLNFibre.Core

open Finset

/-! ## The rectangle-in-support family `A` and its row fibres -/

/-- Column `e` is **good** for the row-band `[a,I]`: `g i e > 0` for every `i ∈ [a,I]`. -/
def goodCol (g : ℤ → ℤ → ℤ) (a I e : ℤ) : Prop := ∀ i ∈ Finset.Icc a I, 0 < g i e

open scoped Classical in
/-- The **rectangle-in-support family**: pairs `(a,e)` with `a ≤ I`, `J ≤ e`, and every column in
`[J,e]` good for `[a,I]` — i.e. `g > 0` on the whole rectangle `[a,I]×[J,e]`. A `Finset` over the
product `Icc 0 I ×ˢ Icc J N`. -/
noncomputable def coveringRect (g : ℤ → ℤ → ℤ) (N I J : ℤ) : Finset (ℤ × ℤ) :=
  (Finset.Icc 0 I ×ˢ Finset.Icc J N).filter (fun p ↦ ∀ j ∈ Finset.Icc J p.2, goodCol g p.1 I j)

/-- The **column difference** `colDiff g a e = g a e − g (a−1) e` (the `D_a(e)` of the telescope):
`diff g a e = colDiff g a e − colDiff g a (e+1)`. -/
def colDiff (g : ℤ → ℤ → ℤ) (a e : ℤ) : ℤ := g a e - g (a - 1) e

/-- `diff g` is the `e`-difference of `colDiff g`. -/
theorem diff_eq_colDiff_sub (g : ℤ → ℤ → ℤ) (a e : ℤ) :
    diff g a e = colDiff g a e - colDiff g a (e + 1) := by
  rw [diff_apply, colDiff, colDiff]; ring

/-- **Inner row telescope.** Over the half-open column interval `[J, F)` the second difference
collapses to one column difference: `∑_{e∈[J,F)} diff g a e = colDiff g a J − colDiff g a F`. -/
theorem sum_Ico_diff_eq (g : ℤ → ℤ → ℤ) (a J : ℤ) {F : ℤ} (hF : J ≤ F) :
    ∑ e ∈ Finset.Ico J F, diff g a e = colDiff g a J - colDiff g a F := by
  induction F, hF using Int.le_induction with
  | base => rw [Finset.Ico_self, Finset.sum_empty]; ring
  | succ F hF ih =>
    have hins : Finset.Ico J (F + 1) = insert F (Finset.Ico J F) := by
      ext x; simp only [Finset.mem_insert, Finset.mem_Ico]; omega
    rw [hins, Finset.sum_insert (by simp), ih, diff_eq_colDiff_sub]
    ring

/-! ## The first bad column `qcol` and the row fibre of `A`

For a row-start `a ≤ I`, the `e`-fibre of `coveringRect` is the half-open interval `[J, qcol a)`,
where `qcol a` is the **first bad column** — the least `q ≥ J` at which some row `i ∈ [a,I]` has
`g i q = 0` (so `[a,I]×[J,q]` leaves the support). A bad column exists in `[J, N+1]` (column `N+1`
is off the support wall), so `qcol a ≤ N+1`; it is nondecreasing in `a`. -/

open scoped Classical in
/-- Column `N+1` is bad for `[a,I]` (it is off the support wall, so `g a (N+1) = 0`). -/
theorem not_goodCol_top (N : ℤ) (g : ℤ → ℤ → ℤ) (hsupp : Supported N g) {a I J : ℤ}
    (haI : a ≤ I) (hJN : J ≤ N) : ¬ goodCol g a I (J + (N + 1 - J).toNat) := by
  intro hgood
  have hcol : (J : ℤ) + ((N + 1 - J).toNat : ℤ) = N + 1 := by
    rw [Int.toNat_of_nonneg (by omega)]; ring
  have := hgood a (Finset.mem_Icc.mpr ⟨le_refl a, haI⟩)
  rw [hcol, hsupp.2 a (N + 1) (by omega)] at this
  exact absurd this (lt_irrefl 0)

/-- A bad column for the band `[a,I]` exists at or beyond `J` (within the range, at `N+1`). -/
theorem exists_badCol (N : ℤ) (g : ℤ → ℤ → ℤ) (hsupp : Supported N g) {a I J : ℤ}
    (haI : a ≤ I) (hJN : J ≤ N) :
    ∃ t : ℕ, ¬ goodCol g a I (J + t) :=
  ⟨(N + 1 - J).toNat, not_goodCol_top N g hsupp haI hJN⟩

open scoped Classical in
/-- The **first bad column** for the band `[a,I]`: `J` plus the least `t` with column `J+t` bad
(`0` fallback if — vacuously — no bad column exists). -/
noncomputable def qcol (g : ℤ → ℤ → ℤ) (I J a : ℤ) : ℤ :=
  if h : ∃ t : ℕ, ¬ goodCol g a I (J + t) then J + (Nat.find h : ℕ) else J

/-- `qcol` is at least `J`. -/
theorem le_qcol (g : ℤ → ℤ → ℤ) (I J a : ℤ) : J ≤ qcol g I J a := by
  rw [qcol]; split_ifs
  · exact le_add_of_nonneg_right (Int.natCast_nonneg _)
  · exact le_refl J

open scoped Classical in
/-- Every column strictly below `qcol` (and `≥ J`) is good for the band `[a,I]`. -/
theorem goodCol_of_lt_qcol (g : ℤ → ℤ → ℤ) {I J a e : ℤ} (hJe : J ≤ e) (he : e < qcol g I J a) :
    goodCol g a I e := by
  rw [qcol] at he
  split_ifs at he with h
  · -- `e = J + t` for `t < Nat.find h`; minimality of `Nat.find` gives `goodCol`
    have ht : (e - J).toNat < Nat.find h := by
      have hlt : ((e - J).toNat : ℤ) < (Nat.find h : ℤ) := by
        rw [Int.toNat_of_nonneg (by omega)]; omega
      exact_mod_cast hlt
    have := Nat.find_min h ht
    rw [not_not] at this
    have hcol : (J : ℤ) + ((e - J).toNat : ℤ) = e := by rw [Int.toNat_of_nonneg (by omega)]; ring
    rwa [hcol] at this
  · omega

open scoped Classical in
/-- The first bad column is itself bad (when a bad column exists). -/
theorem not_goodCol_qcol (g : ℤ → ℤ → ℤ) {I J a : ℤ} (h : ∃ t : ℕ, ¬ goodCol g a I (J + t)) :
    ¬ goodCol g a I (qcol g I J a) := by
  rw [qcol, dif_pos h]
  exact Nat.find_spec h

/-- A bad column for `[a,I]` exists whenever `a ≤ I` and `J ≤ N` (it is the hypothesis feeding the
`dif_pos` branch of `qcol`). -/
theorem exists_badCol' (N : ℤ) (g : ℤ → ℤ → ℤ) (hsupp : Supported N g) {a I J : ℤ}
    (haI : a ≤ I) (hJN : J ≤ N) : ∃ t : ℕ, ¬ goodCol g a I (J + t) :=
  exists_badCol N g hsupp haI hJN

/-- The band-shrinking gives a wider bad-column set: a column bad for `[a+1,I]` is bad for `[a,I]`
(since `[a+1,I] ⊆ [a,I]`). -/
theorem not_goodCol_of_not_goodCol_succ {g : ℤ → ℤ → ℤ} {a I e : ℤ}
    (h : ¬ goodCol g (a + 1) I e) : ¬ goodCol g a I e := by
  intro hgood
  exact h fun i hi ↦ hgood i (Finset.mem_Icc.mpr ⟨le_trans (by omega) (Finset.mem_Icc.mp hi).1,
    (Finset.mem_Icc.mp hi).2⟩)

open scoped Classical in
/-- `qcol` is **nondecreasing** in the row-start: `qcol a ≤ qcol (a+1)`. -/
theorem qcol_le_succ (N : ℤ) (g : ℤ → ℤ → ℤ) (hsupp : Supported N g) {I J a : ℤ}
    (haI : a + 1 ≤ I) (hJN : J ≤ N) : qcol g I J a ≤ qcol g I J (a + 1) := by
  have ha : a ≤ I := by omega
  have hsucc : ∃ t : ℕ, ¬ goodCol g (a + 1) I (J + t) := exists_badCol' N g hsupp haI hJN
  have hcur : ∃ t : ℕ, ¬ goodCol g a I (J + t) := exists_badCol' N g hsupp ha hJN
  rw [qcol, dif_pos hcur, qcol, dif_pos hsucc]
  have hfind : Nat.find hcur ≤ Nat.find hsucc :=
    Nat.find_mono fun t ht ↦ not_goodCol_of_not_goodCol_succ ht
  have : (Nat.find hcur : ℤ) ≤ (Nat.find hsucc : ℤ) := by exact_mod_cast hfind
  omega

/-- At the first bad column the band-bottom row `a` … the band has a zero: `∃ i ∈ [a,I]`,
`g i (qcol a) = 0`. -/
theorem exists_g_qcol_eq_zero (N : ℤ) (g : ℤ → ℤ → ℤ) (hsupp : Supported N g)
    (hpos : ∀ i j, 0 ≤ g i j) {I J a : ℤ} (haI : a ≤ I) (hJN : J ≤ N) :
    ∃ i ∈ Finset.Icc a I, g i (qcol g I J a) = 0 := by
  have h : ∃ t : ℕ, ¬ goodCol g a I (J + t) := exists_badCol' N g hsupp haI hJN
  have hbad := not_goodCol_qcol g h
  rw [goodCol] at hbad
  push Not at hbad
  obtain ⟨i, hi, hle⟩ := hbad
  exact ⟨i, hi, le_antisymm hle (hpos i _)⟩

open scoped Classical in
/-- `qcol ≤ N+1`: column `N+1` is bad (off the support wall), so first bad column is no later. -/
theorem qcol_le (N : ℤ) (g : ℤ → ℤ → ℤ) (hsupp : Supported N g) {I J a : ℤ}
    (haI : a ≤ I) (hJN : J ≤ N) : qcol g I J a ≤ N + 1 := by
  have h : ∃ t : ℕ, ¬ goodCol g a I (J + t) := exists_badCol' N g hsupp haI hJN
  rw [qcol, dif_pos h]
  have hbound : Nat.find h ≤ (N + 1 - J).toNat :=
    Nat.find_min' h (not_goodCol_top N g hsupp haI hJN)
  have : (Nat.find h : ℤ) ≤ ((N + 1 - J).toNat : ℤ) := by exact_mod_cast hbound
  rw [Int.toNat_of_nonneg (by omega)] at this
  omega

open scoped Classical in
/-- **Row-fibre identity.** For `e` in range (`J ≤ e ≤ N`) the rectangle covers `[a,I]×[J,e]`
exactly when `e < qcol a`: the `e`-fibre of `coveringRect` at row `a` is `Ico J (qcol a)`. -/
theorem rowFibre_eq (N : ℤ) (g : ℤ → ℤ → ℤ) (hsupp : Supported N g) {I J a : ℤ}
    (haI : a ≤ I) (hJN : J ≤ N) :
    (Finset.Icc J N).filter (fun e ↦ ∀ j ∈ Finset.Icc J e, goodCol g a I j)
      = Finset.Ico J (qcol g I J a) := by
  have h : ∃ t : ℕ, ¬ goodCol g a I (J + t) := exists_badCol' N g hsupp haI hJN
  ext e
  rw [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ico]
  constructor
  · rintro ⟨⟨hJe, _⟩, hgood⟩
    refine ⟨hJe, ?_⟩
    by_contra hge
    exact not_goodCol_qcol g h
      (hgood _ (Finset.mem_Icc.mpr ⟨le_qcol g I J a, by omega⟩))
  · rintro ⟨hJe, hlt⟩
    refine ⟨⟨hJe, ?_⟩, fun j hj ↦ ?_⟩
    · -- `e < qcol a ≤ N+1`
      have := qcol_le N g hsupp haI hJN; omega
    · exact goodCol_of_lt_qcol g (Finset.mem_Icc.mp hj).1 (by
        have := (Finset.mem_Icc.mp hj).2; omega)

/-! ## Outer telescopes -/

/-- **Outer column telescope.** `∑_{a∈[0,I]} colDiff a c = g I c − g (-1) c` for `0 ≤ I`: the row
sum of a fixed-column difference telescopes. -/
theorem sum_Icc_colDiff (g : ℤ → ℤ → ℤ) (c : ℤ) {I : ℤ} (hI : 0 ≤ I) :
    ∑ a ∈ Finset.Icc 0 I, colDiff g a c = g I c - g (-1) c := by
  induction I, hI using Int.le_induction with
  | base => rw [show (0 : ℤ) = 0 from rfl, Finset.Icc_self, Finset.sum_singleton, colDiff]; ring
  | succ I hI ih =>
    have hins : Finset.Icc 0 (I + 1) = insert (I + 1) (Finset.Icc 0 I) := by
      ext x; simp only [Finset.mem_insert, Finset.mem_Icc]; omega
    rw [hins, Finset.sum_insert (by simp), ih, colDiff]; ring

/-- **Abel shift (a pure reindex identity).** For any column-assignment `q`, the row sum of column
differences equals a boundary part plus an adjacent-difference part:
`∑_{[0,I]} colDiff a (q a) = g I (q I) − g (-1)(q 0) + ∑_{[0,I)} (g a (q a) − g a (q (a+1)))`. -/
theorem sum_Icc_colDiff_abel (g : ℤ → ℤ → ℤ) (q : ℤ → ℤ) {I : ℤ} (hI : 0 ≤ I) :
    ∑ a ∈ Finset.Icc 0 I, colDiff g a (q a)
      = g I (q I) - g (-1) (q 0)
        + ∑ a ∈ Finset.Ico 0 I, (g a (q a) - g a (q (a + 1))) := by
  induction I, hI using Int.le_induction with
  | base =>
    rw [Finset.Icc_self, Finset.sum_singleton, colDiff, Finset.Ico_self, Finset.sum_empty]; ring
  | succ I hI ih =>
    have hIcc : Finset.Icc 0 (I + 1) = insert (I + 1) (Finset.Icc 0 I) := by
      ext x; simp only [Finset.mem_insert, Finset.mem_Icc]; omega
    have hIco : Finset.Ico 0 (I + 1) = insert I (Finset.Ico 0 I) := by
      ext x; simp only [Finset.mem_insert, Finset.mem_Ico]; omega
    rw [hIcc, Finset.sum_insert (by simp), ih, hIco, Finset.sum_insert (by simp), colDiff]
    ring

/-- **The remainder is nonpositive (Abel shift + the jump fact).** `∑_{a∈[0,I]} colDiff a (qcol a)
≤ 0`: after the adjacent shift the boundary terms vanish (`g (-1) · = 0`, `g I (qcol I) = 0`) and
each remaining step is `≤ 0` (either `qcol` is constant or the band-bottom row is a zero). -/
theorem sum_Icc_colDiff_qcol_nonpos (N : ℤ) (g : ℤ → ℤ → ℤ) (hsupp : Supported N g)
    (hpos : ∀ i j, 0 ≤ g i j) {I J : ℤ} (hI : 0 ≤ I) (hIJ : I < J) (hJN : J ≤ N) :
    ∑ a ∈ Finset.Icc 0 I, colDiff g a (qcol g I J a) ≤ 0 := by
  rw [sum_Icc_colDiff_abel g (qcol g I J) hI]
  -- boundary: `g (-1) (qcol 0) = 0` (support `i < 0`) and `g I (qcol I) = 0` (`[I,I]` bad there)
  rw [hsupp.1 (-1) (qcol g I J 0) (by omega)]
  have hII : g I (qcol g I J I) = 0 := by
    obtain ⟨i, hi, hgi⟩ := exists_g_qcol_eq_zero N g hsupp hpos (le_refl I) hJN
    rw [Finset.mem_Icc] at hi
    have : i = I := by omega
    rwa [this] at hgi
  rw [hII, sub_zero, zero_add]
  -- each adjacent term is `≤ 0`
  refine Finset.sum_nonpos fun a ha ↦ ?_
  rw [Finset.mem_Ico] at ha
  have haI : a + 1 ≤ I := by omega
  have ha0 : 0 ≤ a := ha.1
  have hmono : qcol g I J a ≤ qcol g I J (a + 1) :=
    qcol_le_succ N g hsupp haI hJN
  rcases eq_or_lt_of_le hmono with heq | hlt
  · rw [heq]; simp
  · -- `qcol a < qcol (a+1)`: column `qcol a` good for `[a+1,I]`, bad for `[a,I]` ⟹ row `a` zero
    have hgood : goodCol g (a + 1) I (qcol g I J a) :=
      goodCol_of_lt_qcol g (le_qcol g I J a) hlt
    -- `qcol a` is bad for `[a,I]`; the offending row must be `a`, giving `g a (qcol a) = 0`
    obtain ⟨i, hi, hgi⟩ := exists_g_qcol_eq_zero N g hsupp hpos (by omega : a ≤ I) hJN
    rw [Finset.mem_Icc] at hi
    have hia : i = a := by
      by_contra hne
      have : i ∈ Finset.Icc (a + 1) I := Finset.mem_Icc.mpr ⟨by omega, hi.2⟩
      exact absurd (hgood i this) (by rw [hgi]; exact lt_irrefl 0)
    rw [hia] at hgi
    rw [hgi, zero_sub, neg_nonpos]
    exact hpos a _

/-! ## Headline (★) -/

/-- **L6.2b-key (★).** For a nonnegative array `g` supported off the half-plane and a cell `(I,J)`
with `I < J` and `g I J > 0`, the sum of `diff g` over the rectangle-in-support family is at least
`g I J`. -/
theorem sum_secondDiff_coveringRect_ge (N : ℤ) (g : ℤ → ℤ → ℤ)
    (hsupp : Supported N g) (hpos : ∀ i j, 0 ≤ g i j) {I J : ℤ}
    (hIJ : I < J) (hJN : J ≤ N) (hgIJ : 0 < g I J) :
    g I J ≤ ∑ p ∈ coveringRect g N I J, diff g p.1 p.2 := by
  classical
  -- `0 ≤ I` (else `g I J = 0` by support)
  have hI0 : 0 ≤ I := by
    by_contra hlt
    rw [hsupp.1 I J (by omega)] at hgIJ
    exact absurd hgIJ (lt_irrefl 0)
  -- split the product-filter sum into a double sum over rows, each row over its `Ico` fibre
  have hsplit : ∑ p ∈ coveringRect g N I J, diff g p.1 p.2
      = ∑ a ∈ Finset.Icc 0 I, ∑ e ∈ Finset.Ico J (qcol g I J a), diff g a e := by
    rw [coveringRect, Finset.sum_filter, Finset.sum_product]
    refine Finset.sum_congr rfl fun a ha ↦ ?_
    have haI : a ≤ I := (Finset.mem_Icc.mp ha).2
    rw [← Finset.sum_filter, rowFibre_eq N g hsupp haI hJN]
  rw [hsplit]
  -- inner telescope each row, then split the outer sum
  have hrow : ∑ a ∈ Finset.Icc 0 I, ∑ e ∈ Finset.Ico J (qcol g I J a), diff g a e
      = ∑ a ∈ Finset.Icc 0 I, (colDiff g a J - colDiff g a (qcol g I J a)) :=
    Finset.sum_congr rfl fun a _ ↦ sum_Ico_diff_eq g a J (le_qcol g I J a)
  rw [hrow, Finset.sum_sub_distrib, sum_Icc_colDiff g J hI0, hsupp.1 (-1) J (by omega), sub_zero]
  -- `g I J - (remainder)`, with remainder ≤ 0
  have hrem := sum_Icc_colDiff_qcol_nonpos N g hsupp hpos hI0 hIJ hJN
  linarith

section Witness

/-! ## Non-vacuity witness

`N = 2`, over `ℤ`. The single-cell residual `g` with `g 0 1 = 1` (else `0` on the triangle, `0`
off it) is nonnegative and supported; at its only positive cell `(I,J) = (0,1)` the
rectangle-in-support family is `{(0,1)}`, so (★) gives `1 ≤ ∑ = diff g 0 1 = 1` — the hypotheses
are jointly satisfiable and the bound is non-trivial. -/

/-- A single-cell nonnegative supported residual: `g 0 1 = 1`, else `0`. -/
def gWitness : ℤ → ℤ → ℤ := fun i j ↦ if i = 0 ∧ j = 1 then 1 else 0

/-- The witness residual is supported (vanishes for `i < 0` and for `j > 2`). -/
theorem supported_gWitness : Supported 2 gWitness := by
  refine ⟨fun i j hi ↦ ?_, fun i j hj ↦ ?_⟩ <;>
    · unfold gWitness; split_ifs with h <;> omega

/-- The witness residual is nonnegative. -/
theorem nonneg_gWitness : ∀ i j, 0 ≤ gWitness i j := by
  intro i j; unfold gWitness; split_ifs <;> norm_num

/-- (★) fires on the witness: at the cell `(0,1)` the covering-rectangle sum of `diff gWitness` is
at least `gWitness 0 1 = 1`. -/
example : gWitness 0 1 ≤ ∑ p ∈ coveringRect gWitness 2 0 1, diff gWitness p.1 p.2 :=
  sum_secondDiff_coveringRect_ge 2 gWitness supported_gWitness nonneg_gWitness
    (by norm_num) (by norm_num) (by norm_num [gWitness])

end Witness

end DLNFibre.Core
