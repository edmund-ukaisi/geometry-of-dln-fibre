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
`q ≥ J` with `g i q = 0` for some `i ∈ [a,I]`); `q_a` is nondecreasing in `a`. The inner telescope
over `[J,q_a)` collapses `diff g` to a column difference `D_a(J) − D_a(q_a)` (empty-fibre rows,
`q_a = J`, contribute `0`), summed over **all** `a ∈ [0,I]`. The outer row telescope of `D_a(J)`
gives `g I J` (`g (−1) J = 0`), and the `D_a(q_a)` remainder is `≤ 0` by an adjacent Abel shift
(boundary `g (−1)(q_0) = 0`, `g I q_I = 0`; at each step either `q_a = q_{a+1}` or `g a q_a = 0`).

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

/-! ## L6.2b — move existence (the covering interval carrying positive multiplicity)

Substituting the dictionary `diff g = diff r − diff s` (`diff` is additive) into (★): if `s` is
achievable (`diff s ≥ 0`, the multiplicities of `s` are nonnegative) and `s ≤ r` with `g = r − s`
positive at `(I,J)`, then some covering interval `[a,e]` carries a positive `r`-multiplicity
`diff r a e ≥ 1` and has its rectangle in `supp g`. This is the interval the linked box move
recombines. -/

/-- `diff` is additive on the pointwise difference: `diff (r − s) = diff r − diff s`. -/
theorem diff_sub (r s : ℤ → ℤ → ℤ) (i j : ℤ) :
    diff (fun i j ↦ r i j - s i j) i j = diff r i j - diff s i j := by
  simp only [diff_apply]; ring

/-- **L6.2b (move existence).** With `g = r − s` nonnegative and supported, `s` achievable
(`diff s ≥ 0`), at any positive cell `(I,J)` of `g` there is a covering interval `[a,e]` (rectangle
`[a,I]×[J,e] ⊆ supp g`) carrying positive `r`-multiplicity `diff r a e ≥ 1`. -/
theorem exists_coveringInterval_diff_pos (N : ℤ) (r s : ℤ → ℤ → ℤ)
    (hsupp : Supported N (fun i j ↦ r i j - s i j)) (hpos : ∀ i j, 0 ≤ r i j - s i j)
    (hms : ∀ i j, 0 ≤ diff s i j) {I J : ℤ}
    (hIJ : I < J) (hJN : J ≤ N) (hgIJ : 0 < r I J - s I J) :
    ∃ p ∈ coveringRect (fun i j ↦ r i j - s i j) N I J, 1 ≤ diff r p.1 p.2 := by
  set g : ℤ → ℤ → ℤ := fun i j ↦ r i j - s i j with hg
  by_contra hcon
  push Not at hcon
  -- assuming `diff r < 1`, i.e. `diff r ≤ 0`, on every covering interval, `diff g ≤ 0` there
  have hle : ∀ p ∈ coveringRect g N I J, diff g p.1 p.2 ≤ 0 := by
    intro p hp
    have hr0 : diff r p.1 p.2 ≤ 0 := by have := hcon p hp; omega
    have : diff g p.1 p.2 = diff r p.1 p.2 - diff s p.1 p.2 := diff_sub r s p.1 p.2
    have hs0 := hms p.1 p.2
    omega
  -- contradicts (★): `g I J ≤ ∑ diff g ≤ 0 < g I J`
  have hgIJ' : 0 < g I J := hgIJ
  have hstar := sum_secondDiff_coveringRect_ge N g hsupp hpos hIJ hJN hgIJ'
  have hsum : ∑ p ∈ coveringRect g N I J, diff g p.1 p.2 ≤ 0 := Finset.sum_nonpos hle
  omega

/-! ## L6.2a — the box move on rank patterns (drop the rectangle `D`)

The box move sends a rank pattern `r` to `r' = r − 1_D` over the **drop rectangle**
`D = [a,c−1]×[b+1,e]` (`a < c ≤ b+1 ≤ e`). The second difference of the indicator `1_D` is a
four-corner pattern (`boxIndicator_diff`): `m' = m(r) + 1_{(a,b)} − 1_{(a,e)} − 1_{(c,b)} +
1_{(c,e)}`. So `r'` stays **achievable** (`diff r' ≥ 0`) once the move is applicable —
`m(r)_{[a,e]} ≥ 1` and (linked case `c ≤ b`) `m(r)_{[c,b]} ≥ 1`; the other two multiplicities rise.
`D` lies strictly above the diagonal, so the **dimension vector is preserved** (`r'_{tt} = r_{tt}`),
and `r' ≤ r` with strict drop on `D` (so `Φ = Σ_{i<j}(r−s)` strictly decreases under the move). -/

/-- The **drop-rectangle indicator** `1_D` for `D = [a,c−1]×[b+1,e]`. -/
def boxIndicator (a c b e : ℤ) (i j : ℤ) : ℤ :=
  if a ≤ i ∧ i ≤ c - 1 ∧ b + 1 ≤ j ∧ j ≤ e then 1 else 0

/-- **Four-corner identity.** `diff (1_D)` is `−1` at `(a,b)` and `(c,e)`, `+1` at `(a,e)` and
`(c,b)`: the box-move multiplicity delta. (Stated as the pointwise value at `(i,j)`.) -/
theorem boxIndicator_diff (a c b e i j : ℤ) (hac : a < c) (hcb : c ≤ b + 1) (hbe : b + 1 ≤ e) :
    diff (boxIndicator a c b e) i j
      = (if i = a ∧ j = b then -1 else 0) + (if i = c ∧ j = e then -1 else 0)
        + (if i = a ∧ j = e then 1 else 0) + (if i = c ∧ j = b then 1 else 0) := by
  rw [diff_apply, boxIndicator, boxIndicator, boxIndicator, boxIndicator]
  split_ifs <;> omega

/-- The **box move on a rank pattern**: `boxDrop r = r − 1_D`, `D = [a,c−1]×[b+1,e]`. -/
def boxDrop (r : ℤ → ℤ → ℤ) (a c b e : ℤ) (i j : ℤ) : ℤ := r i j - boxIndicator a c b e i j

/-- **The box move preserves achievability (on the upper triangle).** For a cell `(i,j)` with
`i ≤ j` — the meaningful domain of a rank pattern's multiplicities — when the move is applicable
(`m(r)_{[a,e]} ≥ 1`, and in the linked case `c ≤ b` also `m(r)_{[c,b]} ≥ 1`) the dropped pattern is
still achievable there: `diff (boxDrop r) i j ≥ 0`. (Below the diagonal the `(c,b)` corner of the
split case `c = b+1` would be negative, but `(c,b)` is then below the diagonal — off the rank
pattern's domain — so achievability as a rank pattern is unaffected.) -/
theorem diff_boxDrop_nonneg (r : ℤ → ℤ → ℤ) {a c b e i j : ℤ} (hac : a < c) (hcb : c ≤ b + 1)
    (hbe : b + 1 ≤ e) (hij : i ≤ j) (hmr : ∀ i j, 0 ≤ diff r i j) (hae : 1 ≤ diff r a e)
    (hcbm : c ≤ b → 1 ≤ diff r c b) : 0 ≤ diff (boxDrop r a c b e) i j := by
  have hdiff : diff (boxDrop r a c b e) i j = diff r i j - diff (boxIndicator a c b e) i j := by
    simp only [boxDrop, diff_apply]; ring
  rw [hdiff, boxIndicator_diff a c b e i j hac hcb hbe]
  have h0 := hmr i j
  -- the two dropping corners are `(a,e)` and (linked) `(c,b)`; the other two rise
  by_cases hae' : i = a ∧ j = e
  · obtain ⟨hi, hj⟩ := hae'
    rw [hi, hj] at h0 ⊢
    rw [if_neg (by rintro ⟨_, h⟩; omega), if_neg (by rintro ⟨h, _⟩; omega),
      if_pos ⟨rfl, rfl⟩, if_neg (by rintro ⟨h, _⟩; omega)]
    omega
  · by_cases hcb' : i = c ∧ j = b
    · obtain ⟨hi, hj⟩ := hcb'
      have hcle : c ≤ b := by rw [hi, hj] at hij; omega
      have hcbm' := hcbm hcle
      rw [hi, hj] at h0 ⊢
      rw [if_neg (by rintro ⟨h, _⟩; omega), if_neg (by rintro ⟨_, h⟩; omega),
        if_neg (by rintro ⟨h, _⟩; omega), if_pos ⟨rfl, rfl⟩]
      omega
    · rw [if_neg fun h ↦ hae' h, if_neg fun h ↦ hcb' h]
      split_ifs <;> omega

/-- **Dimension preservation.** The drop rectangle is strictly above the diagonal, so the box move
fixes the diagonal: `boxDrop r t t = r t t`. -/
theorem boxDrop_diag (r : ℤ → ℤ → ℤ) {a c b e : ℤ} (hac : a < c) (hcb : c ≤ b + 1)
    (hbe : b + 1 ≤ e) (t : ℤ) : boxDrop r a c b e t t = r t t := by
  rw [boxDrop, boxIndicator, if_neg (by omega), sub_zero]

/-- **The move drops the pattern.** `boxDrop r ≤ r` everywhere, strictly on `D` (e.g. at `(a,b+1)`,
which is in `D`). -/
theorem boxDrop_le (r : ℤ → ℤ → ℤ) (a c b e i j : ℤ) : boxDrop r a c b e i j ≤ r i j := by
  rw [boxDrop, boxIndicator]; split_ifs <;> omega

/-- **The drop is strict on `D`.** At `(a, b+1) ∈ D` the move strictly lowers the pattern:
`boxDrop r a c b e a (b+1) = r a (b+1) − 1`. So `Φ = Σ_{i≤j}(r − s)` strictly decreases under the
move (the witness cell for termination). -/
theorem boxDrop_strict (r : ℤ → ℤ → ℤ) {a c b e : ℤ} (hac : a < c) (hbe : b + 1 ≤ e) :
    boxDrop r a c b e a (b + 1) = r a (b + 1) - 1 := by
  rw [boxDrop, boxIndicator, if_pos ⟨le_refl a, by omega, le_refl (b + 1), hbe⟩]

/-! ## The box-move step relation (reusable interface for L6.2c and L6.4)

A single applicable box move, packaged as a relation on rank patterns. `BoxMoveStep r r'` holds
when `r' = boxDrop r a c b e` for a valid linked move `a < c ≤ b+1 ≤ e` whose applicability
conditions hold on `r` (`m(r)_{[a,e]} ≥ 1`, and `m(r)_{[c,b]} ≥ 1` in the linked case). The
reflexive-transitive closure `Relation.ReflTransGen BoxMoveStep` is the **box-move chain**; L6.2c
(the `Φ`-induction) establishes `s ≤ r → BoxMoveChain r s`, and L6.4 composes each step with the
per-move degeneration `Core.BoxMoveGeneral`. -/

/-- **Sub-fact 1 (the linked applicability, elementary).** At an extremal deficient cell `(i0,j0)`
of `g = r − s` (its three neighbours `g (i0+1)(j0−1)`, `g (i0+1) j0`, `g i0 (j0−1)` vanish, as the
extremal choice's minimality/maximality provides) with `g i0 j0 ≥ 1`, the linked multiplicity is
positive: `diff r (i0+1) (j0−1) ≥ 1`. (The second difference of `g` collapses to `g i0 j0`, and
`diff r = diff g + diff s ≥ diff g` since `diff s ≥ 0`.) -/
theorem one_le_diff_linked (r s : ℤ → ℤ → ℤ) {i0 j0 : ℤ}
    (hms : ∀ i j, 0 ≤ diff s i j)
    (hv1 : r (i0 + 1) (j0 - 1) - s (i0 + 1) (j0 - 1) = 0)
    (hv2 : r (i0 + 1) j0 - s (i0 + 1) j0 = 0)
    (hv3 : r i0 (j0 - 1) - s i0 (j0 - 1) = 0)
    (hgIJ : 1 ≤ r i0 j0 - s i0 j0) :
    1 ≤ diff r (i0 + 1) (j0 - 1) := by
  -- `diff g (i0+1)(j0−1) = g i0 j0` (the three neighbours vanish); `diff r ≥ diff g`
  have hg : diff (fun i j ↦ r i j - s i j) (i0 + 1) (j0 - 1) = r i0 j0 - s i0 j0 := by
    rw [diff_apply]
    have e1 : (j0 - 1) + 1 = j0 := by ring
    have e2 : (i0 + 1) - 1 = i0 := by ring
    rw [e1, e2]
    simp only [hv1, hv2, hv3]
    ring
  have hsub := diff_sub r s (i0 + 1) (j0 - 1)
  have hs0 := hms (i0 + 1) (j0 - 1)
  -- `diff r = diff g + diff s ≥ g i0 j0 + 0 ≥ 1`
  have : diff (fun i j ↦ r i j - s i j) (i0 + 1) (j0 - 1) = diff r (i0 + 1) (j0 - 1)
      - diff s (i0 + 1) (j0 - 1) := hsub
  rw [hg] at this
  omega

/-- A single applicable linked box move from `r` to `r'`. -/
def BoxMoveStep (r r' : ℤ → ℤ → ℤ) : Prop :=
  ∃ a c b e : ℤ, a < c ∧ c ≤ b + 1 ∧ b + 1 ≤ e ∧
    (1 ≤ diff r a e) ∧ (c ≤ b → 1 ≤ diff r c b) ∧ r' = boxDrop r a c b e

/-- The **box-move chain**: a finite sequence of applicable box moves. -/
def BoxMoveChain (r s : ℤ → ℤ → ℤ) : Prop := Relation.ReflTransGen BoxMoveStep r s

/-! ## L6.2c, piece 1 — the extremal deficient cell

For `g = r − s` nonnegative, supported, and vanishing on/below the diagonal (`j ≤ i ⟹ g i j = 0`,
forced because box moves only touch the strict upper triangle), with *some* positive cell: choose
`(i0,j0)` with `j0` the minimal column carrying a positive cell, then `i0` the maximal row positive
in column `j0`. This gives the three neighbour vanishings `one_le_diff_linked` needs:
`g i0 (j0−1) = 0` and `g (i0+1)(j0−1) = 0` by `j0`-minimality (column `j0−1` is empty), and
`g (i0+1) j0 = 0` by `i0`-maximality in column `j0`. -/

/-- **The extremal deficient cell.** For nonnegative supported `g` vanishing on/below the diagonal,
with a positive cell `(I,J)` (`I < J ≤ N`, `0 < g I J`), there is an extremal cell `(i0,j0)` —
`0 ≤ i0 < j0 ≤ N`, `1 ≤ g i0 j0` — with the three neighbour vanishings: `g i0 (j0−1) = 0`,
`g (i0+1)(j0−1) = 0`, `g (i0+1) j0 = 0`. -/
theorem exists_extremalCell (N : ℤ) (g : ℤ → ℤ → ℤ) (hsupp : Supported N g)
    (hpos : ∀ i j, 0 ≤ g i j) (hbelow : ∀ i j, j ≤ i → g i j = 0)
    {I J : ℤ} (hIJ : I < J) (hJN : J ≤ N) (hgIJ : 0 < g I J) :
    ∃ i0 j0 : ℤ, 0 ≤ i0 ∧ i0 < j0 ∧ j0 ≤ N ∧ 1 ≤ g i0 j0 ∧
      g i0 (j0 - 1) = 0 ∧ g (i0 + 1) (j0 - 1) = 0 ∧ g (i0 + 1) j0 = 0 := by
  -- `I ≥ 0` (else `g I J = 0` by support)
  have hI0 : 0 ≤ I := by
    by_contra hlt; rw [hsupp.1 I J (by omega)] at hgIJ; exact absurd hgIJ (lt_irrefl 0)
  -- the finite positive-cell set inside the box `[0,N]²`; the cell `(I,J)` witnesses nonemptiness.
  set S : Finset (ℤ × ℤ) :=
    (Finset.Icc 0 N ×ˢ Finset.Icc 0 N).filter (fun p ↦ 0 < g p.1 p.2) with hS
  have hmemS : ∀ {i j : ℤ}, (i, j) ∈ S ↔ (0 ≤ i ∧ i ≤ N ∧ 0 ≤ j ∧ j ≤ N) ∧ 0 < g i j := by
    intro i j
    rw [hS, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨⟨h1, h2⟩, h3, h4⟩, h5⟩; exact ⟨⟨h1, h2, h3, h4⟩, h5⟩
    · rintro ⟨⟨h1, h2, h3, h4⟩, h5⟩; exact ⟨⟨⟨h1, h2⟩, h3, h4⟩, h5⟩
  have hIJS : (I, J) ∈ S := hmemS.mpr ⟨⟨hI0, by omega, by omega, hJN⟩, hgIJ⟩
  -- column projection: minimal column with a positive cell.
  set cols : Finset ℤ := S.image Prod.snd with hcols
  have hne : cols.Nonempty := ⟨J, by rw [hcols, Finset.mem_image]; exact ⟨(I, J), hIJS, rfl⟩⟩
  set j0 : ℤ := cols.min' hne with hj0
  have hj0mem : j0 ∈ cols := Finset.min'_mem cols hne
  rw [hcols, Finset.mem_image] at hj0mem
  obtain ⟨⟨i', j'⟩, hpS, hproj⟩ := hj0mem
  simp only at hproj; subst hproj
  have hi'props := hmemS.mp hpS
  have hj0N : j0 ≤ N := hi'props.1.2.2.2
  have hi'pos : 0 < g i' j0 := hi'props.2
  have hi'range : 0 ≤ i' ∧ i' ≤ N := ⟨hi'props.1.1, hi'props.1.2.1⟩
  have hi'lt : i' < j0 := by
    by_contra hge; rw [hbelow i' j0 (by omega)] at hi'pos; exact absurd hi'pos (lt_irrefl 0)
  -- every positive cell sits at column `≥ j0`; column `j0 − 1` is empty.
  have hcolmin : ∀ {i j : ℤ}, 0 < g i j → 0 ≤ i → i ≤ N → 0 ≤ j → j ≤ N → j0 ≤ j := by
    intro i j hg hi0 hiN hj0' hjN
    have : j ∈ cols := by
      rw [hcols, Finset.mem_image]
      exact ⟨(i, j), hmemS.mpr ⟨⟨hi0, hiN, hj0', hjN⟩, hg⟩, rfl⟩
    exact hj0 ▸ Finset.min'_le cols j this
  -- row projection within column `j0`: maximal row.
  set rows : Finset ℤ := (S.filter (fun p ↦ p.2 = j0)).image Prod.fst with hrows
  have hrne : rows.Nonempty :=
    ⟨i', by rw [hrows, Finset.mem_image]; exact ⟨(i', j0), Finset.mem_filter.mpr ⟨hpS, rfl⟩, rfl⟩⟩
  set i0 : ℤ := rows.max' hrne with hi0
  have hi0mem : i0 ∈ rows := Finset.max'_mem rows hrne
  rw [hrows, Finset.mem_image] at hi0mem
  obtain ⟨⟨i'', j''⟩, hp2, hproj2⟩ := hi0mem
  simp only at hproj2; subst hproj2
  obtain ⟨hp2S, hp2col⟩ := Finset.mem_filter.mp hp2
  simp only at hp2col; subst hp2col
  have hi0props := hmemS.mp hp2S
  have hi00 : 0 ≤ i0 := hi0props.1.1
  have hi0N : i0 ≤ N := hi0props.1.2.1
  have hi0pos : 0 < g i0 j0 := hi0props.2
  have hi0lt : i0 < j0 := by
    by_contra hge; rw [hbelow i0 j0 (by omega)] at hi0pos; exact absurd hi0pos (lt_irrefl 0)
  refine ⟨i0, j0, hi00, hi0lt, hj0N, hi0pos, ?_, ?_, ?_⟩
  · -- `g i0 (j0−1) = 0`: column `j0−1 < j0` carries no positive cell (minimality of `j0`)
    by_contra hne0
    have hgt : 0 < g i0 (j0 - 1) := lt_of_le_of_ne (hpos _ _) (Ne.symm hne0)
    have := hcolmin hgt hi00 hi0N (by omega) (by omega); omega
  · -- `g (i0+1)(j0−1) = 0`: same column `j0−1` empty
    by_contra hne0
    have hgt : 0 < g (i0 + 1) (j0 - 1) := lt_of_le_of_ne (hpos _ _) (Ne.symm hne0)
    -- `i0+1 ≤ N` (else off support); then column-minimality forces `j0 ≤ j0−1`
    have hi1N : i0 + 1 ≤ N := by
      by_contra hgtN
      rw [hbelow (i0 + 1) (j0 - 1) (by omega)] at hgt; exact absurd hgt (lt_irrefl 0)
    have := hcolmin hgt (by omega) hi1N (by omega) (by omega); omega
  · -- `g (i0+1) j0 = 0`: `i0` is the max row positive in column `j0`
    by_contra hne0
    have hgt : 0 < g (i0 + 1) j0 := lt_of_le_of_ne (hpos _ _) (Ne.symm hne0)
    have hi1N : i0 + 1 ≤ N := by
      by_contra hgtN
      rw [hbelow (i0 + 1) j0 (by omega)] at hgt; exact absurd hgt (lt_irrefl 0)
    have hmem : (i0 + 1) ∈ rows := by
      rw [hrows, Finset.mem_image]
      exact ⟨(i0 + 1, j0),
        Finset.mem_filter.mpr ⟨hmemS.mpr ⟨⟨by omega, hi1N, by omega, hj0N⟩, hgt⟩, rfl⟩, rfl⟩
    have hcontra : i0 + 1 ≤ i0 := hi0 ▸ Finset.le_max' rows (i0 + 1) hmem
    omega

/-! ## L6.2c, piece 2 — the descent step

Combine the extremal cell (piece 1) with the linked applicability (`one_le_diff_linked`) and
move-existence (`exists_coveringInterval_diff_pos`) into a single `BoxMoveStep r r'` whose drop
rectangle lies in `supp(r − s)`, so the dropped pattern `r'` still dominates `s` on the upper
triangle, and strictly lowers `r` at `(a, j0)` (so the deficiency `Φ` decreases). -/

open scoped Classical in
/-- A covering interval's rectangle lies in `supp g`: `g > 0` on `[a,I]×[J,e]`. -/
theorem coveringRect_pos (g : ℤ → ℤ → ℤ) {N I J a e i j : ℤ}
    (hp : (a, e) ∈ coveringRect g N I J) (hi : a ≤ i ∧ i ≤ I) (hj : J ≤ j ∧ j ≤ e) :
    0 < g i j := by
  rw [coveringRect, Finset.mem_filter] at hp
  exact hp.2 j (Finset.mem_Icc.mpr hj) i (Finset.mem_Icc.mpr hi)

/-- **The descent step.** With `g = r − s` nonnegative, supported, vanishing on/below the diagonal,
`s` and `r` achievable (`diff s, diff r ≥ 0`), and a positive cell `(I,J)`: there is a single box
move `r' = boxDrop r a c b e` (a `BoxMoveStep r r'`) whose drop rectangle is in `supp g`, so `r'`
still dominates `s` on the upper triangle, drops `r` everywhere, and strictly at `(a, b+1)`. -/
theorem exists_boxMoveStep_descent (N : ℤ) (r s : ℤ → ℤ → ℤ)
    (hsupp : Supported N (fun i j ↦ r i j - s i j)) (hpos : ∀ i j, 0 ≤ r i j - s i j)
    (hbelow : ∀ i j, j ≤ i → r i j - s i j = 0)
    (hms : ∀ i j, 0 ≤ diff s i j)
    {I J : ℤ} (hIJ : I < J) (hJN : J ≤ N) (hgIJ : 0 < r I J - s I J) :
    ∃ a c b e : ℤ, BoxMoveStep r (boxDrop r a c b e) ∧
      (∀ i j, i ≤ j → s i j ≤ boxDrop r a c b e i j) ∧
      0 ≤ a ∧ a < c ∧ c ≤ b + 1 ∧ a < b + 1 ∧ b + 1 ≤ e ∧ e ≤ N := by
  classical
  set g : ℤ → ℤ → ℤ := fun i j ↦ r i j - s i j with hg
  -- piece 1: the extremal cell `(i0,j0)` and its three neighbour vanishings
  obtain ⟨i0, j0, hi00, hi0lt, hj0N, hg0pos, hv3, hv1, hv2⟩ :=
    exists_extremalCell N g hsupp hpos (fun i j h ↦ hbelow i j h) hIJ hJN hgIJ
  -- piece 2a: move-existence at `(i0,j0)` gives the covering interval `(a,e)`
  obtain ⟨⟨a, e⟩, hpmem, hae⟩ :=
    exists_coveringInterval_diff_pos N r s hsupp hpos hms hi0lt (by omega) hg0pos
  -- read off `a ≤ i0`, `j0 ≤ e` from covering-rect membership (keep `hpmem` for the rectangle fact)
  have hbounds := hpmem
  rw [coveringRect, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
    at hbounds
  obtain ⟨⟨⟨ha0, hai0⟩, hj0e, heN⟩, _⟩ := hbounds
  -- the move anchor `c = i0+1, b = j0−1`
  refine ⟨a, i0 + 1, j0 - 1, e, ?_, ?_, by omega, by omega, by omega, by omega, by omega, by omega⟩
  · -- the `BoxMoveStep`
    refine ⟨a, i0 + 1, j0 - 1, e, by omega, by omega, by omega, hae, ?_, rfl⟩
    -- linked: `i0+1 ≤ j0−1 → 1 ≤ diff r (i0+1)(j0−1)` from sub-fact 1
    intro _
    exact one_le_diff_linked r s hms (by simpa [hg] using hv1)
      (by simpa [hg] using hv2) (by simpa [hg] using hv3) (by simpa [hg] using hg0pos)
  · -- domination `s ≤ boxDrop r` on the triangle
    intro i j hij
    rw [boxDrop, boxIndicator]
    split_ifs with hin
    · -- `(i,j) ∈ D = [a,i0]×[j0,e]`: rectangle in `supp g`, so `g i j ≥ 1`
      obtain ⟨ha, hci, hbj, hje⟩ := hin
      have hgpos : 0 < g i j :=
        coveringRect_pos g hpmem ⟨ha, by omega⟩ ⟨by omega, hje⟩
      simp only [hg] at hgpos; omega
    · -- off `D`: `boxDrop = r`, dominates `s` by `hpos`
      have := hpos i j; omega

/-! ## L6.2c, piece 3 — the deficiency `Φ` and the generation induction

`deficiency N r s = ∑_{0 ≤ i ≤ j ≤ N} (r_{ij} − s_{ij})` (the upper-triangle box `triBox N`) is a
nonnegative `ℤ`-valued potential that the descent step strictly lowers. Strong induction on its
`toNat` value drives `s ≤ r → BoxMoveChain r s`: at `Φ = 0` the patterns coincide
(`ReflTransGen.refl`); otherwise a positive triangle cell feeds the descent step, lowering `Φ`. -/

/-- The upper-triangle box `{(i,j) : 0 ≤ i ≤ j ≤ N}` — the index set of the deficiency. -/
def triBox (N : ℤ) : Finset (ℤ × ℤ) :=
  (Finset.Icc 0 N ×ˢ Finset.Icc 0 N).filter (fun p ↦ p.1 ≤ p.2)

/-- Membership in `triBox`: `0 ≤ i ≤ j ≤ N` and `i ≤ N`. -/
theorem mem_triBox {N i j : ℤ} :
    (i, j) ∈ triBox N ↔ (0 ≤ i ∧ i ≤ N) ∧ (0 ≤ j ∧ j ≤ N) ∧ i ≤ j := by
  rw [triBox, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
  tauto

/-- The **deficiency** `Φ r s = ∑_{0 ≤ i ≤ j ≤ N} (r_{ij} − s_{ij})`. -/
def deficiency (N : ℤ) (r s : ℤ → ℤ → ℤ) : ℤ :=
  ∑ p ∈ triBox N, (r p.1 p.2 - s p.1 p.2)

/-- The deficiency is nonnegative when `s ≤ r` on the triangle. -/
theorem deficiency_nonneg (N : ℤ) (r s : ℤ → ℤ → ℤ)
    (hle : ∀ i j, i ≤ j → s i j ≤ r i j) : 0 ≤ deficiency N r s := by
  apply Finset.sum_nonneg
  rintro ⟨i, j⟩ hp
  exact sub_nonneg.mpr (hle i j (mem_triBox.mp hp).2.2)

/-- `Φ = 0` forces equality on the triangle box: each summand vanishes. -/
theorem eq_of_deficiency_eq_zero (N : ℤ) (r s : ℤ → ℤ → ℤ)
    (hle : ∀ i j, i ≤ j → s i j ≤ r i j) (h0 : deficiency N r s = 0)
    {i j : ℤ} (hp : (i, j) ∈ triBox N) : r i j = s i j := by
  have hnn : ∀ p ∈ triBox N, 0 ≤ (r p.1 p.2 - s p.1 p.2) := by
    rintro ⟨a, b⟩ hp; exact sub_nonneg.mpr (hle a b (mem_triBox.mp hp).2.2)
  have := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp h0 (i, j) hp
  simpa [sub_eq_zero] using this

/-- The full function equality `r = s` from `Φ = 0`, using support and below-diagonal agreement. -/
theorem funext_of_deficiency_eq_zero (N : ℤ) (r s : ℤ → ℤ → ℤ)
    (hsupp : Supported N (fun i j ↦ r i j - s i j))
    (hle : ∀ i j, i ≤ j → s i j ≤ r i j) (hbelow : ∀ i j, j ≤ i → r i j - s i j = 0)
    (h0 : deficiency N r s = 0) : r = s := by
  funext i j
  rcases lt_or_ge i 0 with hi | hi
  · have := hsupp.1 i j hi; simpa [sub_eq_zero] using this
  rcases lt_or_ge N j with hj | hj
  · have := hsupp.2 i j hj; simpa [sub_eq_zero] using this
  rcases le_or_gt j i with hji | hij
  · have := hbelow i j hji; simpa [sub_eq_zero] using this
  · exact eq_of_deficiency_eq_zero N r s hle h0
      (mem_triBox.mpr ⟨⟨hi, by omega⟩, ⟨by omega, hj⟩, by omega⟩)

/-- The descent strictly lowers the deficiency: `Φ (boxDrop r a c b e) s < Φ r s` when the strict
drop cell `(a, b+1)` is in the triangle box (`0 ≤ a < b+1 ≤ N`). -/
theorem deficiency_boxDrop_lt (N : ℤ) (r s : ℤ → ℤ → ℤ) {a c b e : ℤ}
    (hac : a < c) (hbe : b + 1 ≤ e) (ha0 : 0 ≤ a) (hab : a < b + 1) (hbN : b + 1 ≤ N) :
    deficiency N (boxDrop r a c b e) s < deficiency N r s := by
  have hsub : deficiency N r s - deficiency N (boxDrop r a c b e) s
      = ∑ p ∈ triBox N, (r p.1 p.2 - boxDrop r a c b e p.1 p.2) := by
    rw [deficiency, deficiency, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun p _ ↦ by ring
  -- each term `≥ 0` (boxDrop_le), and `= 1` at `(a,b+1)` (boxDrop_strict)
  have hcell : (a, b + 1) ∈ triBox N :=
    mem_triBox.mpr ⟨⟨ha0, by omega⟩, ⟨by omega, hbN⟩, by omega⟩
  have hnn : ∀ p ∈ triBox N, 0 ≤ (r p.1 p.2 - boxDrop r a c b e p.1 p.2) := fun p _ ↦
    sub_nonneg.mpr (boxDrop_le r a c b e p.1 p.2)
  have hpos1 : (1 : ℤ) ≤ ∑ p ∈ triBox N, (r p.1 p.2 - boxDrop r a c b e p.1 p.2) := by
    calc (1 : ℤ) = r a (b + 1) - boxDrop r a c b e a (b + 1) := by
            rw [boxDrop_strict r hac hbe]; ring
      _ ≤ _ := Finset.single_le_sum hnn hcell
  omega

/-- Strong-induction core: `Φ ≤ n` and the invariants give a box-move chain `r ↠ s`. -/
theorem box_move_chain_aux (N : ℤ) (s : ℤ → ℤ → ℤ) (hms : ∀ i j, 0 ≤ diff s i j) :
    ∀ (n : ℕ) (r : ℤ → ℤ → ℤ), Supported N (fun i j ↦ r i j - s i j) →
      (∀ i j, 0 ≤ r i j - s i j) → (∀ i j, j ≤ i → r i j - s i j = 0) →
      (deficiency N r s).toNat ≤ n → BoxMoveChain r s := by
  intro n
  induction n with
  | zero =>
    intro r hsupp hpos hbelow hΦ
    -- `Φ ≤ 0` and `Φ ≥ 0` ⟹ `Φ = 0` ⟹ `r = s`
    have hle : ∀ i j, i ≤ j → s i j ≤ r i j := fun i j _ ↦ by have := hpos i j; omega
    have hnn := deficiency_nonneg N r s hle
    have hΦ0 : deficiency N r s = 0 := by omega
    rw [funext_of_deficiency_eq_zero N r s hsupp hle hbelow hΦ0]
    exact Relation.ReflTransGen.refl
  | succ n ih =>
    intro r hsupp hpos hbelow hΦ
    have hle : ∀ i j, i ≤ j → s i j ≤ r i j := fun i j _ ↦ by have := hpos i j; omega
    have hnn := deficiency_nonneg N r s hle
    rcases eq_or_lt_of_le hnn with hΦ0 | hΦpos
    · -- `Φ = 0`: done by refl
      rw [funext_of_deficiency_eq_zero N r s hsupp hle hbelow hΦ0.symm]
      exact Relation.ReflTransGen.refl
    · -- `Φ > 0`: a positive triangle cell exists; run the descent
      have hexists : ∃ p ∈ triBox N, 0 < r p.1 p.2 - s p.1 p.2 := by
        by_contra hcon
        push Not at hcon
        have : deficiency N r s = 0 := by
          apply Finset.sum_eq_zero
          rintro ⟨i, j⟩ hp
          have h1 := hcon (i, j) hp
          have h2 := hpos i j
          simp only at h1 ⊢
          omega
        omega
      obtain ⟨⟨I, J⟩, hpmem, hcellpos⟩ := hexists
      obtain ⟨hI, hJ, hIJ⟩ := mem_triBox.mp hpmem
      -- positive triangle cell ⟹ strict upper (`I < J`) by below-diagonal vanishing
      have hIlt : I < J := by
        rcases eq_or_lt_of_le hIJ with heq | hlt
        · rw [← heq] at hcellpos; rw [hbelow I I (le_refl I)] at hcellpos
          exact absurd hcellpos (lt_irrefl 0)
        · exact hlt
      -- descent step
      obtain ⟨a, c, b, e, hstep, hdom, ha0, hac, hcb, hab, hbe, heN⟩ :=
        exists_boxMoveStep_descent N r s hsupp hpos hbelow hms hIlt hJ.2 hcellpos
      set r' : ℤ → ℤ → ℤ := boxDrop r a c b e with hr'
      -- invariants for `r'`
      have hbelow' : ∀ i j, j ≤ i → r' i j - s i j = 0 := by
        intro i j hji
        have hind : boxIndicator a c b e i j = 0 := by
          rw [boxIndicator, if_neg (by rintro ⟨_, h2, h3, _⟩; omega)]
        have := hbelow i j hji
        rw [hr', boxDrop, hind]; omega
      have hpos' : ∀ i j, 0 ≤ r' i j - s i j := by
        intro i j
        rcases le_or_gt j i with hji | hij
        · rw [hbelow' i j hji]
        · exact sub_nonneg.mpr (hdom i j (le_of_lt hij))
      have hsupp' : Supported N (fun i j ↦ r' i j - s i j) := by
        refine ⟨fun i j hi ↦ ?_, fun i j hj ↦ ?_⟩
        · have hind : boxIndicator a c b e i j = 0 := by
            rw [boxIndicator, if_neg (by rintro ⟨h1, _⟩; omega)]
          have := hsupp.1 i j hi
          simp only at this ⊢; rw [hr', boxDrop, hind]; omega
        · have hind : boxIndicator a c b e i j = 0 := by
            rw [boxIndicator, if_neg (by rintro ⟨_, _, _, h4⟩; omega)]
          have := hsupp.2 i j hj
          simp only at this ⊢; rw [hr', boxDrop, hind]; omega
      -- `Φ` strictly drops
      have hdrop : deficiency N r' s < deficiency N r s :=
        deficiency_boxDrop_lt N r s hac hbe ha0 hab (by omega)
      have hΦ' : (deficiency N r' s).toNat ≤ n := by
        have hnn' := deficiency_nonneg N r' s (fun i j _ ↦ by have := hpos' i j; omega)
        omega
      exact Relation.ReflTransGen.head hstep (ih r' hsupp' hpos' hbelow' hΦ')

/-- **L6.2c (box-move generation).** Achievable rank patterns `s ≤ r` over the same dimension
vector (`s` dominated by `r` on the upper triangle, agreeing on/below the diagonal, both supported,
`s` achievable) are connected by a finite chain of applicable box moves: `BoxMoveChain r s`. -/
theorem box_move_chain_of_le (N : ℤ) (r s : ℤ → ℤ → ℤ)
    (hsupp : Supported N (fun i j ↦ r i j - s i j)) (hpos : ∀ i j, 0 ≤ r i j - s i j)
    (hbelow : ∀ i j, j ≤ i → r i j - s i j = 0) (hms : ∀ i j, 0 ≤ diff s i j) :
    BoxMoveChain r s :=
  box_move_chain_aux N s hms (deficiency N r s).toNat r hsupp hpos hbelow (le_refl _)

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

/-! ### A non-trivial generation witness (`box_move_chain_of_le`)

`N = 2`, dimension vector `(1,2,2)`. The achievable pattern `s = cumul 2 msWitness` for the Kostant
partition `msWitness = {[0,1], [1,2], [2,2]}` and the pattern `r = s + 1_{(0,2)}` (achievable, the
partition `{[0,2], [1,1], [2,2]}`) differ only at the single strict-upper cell `(0,2)`. Their
residual `r − s` is the single-cell array (`1` at `(0,2)`, else `0`), which is nonnegative,
supported, and vanishes on/below the diagonal; `s` is achievable (`diff s = msWitness ≥ 0`). So
`box_move_chain_of_le` fires and `BoxMoveChain r s` holds — the chain is **non-trivial** (`r ≠ s`,
the single split box move `[0,2] + [1,1] ↦ [0,1] + [1,2]`). -/

/-- Witness Kostant partition for `(1,2,2)`: `m₀₁ = m₁₂ = m₂₂ = 1`, else `0`. -/
def bmcPartition : ℤ → ℤ → ℤ := fun i j ↦
  if i = 0 ∧ j = 1 then 1 else if i = 1 ∧ j = 2 then 1 else if i = 2 ∧ j = 2 then 1 else 0

/-- The witness partition is supported (vanishes for `i < 0` and for `j > 2`). -/
theorem supported_bmcPartition : Supported 2 bmcPartition := by
  refine ⟨fun i j hi ↦ ?_, fun i j hj ↦ ?_⟩ <;>
    · unfold bmcPartition; split_ifs <;> omega

/-- The witness partition is nonnegative. -/
theorem nonneg_bmcPartition : ∀ i j, 0 ≤ bmcPartition i j := by
  intro i j; unfold bmcPartition; split_ifs <;> norm_num

/-- The single dropped cell `(0,2)` (the residual `r − s`). -/
def bmcCell : ℤ → ℤ → ℤ := fun i j ↦ if i = 0 ∧ j = 2 then 1 else 0

/-- The achievable lower pattern `s = cumul 2 bmcPartition`. -/
noncomputable def bmcLower : ℤ → ℤ → ℤ := cumul 2 bmcPartition

/-- The upper pattern `r = s + 1_{(0,2)}`. -/
noncomputable def bmcUpper : ℤ → ℤ → ℤ := fun i j ↦ bmcLower i j + bmcCell i j

/-- `box_move_chain_of_le` fires: `BoxMoveChain bmcUpper bmcLower` holds, and the patterns differ
(`r 0 2 = s 0 2 + 1`), so the chain is non-trivial. -/
example : BoxMoveChain bmcUpper bmcLower := by
  have hrs : ∀ i j, bmcUpper i j - bmcLower i j = bmcCell i j := fun i j ↦ by
    rw [bmcUpper]; ring
  refine box_move_chain_of_le 2 bmcUpper bmcLower ⟨fun i j hi ↦ ?_, fun i j hj ↦ ?_⟩
    (fun i j ↦ ?_) (fun i j hji ↦ ?_) (fun i j ↦ ?_)
  · simp only; rw [hrs]; unfold bmcCell; split_ifs <;> omega
  · simp only; rw [hrs]; unfold bmcCell; split_ifs <;> omega
  · rw [hrs]; unfold bmcCell; split_ifs <;> norm_num
  · rw [hrs]; unfold bmcCell; split_ifs <;> omega
  · -- `diff bmcLower = bmcPartition ≥ 0`
    rw [bmcLower, diff_cumul 2 bmcPartition supported_bmcPartition.1 supported_bmcPartition.2]
    exact nonneg_bmcPartition i j

/-- The witness chain is non-trivial: `bmcUpper ≠ bmcLower` (they differ at `(0,2)`). -/
example : bmcUpper 0 2 ≠ bmcLower 0 2 := by
  have : bmcUpper 0 2 - bmcLower 0 2 = 1 := by
    rw [bmcUpper]; unfold bmcCell; norm_num
  omega

end Witness

end DLNFibre.Core
