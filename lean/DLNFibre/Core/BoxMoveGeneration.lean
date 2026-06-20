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
