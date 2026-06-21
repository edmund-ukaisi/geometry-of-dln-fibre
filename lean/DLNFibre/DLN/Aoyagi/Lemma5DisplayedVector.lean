import DLNFibre.DLN.Aoyagi.Lemma5IntervalArithmetic
import DLNFibre.DLN.Aoyagi.HtildeChainArithmetic

/-!
# Conditional displayed-vector data for Aoyagi's Lemma 5

This file introduces source-layer cutpoints and supplied piecewise certificates
for Aoyagi Lemma 5 equations `(3)` and `(4)`.  It does not construct the
displayed vector, prove terminal `tilde t=0`, chart coverage, pole order,
normal crossings, or RLCT extraction.
-/

namespace DLNFibre
namespace DLN
namespace Aoyagi

/-- Source-selected cutpoints `S_1,...,S_(ell+1)`, indexed zero-based in Lean. -/
structure AoyagiSelectedCutpoints (ell : ℕ) where
  cut : Fin (ell + 1) → ℕ
  pos : ∀ i, 1 ≤ cut i
  strict : ∀ i : Fin ell, cut i.castSucc < cut i.succ

namespace AoyagiSelectedCutpoints

/-- The supplied adjacent inequalities make the selected cutpoints strictly
monotone on their finite index type. -/
theorem cut_strictMono {ell : ℕ} (C : AoyagiSelectedCutpoints ell) :
    StrictMono C.cut := by
  exact (Fin.strictMono_iff_lt_succ).2 C.strict

/-- Total accessor: `C.point i` is source `S_(i+1)` when `i<=ell`, and `0`
outside the selected range. -/
def point {ell : ℕ} (C : AoyagiSelectedCutpoints ell) (i : ℕ) : ℕ :=
  if h : i < ell + 1 then C.cut ⟨i, h⟩ else 0

@[simp] theorem point_of_lt {ell : ℕ} (C : AoyagiSelectedCutpoints ell)
    {i : ℕ} (hi : i < ell + 1) :
    C.point i = C.cut ⟨i, hi⟩ := by
  simp [point, hi]

theorem point_pos_of_lt {ell : ℕ} (C : AoyagiSelectedCutpoints ell)
    {i : ℕ} (hi : i < ell + 1) :
    1 ≤ C.point i := by
  rw [C.point_of_lt hi]
  exact C.pos ⟨i, hi⟩

theorem point_strict_succ {ell : ℕ} (C : AoyagiSelectedCutpoints ell)
    {i : ℕ} (hi : i < ell) :
    C.point i < C.point (i + 1) := by
  rw [C.point_of_lt (by omega), C.point_of_lt (by omega)]
  simpa using C.strict ⟨i, hi⟩

theorem point_strict_of_lt {ell : ℕ} (C : AoyagiSelectedCutpoints ell)
    {i j : ℕ} (hij : i < j) (hj : j < ell + 1) :
    C.point i < C.point j := by
  have hi : i < ell + 1 := by omega
  rw [C.point_of_lt hi, C.point_of_lt hj]
  exact C.cut_strictMono (by simpa using hij)

theorem point_le_of_le {ell : ℕ} (C : AoyagiSelectedCutpoints ell)
    {i j : ℕ} (hij : i ≤ j) (hj : j < ell + 1) :
    C.point i ≤ C.point j := by
  rcases lt_or_eq_of_le hij with hlt | rfl
  · exact le_of_lt (C.point_strict_of_lt hlt hj)
  · exact le_rfl

/-- Zero-based selected block:
`block C b S` means `S_(b+1)-1 <= S < S_(b+2)-1`. -/
def block {ell : ℕ} (C : AoyagiSelectedCutpoints ell) (b S : ℕ) : Prop :=
  b < ell ∧ C.point b - 1 ≤ S ∧ S < C.point (b + 1) - 1

/-- The left endpoint of a selected block belongs to that block. -/
theorem leftEndpoint_mem_block {ell : ℕ} (C : AoyagiSelectedCutpoints ell)
    {b : ℕ} (hb : b < ell) :
    C.block b (C.point b - 1) := by
  have hpos : 1 ≤ C.point b := C.point_pos_of_lt (by omega)
  have hstrict : C.point b < C.point (b + 1) := C.point_strict_succ hb
  unfold block
  constructor
  · exact hb
  constructor
  · rfl
  · omega

/-- Selected blocks are pairwise disjoint. -/
theorem block_index_unique {ell : ℕ} (C : AoyagiSelectedCutpoints ell)
    {b c S : ℕ} (hb : C.block b S) (hc : C.block c S) :
    b = c := by
  rcases hb with ⟨hb_lt, hb_lo, hb_hi⟩
  rcases hc with ⟨hc_lt, hc_lo, hc_hi⟩
  by_contra hne
  rcases lt_or_gt_of_ne hne with hbc | hcb
  · have hle : C.point (b + 1) ≤ C.point c := by
      exact C.point_le_of_le (by omega) (by omega)
    have hsub_le : C.point (b + 1) - 1 ≤ C.point c - 1 := by
      omega
    omega
  · have hle : C.point (c + 1) ≤ C.point b := by
      exact C.point_le_of_le (by omega) (by omega)
    have hsub_le : C.point (c + 1) - 1 ≤ C.point b - 1 := by
      omega
    omega

/-- A selected block's left endpoint belongs only to that block. -/
theorem block_leftEndpoint_iff {ell : ℕ} (C : AoyagiSelectedCutpoints ell)
    {b c : ℕ} (hb : b < ell) :
    C.block c (C.point b - 1) ↔ c = b := by
  constructor
  · intro h
    exact (C.block_index_unique (C.leftEndpoint_mem_block hb) h).symm
  · intro h
    subst h
    exact C.leftEndpoint_mem_block hb

/-- A non-left-endpoint member of a selected block is strictly after the block's
left endpoint. -/
theorem block_leftEndpoint_lt_of_ne {ell : ℕ} (C : AoyagiSelectedCutpoints ell)
    {b S : ℕ} (hb : C.block b S) (hne : S ≠ C.point b - 1) :
    C.point b - 1 < S := by
  rcases hb with ⟨_, hb_lo, _⟩
  omega

/-- Every member of a later selected block is strictly after an earlier block's
left endpoint. -/
theorem leftEndpoint_lt_of_lt_block {ell : ℕ} (C : AoyagiSelectedCutpoints ell)
    {q b S : ℕ} (hqb : q < b) (hb : C.block b S) :
    C.point q - 1 < S := by
  rcases hb with ⟨hb_lt, hb_lo, _⟩
  have hstrict : C.point q < C.point b :=
    C.point_strict_of_lt hqb (by omega)
  have hpos : 1 ≤ C.point q := C.point_pos_of_lt (by omega)
  omega

/-- Every selected block lies in the selected span from `S_1-1` to
`S_(ell+1)-1`. -/
theorem block_mem_selectedSpan {ell : ℕ} (C : AoyagiSelectedCutpoints ell)
    {b S : ℕ} (h : C.block b S) :
    C.point 0 - 1 ≤ S ∧ S < C.point ell - 1 := by
  rcases h with ⟨hb_lt, hb_lo, hb_hi⟩
  have hleft : C.point 0 ≤ C.point b := by
    exact C.point_le_of_le (by omega) (by omega)
  have hright : C.point (b + 1) ≤ C.point ell := by
    exact C.point_le_of_le (by omega) (by omega)
  constructor <;> omega

/-- Every source index in the selected span lies in some selected block. -/
theorem exists_block_of_mem_selectedSpan {ell : ℕ} (C : AoyagiSelectedCutpoints ell)
    {S : ℕ} (hlo : C.point 0 - 1 ≤ S) (hhi : S < C.point ell - 1) :
    ∃ b, C.block b S := by
  let P : ℕ → Prop := fun j ↦ j ≤ ell ∧ S < C.point j - 1
  have hP : ∃ j, P j := ⟨ell, le_rfl, hhi⟩
  let j := Nat.find hP
  have hj : P j := Nat.find_spec hP
  rcases hj with ⟨hj_le, hj_hi⟩
  have hj_pos : 0 < j := by
    by_contra hnot
    have hj0 : j = 0 := by omega
    rw [hj0] at hj_hi
    omega
  have hpred_not : ¬ P (j - 1) := Nat.find_min hP (by omega)
  have hb_lo : C.point (j - 1) - 1 ≤ S := by
    by_contra hnot
    have hlt : S < C.point (j - 1) - 1 := by omega
    exact hpred_not ⟨by omega, hlt⟩
  have hb_lt : j - 1 < ell := by omega
  have hsucc : (j - 1) + 1 = j := by omega
  refine ⟨j - 1, hb_lt, hb_lo, ?_⟩
  simpa [hsucc] using hj_hi

/-- Selected blocks cover exactly the selected span
`S_1-1 <= S < S_(ell+1)-1`. -/
theorem exists_block_iff_mem_selectedSpan {ell : ℕ}
    (C : AoyagiSelectedCutpoints ell) {S : ℕ} :
    (∃ b, C.block b S) ↔ C.point 0 - 1 ≤ S ∧ S < C.point ell - 1 := by
  constructor
  · rintro ⟨b, hb⟩
    exact C.block_mem_selectedSpan hb
  · intro h
    exact C.exists_block_of_mem_selectedSpan h.1 h.2

/-- The terminal selected endpoint `S_(ell+1)-1` is not in any half-open
selected block. -/
theorem not_block_terminalEndpoint {ell : ℕ} (C : AoyagiSelectedCutpoints ell)
    {b : ℕ} :
    ¬ C.block b (C.point ell - 1) := by
  intro hb
  exact (lt_irrefl (C.point ell - 1)) (C.block_mem_selectedSpan hb).2

end AoyagiSelectedCutpoints

/-- Supplied source-layer piecewise data for Aoyagi Lemma 5 equation `(4)`.

This is a certificate that a function `T` has the displayed branch values on
the selected blocks.  It is not a construction of such a function and carries
no terminal or chart-coverage claim. -/
structure AoyagiLemma5Eq4PiecewiseSourceVector
    (ell a p : ℕ) (M : ℤ) (m : Fin (ell + 1) → ℤ)
    (C : AoyagiSelectedCutpoints ell) (layerWidth T : ℕ → ℤ) : Prop where
  a_le_ell : a ≤ ell
  indexGuard : p + 1 ≤ a
  first :
    ∀ S, S < C.point 1 - 1 → T S = layerWidth (S + 1)
  prefixBranch :
    ∀ b S, 1 ≤ b → b ≤ p → C.block b S →
      T S = aoyagiHtildeUpperNat ell a M m b - (b : ℤ)
  middle :
    ∀ b S, p < b → b ≤ p + (ell - a) → C.block b S →
      T S = aoyagiHtildeUpperNat ell a M m b - (p : ℤ)
  boundary :
    T (C.point (p + (ell - a) + 1) - 1) =
      aoyagiHtildeUpperNat ell a M m (p + (ell - a)) - (p : ℤ) + 1
  tail :
    ∀ b S, p + (ell - a) + 1 ≤ b → C.block b S →
      C.point (p + (ell - a) + 1) - 1 < S →
        T S = aoyagiHtildeUpperNat ell a M m b

/-- The repaired equation `(4)` selected-index guard makes the displayed
boundary `S_(p+ell-a+2)-1` a selected cutpoint index. -/
theorem aoyagiLemma5Eq4_boundaryIndex_le_ell_of_piecewiseSourceVector
    (ell a p : ℕ) (M : ℤ) (m : Fin (ell + 1) → ℤ)
    (C : AoyagiSelectedCutpoints ell) (layerWidth T : ℕ → ℤ)
    (hT : AoyagiLemma5Eq4PiecewiseSourceVector ell a p M m C layerWidth T) :
    p + (ell - a) + 1 ≤ ell := by
  have ha : a ≤ ell := hT.a_le_ell
  have hp : p + 1 ≤ a := hT.indexGuard
  omega

/-- In the strict equation `(4)` boundary case, the displayed boundary point is
the left endpoint of the next selected block. -/
theorem aoyagiLemma5Eq4_boundaryEndpoint_mem_block_of_strictGuard
    (ell a p : ℕ) (M : ℤ) (m : Fin (ell + 1) → ℤ)
    (C : AoyagiSelectedCutpoints ell) (layerWidth T : ℕ → ℤ)
    (hT : AoyagiLemma5Eq4PiecewiseSourceVector ell a p M m C layerWidth T)
    (hp_strict : p + 1 < a) :
    C.block (p + (ell - a) + 1) (C.point (p + (ell - a) + 1) - 1) := by
  have hlt :
      p + (ell - a) + 1 < ell :=
    (aoyagiLemma5Eq4_boundaryIndex_lt_ell_iff ell a p hT.a_le_ell).2 hp_strict
  exact C.leftEndpoint_mem_block hlt

/-- In the strict equation `(4)` boundary case, the displayed boundary point
lies in the half-open selected span. -/
theorem aoyagiLemma5Eq4_boundaryEndpoint_mem_selectedSpan_of_strictGuard
    (ell a p : ℕ) (M : ℤ) (m : Fin (ell + 1) → ℤ)
    (C : AoyagiSelectedCutpoints ell) (layerWidth T : ℕ → ℤ)
    (hT : AoyagiLemma5Eq4PiecewiseSourceVector ell a p M m C layerWidth T)
    (hp_strict : p + 1 < a) :
    C.point 0 - 1 ≤ C.point (p + (ell - a) + 1) - 1 ∧
      C.point (p + (ell - a) + 1) - 1 < C.point ell - 1 := by
  exact C.block_mem_selectedSpan
    (aoyagiLemma5Eq4_boundaryEndpoint_mem_block_of_strictGuard
      ell a p M m C layerWidth T hT hp_strict)

/-- In the terminal equation `(4)` boundary case, the displayed boundary point
is the terminal selected endpoint. -/
theorem aoyagiLemma5Eq4_boundaryEndpoint_eq_terminal_of_predBoundary
    (ell a p : ℕ) (M : ℤ) (m : Fin (ell + 1) → ℤ)
    (C : AoyagiSelectedCutpoints ell) (layerWidth T : ℕ → ℤ)
    (hT : AoyagiLemma5Eq4PiecewiseSourceVector ell a p M m C layerWidth T)
    (hp : p + 1 = a) :
    C.point (p + (ell - a) + 1) - 1 = C.point ell - 1 := by
  have hidx :
      p + (ell - a) + 1 = ell :=
    (aoyagiLemma5Eq4_boundaryIndex_eq_ell_iff ell a p hT.a_le_ell).2 hp
  rw [hidx]

/-- In the terminal equation `(4)` boundary case, the displayed boundary point
is not in any half-open selected block. -/
theorem aoyagiLemma5Eq4_boundaryEndpoint_not_block_of_predBoundary
    (ell a p : ℕ) (M : ℤ) (m : Fin (ell + 1) → ℤ)
    (C : AoyagiSelectedCutpoints ell) (layerWidth T : ℕ → ℤ)
    (hT : AoyagiLemma5Eq4PiecewiseSourceVector ell a p M m C layerWidth T)
    (hp : p + 1 = a) {b : ℕ} :
    ¬ C.block b (C.point (p + (ell - a) + 1) - 1) := by
  rw [aoyagiLemma5Eq4_boundaryEndpoint_eq_terminal_of_predBoundary
    ell a p M m C layerWidth T hT hp]
  exact C.not_block_terminalEndpoint

/-- In the strict equation `(4)` case, the special boundary value belongs to
the same-coordinate interval at index `p + (ell-a)` exactly in the balanced
range `2*p <= a+1`.

This records only finite branch arithmetic for a supplied equation `(4)`
certificate.  It does not construct the displayed source vector, prove
terminality, admissibility, chart coverage, pole order, normal crossings, or
RLCT extraction. -/
theorem aoyagiLemma5Eq4_boundaryValue_mem_intervalValueSetNat_iff_two_mul_le
    (ell a p : ℕ) (M : ℤ) (m : Fin (ell + 1) → ℤ)
    (C : AoyagiSelectedCutpoints ell) (layerWidth T : ℕ → ℤ)
    (hT : AoyagiLemma5Eq4PiecewiseSourceVector ell a p M m C layerWidth T)
    (hp0 : 1 ≤ p) (hp_strict : p + 1 < a) (hp_c : p ≤ ell - a) :
    T (C.point (p + (ell - a) + 1) - 1) ∈
        aoyagiHtildeIntervalValueSetNat ell a M m (p + (ell - a)) ↔
      2 * p ≤ a + 1 := by
  have hj : p + (ell - a) < ell + 1 := by
    have ha : a ≤ ell := hT.a_le_ell
    omega
  have hexcess :
      aoyagiLemma5IntervalExcess ell a (p + (ell - a)) =
        min (ell - a) (a - p) := by
    unfold aoyagiLemma5IntervalExcess
    have hell_sub : ell - (p + (ell - a)) = a - p := by
      have ha : a ≤ ell := hT.a_le_ell
      omega
    rw [hell_sub]
    have hinner_le : min (a - p) (min a (ell - a)) ≤ p + (ell - a) := by
      have hle_c : min (a - p) (min a (ell - a)) ≤ ell - a := by
        exact le_trans (Nat.min_le_right (a - p) (min a (ell - a)))
          (Nat.min_le_right a (ell - a))
      omega
    rw [Nat.min_eq_right hinner_le]
    rw [← Nat.min_assoc]
    have hmin_ap_a : min (a - p) a = a - p := Nat.min_eq_left (Nat.sub_le a p)
    rw [hmin_ap_a]
    rw [Nat.min_comm]
  rw [aoyagiHtildeIntervalValueSetNat]
  simp only [hj, ↓reduceDIte]
  rw [aoyagiHtilde_mem_intervalValueSet_iff_bounds ell a M m hT.a_le_ell
    ⟨p + (ell - a), hj⟩]
  constructor
  · intro hbounds
    have hgap := aoyagiHtildeUpper_sub_lower_eq_intervalExcess ell a M m hT.a_le_ell
      ⟨p + (ell - a), hj⟩
    rw [hT.boundary] at hbounds
    simp [aoyagiHtildeLowerChain, aoyagiHtildeUpperChain] at hbounds hgap
    have hge_int :
        (p : ℤ) - 1 ≤
          (aoyagiLemma5IntervalExcess ell a (p + (ell - a)) : ℤ) := by
      omega
    have hle_nat : aoyagiLemma5IntervalExcess ell a (p + (ell - a)) ≤ a - p := by
      rw [hexcess]
      exact Nat.min_le_right (ell - a) (a - p)
    have hle_int :
        (aoyagiLemma5IntervalExcess ell a (p + (ell - a)) : ℤ) ≤
          (a - p : ℕ) := by
      exact_mod_cast hle_nat
    omega
  · intro hbalanced
    have hgap := aoyagiHtildeUpper_sub_lower_eq_intervalExcess ell a M m hT.a_le_ell
      ⟨p + (ell - a), hj⟩
    rw [hT.boundary]
    simp [aoyagiHtildeLowerChain, aoyagiHtildeUpperChain] at hgap ⊢
    constructor
    · have hge_nat :
          p - 1 ≤ aoyagiLemma5IntervalExcess ell a (p + (ell - a)) := by
        rw [hexcess]
        apply le_min
        · omega
        · omega
      omega
    · omega

/-- Balanced strict equation `(4)` boundary values are counted by the
same-coordinate interval at index `p + (ell-a)`. -/
theorem aoyagiLemma5Eq4_boundaryValue_mem_intervalValueSetNat_of_two_mul_le
    (ell a p : ℕ) (M : ℤ) (m : Fin (ell + 1) → ℤ)
    (C : AoyagiSelectedCutpoints ell) (layerWidth T : ℕ → ℤ)
    (hT : AoyagiLemma5Eq4PiecewiseSourceVector ell a p M m C layerWidth T)
    (hp0 : 1 ≤ p) (hp_strict : p + 1 < a) (hp_c : p ≤ ell - a)
    (hbalanced : 2 * p ≤ a + 1) :
    T (C.point (p + (ell - a) + 1) - 1) ∈
      aoyagiHtildeIntervalValueSetNat ell a M m (p + (ell - a)) := by
  exact (aoyagiLemma5Eq4_boundaryValue_mem_intervalValueSetNat_iff_two_mul_le
    ell a p M m C layerWidth T hT hp0 hp_strict hp_c).2 hbalanced

/-- Unbalanced strict equation `(4)` boundary values are not counted by the
same-coordinate interval at index `p + (ell-a)`. -/
theorem aoyagiLemma5Eq4_boundaryValue_not_mem_intervalValueSetNat_of_lt_two_mul
    (ell a p : ℕ) (M : ℤ) (m : Fin (ell + 1) → ℤ)
    (C : AoyagiSelectedCutpoints ell) (layerWidth T : ℕ → ℤ)
    (hT : AoyagiLemma5Eq4PiecewiseSourceVector ell a p M m C layerWidth T)
    (hp0 : 1 ≤ p) (hp_strict : p + 1 < a) (hp_c : p ≤ ell - a)
    (hunbalanced : a + 1 < 2 * p) :
    T (C.point (p + (ell - a) + 1) - 1) ∉
      aoyagiHtildeIntervalValueSetNat ell a M m (p + (ell - a)) := by
  intro hmem
  have hbalanced :=
    (aoyagiLemma5Eq4_boundaryValue_mem_intervalValueSetNat_iff_two_mul_le
      ell a p M m C layerWidth T hT hp0 hp_strict hp_c).1 hmem
  omega

/-- At the boundary block's own coordinate, equation `(4)`'s strict-boundary
value is shifted from the next upper-chain endpoint by one selected width.

This is only supplied branch arithmetic for a supplied equation `(4)`
certificate.  It does not construct the displayed source vector, prove
terminality, admissibility, chart coverage, pole order, normal crossings, or
RLCT extraction. -/
theorem aoyagiLemma5Eq4_boundaryValue_sub_upperNat_boundaryCoordinate
    (ell a p : ℕ) (M : ℤ) (m : Fin (ell + 1) → ℤ)
    (C : AoyagiSelectedCutpoints ell) (layerWidth T : ℕ → ℤ)
    (hT : AoyagiLemma5Eq4PiecewiseSourceVector ell a p M m C layerWidth T)
    (hp_strict : p + 1 < a) :
    T (C.point (p + (ell - a) + 1) - 1) -
        aoyagiHtildeUpperNat ell a M m (p + (ell - a) + 1) =
      M - aoyagiSelectedWidthNat ell m (p + (ell - a) + 1) - (p : ℤ) + 1 := by
  have ha : a ≤ ell := hT.a_le_ell
  have hsucc :=
    aoyagiHtildeUpperNat_succ_eq_add_selectedWidthNat_sub_increment
      ell a (p + (ell - a)) M m ha (by omega)
  have hnot : ¬ p + (ell - a) < ell - a := by omega
  rw [if_neg hnot] at hsucc
  rw [hT.boundary, hsucc]
  ring

/-- At the boundary block's own coordinate, equation `(4)`'s strict-boundary
value lies in the same-coordinate interval exactly when the next selected width
lies in the corresponding width window. -/
theorem aoyagiLemma5Eq4_boundaryValue_mem_boundaryCoordinateIntervalValueSetNat_iff_widthWindow
    (ell a p : ℕ) (M : ℤ) (m : Fin (ell + 1) → ℤ)
    (C : AoyagiSelectedCutpoints ell) (layerWidth T : ℕ → ℤ)
    (hT : AoyagiLemma5Eq4PiecewiseSourceVector ell a p M m C layerWidth T)
    (hp_strict : p + 1 < a) :
    T (C.point (p + (ell - a) + 1) - 1) ∈
        aoyagiHtildeIntervalValueSetNat ell a M m (p + (ell - a) + 1) ↔
      M - (p : ℤ) + 1 ≤ aoyagiSelectedWidthNat ell m (p + (ell - a) + 1) ∧
        aoyagiSelectedWidthNat ell m (p + (ell - a) + 1) ≤
          M - (p : ℤ) + 1 +
            (aoyagiLemma5IntervalExcess ell a (p + (ell - a) + 1) : ℤ) := by
  have hr : p + (ell - a) + 1 < ell + 1 := by
    have ha : a ≤ ell := hT.a_le_ell
    omega
  rw [aoyagiHtildeIntervalValueSetNat]
  simp only [hr, ↓reduceDIte]
  rw [aoyagiHtilde_mem_intervalValueSet_iff_bounds ell a M m hT.a_le_ell
    ⟨p + (ell - a) + 1, hr⟩]
  constructor
  · intro hbounds
    have hgap := aoyagiHtildeUpper_sub_lower_eq_intervalExcess ell a M m hT.a_le_ell
      ⟨p + (ell - a) + 1, hr⟩
    have hoffset :=
      aoyagiLemma5Eq4_boundaryValue_sub_upperNat_boundaryCoordinate
        ell a p M m C layerWidth T hT hp_strict
    simp [aoyagiHtildeLowerChain, aoyagiHtildeUpperChain] at hbounds hgap
    constructor <;> omega
  · intro hwindow
    have hgap := aoyagiHtildeUpper_sub_lower_eq_intervalExcess ell a M m hT.a_le_ell
      ⟨p + (ell - a) + 1, hr⟩
    have hoffset :=
      aoyagiLemma5Eq4_boundaryValue_sub_upperNat_boundaryCoordinate
        ell a p M m C layerWidth T hT hp_strict
    simp [aoyagiHtildeLowerChain, aoyagiHtildeUpperChain] at hgap ⊢
    constructor <;> omega

/-- Reduced-minimum form of the equation `(4)` own-coordinate width window. -/
theorem aoyagiLemma5Eq4_boundaryValue_mem_boundaryCoordinateIntervalValueSetNat_iff_widthWindow_min
    (ell a p : ℕ) (M : ℤ) (m : Fin (ell + 1) → ℤ)
    (C : AoyagiSelectedCutpoints ell) (layerWidth T : ℕ → ℤ)
    (hT : AoyagiLemma5Eq4PiecewiseSourceVector ell a p M m C layerWidth T)
    (hp_strict : p + 1 < a) :
    T (C.point (p + (ell - a) + 1) - 1) ∈
        aoyagiHtildeIntervalValueSetNat ell a M m (p + (ell - a) + 1) ↔
      M - (p : ℤ) + 1 ≤ aoyagiSelectedWidthNat ell m (p + (ell - a) + 1) ∧
        aoyagiSelectedWidthNat ell m (p + (ell - a) + 1) ≤
          M - (p : ℤ) + 1 + ((min (ell - a) (a - p - 1) : ℕ) : ℤ) := by
  rw [aoyagiLemma5Eq4_boundaryValue_mem_boundaryCoordinateIntervalValueSetNat_iff_widthWindow
    ell a p M m C layerWidth T hT hp_strict]
  rw [aoyagiLemma5Eq4_boundaryCoordinate_intervalExcess_eq_min
    ell a p hT.a_le_ell hp_strict]

/-- Under Definition 3's selected-width hypotheses, membership in equation
`(4)`'s boundary-coordinate interval forces `2 <= p`.

This is a necessary condition only.  It does not prove membership for
`2 <= p`, construct the displayed source vector, prove terminality,
admissibility, chart coverage, pole order, normal crossings, or RLCT
extraction. -/
theorem aoyagiLemma5Eq4_boundaryValue_mem_boundaryInterval_forces_two_le_p_of_sourceSelected
    (ell a p : ℕ) (M : ℤ) (m : Fin (ell + 1) → ℤ)
    (C : AoyagiSelectedCutpoints ell) (layerWidth T : ℕ → ℤ)
    (hT : AoyagiLemma5Eq4PiecewiseSourceVector ell a p M m C layerWidth T)
    (hp_strict : p + 1 < a)
    (hselected : (∑ j : Fin (ell + 1), m j) = (ell : ℤ) * (M - 1) + a)
    (hsource : ∀ i : Fin (ell + 1),
      (ell : ℤ) * m i < ∑ j : Fin (ell + 1), m j)
    (hmem :
      T (C.point (p + (ell - a) + 1) - 1) ∈
        aoyagiHtildeIntervalValueSetNat ell a M m (p + (ell - a) + 1)) :
    2 ≤ p := by
  have hwindow :=
    (aoyagiLemma5Eq4_boundaryValue_mem_boundaryCoordinateIntervalValueSetNat_iff_widthWindow
      ell a p M m C layerWidth T hT hp_strict).1 hmem
  have hwidth_ge :
      M - (p : ℤ) + 1 ≤
        aoyagiSelectedWidthNat ell m (p + (ell - a) + 1) := hwindow.1
  have hell : 1 ≤ ell := by
    have ha : a ≤ ell := hT.a_le_ell
    omega
  have hr : p + (ell - a) + 1 < ell + 1 := by
    have ha : a ≤ ell := hT.a_le_ell
    omega
  have hwidth_le :
      aoyagiSelectedWidthNat ell m (p + (ell - a) + 1) ≤ M - 1 := by
    rw [aoyagiSelectedWidthNat_of_lt hr]
    exact aoyagiSelectedWidth_le_pred_of_sourceSelectedInequality
      ell a M m hell hT.a_le_ell hselected hsource
      ⟨p + (ell - a) + 1, hr⟩
  omega

/-- Under Definition 3's selected-width hypotheses, the strict equation `(4)`
boundary value is not in its boundary-coordinate interval when `p < 2`. -/
theorem aoyagiLemma5Eq4_boundaryValue_not_mem_boundaryInterval_of_sourceSelected_of_p_lt_two
    (ell a p : ℕ) (M : ℤ) (m : Fin (ell + 1) → ℤ)
    (C : AoyagiSelectedCutpoints ell) (layerWidth T : ℕ → ℤ)
    (hT : AoyagiLemma5Eq4PiecewiseSourceVector ell a p M m C layerWidth T)
    (hp_strict : p + 1 < a) (hp_lt_two : p < 2)
    (hselected : (∑ j : Fin (ell + 1), m j) = (ell : ℤ) * (M - 1) + a)
    (hsource : ∀ i : Fin (ell + 1),
      (ell : ℤ) * m i < ∑ j : Fin (ell + 1), m j) :
    T (C.point (p + (ell - a) + 1) - 1) ∉
      aoyagiHtildeIntervalValueSetNat ell a M m (p + (ell - a) + 1) := by
  intro hmem
  have hp_ge_two :=
    aoyagiLemma5Eq4_boundaryValue_mem_boundaryInterval_forces_two_le_p_of_sourceSelected
      ell a p M m C layerWidth T hT hp_strict hselected hsource hmem
  omega

/-- A concrete `p=2` constant-width guardrail: for this Definition 3-shaped
selected-width tuple, a supplied equation `(4)` certificate puts the strict
boundary value in the boundary-coordinate interval.

This does not construct the supplied certificate or displayed source vector.
It only records that the necessary condition `2 <= p` is not a hidden
nonmembership theorem for all `p >= 2`. -/
theorem aoyagiLemma5Eq4_boundaryValue_mem_boundaryInterval_p2_constantWidth_example
    (C : AoyagiSelectedCutpoints 5) (layerWidth T : ℕ → ℤ)
    (hT : AoyagiLemma5Eq4PiecewiseSourceVector 5 4 2 (5 : ℤ)
      (fun _ : Fin (5 + 1) => (4 : ℤ)) C layerWidth T) :
    T (C.point (2 + (5 - 4) + 1) - 1) ∈
      aoyagiHtildeIntervalValueSetNat 5 4 (5 : ℤ)
        (fun _ : Fin (5 + 1) => (4 : ℤ)) (2 + (5 - 4) + 1) := by
  exact (aoyagiLemma5Eq4_boundaryValue_mem_boundaryCoordinateIntervalValueSetNat_iff_widthWindow_min
    5 4 2 (5 : ℤ) (fun _ : Fin (5 + 1) => (4 : ℤ)) C layerWidth T hT
      (by norm_num)).2 (by
    constructor
    · norm_num [aoyagiSelectedWidthNat]
    · norm_num [aoyagiSelectedWidthNat])

/-- The `p=2` constant-width guardrail also satisfies the selected-width
arithmetic hypotheses from Aoyagi Definition 3.

The final membership conclusion remains conditional on a supplied equation
`(4)` certificate; this theorem does not construct that certificate or the
displayed source vector. -/
theorem aoyagiLemma5Eq4_boundaryValue_mem_boundaryInterval_p2_constantWidth_sourceSelected_example :
    let ell : ℕ := 5
    let a : ℕ := 4
    let p : ℕ := 2
    let M : ℤ := 5
    let m : Fin (ell + 1) → ℤ := fun _ => 4
    1 ≤ ell ∧ a ≤ ell ∧ 1 ≤ p ∧ p + 1 < a ∧
      (∀ i : Fin (ell + 1), 1 ≤ m i) ∧
      (∑ j : Fin (ell + 1), m j) = (ell : ℤ) * (M - 1) + a ∧
      (∀ i : Fin (ell + 1), (ell : ℤ) * m i < ∑ j : Fin (ell + 1), m j) ∧
      ∀ (C : AoyagiSelectedCutpoints ell) (layerWidth T : ℕ → ℤ),
        AoyagiLemma5Eq4PiecewiseSourceVector ell a p M m C layerWidth T →
          T (C.point (p + (ell - a) + 1) - 1) ∈
            aoyagiHtildeIntervalValueSetNat ell a M m (p + (ell - a) + 1) := by
  dsimp
  constructor
  · norm_num
  constructor
  · norm_num
  constructor
  · norm_num
  constructor
  · norm_num
  constructor
  · intro i
    fin_cases i <;> norm_num
  constructor
  · norm_num
  constructor
  · intro i
    fin_cases i <;> norm_num
  · intro C layerWidth T hT
    exact aoyagiLemma5Eq4_boundaryValue_mem_boundaryInterval_p2_constantWidth_example
      C layerWidth T hT

/-- In the `p=1` strict equation `(4)` case, Definition 3's selected-width
upper bound puts the boundary value strictly above the boundary-coordinate
upper endpoint. -/
theorem aoyagiLemma5Eq4_boundaryValue_gt_boundaryUpper_of_p1_sourceSelected
    (ell a : ℕ) (M : ℤ) (m : Fin (ell + 1) → ℤ)
    (C : AoyagiSelectedCutpoints ell) (layerWidth T : ℕ → ℤ)
    (hT : AoyagiLemma5Eq4PiecewiseSourceVector ell a 1 M m C layerWidth T)
    (hp_strict : 1 + 1 < a)
    (hselected : (∑ j : Fin (ell + 1), m j) = (ell : ℤ) * (M - 1) + a)
    (hsource : ∀ i : Fin (ell + 1),
      (ell : ℤ) * m i < ∑ j : Fin (ell + 1), m j) :
    aoyagiHtildeUpperNat ell a M m (1 + (ell - a) + 1) <
      T (C.point (1 + (ell - a) + 1) - 1) := by
  have hwidth_le :
      aoyagiSelectedWidthNat ell m (1 + (ell - a) + 1) ≤ M - 1 := by
    have hell : 1 ≤ ell := by
      have ha : a ≤ ell := hT.a_le_ell
      omega
    have hr : 1 + (ell - a) + 1 < ell + 1 := by
      have ha : a ≤ ell := hT.a_le_ell
      omega
    rw [aoyagiSelectedWidthNat_of_lt hr]
    exact aoyagiSelectedWidth_le_pred_of_sourceSelectedInequality
      ell a M m hell hT.a_le_ell hselected hsource ⟨1 + (ell - a) + 1, hr⟩
  have hoffset :=
    aoyagiLemma5Eq4_boundaryValue_sub_upperNat_boundaryCoordinate
      ell a 1 M m C layerWidth T hT hp_strict
  omega

/-- Consequently, in the `p=1` strict equation `(4)` case, Definition 3's
selected-width hypotheses force nonmembership in the boundary-coordinate
same-coordinate interval. -/
theorem aoyagiLemma5Eq4_boundaryValue_not_mem_boundaryInterval_of_p1_sourceSelected
    (ell a : ℕ) (M : ℤ) (m : Fin (ell + 1) → ℤ)
    (C : AoyagiSelectedCutpoints ell) (layerWidth T : ℕ → ℤ)
    (hT : AoyagiLemma5Eq4PiecewiseSourceVector ell a 1 M m C layerWidth T)
    (hp_strict : 1 + 1 < a)
    (hselected : (∑ j : Fin (ell + 1), m j) = (ell : ℤ) * (M - 1) + a)
    (hsource : ∀ i : Fin (ell + 1),
      (ell : ℤ) * m i < ∑ j : Fin (ell + 1), m j) :
    T (C.point (1 + (ell - a) + 1) - 1) ∉
      aoyagiHtildeIntervalValueSetNat ell a M m (1 + (ell - a) + 1) := by
  intro hmem
  have hr : 1 + (ell - a) + 1 < ell + 1 := by
    have ha : a ≤ ell := hT.a_le_ell
    omega
  rw [aoyagiHtildeIntervalValueSetNat] at hmem
  simp only [hr, ↓reduceDIte] at hmem
  have hbounds :=
    (aoyagiHtilde_mem_intervalValueSet_iff_bounds ell a M m hT.a_le_ell
      ⟨1 + (ell - a) + 1, hr⟩
      (T (C.point (1 + (ell - a) + 1) - 1))).1 hmem
  have hgt :=
    aoyagiLemma5Eq4_boundaryValue_gt_boundaryUpper_of_p1_sourceSelected
      ell a M m C layerWidth T hT hp_strict hselected hsource
  simp [aoyagiHtildeUpperChain] at hbounds
  omega

/-- Branch-value alternatives for Aoyagi Lemma 5 equation `(4)` on the selected
span.

This is only a domain/value classification for a supplied piecewise
certificate.  It does not construct the displayed source vector and makes no
terminality, admissibility, chart-coverage, pole-order, normal-crossing, or
RLCT claim. -/
inductive AoyagiLemma5Eq4SelectedSpanBranchValue
    (ell a p : ℕ) (M : ℤ) (m : Fin (ell + 1) → ℤ)
    (C : AoyagiSelectedCutpoints ell) (layerWidth T : ℕ → ℤ) (S : ℕ) : Prop where
  | first
      (hS : S < C.point 1 - 1)
      (hvalue : T S = layerWidth (S + 1))
  | prefix
      (b : ℕ) (hb_pos : 1 ≤ b) (hb_le : b ≤ p) (hb : C.block b S)
      (hvalue : T S = aoyagiHtildeUpperNat ell a M m b - (b : ℤ))
  | middle
      (b : ℕ) (hp_lt : p < b) (hb_le : b ≤ p + (ell - a)) (hb : C.block b S)
      (hvalue : T S = aoyagiHtildeUpperNat ell a M m b - (p : ℤ))
  | boundary
      (hS : S = C.point (p + (ell - a) + 1) - 1)
      (hvalue :
        T S =
          aoyagiHtildeUpperNat ell a M m (p + (ell - a)) - (p : ℤ) + 1)
  | tail
      (b : ℕ) (hb_tail : p + (ell - a) + 1 ≤ b) (hb : C.block b S)
      (hS : C.point (p + (ell - a) + 1) - 1 < S)
      (hvalue : T S = aoyagiHtildeUpperNat ell a M m b)

/-- A supplied equation `(4)` piecewise certificate classifies any selected
block point by one of its advertised branches.

This is half-open block bookkeeping plus the supplied branch equalities. -/
theorem aoyagiLemma5Eq4_branchValue_of_block
    (ell a p : ℕ) (M : ℤ) (m : Fin (ell + 1) → ℤ)
    (C : AoyagiSelectedCutpoints ell) (layerWidth T : ℕ → ℤ)
    (hT : AoyagiLemma5Eq4PiecewiseSourceVector ell a p M m C layerWidth T)
    {b S : ℕ} (hb : C.block b S) :
    AoyagiLemma5Eq4SelectedSpanBranchValue ell a p M m C layerWidth T S := by
  by_cases hb0 : b = 0
  · subst b
    exact AoyagiLemma5Eq4SelectedSpanBranchValue.first
      hb.2.2 (hT.first S hb.2.2)
  have hb_pos : 1 ≤ b := by omega
  by_cases hb_le_p : b ≤ p
  · exact AoyagiLemma5Eq4SelectedSpanBranchValue.prefix b hb_pos hb_le_p hb
      (hT.prefixBranch b S hb_pos hb_le_p hb)
  have hp_lt_b : p < b := by omega
  by_cases hb_le_middle : b ≤ p + (ell - a)
  · exact AoyagiLemma5Eq4SelectedSpanBranchValue.middle b hp_lt_b hb_le_middle hb
      (hT.middle b S hp_lt_b hb_le_middle hb)
  have hb_tail : p + (ell - a) + 1 ≤ b := by omega
  by_cases hboundary : S = C.point (p + (ell - a) + 1) - 1
  · exact AoyagiLemma5Eq4SelectedSpanBranchValue.boundary hboundary
      (by simpa [hboundary] using hT.boundary)
  have hafter : C.point (p + (ell - a) + 1) - 1 < S := by
    by_cases hb_eq : b = p + (ell - a) + 1
    · subst b
      exact C.block_leftEndpoint_lt_of_ne hb hboundary
    · have hlt : p + (ell - a) + 1 < b := by omega
      exact C.leftEndpoint_lt_of_lt_block hlt hb
  exact AoyagiLemma5Eq4SelectedSpanBranchValue.tail b hb_tail hb hafter
    (hT.tail b S hb_tail hb hafter)

/-- A supplied equation `(4)` piecewise certificate covers every source index in
the selected span by one of its advertised branches.

This is only a selected-span consequence of the block classifier.  It does not
claim coverage before `S_1-1`, at `S_(ell+1)-1`, or after it. -/
theorem aoyagiLemma5Eq4_selectedSpan_branchValue
    (ell a p : ℕ) (M : ℤ) (m : Fin (ell + 1) → ℤ)
    (C : AoyagiSelectedCutpoints ell) (layerWidth T : ℕ → ℤ)
    (hT : AoyagiLemma5Eq4PiecewiseSourceVector ell a p M m C layerWidth T)
    {S : ℕ} (hlo : C.point 0 - 1 ≤ S) (hhi : S < C.point ell - 1) :
    AoyagiLemma5Eq4SelectedSpanBranchValue ell a p M m C layerWidth T S := by
  rcases C.exists_block_of_mem_selectedSpan hlo hhi with ⟨b, hb⟩
  exact aoyagiLemma5Eq4_branchValue_of_block ell a p M m C layerWidth T hT hb

/-- Prefix-branch value at a selected block's left endpoint. -/
theorem aoyagiLemma5Eq4_prefix_leftEndpoint
    (ell a p : ℕ) (M : ℤ) (m : Fin (ell + 1) → ℤ)
    (C : AoyagiSelectedCutpoints ell) (layerWidth T : ℕ → ℤ)
    (hT : AoyagiLemma5Eq4PiecewiseSourceVector ell a p M m C layerWidth T)
    {b : ℕ} (hb_pos : 1 ≤ b) (hb_le : b ≤ p) (hb_lt : b < ell) :
    T (C.point b - 1) = aoyagiHtildeUpperNat ell a M m b - (b : ℤ) := by
  exact hT.prefixBranch b (C.point b - 1) hb_pos hb_le
    (C.leftEndpoint_mem_block hb_lt)

/-- Middle-branch value at a selected block's left endpoint. -/
theorem aoyagiLemma5Eq4_middle_leftEndpoint
    (ell a p : ℕ) (M : ℤ) (m : Fin (ell + 1) → ℤ)
    (C : AoyagiSelectedCutpoints ell) (layerWidth T : ℕ → ℤ)
    (hT : AoyagiLemma5Eq4PiecewiseSourceVector ell a p M m C layerWidth T)
    {b : ℕ} (hp_lt : p < b) (hb_le : b ≤ p + (ell - a)) (hb_lt : b < ell) :
    T (C.point b - 1) = aoyagiHtildeUpperNat ell a M m b - (p : ℤ) := by
  exact hT.middle b (C.point b - 1) hp_lt hb_le
    (C.leftEndpoint_mem_block hb_lt)

/-- Tail-branch value at a selected block's left endpoint strictly after the
special boundary block. -/
theorem aoyagiLemma5Eq4_tail_leftEndpoint_of_cutoff_lt
    (ell a p : ℕ) (M : ℤ) (m : Fin (ell + 1) → ℤ)
    (C : AoyagiSelectedCutpoints ell) (layerWidth T : ℕ → ℤ)
    (hT : AoyagiLemma5Eq4PiecewiseSourceVector ell a p M m C layerWidth T)
    {b : ℕ} (hcut_lt : p + (ell - a) + 1 < b) (hb_lt : b < ell) :
    T (C.point b - 1) = aoyagiHtildeUpperNat ell a M m b := by
  have hb : C.block b (C.point b - 1) := C.leftEndpoint_mem_block hb_lt
  have hafter :
      C.point (p + (ell - a) + 1) - 1 < C.point b - 1 :=
    C.leftEndpoint_lt_of_lt_block hcut_lt hb
  exact hT.tail b (C.point b - 1) (by omega) hb hafter

/-- If a supplied equation `(4)` endpoint extension gives the terminal selected
endpoint the upper-chain terminal value, then that endpoint value is zero.

This is only a conditional endpoint fact.  It does not prove that the displayed
source vector is constructed, admissible, terminal as a whole, or usable in the
Case 1(2) chart sequence. -/
theorem aoyagiLemma5Eq4_terminalEndpoint_zero_of_upperNatExtension
    (ell a : ℕ) (M : ℤ) (m : Fin (ell + 1) → ℤ)
    (C : AoyagiSelectedCutpoints ell) (T : ℕ → ℤ)
    (ha : a ≤ ell)
    (hselected : (∑ j : Fin (ell + 1), m j) = (ell : ℤ) * (M - 1) + a)
    (hterminal :
      T (C.point ell - 1) = aoyagiHtildeUpperNat ell a M m ell) :
    T (C.point ell - 1) = 0 := by
  rw [hterminal]
  exact aoyagiHtildeUpperNat_last_eq_zero_of_selectedSum ell a M m ha hselected

/-- If equation `(4)`'s special boundary is the terminal selected endpoint,
then its supplied branch value is `M-W_(ell+1)-p+1`.

This is a finite obstruction record.  It does not say that equation `(4)`
constructs a terminal vector or that the value is zero. -/
theorem aoyagiLemma5Eq4_terminalEndpoint_value_of_predBoundary
    (ell a p : ℕ) (M : ℤ) (m : Fin (ell + 1) → ℤ)
    (C : AoyagiSelectedCutpoints ell) (layerWidth T : ℕ → ℤ)
    (hp : p + 1 = a)
    (hselected : (∑ j : Fin (ell + 1), m j) = (ell : ℤ) * (M - 1) + a)
    (hT : AoyagiLemma5Eq4PiecewiseSourceVector ell a p M m C layerWidth T) :
    T (C.point ell - 1) =
      M - aoyagiSelectedWidthNat ell m ell - (p : ℤ) + 1 := by
  have ha_pos : 1 ≤ a := by omega
  have ha : a ≤ ell := hT.a_le_ell
  have hboundary_index : p + (ell - a) + 1 = ell := by omega
  have hupper_index : p + (ell - a) = ell - 1 := by omega
  have hboundary := hT.boundary
  rw [hboundary_index, hupper_index] at hboundary
  have hpred :=
    aoyagiHtildeUpperNat_pred_eq_sub_lastWidth_of_selectedSum
      ell a M m ha_pos hT.a_le_ell hselected
  rw [hpred] at hboundary
  simpa using hboundary

/-- Exact compatibility condition for terminal zero in equation `(4)`'s
terminal-boundary case.

This does not prove terminality; it states what the supplied boundary value
would have to satisfy to be zero. -/
theorem aoyagiLemma5Eq4_terminalEndpoint_zero_iff_lastWidth_of_predBoundary
    (ell a p : ℕ) (M : ℤ) (m : Fin (ell + 1) → ℤ)
    (C : AoyagiSelectedCutpoints ell) (layerWidth T : ℕ → ℤ)
    (hp : p + 1 = a)
    (hselected : (∑ j : Fin (ell + 1), m j) = (ell : ℤ) * (M - 1) + a)
    (hT : AoyagiLemma5Eq4PiecewiseSourceVector ell a p M m C layerWidth T) :
    T (C.point ell - 1) = 0 ↔
      aoyagiSelectedWidthNat ell m ell = M - (p : ℤ) + 1 := by
  rw [aoyagiLemma5Eq4_terminalEndpoint_value_of_predBoundary
    ell a p M m C layerWidth T hp hselected hT]
  constructor <;> intro h <;> linarith

/-- A supplied equation `(4)` terminal endpoint extension is compatible with
the terminal-collision boundary only under the last-width condition.

This records an obstruction to adding the terminal convention silently: in the
case `p+1=a`, the supplied singleton boundary already assigns the terminal
endpoint, so a terminal extension to `Htilde'_ell` forces
`W_(ell+1)=M-p+1`. -/
theorem aoyagiLemma5Eq4_terminalExtension_forces_lastWidth_of_predBoundary
    (ell a p : ℕ) (M : ℤ) (m : Fin (ell + 1) → ℤ)
    (C : AoyagiSelectedCutpoints ell) (layerWidth T : ℕ → ℤ)
    (hp : p + 1 = a)
    (hselected : (∑ j : Fin (ell + 1), m j) = (ell : ℤ) * (M - 1) + a)
    (hT : AoyagiLemma5Eq4PiecewiseSourceVector ell a p M m C layerWidth T)
    (hterminal :
      T (C.point ell - 1) = aoyagiHtildeUpperNat ell a M m ell) :
    aoyagiSelectedWidthNat ell m ell = M - (p : ℤ) + 1 := by
  have hzero :=
    aoyagiLemma5Eq4_terminalEndpoint_zero_of_upperNatExtension
      ell a M m C T hT.a_le_ell hselected hterminal
  exact (aoyagiLemma5Eq4_terminalEndpoint_zero_iff_lastWidth_of_predBoundary
    ell a p M m C layerWidth T hp hselected hT).1 hzero

/-- If the last-width compatibility fails in the terminal-collision case, the
supplied equation `(4)` certificate cannot also satisfy the terminal endpoint
extension to `Htilde'_ell`. -/
theorem aoyagiLemma5Eq4_no_terminalExtension_of_lastWidth_ne_predBoundary
    (ell a p : ℕ) (M : ℤ) (m : Fin (ell + 1) → ℤ)
    (C : AoyagiSelectedCutpoints ell) (layerWidth T : ℕ → ℤ)
    (hp : p + 1 = a)
    (hselected : (∑ j : Fin (ell + 1), m j) = (ell : ℤ) * (M - 1) + a)
    (hT : AoyagiLemma5Eq4PiecewiseSourceVector ell a p M m C layerWidth T)
    (hne : aoyagiSelectedWidthNat ell m ell ≠ M - (p : ℤ) + 1) :
    ¬ T (C.point ell - 1) = aoyagiHtildeUpperNat ell a M m ell := by
  intro hterminal
  exact hne
    (aoyagiLemma5Eq4_terminalExtension_forces_lastWidth_of_predBoundary
      ell a p M m C layerWidth T hp hselected hT hterminal)

/-- Under Definition 3's selected-width hypotheses, a supplied terminal
upper-chain extension in the terminal-collision equation `(4)` case forces
`2 <= p`.

This is a necessary condition only.  It does not construct equation `(4)`'s
certificate, construct a terminal extension, prove terminal `tilde t=0`, or
prove Aoyagi Lemma 5. -/
theorem aoyagiLemma5Eq4_terminalExtension_forces_two_le_p_of_sourceSelected
    (ell a p : ℕ) (M : ℤ) (m : Fin (ell + 1) → ℤ)
    (C : AoyagiSelectedCutpoints ell) (layerWidth T : ℕ → ℤ)
    (hp : p + 1 = a)
    (hselected : (∑ j : Fin (ell + 1), m j) = (ell : ℤ) * (M - 1) + a)
    (hsource : ∀ i : Fin (ell + 1),
      (ell : ℤ) * m i < ∑ j : Fin (ell + 1), m j)
    (hT : AoyagiLemma5Eq4PiecewiseSourceVector ell a p M m C layerWidth T)
    (hterminal :
      T (C.point ell - 1) = aoyagiHtildeUpperNat ell a M m ell) :
    2 ≤ p := by
  have hcompat :=
    aoyagiLemma5Eq4_terminalExtension_forces_lastWidth_of_predBoundary
      ell a p M m C layerWidth T hp hselected hT hterminal
  have hell : 1 ≤ ell := by
    have ha : a ≤ ell := hT.a_le_ell
    omega
  have hwidth_le :
      aoyagiSelectedWidthNat ell m ell ≤ M - 1 := by
    rw [aoyagiSelectedWidthNat_of_lt (by omega)]
    exact aoyagiSelectedWidth_le_pred_of_sourceSelectedInequality
      ell a M m hell hT.a_le_ell hselected hsource ⟨ell, by omega⟩
  omega

/-- Under Definition 3's selected-width hypotheses, a supplied terminal
upper-chain extension in the terminal-collision equation `(4)` case is
impossible when `p < 2`. -/
theorem aoyagiLemma5Eq4_no_terminalExtension_of_sourceSelected_of_p_lt_two
    (ell a p : ℕ) (M : ℤ) (m : Fin (ell + 1) → ℤ)
    (C : AoyagiSelectedCutpoints ell) (layerWidth T : ℕ → ℤ)
    (hp : p + 1 = a) (hp_lt_two : p < 2)
    (hselected : (∑ j : Fin (ell + 1), m j) = (ell : ℤ) * (M - 1) + a)
    (hsource : ∀ i : Fin (ell + 1),
      (ell : ℤ) * m i < ∑ j : Fin (ell + 1), m j)
    (hT : AoyagiLemma5Eq4PiecewiseSourceVector ell a p M m C layerWidth T) :
    T (C.point ell - 1) ≠ aoyagiHtildeUpperNat ell a M m ell := by
  intro hterminal
  have hp_ge_two :=
    aoyagiLemma5Eq4_terminalExtension_forces_two_le_p_of_sourceSelected
      ell a p M m C layerWidth T hp hselected hsource hT hterminal
  omega

/-- In the `p=1` terminal-collision equation `(4)` case, Definition 3's
selected-width hypotheses rule out a supplied terminal upper-chain extension.

This is a supplied-data incompatibility only.  It does not construct equation
`(4)`'s certificate, construct a terminal extension, prove terminal
`tilde t=0`, or prove Aoyagi Lemma 5. -/
theorem aoyagiLemma5Eq4_no_terminalUpperNatExtension_of_p1_sourceSelectedInequality
    (ell a : ℕ) (M : ℤ) (m : Fin (ell + 1) → ℤ)
    (C : AoyagiSelectedCutpoints ell) (layerWidth T : ℕ → ℤ)
    (hp : 1 + 1 = a)
    (hselected : (∑ j : Fin (ell + 1), m j) = (ell : ℤ) * (M - 1) + a)
    (hsource : ∀ i : Fin (ell + 1),
      (ell : ℤ) * m i < ∑ j : Fin (ell + 1), m j)
    (hT : AoyagiLemma5Eq4PiecewiseSourceVector ell a 1 M m C layerWidth T) :
    T (C.point ell - 1) ≠ aoyagiHtildeUpperNat ell a M m ell := by
  have hell : 1 ≤ ell := by
    have ha : a ≤ ell := hT.a_le_ell
    omega
  have hwidth_le :
      aoyagiSelectedWidthNat ell m ell ≤ M - 1 := by
    rw [aoyagiSelectedWidthNat_of_lt (by omega)]
    exact aoyagiSelectedWidth_le_pred_of_sourceSelectedInequality
      ell a M m hell hT.a_le_ell hselected hsource ⟨ell, by omega⟩
  have hne :
      aoyagiSelectedWidthNat ell m ell ≠ M - (1 : ℤ) + 1 := by
    omega
  exact aoyagiLemma5Eq4_no_terminalExtension_of_lastWidth_ne_predBoundary
    ell a 1 M m C layerWidth T hp hselected hT hne

/-- For the closed `ell=3`, `a=2`, `p=1`, all-widths-two tuple, a supplied
equation `(4)` certificate gives terminal endpoint value `1`, while the
terminal upper-chain endpoint is `0`.

This is a concrete endpoint calculation only; it does not construct the
supplied certificate or a terminal extension. -/
theorem aoyagiLemma5Eq4_terminalEndpoint_values_ell3_a2_p1_allWidthsTwo
    (C : AoyagiSelectedCutpoints 3) (layerWidth T : ℕ → ℤ)
    (hT : AoyagiLemma5Eq4PiecewiseSourceVector
      3 2 1 (3 : ℤ) (fun _ : Fin (3 + 1) => (2 : ℤ)) C layerWidth T) :
    T (C.point 3 - 1) = 1 ∧
      aoyagiHtildeUpperNat 3 2 (3 : ℤ)
        (fun _ : Fin (3 + 1) => (2 : ℤ)) 3 = 0 := by
  constructor
  · have hselected :
        (∑ j : Fin (3 + 1), (fun _ : Fin (3 + 1) => (2 : ℤ)) j) =
          (3 : ℤ) * ((3 : ℤ) - 1) + (2 : ℕ) := by
      norm_num
    have hvalue :=
      aoyagiLemma5Eq4_terminalEndpoint_value_of_predBoundary
        3 2 1 (3 : ℤ) (fun _ : Fin (3 + 1) => (2 : ℤ)) C layerWidth T
        (by norm_num) hselected hT
    simpa [aoyagiSelectedWidthNat] using hvalue
  · exact aoyagiHtildeUpperNat_last_eq_zero_of_selectedSum
      3 2 (3 : ℤ) (fun _ : Fin (3 + 1) => (2 : ℤ))
      (by norm_num) (by norm_num)

/-- For the closed `ell=3`, `a=2`, `p=1`, all-widths-two tuple, any supplied
equation `(4)` certificate rules out the supplied terminal upper-chain
extension at the terminal selected endpoint.

This does not construct the supplied certificate, construct a terminal
extension, prove terminal `tilde t=0`, or prove Aoyagi Lemma 5. -/
theorem aoyagiLemma5Eq4_no_terminalUpperNatExtension_ell3_a2_p1_allWidthsTwo
    (C : AoyagiSelectedCutpoints 3) (layerWidth T : ℕ → ℤ)
    (hT : AoyagiLemma5Eq4PiecewiseSourceVector
      3 2 1 (3 : ℤ) (fun _ : Fin (3 + 1) => (2 : ℤ)) C layerWidth T) :
    T (C.point 3 - 1) ≠
      aoyagiHtildeUpperNat 3 2 (3 : ℤ)
        (fun _ : Fin (3 + 1) => (2 : ℤ)) 3 := by
  exact aoyagiLemma5Eq4_no_terminalExtension_of_lastWidth_ne_predBoundary
    3 2 1 (3 : ℤ) (fun _ : Fin (3 + 1) => (2 : ℤ)) C layerWidth T
    (by norm_num) (by norm_num) hT (by norm_num [aoyagiSelectedWidthNat])

/-- A supplied equation `(4)` piecewise vector has the correct own-coordinate
value and legal source label under the repaired guards.

This theorem is source-vector-facing but still conditional: it assumes the
piecewise branch certificate. -/
theorem aoyagiLemma5Eq4_piecewise_ownCoordinate_of_sourceSelectedInequality
    (ell a p : ℕ) (M : ℤ) (m : Fin (ell + 1) → ℤ)
    (C : AoyagiSelectedCutpoints ell) (layerWidth T : ℕ → ℤ)
    (hell : 1 ≤ ell) (hp0 : 1 ≤ p) (hp_c : p ≤ ell - a)
    (hselected : (∑ j : Fin (ell + 1), m j) = (ell : ℤ) * (M - 1) + a)
    (hsource : ∀ i : Fin (ell + 1),
      (ell : ℤ) * m i < ∑ j : Fin (ell + 1), m j)
    (hT : AoyagiLemma5Eq4PiecewiseSourceVector ell a p M m C layerWidth T) :
    p + (ell - a) + 2 ≤ ell + 1 ∧
      T (C.point p - 1) = aoyagiHtildeLowerNat ell a M m p ∧
      (1 ≤ aoyagiHtildeLowerNat ell a M m p + 1 ∧
        aoyagiHtildeLowerNat ell a M m p + 1 ≤
          aoyagiSelectedWidthNat ell m p) := by
  have hlocal := aoyagiLemma5Eq4_localData_of_sourceSelectedInequality
    ell a p M m hell hT.a_le_ell hp0 hT.indexGuard hp_c hselected hsource
  rcases hlocal with ⟨hcutoff, hown, hlabel⟩
  have hp_lt_ell : p < ell := by omega
  have hblock : C.block p (C.point p - 1) :=
    C.leftEndpoint_mem_block hp_lt_ell
  have hvalue := hT.prefixBranch p (C.point p - 1) hp0 le_rfl hblock
  constructor
  · exact hcutoff
  constructor
  · rw [hvalue]
    exact hown
  · exact hlabel

/-- Supplied source-layer piecewise data for Aoyagi Lemma 5 equation `(3)`.

This is a certificate that a function `T` has the displayed branch values on
the selected blocks.  It is not a construction of such a function and carries
no terminal or chart-coverage claim. -/
structure AoyagiLemma5Eq3PiecewiseSourceVector
    (ell a : ℕ) (M : ℤ) (m : Fin (ell + 1) → ℤ)
    (C : AoyagiSelectedCutpoints ell) (layerWidth T : ℕ → ℤ) : Prop where
  a_le_ell : a ≤ ell
  indexGuard : 1 ≤ a
  first :
    ∀ S, S < C.point 1 - 1 → T S = layerWidth (S + 1)
  upper :
    ∀ b S, 1 ≤ b → b ≤ ell - a → C.block b S →
      T S = aoyagiHtildeUpperNat ell a M m b
  boundary :
    T (C.point (ell - a + 1) - 1) =
      aoyagiHtildeUpperNat ell a M m (ell - a + 1) + 1
  tail :
    ∀ b S, ell - a + 1 ≤ b → C.block b S →
      C.point (ell - a + 1) - 1 < S →
        T S = aoyagiHtildeUpperNat ell a M m b

/-- The equation `(3)` boundary index `ell-a+1` is a selected cutpoint index
under the supplied source guard. -/
theorem aoyagiLemma5Eq3_boundaryIndex_le_ell_of_piecewiseSourceVector
    (ell a : ℕ) (M : ℤ) (m : Fin (ell + 1) → ℤ)
    (C : AoyagiSelectedCutpoints ell) (layerWidth T : ℕ → ℤ)
    (hT : AoyagiLemma5Eq3PiecewiseSourceVector ell a M m C layerWidth T) :
    ell - a + 1 ≤ ell := by
  have ha : a ≤ ell := hT.a_le_ell
  have ha_pos : 1 ≤ a := hT.indexGuard
  omega

/-- The equation `(3)` boundary is inside the half-open selected blocks
exactly when `2<=a`; for `a=1` it is the terminal selected endpoint. -/
theorem aoyagiLemma5Eq3_boundaryIndex_lt_ell_iff
    (ell a : ℕ) (ha : a ≤ ell) (ha_pos : 1 ≤ a) :
    ell - a + 1 < ell ↔ 2 ≤ a := by
  constructor <;> intro h <;> omega

/-- In the strict equation `(3)` boundary case `2<=a`, the displayed boundary
point is the left endpoint of an ordinary selected block. -/
theorem aoyagiLemma5Eq3_boundaryEndpoint_mem_block_of_two_le
    (ell a : ℕ) (M : ℤ) (m : Fin (ell + 1) → ℤ)
    (C : AoyagiSelectedCutpoints ell) (layerWidth T : ℕ → ℤ)
    (hT : AoyagiLemma5Eq3PiecewiseSourceVector ell a M m C layerWidth T)
    (ha_two : 2 ≤ a) :
    C.block (ell - a + 1) (C.point (ell - a + 1) - 1) := by
  have hlt :
      ell - a + 1 < ell :=
    (aoyagiLemma5Eq3_boundaryIndex_lt_ell_iff
      ell a hT.a_le_ell hT.indexGuard).2 ha_two
  exact C.leftEndpoint_mem_block hlt

/-- In the strict equation `(3)` boundary case `2<=a`, the displayed boundary
point lies in the half-open selected span. -/
theorem aoyagiLemma5Eq3_boundaryEndpoint_mem_selectedSpan_of_two_le
    (ell a : ℕ) (M : ℤ) (m : Fin (ell + 1) → ℤ)
    (C : AoyagiSelectedCutpoints ell) (layerWidth T : ℕ → ℤ)
    (hT : AoyagiLemma5Eq3PiecewiseSourceVector ell a M m C layerWidth T)
    (ha_two : 2 ≤ a) :
    C.point 0 - 1 ≤ C.point (ell - a + 1) - 1 ∧
      C.point (ell - a + 1) - 1 < C.point ell - 1 := by
  exact C.block_mem_selectedSpan
    (aoyagiLemma5Eq3_boundaryEndpoint_mem_block_of_two_le
      ell a M m C layerWidth T hT ha_two)

/-- In the terminal equation `(3)` boundary case `a=1`, the displayed boundary
point is the terminal selected endpoint. -/
theorem aoyagiLemma5Eq3_boundaryEndpoint_eq_terminal_of_one
    (ell : ℕ) (M : ℤ) (m : Fin (ell + 1) → ℤ)
    (C : AoyagiSelectedCutpoints ell) (layerWidth T : ℕ → ℤ)
    (hT : AoyagiLemma5Eq3PiecewiseSourceVector ell 1 M m C layerWidth T) :
    C.point (ell - 1 + 1) - 1 = C.point ell - 1 := by
  have hidx : ell - 1 + 1 = ell := by
    have hell_pos : 1 ≤ ell := hT.a_le_ell
    omega
  rw [hidx]

/-- In the terminal equation `(3)` boundary case `a=1`, the displayed boundary
point is not in any half-open selected block. -/
theorem aoyagiLemma5Eq3_boundaryEndpoint_not_block_of_one
    (ell : ℕ) (M : ℤ) (m : Fin (ell + 1) → ℤ)
    (C : AoyagiSelectedCutpoints ell) (layerWidth T : ℕ → ℤ)
    (hT : AoyagiLemma5Eq3PiecewiseSourceVector ell 1 M m C layerWidth T)
    {b : ℕ} :
    ¬ C.block b (C.point (ell - 1 + 1) - 1) := by
  rw [aoyagiLemma5Eq3_boundaryEndpoint_eq_terminal_of_one
    ell M m C layerWidth T hT]
  exact C.not_block_terminalEndpoint

/-- Equation `(3)`'s special boundary lies in the half-open selected span
exactly in the strict case `2<=a`. -/
theorem aoyagiLemma5Eq3_boundaryEndpoint_mem_selectedSpan_iff_two_le
    (ell a : ℕ) (M : ℤ) (m : Fin (ell + 1) → ℤ)
    (C : AoyagiSelectedCutpoints ell) (layerWidth T : ℕ → ℤ)
    (hT : AoyagiLemma5Eq3PiecewiseSourceVector ell a M m C layerWidth T) :
    (C.point 0 - 1 ≤ C.point (ell - a + 1) - 1 ∧
        C.point (ell - a + 1) - 1 < C.point ell - 1) ↔
      2 ≤ a := by
  constructor
  · intro hspan
    by_contra hnot
    have ha_pos : 1 ≤ a := hT.indexGuard
    have ha_one : a = 1 := by omega
    subst a
    have hterm :=
      aoyagiLemma5Eq3_boundaryEndpoint_eq_terminal_of_one
        ell M m C layerWidth T hT
    rw [hterm] at hspan
    exact (lt_irrefl (C.point ell - 1)) hspan.2
  · intro ha_two
    exact aoyagiLemma5Eq3_boundaryEndpoint_mem_selectedSpan_of_two_le
      ell a M m C layerWidth T hT ha_two

/-- Equation `(3)` assigns its special boundary one unit above the upper
same-coordinate `Htilde` value.

This is only supplied branch arithmetic.  It does not construct the displayed
source vector, prove terminality, chart coverage, or order counting. -/
theorem aoyagiLemma5Eq3_boundaryValue_gt_upperNat
    (ell a : ℕ) (M : ℤ) (m : Fin (ell + 1) → ℤ)
    (C : AoyagiSelectedCutpoints ell) (layerWidth T : ℕ → ℤ)
    (hT : AoyagiLemma5Eq3PiecewiseSourceVector ell a M m C layerWidth T) :
    aoyagiHtildeUpperNat ell a M m (ell - a + 1) <
      T (C.point (ell - a + 1) - 1) := by
  rw [hT.boundary]
  omega

/-- Equation `(3)`'s special boundary value is not one of the same-coordinate
interval values at the boundary coordinate.

The point is the finite obstruction `Htilde'_j + 1 > Htilde'_j`.  This does
not disprove Aoyagi's Lemma 5; it only records that the special boundary is
not counted by the same-coordinate interval family. -/
theorem aoyagiLemma5Eq3_boundaryValue_not_mem_intervalValueSetNat
    (ell a : ℕ) (M : ℤ) (m : Fin (ell + 1) → ℤ)
    (C : AoyagiSelectedCutpoints ell) (layerWidth T : ℕ → ℤ)
    (hT : AoyagiLemma5Eq3PiecewiseSourceVector ell a M m C layerWidth T) :
    T (C.point (ell - a + 1) - 1) ∉
      aoyagiHtildeIntervalValueSetNat ell a M m (ell - a + 1) := by
  intro hmem
  have hj : ell - a + 1 < ell + 1 := by
    have ha : a ≤ ell := hT.a_le_ell
    have ha_pos : 1 ≤ a := hT.indexGuard
    omega
  have hmem_fin :
      T (C.point (ell - a + 1) - 1) ∈
        aoyagiHtildeIntervalValueSet ell a M m ⟨ell - a + 1, hj⟩ := by
    simpa [aoyagiHtildeIntervalValueSetNat, hj] using hmem
  have hbounds :=
    (aoyagiHtilde_mem_intervalValueSet_iff_bounds ell a M m hT.a_le_ell
      ⟨ell - a + 1, hj⟩ (T (C.point (ell - a + 1) - 1))).1 hmem_fin
  have hle :
      T (C.point (ell - a + 1) - 1) ≤
        aoyagiHtildeUpperNat ell a M m (ell - a + 1) := by
    simpa [aoyagiHtildeUpperChain] using hbounds.2
  have hgt :=
    aoyagiLemma5Eq3_boundaryValue_gt_upperNat ell a M m C layerWidth T hT
  omega

/-- In the strict equation `(3)` boundary case, the special boundary lies in
the selected span but its value is still outside the same-coordinate interval
at that boundary coordinate. -/
theorem aoyagiLemma5Eq3_boundaryValue_not_mem_intervalValueSetNat_of_two_le
    (ell a : ℕ) (M : ℤ) (m : Fin (ell + 1) → ℤ)
    (C : AoyagiSelectedCutpoints ell) (layerWidth T : ℕ → ℤ)
    (hT : AoyagiLemma5Eq3PiecewiseSourceVector ell a M m C layerWidth T)
    (ha_two : 2 ≤ a) :
    T (C.point (ell - a + 1) - 1) ∉
      aoyagiHtildeIntervalValueSetNat ell a M m (ell - a + 1) := by
  have _hspan :=
    aoyagiLemma5Eq3_boundaryEndpoint_mem_selectedSpan_of_two_le
      ell a M m C layerWidth T hT ha_two
  exact aoyagiLemma5Eq3_boundaryValue_not_mem_intervalValueSetNat
    ell a M m C layerWidth T hT

/-- Branch-value alternatives for Aoyagi Lemma 5 equation `(3)` on the
selected span.

This is only a domain/value classification for a supplied piecewise
certificate.  It does not construct the displayed source vector and makes no
terminality, admissibility, chart-coverage, pole-order, normal-crossing, or
RLCT claim. -/
inductive AoyagiLemma5Eq3SelectedSpanBranchValue
    (ell a : ℕ) (M : ℤ) (m : Fin (ell + 1) → ℤ)
    (C : AoyagiSelectedCutpoints ell) (layerWidth T : ℕ → ℤ) (S : ℕ) : Prop where
  | first
      (hS : S < C.point 1 - 1)
      (hvalue : T S = layerWidth (S + 1))
  | upper
      (b : ℕ) (hb_pos : 1 ≤ b) (hb_le : b ≤ ell - a) (hb : C.block b S)
      (hvalue : T S = aoyagiHtildeUpperNat ell a M m b)
  | boundary
      (hS : S = C.point (ell - a + 1) - 1)
      (hvalue :
        T S = aoyagiHtildeUpperNat ell a M m (ell - a + 1) + 1)
  | tail
      (b : ℕ) (hb_tail : ell - a + 1 ≤ b) (hb : C.block b S)
      (hS : C.point (ell - a + 1) - 1 < S)
      (hvalue : T S = aoyagiHtildeUpperNat ell a M m b)

/-- A supplied equation `(3)` piecewise certificate classifies any selected
block point by one of its advertised branches.

This is half-open block bookkeeping plus the supplied branch equalities. -/
theorem aoyagiLemma5Eq3_branchValue_of_block
    (ell a : ℕ) (M : ℤ) (m : Fin (ell + 1) → ℤ)
    (C : AoyagiSelectedCutpoints ell) (layerWidth T : ℕ → ℤ)
    (hT : AoyagiLemma5Eq3PiecewiseSourceVector ell a M m C layerWidth T)
    {b S : ℕ} (hb : C.block b S) :
    AoyagiLemma5Eq3SelectedSpanBranchValue ell a M m C layerWidth T S := by
  by_cases hb0 : b = 0
  · subst b
    exact AoyagiLemma5Eq3SelectedSpanBranchValue.first
      hb.2.2 (hT.first S hb.2.2)
  have hb_pos : 1 ≤ b := by omega
  by_cases hb_upper : b ≤ ell - a
  · exact AoyagiLemma5Eq3SelectedSpanBranchValue.upper b hb_pos hb_upper hb
      (hT.upper b S hb_pos hb_upper hb)
  have hb_tail : ell - a + 1 ≤ b := by omega
  by_cases hboundary : S = C.point (ell - a + 1) - 1
  · exact AoyagiLemma5Eq3SelectedSpanBranchValue.boundary hboundary
      (by simpa [hboundary] using hT.boundary)
  have hafter : C.point (ell - a + 1) - 1 < S := by
    by_cases hb_eq : b = ell - a + 1
    · subst b
      exact C.block_leftEndpoint_lt_of_ne hb hboundary
    · have hlt : ell - a + 1 < b := by omega
      exact C.leftEndpoint_lt_of_lt_block hlt hb
  exact AoyagiLemma5Eq3SelectedSpanBranchValue.tail b hb_tail hb hafter
    (hT.tail b S hb_tail hb hafter)

/-- A supplied equation `(3)` piecewise certificate covers every source index in
the selected span by one of its advertised branches.

This is only a selected-span consequence of the block classifier.  It does not
claim coverage before `S_1-1`, at `S_(ell+1)-1`, or after it. -/
theorem aoyagiLemma5Eq3_selectedSpan_branchValue
    (ell a : ℕ) (M : ℤ) (m : Fin (ell + 1) → ℤ)
    (C : AoyagiSelectedCutpoints ell) (layerWidth T : ℕ → ℤ)
    (hT : AoyagiLemma5Eq3PiecewiseSourceVector ell a M m C layerWidth T)
    {S : ℕ} (hlo : C.point 0 - 1 ≤ S) (hhi : S < C.point ell - 1) :
    AoyagiLemma5Eq3SelectedSpanBranchValue ell a M m C layerWidth T S := by
  rcases C.exists_block_of_mem_selectedSpan hlo hhi with ⟨b, hb⟩
  exact aoyagiLemma5Eq3_branchValue_of_block ell a M m C layerWidth T hT hb

/-- A supplied equation `(3)` piecewise vector has the correct own-coordinate
value and legal source label under the explicit slack hypothesis.

This theorem is source-vector-facing but still conditional: it assumes the
piecewise branch certificate and does not prove terminality or chart coverage. -/
theorem aoyagiLemma5Eq3_piecewise_ownCoordinate_of_sourceSelectedInequality_and_slack
    (ell a : ℕ) (M : ℤ) (m : Fin (ell + 1) → ℤ)
    (C : AoyagiSelectedCutpoints ell) (layerWidth T : ℕ → ℤ)
    (hell : 1 ≤ ell) (ha_lt : a < ell)
    (hselected : (∑ j : Fin (ell + 1), m j) = (ell : ℤ) * (M - 1) + a)
    (hsource : ∀ i : Fin (ell + 1),
      (ell : ℤ) * m i < ∑ j : Fin (ell + 1), m j)
    (hslack : aoyagiSelectedWidthNat ell m 0 + 2 ≤ M)
    (hT : AoyagiLemma5Eq3PiecewiseSourceVector ell a M m C layerWidth T) :
    (ell - a) + 2 ≤ ell + 1 ∧
      T (C.point 1 - 1) = aoyagiHtildeUpperNat ell a M m 1 ∧
      (1 ≤ aoyagiHtildeUpperNat ell a M m 1 + 1 ∧
        aoyagiHtildeUpperNat ell a M m 1 + 1 ≤
          aoyagiSelectedWidthNat ell m 1) := by
  have hlocal :=
    aoyagiLemma5Eq3_localData_of_sourceSelectedInequality_and_slack
      ell a M m hell hT.a_le_ell hT.indexGuard ha_lt hselected hsource hslack
  rcases hlocal with ⟨hcutoff, _hgap, hlabel⟩
  have hblock : C.block 1 (C.point 1 - 1) :=
    C.leftEndpoint_mem_block (by omega)
  have hvalue := hT.upper 1 (C.point 1 - 1) le_rfl (by omega) hblock
  constructor
  · exact hcutoff
  constructor
  · exact hvalue
  · exact hlabel

/-- In the boundary case `a=1`, a supplied equation `(3)` certificate assigns
the terminal selected endpoint the value `1`.

This is an obstruction record: it shows that equation `(3)` cannot by itself
give terminal endpoint zero uniformly. -/
theorem aoyagiLemma5Eq3_terminalEndpoint_one_of_one
    (ell : ℕ) (M : ℤ) (m : Fin (ell + 1) → ℤ)
    (C : AoyagiSelectedCutpoints ell) (layerWidth T : ℕ → ℤ)
    (hselected : (∑ j : Fin (ell + 1), m j) = (ell : ℤ) * (M - 1) + 1)
    (hT : AoyagiLemma5Eq3PiecewiseSourceVector ell 1 M m C layerWidth T) :
    T (C.point ell - 1) = 1 := by
  have hell_pos : 1 ≤ ell := hT.a_le_ell
  have hidx : ell - 1 + 1 = ell := by omega
  have hboundary := hT.boundary
  rw [hidx] at hboundary
  have hzero := aoyagiHtildeUpperNat_last_eq_zero_of_selectedSum
    ell 1 M m hT.a_le_ell hselected
  rw [hzero] at hboundary
  simpa using hboundary

/-- In the boundary case `a=1`, a supplied equation `(3)` certificate cannot
also assign terminal endpoint zero. -/
theorem aoyagiLemma5Eq3_no_terminalEndpointZero_of_one
    (ell : ℕ) (M : ℤ) (m : Fin (ell + 1) → ℤ)
    (C : AoyagiSelectedCutpoints ell) (layerWidth T : ℕ → ℤ)
    (hselected : (∑ j : Fin (ell + 1), m j) = (ell : ℤ) * (M - 1) + 1)
    (hT : AoyagiLemma5Eq3PiecewiseSourceVector ell 1 M m C layerWidth T) :
    ¬ T (C.point ell - 1) = 0 := by
  intro hzero
  have hone :=
    aoyagiLemma5Eq3_terminalEndpoint_one_of_one
      ell M m C layerWidth T hselected hT
  omega

end Aoyagi
end DLN
end DLNFibre
