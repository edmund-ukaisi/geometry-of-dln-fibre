import DLNFibre.DLN.Aoyagi.Lemma5IntervalArithmetic
import DLNFibre.DLN.Aoyagi.HtildeChainArithmetic

/-!
# Conditional displayed-vector data for Aoyagi's Lemma 5

This file introduces source-layer cutpoints and supplied piecewise certificates
for Aoyagi Lemma 5 equations `(3)`, `(4)`, and `(5)`.  It does not construct the
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

/-- A point in the half-open selected span is in the source range whenever the
terminal selected endpoint is in the source range. -/
theorem selectedSpan_sourceIndex_le_of_terminalEndpoint_le {ell : ℕ}
    (C : AoyagiSelectedCutpoints ell) {L S : ℕ}
    (hhi : S < C.point ell - 1)
    (hterminal : C.point ell - 1 ≤ L) :
    S ≤ L := by
  omega

/-- Source-shaped endpoint version: if the last selected cutpoint
`S_(ell+1)` is at most `L+1`, then every point in the selected span has
source index at most `L`. -/
theorem selectedSpan_sourceIndex_le_of_lastPoint_le {ell : ℕ}
    (C : AoyagiSelectedCutpoints ell) {L S : ℕ}
    (hhi : S < C.point ell - 1)
    (hlast : C.point ell ≤ L + 1) :
    S ≤ L := by
  have hpos : 1 ≤ C.point ell := C.point_pos_of_lt (by omega)
  exact C.selectedSpan_sourceIndex_le_of_terminalEndpoint_le hhi (by omega)

/-- A selected-block member is in the source range whenever the terminal
selected endpoint is in the source range. -/
theorem block_sourceIndex_le_of_terminalEndpoint_le {ell : ℕ}
    (C : AoyagiSelectedCutpoints ell) {L b S : ℕ}
    (hblock : C.block b S) (hterminal : C.point ell - 1 ≤ L) :
    S ≤ L := by
  exact C.selectedSpan_sourceIndex_le_of_terminalEndpoint_le
    (C.block_mem_selectedSpan hblock).2 hterminal

/-- Source-shaped endpoint version for selected blocks. -/
theorem block_sourceIndex_le_of_lastPoint_le {ell : ℕ}
    (C : AoyagiSelectedCutpoints ell) {L b S : ℕ}
    (hblock : C.block b S) (hlast : C.point ell ≤ L + 1) :
    S ≤ L := by
  exact C.selectedSpan_sourceIndex_le_of_lastPoint_le
    (C.block_mem_selectedSpan hblock).2 hlast

/-- A selected-block member `S` has source layer `S+1` between the two
adjacent selected cutpoints. -/
theorem block_sourceLayer_mem_Ico {ell : ℕ}
    (C : AoyagiSelectedCutpoints ell) {b S : ℕ}
    (hblock : C.block b S) :
    C.point b ≤ S + 1 ∧ S + 1 < C.point (b + 1) := by
  rcases hblock with ⟨hb_lt, hlo, hhi⟩
  have hpos : 1 ≤ C.point b := C.point_pos_of_lt (by omega)
  constructor <;> omega

/-- A selected-block source layer is either the block's left selected layer or
strictly between adjacent selected cutpoints. -/
theorem block_sourceLayer_eq_left_or_between {ell : ℕ}
    (C : AoyagiSelectedCutpoints ell) {b S : ℕ}
    (hblock : C.block b S) :
    S + 1 = C.point b ∨
      C.point b < S + 1 ∧ S + 1 < C.point (b + 1) := by
  have hIco := C.block_sourceLayer_mem_Ico hblock
  omega

/-- A layer strictly between adjacent selected cutpoints is not one of the
selected cutpoints. -/
theorem point_ne_of_between_adjacent {ell : ℕ}
    (C : AoyagiSelectedCutpoints ell) {b t : ℕ}
    (hb : b < ell) (hlo : C.point b < t) (hhi : t < C.point (b + 1))
    (i : Fin (ell + 1)) :
    t ≠ C.point i.val := by
  intro ht
  by_cases hi_le : i.val ≤ b
  · have hle : C.point i.val ≤ C.point b :=
      C.point_le_of_le hi_le (by omega)
    rw [← ht] at hle
    omega
  · have hge : b + 1 ≤ i.val := by omega
    have hle : C.point (b + 1) ≤ C.point i.val :=
      C.point_le_of_le hge i.isLt
    rw [← ht] at hle
    omega

/-- Width bound for a source layer in a selected block, from an explicit
block-local actual-width lower-bound hypothesis. -/
theorem selectedWidthNat_le_actualWidth_of_block
    {ell : ℕ} (C : AoyagiSelectedCutpoints ell)
    (n : ℕ → ℕ) (m : Fin (ell + 1) → ℤ)
    {p S : ℕ}
    (hactual :
      ∀ i : Fin ell, ∀ r : ℕ,
        C.point i.val ≤ r → r < C.point (i.val + 1) →
          aoyagiSelectedWidthNat ell m i.val ≤ (n r : ℤ))
    (hblock : C.block p S) :
    aoyagiSelectedWidthNat ell m p ≤ (n (S + 1) : ℤ) := by
  have hp : p < ell := hblock.1
  have hIco := C.block_sourceLayer_mem_Ico hblock
  exact hactual ⟨p, hp⟩ (S + 1) hIco.1 hIco.2

/-- Width bound for a source layer in a selected block, from a selected
left-endpoint width identity and block-local minimum condition. -/
theorem selectedWidthNat_le_actualWidth_of_block_of_leftEndpoint_min
    {ell : ℕ} (C : AoyagiSelectedCutpoints ell)
    (n : ℕ → ℕ) (m : Fin (ell + 1) → ℤ)
    {p S : ℕ}
    (hleft :
      ∀ i : Fin ell,
        (n (C.point i.val) : ℤ) = aoyagiSelectedWidthNat ell m i.val)
    (hmin :
      ∀ i : Fin ell, ∀ r : ℕ,
        C.point i.val ≤ r → r < C.point (i.val + 1) →
          n (C.point i.val) ≤ n r)
    (hblock : C.block p S) :
    aoyagiSelectedWidthNat ell m p ≤ (n (S + 1) : ℤ) := by
  exact C.selectedWidthNat_le_actualWidth_of_block n m
    (fun i r hlo hhi ↦ by
      rw [← hleft i]
      exact_mod_cast hmin i r hlo hhi)
    hblock

/-- Width bound for a source layer in a selected block, from explicit selected
widths and off-selected-layer dominance.

The hypothesis `hselectedWidth` identifies selected widths with actual widths
at selected cutpoints.  The hypothesis `hoffSelected` is deliberately
position-based: every layer not equal to a selected cutpoint is at least as
wide as every selected width.  This avoids reading extra uniqueness or
duplicate-value assumptions into Aoyagi's Definition 3. -/
theorem selectedWidthNat_le_actualWidth_of_block_of_offSelected
    {ell : ℕ} (C : AoyagiSelectedCutpoints ell)
    (n : ℕ → ℕ) (m : Fin (ell + 1) → ℤ)
    {p S : ℕ} (hblock : C.block p S)
    (hselectedWidth : ∀ i : Fin (ell + 1), (n (C.point i.val) : ℤ) = m i)
    (hoffSelected :
      ∀ t : ℕ, (∀ i : Fin (ell + 1), t ≠ C.point i.val) →
        ∀ i : Fin (ell + 1), m i ≤ (n t : ℤ)) :
    aoyagiSelectedWidthNat ell m p ≤ (n (S + 1) : ℤ) := by
  have hp_block : p < ell := hblock.1
  have hp_lt : p < ell + 1 := by omega
  let ip : Fin (ell + 1) := ⟨p, hp_lt⟩
  have hW : aoyagiSelectedWidthNat ell m p = m ip := by
    exact aoyagiSelectedWidthNat_of_lt hp_lt
  rcases C.block_sourceLayer_eq_left_or_between hblock with hleft | hbetween
  · have hsel := hselectedWidth ip
    rw [hW, hleft, ← hsel]
  · rw [hW]
    exact hoffSelected (S + 1)
      (fun i ↦ C.point_ne_of_between_adjacent hblock.1 hbetween.1 hbetween.2 i)
      ip

/-- Strict off-selected-layer dominance version of
`selectedWidthNat_le_actualWidth_of_block_of_offSelected`. -/
theorem selectedWidthNat_le_actualWidth_of_block_of_offSelected_lt
    {ell : ℕ} (C : AoyagiSelectedCutpoints ell)
    (n : ℕ → ℕ) (m : Fin (ell + 1) → ℤ)
    {p S : ℕ} (hblock : C.block p S)
    (hselectedWidth : ∀ i : Fin (ell + 1), (n (C.point i.val) : ℤ) = m i)
    (hoffSelected :
      ∀ t : ℕ, (∀ i : Fin (ell + 1), t ≠ C.point i.val) →
        ∀ i : Fin (ell + 1), m i < (n t : ℤ)) :
    aoyagiSelectedWidthNat ell m p ≤ (n (S + 1) : ℤ) := by
  exact C.selectedWidthNat_le_actualWidth_of_block_of_offSelected n m hblock
    hselectedWidth
    (fun t ht i ↦ le_of_lt (hoffSelected t ht i))

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

/-- A concrete guardrail showing that Definition 3-shaped selected-width data
do not force the block width bound needed by Lemma 5 equation `(5)`.

The selected cutpoints are `1,3,5,7`, the selected widths are `1,2,2,2`,
and the unselected layer `6` has actual width `1`.  This actual width value is
selected elsewhere, so Aoyagi's value-level nonselected-width condition is
vacuous at that layer; nevertheless it lies in block `p=2`, where the selected
width is `2`. -/
theorem aoyagiLemma5Eq5_blockWidthBound_not_forced_by_selectedWidthHypotheses_example :
    ∃ (C : AoyagiSelectedCutpoints 3) (n : ℕ → ℕ) (m : Fin 4 → ℤ)
      (p S : ℕ),
      C.block p S ∧
      (∀ i : Fin 4, (n (C.point i.val) : ℤ) = m i) ∧
      (∀ i : Fin 4, 1 ≤ m i) ∧
      (∑ j : Fin 4, m j) = (3 : ℤ) * (3 - 1) + 1 ∧
      (∀ i : Fin 4, (3 : ℤ) * m i < ∑ j : Fin 4, m j) ∧
      (∀ t : ℕ, (∀ i : Fin 4, (n t : ℤ) ≠ m i) →
        ∀ i : Fin 4, m i ≤ (n t : ℤ)) ∧
      ¬ aoyagiSelectedWidthNat 3 m p ≤ (n (S + 1) : ℤ) := by
  let C : AoyagiSelectedCutpoints 3 :=
    { cut := fun i =>
        match i.val with
        | 0 => 1
        | 1 => 3
        | 2 => 5
        | _ => 7
      pos := by
        intro i
        fin_cases i <;> norm_num
      strict := by
        intro i
        fin_cases i <;> norm_num }
  let n : ℕ → ℕ := fun t =>
    if t = 1 then 1
    else if t = 3 then 2
    else if t = 5 then 2
    else if t = 7 then 2
    else if t = 6 then 1
    else 1
  let m : Fin 4 → ℤ := fun i =>
    match i.val with
    | 0 => 1
    | _ => 2
  refine ⟨C, n, m, 2, 5, ?_⟩
  constructor
  · unfold AoyagiSelectedCutpoints.block C AoyagiSelectedCutpoints.point
    norm_num
  constructor
  · intro i
    fin_cases i <;> norm_num [C, n, m, AoyagiSelectedCutpoints.point]
  constructor
  · intro i
    fin_cases i <;> norm_num [m]
  constructor
  · norm_num [m, Fin.sum_univ_four]
  constructor
  · intro i
    fin_cases i <;> norm_num [m, Fin.sum_univ_four]
  constructor
  · intro t hnot i
    have hhit : ∃ j : Fin 4, (n t : ℤ) = m j := by
      by_cases h1 : t = 1
      · refine ⟨0, ?_⟩
        norm_num [n, m, h1]
      · by_cases h3 : t = 3
        · refine ⟨1, ?_⟩
          norm_num [n, m, h1, h3]
        · by_cases h5 : t = 5
          · refine ⟨1, ?_⟩
            norm_num [n, m, h1, h3, h5]
          · by_cases h7 : t = 7
            · refine ⟨1, ?_⟩
              norm_num [n, m, h1, h3, h5, h7]
            · by_cases h6 : t = 6
              · refine ⟨0, ?_⟩
                norm_num [n, m, h1, h3, h5, h7, h6]
              · refine ⟨0, ?_⟩
                norm_num [n, m, h1, h3, h5, h7, h6]
    exact False.elim (hnot hhit.choose hhit.choose_spec)
  · norm_num [n, m, aoyagiSelectedWidthNat]

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

/-- Equation `(4)`'s printed special one-point line forces the corresponding
Lemma 4 increment to be the next selected width minus one.

This is finite chain arithmetic for supplied adjacent `H` values.  It does
not construct the displayed vector or prove that those `H` values come from a
source chart. -/
theorem aoyagiLemma5Eq4_specialIncrement_eq_selectedWidth_sub_one
    (ell a p : ℕ) (M : ℤ) (m H : Fin (ell + 1) → ℤ)
    (ha : a ≤ ell) (hp_strict : p + 1 < a)
    (hprev :
      H ⟨p + (ell - a), by omega⟩ =
        aoyagiHtildeUpperNat ell a M m (p + (ell - a)) - (p : ℤ))
    (hboundary :
      H ⟨p + (ell - a) + 1, by omega⟩ =
        aoyagiHtildeUpperNat ell a M m (p + (ell - a)) - (p : ℤ) + 1) :
    aoyagiLemma4F ell m H ⟨p + (ell - a), by omega⟩ =
      aoyagiSelectedWidthNat ell m (p + (ell - a) + 1) - 1 := by
  unfold aoyagiLemma4F
  change
    H ⟨p + (ell - a), by omega⟩ -
          H ⟨p + (ell - a) + 1, by omega⟩ +
        m ⟨p + (ell - a) + 1, by omega⟩ =
      aoyagiSelectedWidthNat ell m (p + (ell - a) + 1) - 1
  rw [hprev, hboundary, aoyagiSelectedWidthNat_of_lt (by omega)]
  ring

/-- Under Definition 3's selected-width inequalities, equation `(4)`'s
special-line increment is strictly below `M-1`.

This is the formal obstruction behind the source calculation
`W_(q+1)-1 <= M-2`. -/
theorem aoyagiLemma5Eq4_specialIncrement_lt_pred_of_sourceSelected
    (ell a p : ℕ) (M : ℤ) (m H : Fin (ell + 1) → ℤ)
    (hell : 1 ≤ ell) (ha : a ≤ ell) (hp_strict : p + 1 < a)
    (hselected : (∑ j : Fin (ell + 1), m j) = (ell : ℤ) * (M - 1) + a)
    (hsource : ∀ i : Fin (ell + 1),
      (ell : ℤ) * m i < ∑ j : Fin (ell + 1), m j)
    (hprev :
      H ⟨p + (ell - a), by omega⟩ =
        aoyagiHtildeUpperNat ell a M m (p + (ell - a)) - (p : ℤ))
    (hboundary :
      H ⟨p + (ell - a) + 1, by omega⟩ =
        aoyagiHtildeUpperNat ell a M m (p + (ell - a)) - (p : ℤ) + 1) :
    aoyagiLemma4F ell m H ⟨p + (ell - a), by omega⟩ < M - 1 := by
  rw [aoyagiLemma5Eq4_specialIncrement_eq_selectedWidth_sub_one
    ell a p M m H ha hp_strict hprev hboundary]
  have hwidth :
      aoyagiSelectedWidthNat ell m (p + (ell - a) + 1) ≤ M - 1 := by
    rw [aoyagiSelectedWidthNat_of_lt (by omega)]
    exact aoyagiSelectedWidth_le_pred_of_sourceSelectedInequality
      ell a M m hell ha hselected hsource ⟨p + (ell - a) + 1, by omega⟩
  omega

/-- Under Definition 3's selected-width inequalities, equation `(4)`'s
special-line increment cannot satisfy Lemma 4's two-value condition. -/
theorem aoyagiLemma5Eq4_specialIncrement_not_twoValue_of_sourceSelected
    (ell a p : ℕ) (M : ℤ) (m H : Fin (ell + 1) → ℤ)
    (hell : 1 ≤ ell) (ha : a ≤ ell) (hp_strict : p + 1 < a)
    (hselected : (∑ j : Fin (ell + 1), m j) = (ell : ℤ) * (M - 1) + a)
    (hsource : ∀ i : Fin (ell + 1),
      (ell : ℤ) * m i < ∑ j : Fin (ell + 1), m j)
    (hprev :
      H ⟨p + (ell - a), by omega⟩ =
        aoyagiHtildeUpperNat ell a M m (p + (ell - a)) - (p : ℤ))
    (hboundary :
      H ⟨p + (ell - a) + 1, by omega⟩ =
        aoyagiHtildeUpperNat ell a M m (p + (ell - a)) - (p : ℤ) + 1) :
    aoyagiLemma4F ell m H ⟨p + (ell - a), by omega⟩ ≠ M - 1 ∧
      aoyagiLemma4F ell m H ⟨p + (ell - a), by omega⟩ ≠ M := by
  have hlt :=
    aoyagiLemma5Eq4_specialIncrement_lt_pred_of_sourceSelected
      ell a p M m H hell ha hp_strict hselected hsource hprev hboundary
  constructor <;> omega

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

/-- In the nonterminal equation `(3)` special-boundary case, raising the
boundary chain value by one forces the next Lemma 4 increment to be `M+1`.

This is finite chain arithmetic for supplied adjacent `H` values.  It does
not construct the displayed vector or prove that those `H` values come from a
source chart. -/
theorem aoyagiLemma5Eq3_specialNextIncrement_eq_succ
    (ell a : ℕ) (M : ℤ) (m H : Fin (ell + 1) → ℤ)
    (ha : a ≤ ell) (ha_two : 2 ≤ a)
    (hboundary :
      H ⟨ell - a + 1, by omega⟩ =
        aoyagiHtildeUpperNat ell a M m (ell - a + 1) + 1)
    (hnext :
      H ⟨ell - a + 2, by omega⟩ =
        aoyagiHtildeUpperNat ell a M m (ell - a + 2)) :
    aoyagiLemma4F ell m H ⟨ell - a + 1, by omega⟩ = M + 1 := by
  have hsucc :=
    aoyagiHtildeUpperNat_succ_eq_add_selectedWidthNat_sub_increment
      ell a (ell - a + 1) M m ha (by omega)
  have hnot : ¬ ell - a + 1 < ell - a := by omega
  rw [if_neg hnot] at hsucc
  unfold aoyagiLemma4F
  change
    H ⟨ell - a + 1, by omega⟩ -
          H ⟨ell - a + 2, by omega⟩ +
        m ⟨ell - a + 2, by omega⟩ =
      M + 1
  rw [hboundary, hnext, hsucc, aoyagiSelectedWidthNat_of_lt (by omega)]
  ring

/-- In the nonterminal equation `(3)` special-boundary case, the next
increment cannot satisfy Lemma 4's two-value condition. -/
theorem aoyagiLemma5Eq3_specialNextIncrement_not_twoValue
    (ell a : ℕ) (M : ℤ) (m H : Fin (ell + 1) → ℤ)
    (ha : a ≤ ell) (ha_two : 2 ≤ a)
    (hboundary :
      H ⟨ell - a + 1, by omega⟩ =
        aoyagiHtildeUpperNat ell a M m (ell - a + 1) + 1)
    (hnext :
      H ⟨ell - a + 2, by omega⟩ =
        aoyagiHtildeUpperNat ell a M m (ell - a + 2)) :
    aoyagiLemma4F ell m H ⟨ell - a + 1, by omega⟩ ≠ M - 1 ∧
      aoyagiLemma4F ell m H ⟨ell - a + 1, by omega⟩ ≠ M := by
  rw [aoyagiLemma5Eq3_specialNextIncrement_eq_succ
    ell a M m H ha ha_two hboundary hnext]
  constructor <;> omega

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

/-- A supplied equation-`(3)`-shaped certificate has the upper endpoint value
on selected block `p` in the rising range.

This is only a component-value consequence of the supplied piecewise
certificate; it is not a source-label legality or terminality theorem. -/
theorem aoyagiLemma5Eq3_piecewise_component_upperEndpoint_of_le_gap
    (ell a p : ℕ) (M : ℤ) (m : Fin (ell + 1) → ℤ)
    (C : AoyagiSelectedCutpoints ell) (layerWidth T : ℕ → ℤ)
    (hp_pos : 1 ≤ p) (hp_c : p ≤ ell - a)
    (hT : AoyagiLemma5Eq3PiecewiseSourceVector ell a M m C layerWidth T) :
    T (C.point p - 1) = aoyagiHtildeUpperNat ell a M m p := by
  have hp_lt_ell : p < ell := by
    have ha : a ≤ ell := hT.a_le_ell
    have ha_pos : 1 ≤ a := hT.indexGuard
    omega
  exact hT.upper p (C.point p - 1) hp_pos hp_c
    (C.leftEndpoint_mem_block hp_lt_ell)

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

/-- Supplied own-coordinate branch data for Aoyagi Lemma 5 equation `(5)`.

Here `p` is the paper's `j_0` in Lean's zero-based selected-coordinate
notation: the own coordinate lies in block `p`, i.e. paper block `j = j_0+1`.
This is not a full equation `(5)` piecewise certificate. -/
structure AoyagiLemma5Eq5OwnCoordinateBranch
    (ell a p alpha : ℕ) (M : ℤ) (m : Fin (ell + 1) → ℤ)
    (C : AoyagiSelectedCutpoints ell) (T : ℕ → ℤ) : Prop where
  a_le_ell : a ≤ ell
  alpha_pos : 1 ≤ alpha
  alpha_lt_p : alpha < p
  alpha_le_excess : alpha ≤ aoyagiLemma5IntervalExcess ell a p
  ownBranch : ∀ S, C.block p S →
    T S = aoyagiHtildeUpperNat ell a M m p - (alpha : ℤ)

/-- Supplied source-layer piecewise data for Aoyagi Lemma 5 equation `(5)`.

This records only the displayed branch values as data.  It is not a
construction of the vector and carries no terminal or chart-coverage claim. -/
structure AoyagiLemma5Eq5PiecewiseSourceVector
    (ell a p alpha : ℕ) (M : ℤ) (m : Fin (ell + 1) → ℤ)
    (C : AoyagiSelectedCutpoints ell) (layerWidth T : ℕ → ℤ) : Prop where
  a_le_ell : a ≤ ell
  alpha_pos : 1 ≤ alpha
  alpha_lt_p : alpha < p
  alpha_le_excess : alpha ≤ aoyagiLemma5IntervalExcess ell a p
  cutoffIndexGuard : p + (a - alpha) + 1 ≤ ell
  first :
    ∀ S, S < C.point 1 - 1 → T S = layerWidth (S + 1)
  preAlpha :
    ∀ b S, 1 ≤ b → b + 2 ≤ alpha → C.block b S →
      T S = aoyagiHtildeUpperNat ell a M m b - (b : ℤ)
  alphaToP :
    ∀ b S, 1 ≤ b → alpha ≤ b + 1 → b + 1 ≤ p → C.block b S →
      T S = aoyagiHtildeUpperNat ell a M m b - (alpha : ℤ) + 1
  postP :
    ∀ b S, p ≤ b → b ≤ p + (a - alpha) → C.block b S →
      T S =
        aoyagiHtildeUpperNat ell a M m b - (alpha : ℤ) + (p : ℤ) - (b : ℤ)
  tail :
    ∀ b S, p + (a - alpha) + 1 ≤ b → C.block b S →
      C.point (p + (a - alpha) + 1) - 1 ≤ S →
        T S = aoyagiHtildeLowerNat ell a M m b

/-- Branch-value alternatives for Aoyagi Lemma 5 equation `(5)` on the
selected span.

This is only a domain/value classification for a supplied piecewise
certificate.  It does not construct the displayed source vector and makes no
terminality, admissibility, chart-coverage, pole-order, normal-crossing, or
RLCT claim. -/
inductive AoyagiLemma5Eq5SelectedSpanBranchValue
    (ell a p alpha : ℕ) (M : ℤ) (m : Fin (ell + 1) → ℤ)
    (C : AoyagiSelectedCutpoints ell) (layerWidth T : ℕ → ℤ) (S : ℕ) : Prop where
  | first
      (hS : S < C.point 1 - 1)
      (hvalue : T S = layerWidth (S + 1))
  | preAlpha
      (b : ℕ) (hb_pos : 1 ≤ b) (hb_pre : b + 2 ≤ alpha)
      (hb : C.block b S)
      (hvalue : T S = aoyagiHtildeUpperNat ell a M m b - (b : ℤ))
  | alphaToP
      (b : ℕ) (hb_pos : 1 ≤ b) (hb_alpha : alpha ≤ b + 1)
      (hb_p : b + 1 ≤ p) (hb : C.block b S)
      (hvalue :
        T S = aoyagiHtildeUpperNat ell a M m b - (alpha : ℤ) + 1)
  | postP
      (b : ℕ) (hb_p : p ≤ b) (hb_hi : b ≤ p + (a - alpha))
      (hb : C.block b S)
      (hvalue :
        T S =
          aoyagiHtildeUpperNat ell a M m b - (alpha : ℤ) + (p : ℤ) - (b : ℤ))
  | tail
      (b : ℕ) (hb_tail : p + (a - alpha) + 1 ≤ b)
      (hb : C.block b S)
      (hS : C.point (p + (a - alpha) + 1) - 1 ≤ S)
      (hvalue : T S = aoyagiHtildeLowerNat ell a M m b)

/-- A supplied equation `(5)` piecewise certificate classifies any selected
block point by one of its advertised branches.

This is half-open block bookkeeping plus the supplied branch equalities. -/
theorem aoyagiLemma5Eq5_branchValue_of_block
    (ell a p alpha : ℕ) (M : ℤ) (m : Fin (ell + 1) → ℤ)
    (C : AoyagiSelectedCutpoints ell) (layerWidth T : ℕ → ℤ)
    (hT : AoyagiLemma5Eq5PiecewiseSourceVector ell a p alpha M m C layerWidth T)
    {b S : ℕ} (hb : C.block b S) :
    AoyagiLemma5Eq5SelectedSpanBranchValue ell a p alpha M m C layerWidth T S := by
  by_cases hb0 : b = 0
  · subst b
    exact AoyagiLemma5Eq5SelectedSpanBranchValue.first
      hb.2.2 (hT.first S hb.2.2)
  have hb_pos : 1 ≤ b := by omega
  by_cases hb_pre : b + 2 ≤ alpha
  · exact AoyagiLemma5Eq5SelectedSpanBranchValue.preAlpha b hb_pos hb_pre hb
      (hT.preAlpha b S hb_pos hb_pre hb)
  have halpha : alpha ≤ b + 1 := by omega
  by_cases hb_p_hi : b + 1 ≤ p
  · exact AoyagiLemma5Eq5SelectedSpanBranchValue.alphaToP
      b hb_pos halpha hb_p_hi hb
      (hT.alphaToP b S hb_pos halpha hb_p_hi hb)
  have hp_le_b : p ≤ b := by omega
  by_cases hb_post : b ≤ p + (a - alpha)
  · exact AoyagiLemma5Eq5SelectedSpanBranchValue.postP b hp_le_b hb_post hb
      (hT.postP b S hp_le_b hb_post hb)
  have hb_tail : p + (a - alpha) + 1 ≤ b := by omega
  have hcut_le_S :
      C.point (p + (a - alpha) + 1) - 1 ≤ S := by
    by_cases hb_eq : b = p + (a - alpha) + 1
    · subst b
      exact hb.2.1
    · have hlt : p + (a - alpha) + 1 < b := by omega
      exact le_of_lt (C.leftEndpoint_lt_of_lt_block hlt hb)
  exact AoyagiLemma5Eq5SelectedSpanBranchValue.tail b hb_tail hb hcut_le_S
    (hT.tail b S hb_tail hb hcut_le_S)

/-- A supplied equation `(5)` piecewise certificate covers every source index in
the selected span by one of its advertised branches.

This is only a selected-span consequence of the block classifier.  It does not
claim coverage before `S_1-1`, at `S_(ell+1)-1`, or after it. -/
theorem aoyagiLemma5Eq5_selectedSpan_branchValue
    (ell a p alpha : ℕ) (M : ℤ) (m : Fin (ell + 1) → ℤ)
    (C : AoyagiSelectedCutpoints ell) (layerWidth T : ℕ → ℤ)
    (hT : AoyagiLemma5Eq5PiecewiseSourceVector ell a p alpha M m C layerWidth T)
    {S : ℕ} (hlo : C.point 0 - 1 ≤ S) (hhi : S < C.point ell - 1) :
    AoyagiLemma5Eq5SelectedSpanBranchValue ell a p alpha M m C layerWidth T S := by
  rcases C.exists_block_of_mem_selectedSpan hlo hhi with ⟨b, hb⟩
  exact aoyagiLemma5Eq5_branchValue_of_block
    ell a p alpha M m C layerWidth T hT hb

/-- A full supplied equation `(5)` piecewise certificate gives the narrower
own-coordinate branch record used by the interval-offset lemmas. -/
theorem aoyagiLemma5Eq5_ownCoordinateBranch_of_piecewiseSourceVector
    (ell a p alpha : ℕ) (M : ℤ) (m : Fin (ell + 1) → ℤ)
    (C : AoyagiSelectedCutpoints ell) (layerWidth T : ℕ → ℤ)
    (hT : AoyagiLemma5Eq5PiecewiseSourceVector ell a p alpha M m C layerWidth T) :
    AoyagiLemma5Eq5OwnCoordinateBranch ell a p alpha M m C T where
  a_le_ell := hT.a_le_ell
  alpha_pos := hT.alpha_pos
  alpha_lt_p := hT.alpha_lt_p
  alpha_le_excess := hT.alpha_le_excess
  ownBranch := by
    intro S hS
    have hvalue := hT.postP p S le_rfl (by omega) hS
    calc
      T S = aoyagiHtildeUpperNat ell a M m p -
          (alpha : ℤ) + (p : ℤ) - (p : ℤ) := hvalue
      _ = aoyagiHtildeUpperNat ell a M m p - (alpha : ℤ) := by ring

/-- A concrete supplied equation `(5)` certificate can put a selected endpoint
below the lower `Htilde` chain even with the current cutoff guard.

For `ell=6`, `a=4`, all selected widths `4`, integer `M=5`, and the printed
equation `(5)` parameters `p=2`, `alpha=1`, the branch at selected coordinate
`4` gives value `-1`, while the lower chain there is `0`.  This is only a
conditional obstruction for supplied branch data; it does not construct the
source vector or assert source-label existence. -/
theorem aoyagiLemma5Eq5_piecewise_belowLowerCounterexample_allWidthsFour
    (C : AoyagiSelectedCutpoints 6) (layerWidth T : ℕ → ℤ)
    (hT : AoyagiLemma5Eq5PiecewiseSourceVector
      6 4 2 1 (5 : ℤ) (fun _ : Fin (6 + 1) => (4 : ℤ)) C layerWidth T) :
    T (C.point 4 - 1) = -1 ∧
      aoyagiHtildeLowerNat 6 4 (5 : ℤ)
        (fun _ : Fin (6 + 1) => (4 : ℤ)) 4 = 0 := by
  constructor
  · have hblock : C.block 4 (C.point 4 - 1) :=
      C.leftEndpoint_mem_block (by norm_num)
    have hvalue := hT.postP 4 (C.point 4 - 1) (by norm_num) (by norm_num) hblock
    simpa [aoyagiHtildeUpperNat, aoyagiHtildeUpperIncrementPrefix,
      aoyagiHtildeUpperHighCount, aoyagiPrefixSum, aoyagiSelectedWidthNat]
      using hvalue
  · norm_num [aoyagiHtildeLowerNat, aoyagiHtildeLowerIncrementPrefix,
      aoyagiHtildeLowerHighCount, aoyagiPrefixSum, aoyagiSelectedWidthNat,
      Finset.sum_range_succ]

/-- The all-widths-four supplied equation `(5)` counterexample is strictly
below the lower `Htilde` chain at selected coordinate `4`. -/
theorem aoyagiLemma5Eq5_piecewise_not_lowerBounded_allWidthsFour
    (C : AoyagiSelectedCutpoints 6) (layerWidth T : ℕ → ℤ)
    (hT : AoyagiLemma5Eq5PiecewiseSourceVector
      6 4 2 1 (5 : ℤ) (fun _ : Fin (6 + 1) => (4 : ℤ)) C layerWidth T) :
    T (C.point 4 - 1) <
      aoyagiHtildeLowerNat 6 4 (5 : ℤ)
        (fun _ : Fin (6 + 1) => (4 : ℤ)) 4 := by
  have h :=
    aoyagiLemma5Eq5_piecewise_belowLowerCounterexample_allWidthsFour C layerWidth T hT
  omega

/-- The finite offset values realised by equation `(5)`'s own-coordinate
branch under the source guard `1 <= alpha < p` and same-coordinate interval
guard `alpha <= Htilde'_p-Htilde_p`. -/
def aoyagiLemma5Eq5OffsetValueSet
    (ell a p : ℕ) (M : ℤ) (m : Fin (ell + 1) → ℤ) : Finset ℤ :=
  (Finset.Icc 1 (min (aoyagiLemma5IntervalExcess ell a p) (p - 1))).image
    (fun alpha : ℕ ↦ aoyagiHtildeUpperNat ell a M m p - (alpha : ℤ))

/-- Offsets below a fixed upper endpoint give distinct integer values. -/
theorem aoyagiLemma5Eq5_offsetValue_injective
    (ell a p : ℕ) (M : ℤ) (m : Fin (ell + 1) → ℤ) :
    Function.Injective
      (fun alpha : ℕ ↦ aoyagiHtildeUpperNat ell a M m p - (alpha : ℤ)) := by
  intro alpha beta h
  have hcast : (alpha : ℤ) = (beta : ℤ) := by
    linarith
  exact_mod_cast hcast

/-- The equation `(5)` offset-value set has the expected finite cardinality.

This is only a count of supplied same-coordinate offset values.  It is not a
chart-family count or a proof of Aoyagi Lemma 5. -/
theorem aoyagiLemma5Eq5OffsetValueSet_card
    (ell a p : ℕ) (M : ℤ) (m : Fin (ell + 1) → ℤ) :
    (aoyagiLemma5Eq5OffsetValueSet ell a p M m).card =
      min (aoyagiLemma5IntervalExcess ell a p) (p - 1) := by
  unfold aoyagiLemma5Eq5OffsetValueSet
  rw [Finset.card_image_of_injOn]
  · rw [Nat.card_Icc]
    omega
  · intro x _ y _ hxy
    exact aoyagiLemma5Eq5_offsetValue_injective ell a p M m hxy

/-- In the rising region, the strict equation `(5)` offsets have cardinality
`p-1`.

This is only the count of the strict offset values `1<=alpha<p` after the
interval excess has simplified to `p`.  It is not a displayed-vector
construction, source-label legality theorem, or Lemma 5 order count. -/
theorem aoyagiLemma5Eq5OffsetValueSet_card_eq_pred_of_le_min
    (ell a p : ℕ) (M : ℤ) (m : Fin (ell + 1) → ℤ)
    (ha : a ≤ ell) (hp_pos : 1 ≤ p) (hp_a : p ≤ a) (hp_c : p ≤ ell - a) :
    (aoyagiLemma5Eq5OffsetValueSet ell a p M m).card = p - 1 := by
  rw [aoyagiLemma5Eq5OffsetValueSet_card]
  have hexcess :
      aoyagiLemma5IntervalExcess ell a p = p :=
    aoyagiLemma5IntervalExcess_eq_self_of_le_min ell a p ha hp_a hp_c
  rw [hexcess]
  exact Nat.min_eq_right (by omega)

/-- Decompose one interval excess into the equation `(5)` offset count and the
remaining rising-coordinate contribution.

The offset set counts the values `Htilde'_p-alpha` with `1<=alpha<p`.  If the
interval excess is still rising at coordinate `p`, namely
`1<=p`, `p<=a`, and `p<=ell-a`, the lower endpoint contributes one additional
value not seen by those strict offsets.  This is finite count bookkeeping only;
it does not construct any displayed vector or prove Aoyagi Lemma 5. -/
theorem aoyagiLemma5IntervalExcess_eq_eq5OffsetCard_add_risingIndicator
    (ell a p : ℕ) (M : ℤ) (m : Fin (ell + 1) → ℤ) (ha : a ≤ ell) :
    aoyagiLemma5IntervalExcess ell a p =
      (aoyagiLemma5Eq5OffsetValueSet ell a p M m).card +
        if 1 ≤ p ∧ p ≤ a ∧ p ≤ ell - a then 1 else 0 := by
  rw [aoyagiLemma5Eq5OffsetValueSet_card]
  by_cases h : 1 ≤ p ∧ p ≤ a ∧ p ≤ ell - a
  · rw [if_pos h]
    have he : aoyagiLemma5IntervalExcess ell a p = p :=
      aoyagiLemma5IntervalExcess_eq_self_of_le_min ell a p ha h.2.1 h.2.2
    rw [he]
    have hmin : min p (p - 1) = p - 1 := Nat.min_eq_right (Nat.sub_le p 1)
    rw [hmin]
    omega
  · rw [if_neg h]
    have hle : aoyagiLemma5IntervalExcess ell a p ≤ p - 1 := by
      by_cases hp : 1 ≤ p
      · by_cases hpa : p ≤ a
        · have hpc_not : ¬ p ≤ ell - a := by
            intro hpc
            exact h ⟨hp, hpa, hpc⟩
          have he_le_inner :
              aoyagiLemma5IntervalExcess ell a p ≤ min a (ell - a) := by
            unfold aoyagiLemma5IntervalExcess
            exact le_trans
              (Nat.min_le_right p (min (ell - p) (min a (ell - a))))
              (Nat.min_le_right (ell - p) (min a (ell - a)))
          have he_le : aoyagiLemma5IntervalExcess ell a p ≤ ell - a :=
            le_trans he_le_inner (Nat.min_le_right a (ell - a))
          omega
        · have he_le_inner :
              aoyagiLemma5IntervalExcess ell a p ≤ min a (ell - a) := by
            unfold aoyagiLemma5IntervalExcess
            exact le_trans
              (Nat.min_le_right p (min (ell - p) (min a (ell - a))))
              (Nat.min_le_right (ell - p) (min a (ell - a)))
          have he_le : aoyagiLemma5IntervalExcess ell a p ≤ a :=
            le_trans he_le_inner (Nat.min_le_left a (ell - a))
          omega
      · have hp0 : p = 0 := by omega
        simp [aoyagiLemma5IntervalExcess, hp0]
    rw [Nat.min_eq_left hle]
    omega

/-- The interval excess equals the coordinate index exactly in the rising
region `p<=a` and `p<=ell-a`.

This is finite arithmetic only. -/
theorem aoyagiLemma5IntervalExcess_eq_self_iff_le_min
    (ell a p : ℕ) (ha : a ≤ ell) :
    aoyagiLemma5IntervalExcess ell a p = p ↔
      p ≤ a ∧ p ≤ ell - a := by
  constructor
  · intro h
    have hle_a : aoyagiLemma5IntervalExcess ell a p ≤ a := by
      unfold aoyagiLemma5IntervalExcess
      exact le_trans
        (Nat.min_le_right p (min (ell - p) (min a (ell - a))))
        (le_trans (Nat.min_le_right (ell - p) (min a (ell - a)))
          (Nat.min_le_left a (ell - a)))
    have hle_c : aoyagiLemma5IntervalExcess ell a p ≤ ell - a := by
      unfold aoyagiLemma5IntervalExcess
      exact le_trans
        (Nat.min_le_right p (min (ell - p) (min a (ell - a))))
        (le_trans (Nat.min_le_right (ell - p) (min a (ell - a)))
          (Nat.min_le_right a (ell - a)))
    omega
  · rintro ⟨hp_a, hp_c⟩
    exact aoyagiLemma5IntervalExcess_eq_self_of_le_min ell a p ha hp_a hp_c

/-- Outside the rising region, the interval excess is at most `p-1`.

This is the arithmetic condition under which Eq5 strict offsets already reach
the lower endpoint. -/
theorem aoyagiLemma5IntervalExcess_le_pred_of_not_le_min
    (ell a p : ℕ) (ha : a ≤ ell) (hp_pos : 1 ≤ p)
    (hnot : ¬ (p ≤ a ∧ p ≤ ell - a)) :
    aoyagiLemma5IntervalExcess ell a p ≤ p - 1 := by
  have hle_p : aoyagiLemma5IntervalExcess ell a p ≤ p := by
    unfold aoyagiLemma5IntervalExcess
    exact Nat.min_le_left p (min (ell - p) (min a (ell - a)))
  have hne : aoyagiLemma5IntervalExcess ell a p ≠ p := by
    intro h
    exact hnot ((aoyagiLemma5IntervalExcess_eq_self_iff_le_min ell a p ha).mp h)
  omega

/-- The same-coordinate interval size is the Eq5 strict-offset count plus the
endpoint deficit.

Eq5 always has an upper-endpoint deficit.  It has one additional
lower-endpoint deficit in the rising region `1<=p`, `p<=a`, `p<=ell-a`.
This is only finite count bookkeeping, not a source branch-family count. -/
theorem aoyagiLemma5Eq5_intervalCard_eq_offsetCard_add_endpointDeficit
    (ell a p : ℕ) (M : ℤ) (m : Fin (ell + 1) → ℤ)
    (ha : a ≤ ell) (hp : p < ell + 1) :
    (aoyagiHtildeIntervalValueSetNat ell a M m p).card =
      (aoyagiLemma5Eq5OffsetValueSet ell a p M m).card + 1 +
        if 1 ≤ p ∧ p ≤ a ∧ p ≤ ell - a then 1 else 0 := by
  have h :=
    aoyagiLemma5IntervalExcess_eq_eq5OffsetCard_add_risingIndicator
      ell a p M m ha
  rw [aoyagiHtildeIntervalValueSetNat_card_of_lt ell a M m p hp]
  simp [aoyagiLemma5IntervalSize]
  omega

/-- Alias with the older `endpointDefect` spelling. -/
theorem aoyagiLemma5Eq5_intervalCard_eq_offsetCard_add_endpointDefect
    (ell a p : ℕ) (M : ℤ) (m : Fin (ell + 1) → ℤ)
    (ha : a ≤ ell) (hp : p < ell + 1) :
    (aoyagiHtildeIntervalValueSetNat ell a M m p).card =
      (aoyagiLemma5Eq5OffsetValueSet ell a p M m).card + 1 +
        if 1 ≤ p ∧ p ≤ a ∧ p ≤ ell - a then 1 else 0 :=
  aoyagiLemma5Eq5_intervalCard_eq_offsetCard_add_endpointDeficit
    ell a p M m ha hp

/-- In the rising part of the interval, the lower endpoint is not one of the
strict Eq5 offset values.

Under `p<=a` and `p<=ell-a`, the interval excess is `p`; reaching the lower
endpoint from `Htilde'_p` would require offset `alpha=p`, while equation `(5)`
uses only strict offsets `alpha<p`.  This identifies the extra contribution in
`aoyagiLemma5IntervalExcess_eq_eq5OffsetCard_add_risingIndicator` as set
bookkeeping, not as a source-vector construction. -/
theorem aoyagiLemma5Eq5_lowerEndpoint_not_mem_offsetValueSet_of_le_min
    (ell a p : ℕ) (M : ℤ) (m : Fin (ell + 1) → ℤ)
    (ha : a ≤ ell) (hp_a : p ≤ a) (hp_c : p ≤ ell - a) :
    aoyagiHtildeLowerNat ell a M m p ∉
      aoyagiLemma5Eq5OffsetValueSet ell a p M m := by
  intro hmem
  rw [aoyagiLemma5Eq5OffsetValueSet, Finset.mem_image] at hmem
  rcases hmem with ⟨alpha, halpha, hvalue⟩
  rw [Finset.mem_Icc] at halpha
  have hp_lt : p < ell + 1 := by omega
  have hgap := aoyagiHtildeUpper_sub_lower_eq_intervalExcess
    ell a M m ha ⟨p, hp_lt⟩
  have hexcess : aoyagiLemma5IntervalExcess ell a p = p :=
    aoyagiLemma5IntervalExcess_eq_self_of_le_min ell a p ha hp_a hp_c
  simp [aoyagiHtildeLowerChain, aoyagiHtildeUpperChain, hexcess] at hgap
  have halpha_eq : alpha = p := by
    have hcast : (alpha : ℤ) = (p : ℤ) := by
      linarith
    exact_mod_cast hcast
  have halpha_le : alpha ≤ p - 1 := by
    simpa [hexcess] using halpha.2
  omega

/-- The lower endpoint belongs to the same-coordinate interval value set.

This is finite interval bookkeeping only.  It does not assert that the lower
endpoint is realised by any displayed source vector. -/
theorem aoyagiLemma5Eq5_lowerEndpoint_mem_intervalValueSetNat_of_lt
    (ell a p : ℕ) (M : ℤ) (m : Fin (ell + 1) → ℤ)
    (ha : a ≤ ell) (hp : p < ell + 1) :
    aoyagiHtildeLowerNat ell a M m p ∈
      aoyagiHtildeIntervalValueSetNat ell a M m p := by
  rw [aoyagiHtildeIntervalValueSetNat]
  simp only [hp, ↓reduceDIte]
  rw [aoyagiHtilde_mem_intervalValueSet_iff_bounds
    ell a M m ha ⟨p, hp⟩]
  constructor
  · rfl
  · simpa [aoyagiHtildeLowerChain] using
      (aoyagiHtildeLowerChain_le_upperChain ell a M m ha ⟨p, hp⟩)

/-- The upper endpoint belongs to the same-coordinate interval value set.

This is finite interval bookkeeping only. -/
theorem aoyagiLemma5Eq5_upperEndpoint_mem_intervalValueSetNat_of_lt
    (ell a p : ℕ) (M : ℤ) (m : Fin (ell + 1) → ℤ)
    (ha : a ≤ ell) (hp : p < ell + 1) :
    aoyagiHtildeUpperNat ell a M m p ∈
      aoyagiHtildeIntervalValueSetNat ell a M m p := by
  rw [aoyagiHtildeIntervalValueSetNat]
  simp only [hp, ↓reduceDIte]
  rw [aoyagiHtilde_mem_intervalValueSet_iff_bounds
    ell a M m ha ⟨p, hp⟩]
  constructor
  · simpa [aoyagiHtildeLowerChain, aoyagiHtildeUpperChain] using
      (aoyagiHtildeLowerChain_le_upperChain ell a M m ha ⟨p, hp⟩)
  · rfl

/-- In the rising region, the strict equation `(5)` offset values plus the
lower endpoint have cardinality equal to the interval excess.

The full same-coordinate interval has one further value, the upper endpoint.
This theorem is count bookkeeping only; it does not say that the inserted lower
endpoint is realised by equation `(3)` or `(4)`. -/
theorem aoyagiLemma5Eq5_insert_lowerEndpoint_offsetValueSet_card_of_le_min
    (ell a p : ℕ) (M : ℤ) (m : Fin (ell + 1) → ℤ)
    (ha : a ≤ ell) (hp_pos : 1 ≤ p) (hp_a : p ≤ a) (hp_c : p ≤ ell - a) :
    (insert (aoyagiHtildeLowerNat ell a M m p)
        (aoyagiLemma5Eq5OffsetValueSet ell a p M m)).card =
      aoyagiLemma5IntervalExcess ell a p := by
  rw [Finset.card_insert_of_notMem
    (aoyagiLemma5Eq5_lowerEndpoint_not_mem_offsetValueSet_of_le_min
      ell a p M m ha hp_a hp_c)]
  rw [aoyagiLemma5Eq5OffsetValueSet_card]
  have hexcess :
      aoyagiLemma5IntervalExcess ell a p = p :=
    aoyagiLemma5IntervalExcess_eq_self_of_le_min ell a p ha hp_a hp_c
  rw [hexcess]
  rw [Nat.min_eq_right (Nat.sub_le p 1)]
  omega

/-- Every equation `(5)` offset value is a same-coordinate interval value. -/
theorem aoyagiLemma5Eq5OffsetValueSet_subset_intervalValueSetNat
    (ell a p : ℕ) (M : ℤ) (m : Fin (ell + 1) → ℤ)
    (ha : a ≤ ell) (hp : p < ell + 1) :
    aoyagiLemma5Eq5OffsetValueSet ell a p M m ⊆
      aoyagiHtildeIntervalValueSetNat ell a M m p := by
  intro z hz
  rw [aoyagiLemma5Eq5OffsetValueSet, Finset.mem_image] at hz
  rcases hz with ⟨alpha, halpha, rfl⟩
  rw [Finset.mem_Icc] at halpha
  rw [aoyagiHtildeIntervalValueSetNat]
  simp only [hp, ↓reduceDIte]
  rw [aoyagiHtilde_mem_intervalValueSet_iff_bounds ell a M m ha ⟨p, hp⟩]
  have hgap :=
    aoyagiHtildeUpper_sub_lower_eq_intervalExcess ell a M m ha ⟨p, hp⟩
  simp [aoyagiHtildeLowerChain, aoyagiHtildeUpperChain] at hgap
  change
    aoyagiHtildeLowerNat ell a M m p ≤
        aoyagiHtildeUpperNat ell a M m p - (alpha : ℤ) ∧
      aoyagiHtildeUpperNat ell a M m p - (alpha : ℤ) ≤
      aoyagiHtildeUpperNat ell a M m p
  constructor <;> omega

/-- The Eq5 strict offset set never contains the upper endpoint.

The upper endpoint would require offset `alpha=0`, while equation `(5)` uses
only offsets with `1<=alpha`. -/
theorem aoyagiLemma5Eq5_upperEndpoint_not_mem_offsetValueSet
    (ell a p : ℕ) (M : ℤ) (m : Fin (ell + 1) → ℤ) :
    aoyagiHtildeUpperNat ell a M m p ∉
      aoyagiLemma5Eq5OffsetValueSet ell a p M m := by
  intro hmem
  rw [aoyagiLemma5Eq5OffsetValueSet, Finset.mem_image] at hmem
  rcases hmem with ⟨alpha, halpha, hvalue⟩
  rw [Finset.mem_Icc] at halpha
  have halpha_zero : (alpha : ℤ) = 0 := by
    linarith
  omega

/-- When the interval excess is at most `p-1`, Eq5 strict offsets are exactly
the same-coordinate interval with the upper endpoint erased.

This is the finite-set complement of the rising-region theorem, where Eq5
also misses the lower endpoint.  It is not a source construction or legality
theorem for the displayed vectors. -/
theorem aoyagiLemma5Eq5_offsets_eq_interval_erase_upper_of_excess_le_pred
    (ell a p : ℕ) (M : ℤ) (m : Fin (ell + 1) → ℤ)
    (ha : a ≤ ell) (hp : p < ell + 1)
    (hexcess_le : aoyagiLemma5IntervalExcess ell a p ≤ p - 1) :
    aoyagiLemma5Eq5OffsetValueSet ell a p M m =
      (aoyagiHtildeIntervalValueSetNat ell a M m p).erase
        (aoyagiHtildeUpperNat ell a M m p) := by
  apply Finset.eq_of_subset_of_card_le
  · intro z hz
    rw [Finset.mem_erase]
    constructor
    · intro hz_upper
      exact aoyagiLemma5Eq5_upperEndpoint_not_mem_offsetValueSet
        ell a p M m (by rwa [hz_upper] at hz)
    · exact aoyagiLemma5Eq5OffsetValueSet_subset_intervalValueSetNat
        ell a p M m ha hp hz
  · have hupper_mem :
        aoyagiHtildeUpperNat ell a M m p ∈
          aoyagiHtildeIntervalValueSetNat ell a M m p :=
      aoyagiLemma5Eq5_upperEndpoint_mem_intervalValueSetNat_of_lt
        ell a p M m ha hp
    have hcard_erase :
        ((aoyagiHtildeIntervalValueSetNat ell a M m p).erase
            (aoyagiHtildeUpperNat ell a M m p)).card =
          aoyagiLemma5IntervalExcess ell a p := by
      have h := Finset.card_erase_add_one hupper_mem
      rw [aoyagiHtildeIntervalValueSetNat_card_of_lt ell a M m p hp] at h
      simp [aoyagiLemma5IntervalSize] at h
      omega
    rw [hcard_erase]
    rw [aoyagiLemma5Eq5OffsetValueSet_card]
    exact Nat.le_of_eq (Nat.min_eq_left hexcess_le).symm

/-- A supplied upper endpoint fills the same-coordinate interval together with
the Eq5 strict offsets in the non-rising case `excess<=p-1`.

This is finite supplied-data bookkeeping.  It does not assert that equation
`(3)` or any other displayed source branch legally supplies the upper
endpoint. -/
theorem aoyagiLemma5_suppliedUpper_Eq5_offsets_eq_intervalValueSetNat_of_excess_le_pred
    (ell a p : ℕ) (M : ℤ) (m : Fin (ell + 1) → ℤ)
    (C : AoyagiSelectedCutpoints ell) (Tupper : ℕ → ℤ)
    (ha : a ≤ ell) (hp : p < ell + 1)
    (hexcess_le : aoyagiLemma5IntervalExcess ell a p ≤ p - 1)
    (hupper :
      Tupper (C.point p - 1) = aoyagiHtildeUpperNat ell a M m p) :
    insert (Tupper (C.point p - 1))
        (aoyagiLemma5Eq5OffsetValueSet ell a p M m) =
      aoyagiHtildeIntervalValueSetNat ell a M m p := by
  have hEq :=
    aoyagiLemma5Eq5_offsets_eq_interval_erase_upper_of_excess_le_pred
      ell a p M m ha hp hexcess_le
  have hupper_mem :
      aoyagiHtildeUpperNat ell a M m p ∈
        aoyagiHtildeIntervalValueSetNat ell a M m p :=
    aoyagiLemma5Eq5_upperEndpoint_mem_intervalValueSetNat_of_lt
      ell a p M m ha hp
  calc
    insert (Tupper (C.point p - 1))
        (aoyagiLemma5Eq5OffsetValueSet ell a p M m)
        =
          insert (aoyagiHtildeUpperNat ell a M m p)
            ((aoyagiHtildeIntervalValueSetNat ell a M m p).erase
              (aoyagiHtildeUpperNat ell a M m p)) := by
            rw [hEq, hupper]
    _ = aoyagiHtildeIntervalValueSetNat ell a M m p :=
      Finset.insert_erase hupper_mem

/-- In the plateau part with `a<p<=ell-a`, a supplied Eq3-shaped upper
component and the Eq5 strict offsets fill the same-coordinate interval.

This uses only the component value from the supplied Eq3-shaped certificate.
It does not prove source-label legality, terminality, chart coverage, or the
full Lemma 5 order count. -/
theorem aoyagiLemma5_suppliedEq3Upper_Eq5_offsets_eq_intervalValueSetNat_of_plateau
    (ell a p : ℕ) (M : ℤ) (m : Fin (ell + 1) → ℤ)
    (C : AoyagiSelectedCutpoints ell) (layerWidth3 T3 : ℕ → ℤ)
    (hp_pos : 1 ≤ p) (ha_lt_p : a < p) (hp_c : p ≤ ell - a)
    (hT3 : AoyagiLemma5Eq3PiecewiseSourceVector ell a M m C layerWidth3 T3) :
    insert (T3 (C.point p - 1))
        (aoyagiLemma5Eq5OffsetValueSet ell a p M m) =
      aoyagiHtildeIntervalValueSetNat ell a M m p := by
  have hp : p < ell + 1 := by
    have ha : a ≤ ell := hT3.a_le_ell
    omega
  have hexcess_le_a : aoyagiLemma5IntervalExcess ell a p ≤ a := by
    unfold aoyagiLemma5IntervalExcess
    exact le_trans
      (Nat.min_le_right p (min (ell - p) (min a (ell - a))))
      (le_trans (Nat.min_le_right (ell - p) (min a (ell - a)))
        (Nat.min_le_left a (ell - a)))
  have hexcess_le :
      aoyagiLemma5IntervalExcess ell a p ≤ p - 1 := by
    omega
  have hupper :=
    aoyagiLemma5Eq3_piecewise_component_upperEndpoint_of_le_gap
      ell a p M m C layerWidth3 T3 hp_pos hp_c hT3
  exact
    aoyagiLemma5_suppliedUpper_Eq5_offsets_eq_intervalValueSetNat_of_excess_le_pred
      ell a p M m C T3 hT3.a_le_ell hp hexcess_le hupper

/-- Alias with the word `Component`, parallel to the rising-region wrapper. -/
theorem aoyagiLemma5_suppliedEq3UpperComponent_Eq5_offsets_eq_intervalValueSetNat_of_plateau
    (ell a p : ℕ) (M : ℤ) (m : Fin (ell + 1) → ℤ)
    (C : AoyagiSelectedCutpoints ell) (layerWidth3 T3 : ℕ → ℤ)
    (hp_pos : 1 ≤ p) (ha_lt_p : a < p) (hp_c : p ≤ ell - a)
    (hT3 : AoyagiLemma5Eq3PiecewiseSourceVector ell a M m C layerWidth3 T3) :
    insert (T3 (C.point p - 1))
        (aoyagiLemma5Eq5OffsetValueSet ell a p M m) =
      aoyagiHtildeIntervalValueSetNat ell a M m p :=
  aoyagiLemma5_suppliedEq3Upper_Eq5_offsets_eq_intervalValueSetNat_of_plateau
    ell a p M m C layerWidth3 T3 hp_pos ha_lt_p hp_c hT3

/-- In the rising region, the lower endpoint together with the strict equation
`(5)` offset values is contained in the same-coordinate interval.

This is only a set-level inclusion for counted values, not a displayed-vector
construction or legality theorem. -/
theorem aoyagiLemma5Eq5_insert_lowerEndpoint_offsetValueSet_subset_intervalValueSetNat_of_le_min
    (ell a p : ℕ) (M : ℤ) (m : Fin (ell + 1) → ℤ)
    (ha : a ≤ ell) (hp_a : p ≤ a) (hp_c : p ≤ ell - a) :
    insert (aoyagiHtildeLowerNat ell a M m p)
        (aoyagiLemma5Eq5OffsetValueSet ell a p M m) ⊆
      aoyagiHtildeIntervalValueSetNat ell a M m p := by
  have hp_lt : p < ell + 1 := by
    have _hp_c : p ≤ ell - a := hp_c
    omega
  intro z hz
  rw [Finset.mem_insert] at hz
  rcases hz with hz | hz
  · subst z
    exact aoyagiLemma5Eq5_lowerEndpoint_mem_intervalValueSetNat_of_lt
      ell a p M m ha hp_lt
  · exact aoyagiLemma5Eq5OffsetValueSet_subset_intervalValueSetNat
      ell a p M m ha hp_lt hz

/-- In the rising region, the strict equation `(5)` offset values plus the
lower endpoint account for all but one value in the same-coordinate interval.

The extra value is not identified here.  This theorem is a cardinality bridge,
not a construction of Aoyagi's displayed vector family. -/
theorem aoyagiLemma5Eq5_insertLower_offsetCard_add_one_eq_intervalCard_of_le_min
    (ell a p : ℕ) (M : ℤ) (m : Fin (ell + 1) → ℤ)
    (ha : a ≤ ell) (hp_pos : 1 ≤ p) (hp_a : p ≤ a) (hp_c : p ≤ ell - a) :
    (insert (aoyagiHtildeLowerNat ell a M m p)
        (aoyagiLemma5Eq5OffsetValueSet ell a p M m)).card + 1 =
      (aoyagiHtildeIntervalValueSetNat ell a M m p).card := by
  rw [aoyagiLemma5Eq5_insert_lowerEndpoint_offsetValueSet_card_of_le_min
    ell a p M m ha hp_pos hp_a hp_c]
  rw [aoyagiHtildeIntervalValueSetNat_card_of_lt ell a M m p (by omega)]
  simp [aoyagiLemma5IntervalSize]
  omega

/-- In the rising region, the upper endpoint is not among the lower endpoint
and strict equation `(5)` offset values.

The strict offsets stop at `alpha=p-1`, while the lower endpoint corresponds
to `alpha=p`; neither gives the upper endpoint, which would require
`alpha=0`. -/
theorem aoyagiLemma5Eq5_upperEndpoint_not_mem_insert_lowerEndpoint_offsets_of_le_min
    (ell a p : ℕ) (M : ℤ) (m : Fin (ell + 1) → ℤ)
    (ha : a ≤ ell) (hp_pos : 1 ≤ p) (hp_a : p ≤ a) (hp_c : p ≤ ell - a) :
    aoyagiHtildeUpperNat ell a M m p ∉
      insert (aoyagiHtildeLowerNat ell a M m p)
        (aoyagiLemma5Eq5OffsetValueSet ell a p M m) := by
  intro hmem
  rw [Finset.mem_insert] at hmem
  rcases hmem with h_eq_lower | h_offset
  · have hgap :=
      aoyagiHtildeUpper_sub_lower_eq_intervalExcess
        ell a M m ha ⟨p, by omega⟩
    have hexcess :
        aoyagiLemma5IntervalExcess ell a p = p :=
      aoyagiLemma5IntervalExcess_eq_self_of_le_min ell a p ha hp_a hp_c
    simp [aoyagiHtildeLowerChain, aoyagiHtildeUpperChain, hexcess] at hgap
    omega
  · rw [aoyagiLemma5Eq5OffsetValueSet, Finset.mem_image] at h_offset
    rcases h_offset with ⟨alpha, halpha, hvalue⟩
    rw [Finset.mem_Icc] at halpha
    have halpha_zero : (alpha : ℤ) = 0 := by
      linarith
    omega

/-- In the rising region, the lower endpoint plus the strict equation `(5)`
offset values are exactly the same-coordinate interval with the upper endpoint
erased.

This identifies the one value not represented by this finite Eq5 count
scaffold.  It is not a construction or legality theorem for Aoyagi's displayed
vectors. -/
theorem aoyagiLemma5Eq5_insertLower_offsets_eq_interval_erase_upper_of_le_min
    (ell a p : ℕ) (M : ℤ) (m : Fin (ell + 1) → ℤ)
    (ha : a ≤ ell) (hp_pos : 1 ≤ p) (hp_a : p ≤ a) (hp_c : p ≤ ell - a) :
    insert (aoyagiHtildeLowerNat ell a M m p)
        (aoyagiLemma5Eq5OffsetValueSet ell a p M m) =
      (aoyagiHtildeIntervalValueSetNat ell a M m p).erase
        (aoyagiHtildeUpperNat ell a M m p) := by
  apply Finset.eq_of_subset_of_card_le
  · intro z hz
    rw [Finset.mem_erase]
    constructor
    · intro hz_upper
      exact
        aoyagiLemma5Eq5_upperEndpoint_not_mem_insert_lowerEndpoint_offsets_of_le_min
          ell a p M m ha hp_pos hp_a hp_c (by rwa [hz_upper] at hz)
    · exact
        aoyagiLemma5Eq5_insert_lowerEndpoint_offsetValueSet_subset_intervalValueSetNat_of_le_min
          ell a p M m ha hp_a hp_c hz
  · have hupper_mem :
        aoyagiHtildeUpperNat ell a M m p ∈
          aoyagiHtildeIntervalValueSetNat ell a M m p :=
      aoyagiLemma5Eq5_upperEndpoint_mem_intervalValueSetNat_of_lt
        ell a p M m ha (by omega)
    have hcard_insert :=
      aoyagiLemma5Eq5_insertLower_offsetCard_add_one_eq_intervalCard_of_le_min
        ell a p M m ha hp_pos hp_a hp_c
    have hcard_erase :=
      Finset.card_erase_add_one hupper_mem
    omega

/-- In the rising region, the strict equation `(5)` offset values are exactly
the same-coordinate interval with both endpoints erased.

This is only finite-set bookkeeping.  It does not assert that the erased
endpoints are realised by equation `(3)` or `(4)`, or construct any displayed
source vector. -/
theorem aoyagiLemma5Eq5_offsets_eq_interval_erase_endpoints_of_le_min
    (ell a p : ℕ) (M : ℤ) (m : Fin (ell + 1) → ℤ)
    (ha : a ≤ ell) (hp_pos : 1 ≤ p) (hp_a : p ≤ a) (hp_c : p ≤ ell - a) :
    aoyagiLemma5Eq5OffsetValueSet ell a p M m =
      ((aoyagiHtildeIntervalValueSetNat ell a M m p).erase
        (aoyagiHtildeUpperNat ell a M m p)).erase
          (aoyagiHtildeLowerNat ell a M m p) := by
  ext z
  constructor
  · intro hz
    rw [Finset.mem_erase]
    constructor
    · exact fun hz_lower =>
        aoyagiLemma5Eq5_lowerEndpoint_not_mem_offsetValueSet_of_le_min
          ell a p M m ha hp_a hp_c (by simpa [hz_lower] using hz)
    · rw [← aoyagiLemma5Eq5_insertLower_offsets_eq_interval_erase_upper_of_le_min
        ell a p M m ha hp_pos hp_a hp_c]
      exact Finset.mem_insert_of_mem hz
  · intro hz
    rw [Finset.mem_erase] at hz
    rw [← aoyagiLemma5Eq5_insertLower_offsets_eq_interval_erase_upper_of_le_min
        ell a p M m ha hp_pos hp_a hp_c] at hz
    rw [Finset.mem_insert] at hz
    rcases hz.2 with hz_lower | hz_offset
    · exact False.elim (hz.1 hz_lower)
    · exact hz_offset

/-- Every positive coordinate falls into one of the two Eq5 endpoint-deficit
set cases.

Outside the rising region, Eq5 offsets are the interval with only the upper
endpoint erased.  In the rising region, Eq5 offsets are the interval with both
upper and lower endpoints erased.  This is an obligation split for later
supplied endpoint realisation; it is not a source coverage theorem. -/
theorem aoyagiLemma5Eq5_offsets_endpointDeficit_split
    (ell a p : ℕ) (M : ℤ) (m : Fin (ell + 1) → ℤ)
    (ha : a ≤ ell) (hp_pos : 1 ≤ p) (hp : p < ell + 1) :
    aoyagiLemma5Eq5OffsetValueSet ell a p M m =
        (aoyagiHtildeIntervalValueSetNat ell a M m p).erase
          (aoyagiHtildeUpperNat ell a M m p) ∨
      (p ≤ a ∧ p ≤ ell - a ∧
        aoyagiLemma5Eq5OffsetValueSet ell a p M m =
          ((aoyagiHtildeIntervalValueSetNat ell a M m p).erase
            (aoyagiHtildeUpperNat ell a M m p)).erase
              (aoyagiHtildeLowerNat ell a M m p)) := by
  by_cases hrising : p ≤ a ∧ p ≤ ell - a
  · right
    exact ⟨hrising.1, hrising.2,
      aoyagiLemma5Eq5_offsets_eq_interval_erase_endpoints_of_le_min
        ell a p M m ha hp_pos hrising.1 hrising.2⟩
  · left
    have hexcess_le :=
      aoyagiLemma5IntervalExcess_le_pred_of_not_le_min
        ell a p ha hp_pos hrising
    exact aoyagiLemma5Eq5_offsets_eq_interval_erase_upper_of_excess_le_pred
      ell a p M m ha hp hexcess_le

/-- A supplied equation `(4)` own-coordinate value supplies the lower endpoint
in the Eq5 lower-plus-strict-offset finite set.

This rewrites the abstract lower endpoint in
`aoyagiLemma5Eq5_insertLower_offsets_eq_interval_erase_upper_of_le_min` using
the supplied Eq4 own-coordinate value.  It is not a construction or legality
theorem for Aoyagi's displayed vectors. -/
theorem aoyagiLemma5Eq4_insertOwnCoordinate_eq5Offsets_eq_interval_erase_upper_of_le_min
    (ell a p : ℕ) (M : ℤ) (m : Fin (ell + 1) → ℤ)
    (C : AoyagiSelectedCutpoints ell) (layerWidth T : ℕ → ℤ)
    (hell : 1 ≤ ell) (hp_pos : 1 ≤ p) (hp_a : p ≤ a) (hp_c : p ≤ ell - a)
    (hselected : (∑ j : Fin (ell + 1), m j) = (ell : ℤ) * (M - 1) + a)
    (hsource : ∀ i : Fin (ell + 1),
      (ell : ℤ) * m i < ∑ j : Fin (ell + 1), m j)
    (hT : AoyagiLemma5Eq4PiecewiseSourceVector ell a p M m C layerWidth T) :
    insert (T (C.point p - 1)) (aoyagiLemma5Eq5OffsetValueSet ell a p M m) =
      (aoyagiHtildeIntervalValueSetNat ell a M m p).erase
        (aoyagiHtildeUpperNat ell a M m p) := by
  have hown :=
    aoyagiLemma5Eq4_piecewise_ownCoordinate_of_sourceSelectedInequality
      ell a p M m C layerWidth T hell hp_pos hp_c hselected hsource hT
  rw [hown.2.1]
  exact aoyagiLemma5Eq5_insertLower_offsets_eq_interval_erase_upper_of_le_min
    ell a p M m hT.a_le_ell hp_pos hp_a hp_c

/-- A supplied equation `(4)` lower endpoint adds one value to the strict Eq5
offset set in the rising region.

This is the cardinality form of the Eq4 lower-endpoint wrapper.  It is still
finite count bookkeeping only; it does not construct displayed vectors or
prove source-label legality. -/
theorem aoyagiLemma5Eq4_insertOwnCoordinate_eq5Offsets_card_eq_offsetCard_add_one_of_le_min
    (ell a p : ℕ) (M : ℤ) (m : Fin (ell + 1) → ℤ)
    (C : AoyagiSelectedCutpoints ell) (layerWidth T : ℕ → ℤ)
    (hell : 1 ≤ ell) (hp_pos : 1 ≤ p) (hp_a : p ≤ a) (hp_c : p ≤ ell - a)
    (hselected : (∑ j : Fin (ell + 1), m j) = (ell : ℤ) * (M - 1) + a)
    (hsource : ∀ i : Fin (ell + 1),
      (ell : ℤ) * m i < ∑ j : Fin (ell + 1), m j)
    (hT : AoyagiLemma5Eq4PiecewiseSourceVector ell a p M m C layerWidth T) :
    (insert (T (C.point p - 1))
        (aoyagiLemma5Eq5OffsetValueSet ell a p M m)).card =
      (aoyagiLemma5Eq5OffsetValueSet ell a p M m).card + 1 := by
  have hown :=
    aoyagiLemma5Eq4_piecewise_ownCoordinate_of_sourceSelectedInequality
      ell a p M m C layerWidth T hell hp_pos hp_c hselected hsource hT
  rw [hown.2.1]
  rw [aoyagiLemma5Eq5_insert_lowerEndpoint_offsetValueSet_card_of_le_min
    ell a p M m hT.a_le_ell hp_pos hp_a hp_c]
  rw [aoyagiLemma5Eq5OffsetValueSet_card_eq_pred_of_le_min
    ell a p M m hT.a_le_ell hp_pos hp_a hp_c]
  have hexcess :
      aoyagiLemma5IntervalExcess ell a p = p :=
    aoyagiLemma5IntervalExcess_eq_self_of_le_min
      ell a p hT.a_le_ell hp_a hp_c
  rw [hexcess]
  omega

/-- At the first interval, a separately supplied Eq3-shaped upper endpoint and
supplied equation `(4)` lower endpoint fill the two endpoints
missing from the strict Eq5 offset set.

This is a finite-set equality for supplied branch certificates only.  It does
not assert that the printed equation `(3)` source branch supplies the excluded
label `(S_2-1,Htilde'_1+1)`, and it does not construct the displayed
source-vector family, prove source-label legality, terminality, chart
coverage, pole order, normal crossings, or RLCT extraction.
-/
theorem aoyagiLemma5_suppliedEq3Upper_Eq4_firstInterval_insertOwnCoordinates_eq_intervalValueSetNat
    (ell a : ℕ) (M : ℤ) (m : Fin (ell + 1) → ℤ)
    (C : AoyagiSelectedCutpoints ell)
    (layerWidth3 T3 layerWidth4 T4 : ℕ → ℤ)
    (hell : 1 ≤ ell)
    (hselected : (∑ j : Fin (ell + 1), m j) = (ell : ℤ) * (M - 1) + a)
    (hsource : ∀ i : Fin (ell + 1),
      (ell : ℤ) * m i < ∑ j : Fin (ell + 1), m j)
    (hslack : aoyagiSelectedWidthNat ell m 0 + 2 ≤ M)
    (hp_c : 1 ≤ ell - a)
    (hT3 : AoyagiLemma5Eq3PiecewiseSourceVector ell a M m C layerWidth3 T3)
    (hT4 : AoyagiLemma5Eq4PiecewiseSourceVector ell a 1 M m C layerWidth4 T4) :
    insert (T3 (C.point 1 - 1))
        (insert (T4 (C.point 1 - 1))
          (aoyagiLemma5Eq5OffsetValueSet ell a 1 M m)) =
      aoyagiHtildeIntervalValueSetNat ell a M m 1 := by
  have hp_a : 1 ≤ a := by
    have hguard : 1 + 1 ≤ a := hT4.indexGuard
    omega
  have ha_lt : a < ell := by
    have ha : a ≤ ell := hT4.a_le_ell
    omega
  have hEq4 :=
    aoyagiLemma5Eq4_insertOwnCoordinate_eq5Offsets_eq_interval_erase_upper_of_le_min
      ell a 1 M m C layerWidth4 T4 hell le_rfl hp_a hp_c hselected hsource hT4
  have hEq3 :=
    aoyagiLemma5Eq3_piecewise_ownCoordinate_of_sourceSelectedInequality_and_slack
      ell a M m C layerWidth3 T3 hell ha_lt hselected hsource hslack hT3
  have hupper_mem :
      aoyagiHtildeUpperNat ell a M m 1 ∈
        aoyagiHtildeIntervalValueSetNat ell a M m 1 :=
    aoyagiLemma5Eq5_upperEndpoint_mem_intervalValueSetNat_of_lt
      ell a 1 M m hT4.a_le_ell (by omega)
  calc
    insert (T3 (C.point 1 - 1))
        (insert (T4 (C.point 1 - 1))
          (aoyagiLemma5Eq5OffsetValueSet ell a 1 M m))
        =
          insert (aoyagiHtildeUpperNat ell a M m 1)
            ((aoyagiHtildeIntervalValueSetNat ell a M m 1).erase
              (aoyagiHtildeUpperNat ell a M m 1)) := by
            rw [hEq4, hEq3.2.1]
    _ = aoyagiHtildeIntervalValueSetNat ell a M m 1 :=
      Finset.insert_erase hupper_mem

/-- In any rising-range interval, a supplied upper endpoint value and supplied
equation `(4)` lower own-coordinate fill the two endpoints missing from the
strict Eq5 offset set.

This is a finite-set equality for supplied certificates only.  It does not
construct an upper-endpoint displayed vector, prove source-label legality,
cover all intervals, prove pole order, normal crossings, or RLCT extraction.
-/
theorem aoyagiLemma5_suppliedUpper_Eq4_insertOwnCoordinate_eq_intervalValueSetNat_of_le_min
    (ell a p : ℕ) (M : ℤ) (m : Fin (ell + 1) → ℤ)
    (C : AoyagiSelectedCutpoints ell)
    (Tupper layerWidth4 T4 : ℕ → ℤ)
    (hell : 1 ≤ ell) (hp_pos : 1 ≤ p) (hp_a : p ≤ a) (hp_c : p ≤ ell - a)
    (hselected : (∑ j : Fin (ell + 1), m j) = (ell : ℤ) * (M - 1) + a)
    (hsource : ∀ i : Fin (ell + 1),
      (ell : ℤ) * m i < ∑ j : Fin (ell + 1), m j)
    (hupper :
      Tupper (C.point p - 1) = aoyagiHtildeUpperNat ell a M m p)
    (hT4 : AoyagiLemma5Eq4PiecewiseSourceVector ell a p M m C layerWidth4 T4) :
    insert (Tupper (C.point p - 1))
        (insert (T4 (C.point p - 1))
          (aoyagiLemma5Eq5OffsetValueSet ell a p M m)) =
      aoyagiHtildeIntervalValueSetNat ell a M m p := by
  have hEq4 :=
    aoyagiLemma5Eq4_insertOwnCoordinate_eq5Offsets_eq_interval_erase_upper_of_le_min
      ell a p M m C layerWidth4 T4 hell hp_pos hp_a hp_c hselected hsource hT4
  have hupper_mem :
      aoyagiHtildeUpperNat ell a M m p ∈
        aoyagiHtildeIntervalValueSetNat ell a M m p :=
    aoyagiLemma5Eq5_upperEndpoint_mem_intervalValueSetNat_of_lt
      ell a p M m hT4.a_le_ell (by omega)
  calc
    insert (Tupper (C.point p - 1))
        (insert (T4 (C.point p - 1))
          (aoyagiLemma5Eq5OffsetValueSet ell a p M m))
        =
          insert (aoyagiHtildeUpperNat ell a M m p)
            ((aoyagiHtildeIntervalValueSetNat ell a M m p).erase
              (aoyagiHtildeUpperNat ell a M m p)) := by
            rw [hEq4, hupper]
    _ = aoyagiHtildeIntervalValueSetNat ell a M m p :=
      Finset.insert_erase hupper_mem

/-- In any rising-range interval, a supplied Eq3-shaped upper component and
supplied equation `(4)` lower own-coordinate fill the two endpoints missing
from the strict Eq5 offset set.

This instantiates the supplied-upper finite-set wrapper with the component
value supplied by an equation-`(3)`-shaped certificate.  It does not assert that
the component is a legal source label, construct displayed vectors, cover all
intervals, prove order count, normal crossings, or RLCT extraction.
-/
theorem aoyagiLemma5_suppliedEq3UpperComponent_Eq4_interval_insertComponents_eq_intervalValueSetNat
    (ell a p : ℕ) (M : ℤ) (m : Fin (ell + 1) → ℤ)
    (C : AoyagiSelectedCutpoints ell)
    (layerWidth3 T3 layerWidth4 T4 : ℕ → ℤ)
    (hell : 1 ≤ ell) (hp_pos : 1 ≤ p) (hp_a : p ≤ a) (hp_c : p ≤ ell - a)
    (hselected : (∑ j : Fin (ell + 1), m j) = (ell : ℤ) * (M - 1) + a)
    (hsource : ∀ i : Fin (ell + 1),
      (ell : ℤ) * m i < ∑ j : Fin (ell + 1), m j)
    (hT3 : AoyagiLemma5Eq3PiecewiseSourceVector ell a M m C layerWidth3 T3)
    (hT4 : AoyagiLemma5Eq4PiecewiseSourceVector ell a p M m C layerWidth4 T4) :
    insert (T3 (C.point p - 1))
        (insert (T4 (C.point p - 1))
          (aoyagiLemma5Eq5OffsetValueSet ell a p M m)) =
      aoyagiHtildeIntervalValueSetNat ell a M m p := by
  have hupper :=
    aoyagiLemma5Eq3_piecewise_component_upperEndpoint_of_le_gap
      ell a p M m C layerWidth3 T3 hp_pos hp_c hT3
  exact
    aoyagiLemma5_suppliedUpper_Eq4_insertOwnCoordinate_eq_intervalValueSetNat_of_le_min
      ell a p M m C T3 layerWidth4 T4 hell hp_pos hp_a hp_c hselected hsource
      hupper hT4

/-- Cardinality form of
`aoyagiLemma5_suppliedEq3UpperComponent_Eq4_interval_insertComponents_eq_intervalValueSetNat`.

This is a one-coordinate count consequence of the supplied Eq3-shaped upper
component, supplied Eq4 lower endpoint, and strict Eq5 offset set.  It is not
an all-branch order-count theorem. -/
theorem aoyagiLemma5_suppliedEq3UpperComponent_Eq4_interval_insertComponents_card_eq_intervalSize
    (ell a p : ℕ) (M : ℤ) (m : Fin (ell + 1) → ℤ)
    (C : AoyagiSelectedCutpoints ell)
    (layerWidth3 T3 layerWidth4 T4 : ℕ → ℤ)
    (hell : 1 ≤ ell) (hp_pos : 1 ≤ p) (hp_a : p ≤ a) (hp_c : p ≤ ell - a)
    (hselected : (∑ j : Fin (ell + 1), m j) = (ell : ℤ) * (M - 1) + a)
    (hsource : ∀ i : Fin (ell + 1),
      (ell : ℤ) * m i < ∑ j : Fin (ell + 1), m j)
    (hT3 : AoyagiLemma5Eq3PiecewiseSourceVector ell a M m C layerWidth3 T3)
    (hT4 : AoyagiLemma5Eq4PiecewiseSourceVector ell a p M m C layerWidth4 T4) :
    (insert (T3 (C.point p - 1))
        (insert (T4 (C.point p - 1))
          (aoyagiLemma5Eq5OffsetValueSet ell a p M m))).card =
      aoyagiLemma5IntervalSize ell a p := by
  rw [aoyagiLemma5_suppliedEq3UpperComponent_Eq4_interval_insertComponents_eq_intervalValueSetNat
    ell a p M m C layerWidth3 T3 layerWidth4 T4 hell hp_pos hp_a hp_c
    hselected hsource hT3 hT4]
  exact aoyagiHtildeIntervalValueSetNat_card_of_lt ell a M m p (by omega)

/-- In the rising region, the supplied Eq3-shaped upper component and supplied
Eq4 lower endpoint add two values to the strict Eq5 offset set.

This is a cardinality consequence of the one-coordinate interval coverage
theorem.  It does not prove displayed-vector construction, source-label
legality, or the full Lemma 5 order count. -/
theorem aoyagiLemma5_suppliedEq3Upper_Eq4_insertComponents_card_eq_offsetCard_add_two
    (ell a p : ℕ) (M : ℤ) (m : Fin (ell + 1) → ℤ)
    (C : AoyagiSelectedCutpoints ell)
    (layerWidth3 T3 layerWidth4 T4 : ℕ → ℤ)
    (hell : 1 ≤ ell) (hp_pos : 1 ≤ p) (hp_a : p ≤ a) (hp_c : p ≤ ell - a)
    (hselected : (∑ j : Fin (ell + 1), m j) = (ell : ℤ) * (M - 1) + a)
    (hsource : ∀ i : Fin (ell + 1),
      (ell : ℤ) * m i < ∑ j : Fin (ell + 1), m j)
    (hT3 : AoyagiLemma5Eq3PiecewiseSourceVector ell a M m C layerWidth3 T3)
    (hT4 : AoyagiLemma5Eq4PiecewiseSourceVector ell a p M m C layerWidth4 T4) :
    (insert (T3 (C.point p - 1))
        (insert (T4 (C.point p - 1))
          (aoyagiLemma5Eq5OffsetValueSet ell a p M m))).card =
      (aoyagiLemma5Eq5OffsetValueSet ell a p M m).card + 2 := by
  rw [aoyagiLemma5_suppliedEq3UpperComponent_Eq4_interval_insertComponents_card_eq_intervalSize
    ell a p M m C layerWidth3 T3 layerWidth4 T4 hell hp_pos hp_a hp_c
    hselected hsource hT3 hT4]
  rw [aoyagiLemma5IntervalSize_eq_succ_of_le_min
    ell a p hT4.a_le_ell (Nat.le_min.mpr ⟨hp_a, hp_c⟩)]
  rw [aoyagiLemma5Eq5OffsetValueSet_card_eq_pred_of_le_min
    ell a p M m hT4.a_le_ell hp_pos hp_a hp_c]
  omega

/-- A supplied equation `(5)` own-coordinate branch has the displayed value
`Htilde'_p - alpha` on block `p`. -/
theorem aoyagiLemma5Eq5_ownCoordinate_value
    (ell a p alpha : ℕ) (M : ℤ) (m : Fin (ell + 1) → ℤ)
    (C : AoyagiSelectedCutpoints ell) (T : ℕ → ℤ)
    (hT : AoyagiLemma5Eq5OwnCoordinateBranch ell a p alpha M m C T)
    {S : ℕ} (hS : C.block p S) :
    T S = aoyagiHtildeUpperNat ell a M m p - (alpha : ℤ) := by
  exact hT.ownBranch S hS

/-- With Aoyagi's equation `(5)` relation
`alpha = Htilde'_p + 1 - k`, the own-coordinate value is `k-1`. -/
theorem aoyagiLemma5Eq5_ownCoordinate_eq_label_pred
    (ell a p alpha : ℕ) (M : ℤ) (m : Fin (ell + 1) → ℤ)
    (C : AoyagiSelectedCutpoints ell) (T : ℕ → ℤ)
    (hT : AoyagiLemma5Eq5OwnCoordinateBranch ell a p alpha M m C T)
    {S k : ℕ} (hS : C.block p S)
    (hk : (k : ℤ) =
      aoyagiHtildeUpperNat ell a M m p + 1 - (alpha : ℤ)) :
    T S = (k : ℤ) - 1 := by
  rw [aoyagiLemma5Eq5_ownCoordinate_value
    ell a p alpha M m C T hT hS, hk]
  ring

/-- A supplied equation `(5)` own-coordinate branch value lies in the
same-coordinate interval at coordinate `p`.

This uses only `alpha <= Htilde'_p-Htilde_p`, recorded as
`alpha_le_excess`.  It does not construct the equation `(5)` vector, prove
source-label legality, terminal `tilde t=0`, chart coverage, or the Lemma 5
order count. -/
theorem aoyagiLemma5Eq5_ownCoordinate_mem_intervalValueSetNat
    (ell a p alpha : ℕ) (M : ℤ) (m : Fin (ell + 1) → ℤ)
    (C : AoyagiSelectedCutpoints ell) (T : ℕ → ℤ)
    (hT : AoyagiLemma5Eq5OwnCoordinateBranch ell a p alpha M m C T)
    {S : ℕ} (hS : C.block p S) :
    T S ∈ aoyagiHtildeIntervalValueSetNat ell a M m p := by
  have hp : p < ell + 1 := by
    have hp_lt : p < ell := hS.1
    omega
  rw [aoyagiHtildeIntervalValueSetNat]
  simp only [hp, ↓reduceDIte]
  rw [aoyagiHtilde_mem_intervalValueSet_iff_bounds ell a M m hT.a_le_ell ⟨p, hp⟩]
  have hgap :=
    aoyagiHtildeUpper_sub_lower_eq_intervalExcess ell a M m hT.a_le_ell ⟨p, hp⟩
  have hvalue := hT.ownBranch S hS
  simp [aoyagiHtildeLowerChain, aoyagiHtildeUpperChain] at hgap
  have halpha_le_int :
      (alpha : ℤ) ≤ (aoyagiLemma5IntervalExcess ell a p : ℤ) := by
    exact_mod_cast hT.alpha_le_excess
  rw [hvalue]
  change
    aoyagiHtildeLowerNat ell a M m p ≤
        aoyagiHtildeUpperNat ell a M m p - (alpha : ℤ) ∧
      aoyagiHtildeUpperNat ell a M m p - (alpha : ℤ) ≤
        aoyagiHtildeUpperNat ell a M m p
  constructor <;> omega

/-- A supplied equation `(5)` own-coordinate branch value belongs to the finite
offset-value set counted by `aoyagiLemma5Eq5OffsetValueSet_card`. -/
theorem aoyagiLemma5Eq5_ownCoordinate_mem_offsetValueSet
    (ell a p alpha : ℕ) (M : ℤ) (m : Fin (ell + 1) → ℤ)
    (C : AoyagiSelectedCutpoints ell) (T : ℕ → ℤ)
    (hT : AoyagiLemma5Eq5OwnCoordinateBranch ell a p alpha M m C T)
    {S : ℕ} (hS : C.block p S) :
    T S ∈ aoyagiLemma5Eq5OffsetValueSet ell a p M m := by
  rw [aoyagiLemma5Eq5_ownCoordinate_value
    ell a p alpha M m C T hT hS]
  exact Finset.mem_image_of_mem
    (fun beta : ℕ ↦ aoyagiHtildeUpperNat ell a M m p - (beta : ℤ)) (by
      rw [Finset.mem_Icc]
      constructor
      · exact hT.alpha_pos
      · exact le_min hT.alpha_le_excess
          (Nat.le_sub_one_of_lt hT.alpha_lt_p))

end Aoyagi
end DLN
end DLNFibre
