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

/-- A supplied equation `(4)` piecewise vector has the correct own-coordinate
value and legal source label under the repaired guards.

This theorem is source-vector-facing but still conditional: it assumes the
piecewise branch certificate. -/
theorem aoyagiLemma5Eq4_piecewise_ownCoordinate_of_sourceSelectedInequality
    (ell a p : ℕ) (M : ℤ) (m : Fin (ell + 1) → ℤ)
    (C : AoyagiSelectedCutpoints ell) (layerWidth T : ℕ → ℤ)
    (hell : 1 ≤ ell) (ha : a ≤ ell) (hp0 : 1 ≤ p)
    (hp_tail : p + 1 ≤ a) (hp_c : p ≤ ell - a)
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
    ell a p M m hell ha hp0 hp_tail hp_c hselected hsource
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

end Aoyagi
end DLN
end DLNFibre
