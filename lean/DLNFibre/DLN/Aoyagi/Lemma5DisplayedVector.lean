import DLNFibre.DLN.Aoyagi.HtildeChainArithmetic

/-!
# Conditional displayed-vector data for Aoyagi's Lemma 5

This file introduces source-layer cutpoints and a supplied piecewise certificate
for Aoyagi Lemma 5 equation `(4)`.  It does not construct the displayed vector,
prove terminal `tilde t=0`, chart coverage, pole order, normal crossings, or
RLCT extraction.
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

end Aoyagi
end DLN
end DLNFibre
