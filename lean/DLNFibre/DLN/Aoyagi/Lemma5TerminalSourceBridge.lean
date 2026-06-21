import DLNFibre.DLN.Aoyagi.Lemma5DisplayedVector
import DLNFibre.DLN.Aoyagi.Lemma5SuppliedFamily

/-!
# Terminal source-coordinate bridge for Aoyagi's Lemma 5

This file connects supplied branch-chain terminal zero to the terminal Eq5
finite-set wrapper, but only under an explicit source-realisation hypothesis.
It does not construct a terminal source branch or prove terminal-label
exactness.
-/

open scoped BigOperators

namespace DLNFibre
namespace DLN
namespace Aoyagi

namespace AoyagiLemma5SuppliedAdmissibleFamily

/-- For a supplied admissible full-family branch, terminal source realisation
is equivalent to a supplied terminal source zero.

This only uses branch-chain terminal zero.  It does not construct the terminal
source value. -/
theorem fullBranch_terminalSource_realisation_iff_terminalZero {β : Type*}
    [DecidableEq β]
    {ell a : ℕ} {M : ℤ} {m : Fin (ell + 1) → ℤ}
    (F : AoyagiLemma5SuppliedAdmissibleFamily β ell a M m)
    (C : AoyagiSelectedCutpoints ell) (T : ℕ → ℤ)
    (ha : a ≤ ell)
    (hselected : (∑ j : Fin (ell + 1), m j) = (ell : ℤ) * (M - 1) + a)
    {x : Option β} (hx : x ∈ F.fullBranches) :
    T (C.point ell - 1) = (F.fullH x) (Fin.last ell) ↔
      T (C.point ell - 1) = 0 := by
  rw [F.fullBranch_terminalH_zero ha hselected hx]

/-- If a supplied admissible full-family branch is explicitly realised at the
terminal source coordinate, then it supplies the terminal zero needed to fill
the terminal Eq5 interval.

The hypothesis `hsource` is essential: it identifies the source-coordinate
value with the branch-chain terminal coordinate. -/
theorem fullBranch_terminalSource_Eq5Coverage {β : Type*} [DecidableEq β]
    {ell a : ℕ} {M : ℤ} {m : Fin (ell + 1) → ℤ}
    (F : AoyagiLemma5SuppliedAdmissibleFamily β ell a M m)
    (C : AoyagiSelectedCutpoints ell) (T : ℕ → ℤ)
    (ha : a ≤ ell)
    (hselected : (∑ j : Fin (ell + 1), m j) = (ell : ℤ) * (M - 1) + a)
    {x : Option β} (hx : x ∈ F.fullBranches)
    (hsource : T (C.point ell - 1) = (F.fullH x) (Fin.last ell)) :
    insert (T (C.point ell - 1))
        (aoyagiLemma5Eq5OffsetValueSet ell a ell M m) =
      aoyagiHtildeIntervalValueSetNat ell a M m ell := by
  have hterminal : T (C.point ell - 1) = 0 := by
    rw [hsource]
    exact F.fullBranch_terminalH_zero ha hselected hx
  exact aoyagiLemma5_suppliedTerminalZero_Eq5_offsets_eq_intervalValueSetNat
    ell a M m C T ha hselected hterminal

end AoyagiLemma5SuppliedAdmissibleFamily

namespace AoyagiLemma5SuppliedBinaryFamily

/-- For a supplied binary full-family branch, terminal source realisation is
equivalent to a supplied terminal source zero.

This only uses branch-chain terminal zero.  It does not construct the terminal
source value. -/
theorem fullBranch_terminalSource_realisation_iff_terminalZero {β : Type*}
    [DecidableEq β]
    {ell a : ℕ} {M : ℤ} {m : Fin (ell + 1) → ℤ}
    (F : AoyagiLemma5SuppliedBinaryFamily β ell a M m)
    (C : AoyagiSelectedCutpoints ell) (T : ℕ → ℤ)
    {x : Option β} (hx : x ∈ F.fullBranches) :
    T (C.point ell - 1) = (F.fullH x) (Fin.last ell) ↔
      T (C.point ell - 1) = 0 := by
  rw [F.fullBranch_terminalH_zero hx]

/-- If a supplied binary full-family branch is explicitly realised at the
terminal source coordinate, then it supplies the terminal zero needed to fill
the terminal Eq5 interval.

The terminal chain value comes from the supplied binary `Hlast`/`baseHlast`
fields, but the source-coordinate realisation is still an explicit hypothesis. -/
theorem fullBranch_terminalSource_Eq5Coverage {β : Type*} [DecidableEq β]
    {ell a : ℕ} {M : ℤ} {m : Fin (ell + 1) → ℤ}
    (F : AoyagiLemma5SuppliedBinaryFamily β ell a M m)
    (C : AoyagiSelectedCutpoints ell) (T : ℕ → ℤ)
    (ha : a ≤ ell)
    (hselected : (∑ j : Fin (ell + 1), m j) = (ell : ℤ) * (M - 1) + a)
    {x : Option β} (hx : x ∈ F.fullBranches)
    (hsource : T (C.point ell - 1) = (F.fullH x) (Fin.last ell)) :
    insert (T (C.point ell - 1))
        (aoyagiLemma5Eq5OffsetValueSet ell a ell M m) =
      aoyagiHtildeIntervalValueSetNat ell a M m ell := by
  have hterminal : T (C.point ell - 1) = 0 := by
    rw [hsource]
    exact F.fullBranch_terminalH_zero hx
  exact aoyagiLemma5_suppliedTerminalZero_Eq5_offsets_eq_intervalValueSetNat
    ell a M m C T ha hselected hterminal

end AoyagiLemma5SuppliedBinaryFamily

end Aoyagi
end DLN
end DLNFibre
