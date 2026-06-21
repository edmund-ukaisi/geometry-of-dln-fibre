import DLNFibre.DLN.Aoyagi.Lemma5DisplayedVector
import DLNFibre.DLN.Aoyagi.Lemma5SuppliedFamily

/-!
# Eq5 counted-datum bridge for Aoyagi's Lemma 5

This file connects the supplied equation `(5)` nonfirst interval-admissibility
wrappers to the counted-datum codomain.  It does not construct equation `(5)`,
classifiers, injections, back-to-label maps, pole order, normal crossings, or
RLCT extraction.
-/

open scoped BigOperators

namespace DLNFibre
namespace DLN
namespace Aoyagi

/-- A nonfirst equation `(5)` block value gives one counted datum under the
strict alpha domain, supplied post-`p` guard, and non-base-value condition. -/
theorem aoyagiLemma5Eq5_nonfirstBlock_countDatumSet_mem_of_alphaDomain_of_postPLowerGuard
    (ell a p alpha : ℕ) (M : ℤ) (m : Fin (ell + 1) → ℤ)
    (baseValue : ℕ → ℤ)
    (C : AoyagiSelectedCutpoints ell) (layerWidth T : ℕ → ℤ)
    (hT : AoyagiLemma5Eq5PiecewiseSourceVector
      ell a p alpha M m C layerWidth T)
    (halpha : alpha ∈ aoyagiLemma5Eq5AlphaDomain ell a p)
    (hpost : aoyagiLemma5Eq5PostPLowerGuard ell a p alpha)
    {b S : ℕ} (hb_pos : 1 ≤ b) (hS : C.block b S)
    (hne_base : T S ≠ baseValue b) :
    some (Sigma.mk b (T S)) ∈
      aoyagiLemma5CountDatumSet ell a M m baseValue := by
  have hb_lt_ell : b < ell := hS.1
  have hbIcc : b ∈ Finset.Icc 1 (ell - 1) := by
    rw [Finset.mem_Icc]
    exact ⟨hb_pos, by omega⟩
  have hmem :
      T S ∈ aoyagiHtildeIntervalValueSetNat ell a M m b :=
    aoyagiLemma5Eq5_nonfirstBlock_mem_intervalValueSetNat_of_alphaDomain_of_postPLowerGuard
      ell a p alpha M m C layerWidth T hT halpha hpost hb_pos hS
  exact aoyagiLemma5CountDatumSet_mem_of_intervalValueSetNat
    ell a M m baseValue hbIcc hmem hne_base

/-- A nonfirst equation `(5)` block value gives one counted datum under the
strict alpha domain, terminal-room guard, and non-base-value condition. -/
theorem aoyagiLemma5Eq5_nonfirstBlock_countDatumSet_mem_of_alphaDomain_of_terminalRoom
    (ell a p alpha : ℕ) (M : ℤ) (m : Fin (ell + 1) → ℤ)
    (baseValue : ℕ → ℤ)
    (C : AoyagiSelectedCutpoints ell) (layerWidth T : ℕ → ℤ)
    (hT : AoyagiLemma5Eq5PiecewiseSourceVector
      ell a p alpha M m C layerWidth T)
    (halpha : alpha ∈ aoyagiLemma5Eq5AlphaDomain ell a p)
    (hroom : p + 2 * a - alpha ≤ ell)
    {b S : ℕ} (hb_pos : 1 ≤ b) (hS : C.block b S)
    (hne_base : T S ≠ baseValue b) :
    some (Sigma.mk b (T S)) ∈
      aoyagiLemma5CountDatumSet ell a M m baseValue := by
  have hb_lt_ell : b < ell := hS.1
  have hmem :
      T S ∈ aoyagiHtildeIntervalValueSetNat ell a M m b :=
    aoyagiLemma5Eq5_nonfirstBlock_mem_intervalValueSetNat_of_alphaDomain_of_terminalRoom
      ell a p alpha M m C layerWidth T hT halpha hroom hb_pos hS
  have hbIcc : b ∈ Finset.Icc 1 (ell - 1) := by
    rw [Finset.mem_Icc]
    exact ⟨hb_pos, by omega⟩
  exact aoyagiLemma5CountDatumSet_mem_of_intervalValueSetNat
    ell a M m baseValue hbIcc hmem hne_base

end Aoyagi
end DLN
end DLNFibre
