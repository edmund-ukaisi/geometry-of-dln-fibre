import DLNFibre.DLN.Aoyagi.Lemma5DisplayedVector
import DLNFibre.DLN.Aoyagi.Lemma5Eq5EndpointProfile
import DLNFibre.DLN.Aoyagi.Lemma5SourceLabel
import DLNFibre.DLN.Aoyagi.Lemma5SuppliedFamily

/-!
# Eq5 counted-datum bridge for Aoyagi's Lemma 5

This file connects the supplied equation `(5)` nonfirst interval-admissibility
wrappers and terminal-room endpoint-chain binary deltas to the counted-datum
codomain.  It does not construct equation `(5)`, classifiers, injections,
back-to-label maps, pole order, normal crossings, or RLCT extraction.
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

/-- A supplied equation `(5)` terminal-room endpoint chain gives one counted
datum at any interior selected coordinate, provided the chain value is not the
supplied base value. -/
theorem aoyagiLemma5Eq5_endpointChain_countDatumSet_mem_of_terminalRoom
    (ell a p alpha : ℕ) (M : ℤ) (m H : Fin (ell + 1) → ℤ)
    (baseValue : ℕ → ℤ)
    (C : AoyagiSelectedCutpoints ell) (layerWidth T : ℕ → ℤ)
    (hT : AoyagiLemma5Eq5PiecewiseSourceVector
      ell a p alpha M m C layerWidth T)
    (hroom : p + 2 * a - alpha ≤ ell)
    (hH0 : H 0 = m 0)
    (hHlast : H (Fin.last ell) = 0)
    (hselected :
      (∑ i : Fin (ell + 1), m i) = (ell : ℤ) * (M - 1) + a)
    (hH_endpoint :
      ∀ b : Fin (ell + 1), 1 ≤ b.val → b.val < ell →
        H b = T (C.point b.val - 1))
    {j : ℕ} (hj : j ∈ Finset.Icc 1 (ell - 1))
    (hne_base :
      H (aoyagiLemma5InteriorCoord ell j hj) ≠ baseValue j) :
    some (Sigma.mk j (H (aoyagiLemma5InteriorCoord ell j hj))) ∈
      aoyagiLemma5CountDatumSet ell a M m baseValue := by
  exact aoyagiLemma5CountDatumSet_mem_of_terminalH_binaryIncrementPrefixDelta
    ell a M m H baseValue hj hT.a_le_ell hH0 hHlast hselected
    (aoyagiLemma5Eq5_endpointChain_binaryIncrementPrefixDelta_of_terminalRoom
      ell a p alpha M m H C layerWidth T hT hroom hH0 hHlast hselected
      hH_endpoint)
    hne_base

/-- A supplied equation `(5)` terminal-room endpoint value gives one counted
datum at any interior selected coordinate, provided that endpoint value is not
the supplied base value. -/
theorem aoyagiLemma5Eq5_endpointValue_countDatumSet_mem_of_terminalRoom
    (ell a p alpha : ℕ) (M : ℤ) (m H : Fin (ell + 1) → ℤ)
    (baseValue : ℕ → ℤ)
    (C : AoyagiSelectedCutpoints ell) (layerWidth T : ℕ → ℤ)
    (hT : AoyagiLemma5Eq5PiecewiseSourceVector
      ell a p alpha M m C layerWidth T)
    (hroom : p + 2 * a - alpha ≤ ell)
    (hH0 : H 0 = m 0)
    (hHlast : H (Fin.last ell) = 0)
    (hselected :
      (∑ i : Fin (ell + 1), m i) = (ell : ℤ) * (M - 1) + a)
    (hH_endpoint :
      ∀ b : Fin (ell + 1), 1 ≤ b.val → b.val < ell →
        H b = T (C.point b.val - 1))
    {j : ℕ} (hj : j ∈ Finset.Icc 1 (ell - 1))
    (hne_base : T (C.point j - 1) ≠ baseValue j) :
    some (Sigma.mk j (T (C.point j - 1))) ∈
      aoyagiLemma5CountDatumSet ell a M m baseValue := by
  have hj_pos : 1 ≤ j := (Finset.mem_Icc.mp hj).1
  have hj_lt_ell : j < ell := by
    have hj_le : j ≤ ell - 1 := (Finset.mem_Icc.mp hj).2
    omega
  have hH_eq_T :
      H (aoyagiLemma5InteriorCoord ell j hj) =
        T (C.point j - 1) := by
    simpa [aoyagiLemma5InteriorCoord] using
      hH_endpoint (aoyagiLemma5InteriorCoord ell j hj) hj_pos hj_lt_ell
  have hne_H :
      H (aoyagiLemma5InteriorCoord ell j hj) ≠ baseValue j := by
    rw [hH_eq_T]
    exact hne_base
  have hmem :=
    aoyagiLemma5Eq5_endpointChain_countDatumSet_mem_of_terminalRoom
      ell a p alpha M m H baseValue C layerWidth T hT hroom hH0 hHlast
      hselected hH_endpoint hj hne_H
  simpa [hH_eq_T] using hmem

/-- A supplied equation `(5)` own-block branch gives both a counted datum and
the corresponding introduced source label, provided its own-block value is not
the supplied base value.

This is a one-branch payload adapter.  It does not construct equation `(5)`,
prove nonbase status, or build classifier/back-to-label data. -/
theorem
    aoyagiLemma5Eq5_ownBlock_countDatumSet_mem_introducedLabelFinset_of_lastPoint_widthBound
    (L ell a p alpha : ℕ) (n : ℕ → ℕ) (M : ℤ)
    (m : Fin (ell + 1) → ℤ) (baseValue : ℕ → ℤ)
    (C : AoyagiSelectedCutpoints ell) (layerWidth T : ℕ → ℤ)
    (hell : 1 ≤ ell)
    (hselected :
      (∑ i : Fin (ell + 1), m i) = (ell : ℤ) * (M - 1) + a)
    (hsource : ∀ i : Fin (ell + 1),
      (ell : ℤ) * m i < ∑ j : Fin (ell + 1), m j)
    (hT : AoyagiLemma5Eq5PiecewiseSourceVector
      ell a p alpha M m C layerWidth T)
    {S k : ℕ} (hp_pos : 1 ≤ p) (hS : C.block p S)
    (hlast : C.point ell ≤ L + 1)
    (hwidth_le : aoyagiSelectedWidthNat ell m p ≤ (n (S + 1) : ℤ))
    (hk : (k : ℤ) =
      aoyagiHtildeUpperNat ell a M m p + 1 - (alpha : ℤ))
    (hne_base : T S ≠ baseValue p) :
    some (Sigma.mk p (T S)) ∈
        aoyagiLemma5CountDatumSet ell a M m baseValue ∧
      T S = (k : ℤ) - 1 ∧
        Sigma.mk S k ∈ introducedLabelFinset L n S k := by
  have hpIcc : p ∈ Finset.Icc 1 (ell - 1) := by
    have hp_lt_ell : p < ell := hS.1
    rw [Finset.mem_Icc]
    exact ⟨hp_pos, by omega⟩
  have hpayload :=
    aoyagiLemma5Eq5_ownBlock_intervalValue_mem_introducedLabelFinset_of_lastPoint_widthBound
      L ell a p alpha n M m C layerWidth T hell hselected hsource hT hS
      hlast hwidth_le hk
  have hcount :
      some (Sigma.mk p (T S)) ∈
        aoyagiLemma5CountDatumSet ell a M m baseValue :=
    aoyagiLemma5CountDatumSet_mem_of_intervalValueSetNat
      ell a M m baseValue hpIcc hpayload.1 hne_base
  exact ⟨hcount, hpayload.2⟩

end Aoyagi
end DLN
end DLNFibre
