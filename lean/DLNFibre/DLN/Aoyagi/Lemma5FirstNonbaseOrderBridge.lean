import DLNFibre.DLN.Aoyagi.Lemma5SuppliedFamily
import DLNFibre.DLN.Aoyagi.FinalFormula

/-!
# Lemma 5 first-nonbase bound in Theorem 2 order notation

This file is a notation handoff: it rewrites the finite first-nonbase
cardinality bound from `a * (ell - a) + 1` to Aoyagi Theorem 2's
`theorem2OrderFormula` under supplied Definition 3 ceiling data.  It does not
construct the source classifier, prove injectivity, prove terminal exactness,
or identify this count with pole order/RLCT data.
-/

open scoped BigOperators

namespace DLNFibre
namespace DLN
namespace Aoyagi

/-- The first-nonbase-or-base selector cardinal bound, stated in Aoyagi
Theorem 2 order notation.

The proof is exactly the existing first-nonbase cardinal bound with
`a = data.aParam` and `M = data.ceilWidth`, followed by the definitional
rewrite of `data.theorem2OrderFormula`.  All source-facing obligations from
the first-nonbase theorem remain explicit. -/
theorem aoyagiLemma5FirstInteriorNonbaseCountDatumOrBase_candidates_card_le_theorem2OrderFormula
    {α : Type*} {ell : ℕ} {m : Fin (ell + 1) → ℤ}
    (data : AoyagiDefinition3CeilData ell m)
    (baseValue : ℕ → ℤ) (candidates : Finset α)
    (H : α → Fin (ell + 1) → ℤ)
    (hH0 : ∀ x ∈ candidates, H x 0 = m 0)
    (hHlast : ∀ x ∈ candidates, H x (Fin.last ell) = 0)
    (hbin : ∀ x ∈ candidates, ∀ r : Fin ell,
      aoyagiLemma4IncrementPrefixDelta ell data.ceilWidth m (H x) r = 0 ∨
        aoyagiLemma4IncrementPrefixDelta ell data.ceilWidth m (H x) r = 1)
    (hbase :
      ∀ {j : ℕ}, j ∈ Finset.Icc 1 (ell - 1) →
        baseValue j ∈
          aoyagiHtildeIntervalValueSetNat
            ell data.aParam data.ceilWidth m j)
    (hinj :
      Set.InjOn
        (fun x ↦ aoyagiLemma5FirstInteriorNonbaseCountDatumOrBase
          ell (H x) baseValue)
        ↑candidates) :
    candidates.card ≤ data.theorem2OrderFormula := by
  have hbound :
      candidates.card ≤ data.aParam * (ell - data.aParam) + 1 :=
    aoyagiLemma5FirstInteriorNonbaseCountDatumOrBase_candidates_card_le
      ell data.aParam data.ceilWidth m baseValue candidates H
      (Nat.succ_le_iff.mpr data.ell_pos)
      data.aParam_le hH0 hHlast data.selectedSum_eq hbin hbase hinj
  simpa [AoyagiDefinition3CeilData.theorem2OrderFormula] using hbound

end Aoyagi
end DLN
end DLNFibre
