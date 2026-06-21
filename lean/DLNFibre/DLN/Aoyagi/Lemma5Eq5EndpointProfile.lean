import DLNFibre.DLN.Aoyagi.Lemma5DisplayedVector

/-!
# Eq5 endpoint prefix profiles for Aoyagi's Lemma 5

This file records branchwise prefix-profile computations for a supplied
equation `(5)` endpoint chain.  It does not prove binary prefix deltas,
two-value increments, displayed-vector construction, pole order, normal
crossings, or RLCT extraction.
-/

open scoped BigOperators

namespace DLNFibre
namespace DLN
namespace Aoyagi

/-- On the pre-alpha branch of supplied equation `(5)`, the endpoint chain has
Lemma 4 prefix value `b`. -/
theorem aoyagiLemma5Eq5_endpointChain_incrementPrefix_preAlpha
    (ell a p alpha : ℕ) (M : ℤ) (m H : Fin (ell + 1) → ℤ)
    (C : AoyagiSelectedCutpoints ell) (layerWidth T : ℕ → ℤ)
    (hT : AoyagiLemma5Eq5PiecewiseSourceVector
      ell a p alpha M m C layerWidth T)
    (hH_endpoint :
      ∀ b : Fin (ell + 1), 1 ≤ b.val → b.val < ell →
        H b = T (C.point b.val - 1))
    {b : ℕ} (hb_pos : 1 ≤ b) (hb_lt : b < ell)
    (hb_pre : b + 2 ≤ alpha) :
    aoyagiLemma4IncrementPrefix ell M m H ⟨b, Nat.lt_succ_of_lt hb_lt⟩ =
      (b : ℤ) := by
  let jb : Fin (ell + 1) := ⟨b, Nat.lt_succ_of_lt hb_lt⟩
  have hb_block : C.block b (C.point b - 1) := C.leftEndpoint_mem_block hb_lt
  have hH :
      H jb = aoyagiHtildeUpperNat ell a M m b - (b : ℤ) := by
    dsimp [jb]
    rw [hH_endpoint ⟨b, Nat.lt_succ_of_lt hb_lt⟩ hb_pos hb_lt]
    exact hT.preAlpha b (C.point b - 1) hb_pos hb_pre hb_block
  have hprefix :=
    aoyagiLemma4IncrementPrefix_eq_upperHighCount_add_of_eq_upperNat_sub
      ell a M m H (j := jb) (r := (b : ℤ)) hH
  have halpha_le_tail : alpha ≤ ell - a := by
    have hexcess := hT.alpha_le_excess
    unfold aoyagiLemma5IntervalExcess at hexcess
    omega
  have hupper0 : aoyagiHtildeUpperHighCount ell a b = 0 := by
    have hb_le_tail : b ≤ ell - a := by omega
    have hsub : b - (ell - a) = 0 := by omega
    simp [aoyagiHtildeUpperHighCount, hsub]
  rw [hprefix, hupper0]
  omega

/-- On the alpha-to-`p` branch of supplied equation `(5)`, the endpoint chain
has Lemma 4 prefix value `alpha-1`. -/
theorem aoyagiLemma5Eq5_endpointChain_incrementPrefix_alphaToP
    (ell a p alpha : ℕ) (M : ℤ) (m H : Fin (ell + 1) → ℤ)
    (C : AoyagiSelectedCutpoints ell) (layerWidth T : ℕ → ℤ)
    (hT : AoyagiLemma5Eq5PiecewiseSourceVector
      ell a p alpha M m C layerWidth T)
    (hroom : p + 2 * a - alpha ≤ ell)
    (hH_endpoint :
      ∀ b : Fin (ell + 1), 1 ≤ b.val → b.val < ell →
        H b = T (C.point b.val - 1))
    {b : ℕ} (hb_pos : 1 ≤ b) (hb_lt : b < ell)
    (halpha_le : alpha ≤ b + 1) (hb_p : b + 1 ≤ p) :
    aoyagiLemma4IncrementPrefix ell M m H ⟨b, Nat.lt_succ_of_lt hb_lt⟩ =
      ((alpha - 1 : ℕ) : ℤ) := by
  let jb : Fin (ell + 1) := ⟨b, Nat.lt_succ_of_lt hb_lt⟩
  have hb_block : C.block b (C.point b - 1) := C.leftEndpoint_mem_block hb_lt
  have hpred_cast : ((alpha - 1 : ℕ) : ℤ) = (alpha : ℤ) - 1 := by
    have halpha_pos := hT.alpha_pos
    omega
  have hH :
      H jb = aoyagiHtildeUpperNat ell a M m b -
        ((alpha - 1 : ℕ) : ℤ) := by
    dsimp [jb]
    rw [hH_endpoint ⟨b, Nat.lt_succ_of_lt hb_lt⟩ hb_pos hb_lt]
    rw [hT.alphaToP b (C.point b - 1) hb_pos halpha_le hb_p hb_block]
    rw [hpred_cast]
    ring
  have hprefix :=
    aoyagiLemma4IncrementPrefix_eq_upperHighCount_add_of_eq_upperNat_sub
      ell a M m H (j := jb) (r := ((alpha - 1 : ℕ) : ℤ)) hH
  have halpha_le_a : alpha ≤ a := by
    have hexcess := hT.alpha_le_excess
    unfold aoyagiLemma5IntervalExcess at hexcess
    omega
  have hupper0 : aoyagiHtildeUpperHighCount ell a b = 0 := by
    have hb_le_tail : b ≤ ell - a := by omega
    have hsub : b - (ell - a) = 0 := by omega
    simp [aoyagiHtildeUpperHighCount, hsub]
  rw [hprefix, hupper0]
  omega

/-- On the post-`p` branch of supplied equation `(5)`, the endpoint chain has
Lemma 4 prefix value `alpha+b-p`. -/
theorem aoyagiLemma5Eq5_endpointChain_incrementPrefix_postP
    (ell a p alpha : ℕ) (M : ℤ) (m H : Fin (ell + 1) → ℤ)
    (C : AoyagiSelectedCutpoints ell) (layerWidth T : ℕ → ℤ)
    (hT : AoyagiLemma5Eq5PiecewiseSourceVector
      ell a p alpha M m C layerWidth T)
    (hroom : p + 2 * a - alpha ≤ ell)
    (hH_endpoint :
      ∀ b : Fin (ell + 1), 1 ≤ b.val → b.val < ell →
        H b = T (C.point b.val - 1))
    {b : ℕ} (hb_pos : 1 ≤ b) (hb_lt : b < ell)
    (hp_le_b : p ≤ b) (hb_hi : b ≤ p + (a - alpha)) :
    aoyagiLemma4IncrementPrefix ell M m H ⟨b, Nat.lt_succ_of_lt hb_lt⟩ =
      ((alpha + b - p : ℕ) : ℤ) := by
  let jb : Fin (ell + 1) := ⟨b, Nat.lt_succ_of_lt hb_lt⟩
  have hb_block : C.block b (C.point b - 1) := C.leftEndpoint_mem_block hb_lt
  have hoffset_cast :
      ((alpha + b - p : ℕ) : ℤ) =
        (alpha : ℤ) + (b : ℤ) - (p : ℤ) := by
    omega
  have hH :
      H jb = aoyagiHtildeUpperNat ell a M m b -
        ((alpha + b - p : ℕ) : ℤ) := by
    dsimp [jb]
    rw [hH_endpoint ⟨b, Nat.lt_succ_of_lt hb_lt⟩ hb_pos hb_lt]
    rw [hT.postP b (C.point b - 1) hp_le_b hb_hi hb_block]
    rw [hoffset_cast]
    ring
  have hprefix :=
    aoyagiLemma4IncrementPrefix_eq_upperHighCount_add_of_eq_upperNat_sub
      ell a M m H (j := jb) (r := ((alpha + b - p : ℕ) : ℤ)) hH
  have halpha_le_a : alpha ≤ a := by
    have hexcess := hT.alpha_le_excess
    unfold aoyagiLemma5IntervalExcess at hexcess
    omega
  have hupper0 : aoyagiHtildeUpperHighCount ell a b = 0 := by
    have hb_le_tail : b ≤ ell - a := by omega
    have hsub : b - (ell - a) = 0 := by omega
    simp [aoyagiHtildeUpperHighCount, hsub]
  rw [hprefix, hupper0]
  omega

/-- On the tail branch of supplied equation `(5)`, the endpoint chain has
terminal Lemma 4 prefix value `a`. -/
theorem aoyagiLemma5Eq5_endpointChain_incrementPrefix_tail
    (ell a p alpha : ℕ) (M : ℤ) (m H : Fin (ell + 1) → ℤ)
    (C : AoyagiSelectedCutpoints ell) (layerWidth T : ℕ → ℤ)
    (hT : AoyagiLemma5Eq5PiecewiseSourceVector
      ell a p alpha M m C layerWidth T)
    (hH_endpoint :
      ∀ b : Fin (ell + 1), 1 ≤ b.val → b.val < ell →
        H b = T (C.point b.val - 1))
    {b : ℕ} (hb_pos : 1 ≤ b) (hb_lt : b < ell)
    (hb_tail : p + (a - alpha) + 1 ≤ b) :
    aoyagiLemma4IncrementPrefix ell M m H ⟨b, Nat.lt_succ_of_lt hb_lt⟩ =
      (a : ℤ) := by
  let jb : Fin (ell + 1) := ⟨b, Nat.lt_succ_of_lt hb_lt⟩
  have hb_block : C.block b (C.point b - 1) := C.leftEndpoint_mem_block hb_lt
  have hcut_le :
      C.point (p + (a - alpha) + 1) - 1 ≤ C.point b - 1 := by
    by_cases hcut_eq : p + (a - alpha) + 1 = b
    · rw [hcut_eq]
    · have hcut_lt : p + (a - alpha) + 1 < b := by omega
      exact le_of_lt (C.leftEndpoint_lt_of_lt_block hcut_lt hb_block)
  have hH : H jb = aoyagiHtildeLowerNat ell a M m b := by
    dsimp [jb]
    rw [hH_endpoint ⟨b, Nat.lt_succ_of_lt hb_lt⟩ hb_pos hb_lt]
    exact hT.tail b (C.point b - 1) hb_tail hb_block hcut_le
  have hprefix :=
    aoyagiLemma4IncrementPrefix_eq_lowerHighCount_of_eq_lowerNat
      ell a M m H (j := jb) hH
  have hlower : aoyagiHtildeLowerHighCount a b = a := by
    have hb_ge_a : a ≤ b := by
      have halpha_lt_p := hT.alpha_lt_p
      omega
    exact Nat.min_eq_right hb_ge_a
  rw [hprefix, hlower]

end Aoyagi
end DLN
end DLNFibre
