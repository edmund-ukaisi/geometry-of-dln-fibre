import DLNFibre.DLN.Aoyagi.Lemma5DisplayedVector

/-!
# Eq5 endpoint prefix profiles for Aoyagi's Lemma 5

This file records branchwise prefix-profile computations for a supplied
equation `(5)` endpoint chain and proves conditional binary prefix deltas for
supplied terminal-room endpoint chains.  It does not prove two-value
increments, displayed-vector construction, pole order, normal crossings, or
RLCT extraction.
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

/-- Terminal-room profile for the supplied equation `(5)` endpoint chain.

This packages the branchwise endpoint-prefix computations together with the
source endpoint `0` and terminal endpoint `a`. -/
theorem aoyagiLemma5Eq5_endpointChain_incrementPrefix_profile_of_terminalRoom
    (ell a p alpha : ℕ) (M : ℤ) (m H : Fin (ell + 1) → ℤ)
    (C : AoyagiSelectedCutpoints ell) (layerWidth T : ℕ → ℤ)
    (hT : AoyagiLemma5Eq5PiecewiseSourceVector
      ell a p alpha M m C layerWidth T)
    (hroom : p + 2 * a - alpha ≤ ell)
    (hH0 : H 0 = m 0)
    (hHlast : H (Fin.last ell) = 0)
    (hselected :
      (∑ j : Fin (ell + 1), m j) = (ell : ℤ) * (M - 1) + a)
    (hH_endpoint :
      ∀ b : Fin (ell + 1), 1 ≤ b.val → b.val < ell →
        H b = T (C.point b.val - 1))
    {i : ℕ} (hi : i ≤ ell) :
    aoyagiLemma4IncrementPrefix ell M m H ⟨i, Nat.lt_succ_of_le hi⟩ =
      if i = 0 then 0
      else if i + 2 ≤ alpha then (i : ℤ)
      else if i + 1 ≤ p then ((alpha - 1 : ℕ) : ℤ)
      else if i ≤ p + (a - alpha) then ((alpha + i - p : ℕ) : ℤ)
      else (a : ℤ) := by
  by_cases hi0 : i = 0
  · subst i
    simpa using aoyagiLemma4IncrementPrefix_zero_of_H0 ell M m H hH0
  by_cases hiell : i = ell
  · subst i
    have halpha_le_a : alpha ≤ a := by
      have hexcess := hT.alpha_le_excess
      unfold aoyagiLemma5IntervalExcess at hexcess
      omega
    have hnot_pre : ¬ ell + 2 ≤ alpha := by omega
    have hnot_alpha_to_p : ¬ ell + 1 ≤ p := by omega
    have hnot_post : ¬ ell ≤ p + (a - alpha) := by
      have halpha_pos := hT.alpha_pos
      omega
    have hlast :=
      aoyagiLemma4IncrementPrefix_last_eq_a_of_terminalH
        ell a M m H hHlast hselected
    simpa [Fin.last, hi0, hnot_pre, hnot_alpha_to_p, hnot_post] using hlast
  have hi_pos : 1 ≤ i := by omega
  have hi_lt : i < ell := by omega
  by_cases hpre : i + 2 ≤ alpha
  · have hprefix :=
      aoyagiLemma5Eq5_endpointChain_incrementPrefix_preAlpha
        ell a p alpha M m H C layerWidth T hT hH_endpoint
        hi_pos hi_lt hpre
    simpa [hi0, hpre] using hprefix
  have halpha_le : alpha ≤ i + 1 := by omega
  by_cases h_alpha_to_p : i + 1 ≤ p
  · have hprefix :=
      aoyagiLemma5Eq5_endpointChain_incrementPrefix_alphaToP
        ell a p alpha M m H C layerWidth T hT hroom hH_endpoint
        hi_pos hi_lt halpha_le h_alpha_to_p
    simpa [hi0, hpre, h_alpha_to_p] using hprefix
  have hp_le_i : p ≤ i := by omega
  by_cases hpost : i ≤ p + (a - alpha)
  · have hprefix :=
      aoyagiLemma5Eq5_endpointChain_incrementPrefix_postP
        ell a p alpha M m H C layerWidth T hT hroom hH_endpoint
        hi_pos hi_lt hp_le_i hpost
    simpa [hi0, hpre, h_alpha_to_p, hpost] using hprefix
  have htail : p + (a - alpha) + 1 ≤ i := by omega
  have hprefix :=
    aoyagiLemma5Eq5_endpointChain_incrementPrefix_tail
      ell a p alpha M m H C layerWidth T hT hH_endpoint
      hi_pos hi_lt htail
  simpa [hi0, hpre, h_alpha_to_p, hpost] using hprefix

/-- Under the terminal-room inequality, a supplied equation `(5)` endpoint
chain has binary Lemma 4 increment-prefix deltas. -/
theorem aoyagiLemma5Eq5_endpointChain_binaryIncrementPrefixDelta_of_terminalRoom
    (ell a p alpha : ℕ) (M : ℤ) (m H : Fin (ell + 1) → ℤ)
    (C : AoyagiSelectedCutpoints ell) (layerWidth T : ℕ → ℤ)
    (hT : AoyagiLemma5Eq5PiecewiseSourceVector
      ell a p alpha M m C layerWidth T)
    (hroom : p + 2 * a - alpha ≤ ell)
    (hH0 : H 0 = m 0)
    (hHlast : H (Fin.last ell) = 0)
    (hselected :
      (∑ j : Fin (ell + 1), m j) = (ell : ℤ) * (M - 1) + a)
    (hH_endpoint :
      ∀ b : Fin (ell + 1), 1 ≤ b.val → b.val < ell →
        H b = T (C.point b.val - 1)) :
    ∀ r : Fin ell,
      aoyagiLemma4IncrementPrefixDelta ell M m H r = 0 ∨
        aoyagiLemma4IncrementPrefixDelta ell M m H r = 1 := by
  intro r
  let b : ℕ := r.val
  have hb_lt : b < ell := r.isLt
  have hb_le : b ≤ ell := by omega
  have hbsucc_le : b + 1 ≤ ell := by omega
  have hD_b :=
    aoyagiLemma5Eq5_endpointChain_incrementPrefix_profile_of_terminalRoom
      ell a p alpha M m H C layerWidth T hT hroom hH0 hHlast hselected
      hH_endpoint hb_le
  have hD_succ :=
    aoyagiLemma5Eq5_endpointChain_incrementPrefix_profile_of_terminalRoom
      ell a p alpha M m H C layerWidth T hT hroom hH0 hHlast hselected
      hH_endpoint hbsucc_le
  have hsucc :
      r.succ = ⟨b + 1, Nat.lt_succ_of_le hbsucc_le⟩ := by
    ext
    simp [b]
  have hcast :
      r.castSucc = ⟨b, Nat.lt_succ_of_le hb_le⟩ := by
    ext
    simp [b]
  unfold aoyagiLemma4IncrementPrefixDelta
  rw [hsucc, hcast]
  have halpha_le_a : alpha ≤ a := by
    have hexcess := hT.alpha_le_excess
    unfold aoyagiLemma5IntervalExcess at hexcess
    omega
  have halpha_pos := hT.alpha_pos
  have halpha_lt_p := hT.alpha_lt_p
  by_cases hrise_first : b + 2 ≤ alpha
  · have hDb :
        aoyagiLemma4IncrementPrefix ell M m H
          ⟨b, Nat.lt_succ_of_le hb_le⟩ = (b : ℤ) := by
      by_cases hb0 : b = 0
      · simpa [hb0] using hD_b
      · simpa [hb0, hrise_first] using hD_b
    by_cases hsucc_pre : b + 3 ≤ alpha
    · have hsucc_ne : b + 1 ≠ 0 := by omega
      have hDs :
          aoyagiLemma4IncrementPrefix ell M m H
            ⟨b + 1, Nat.lt_succ_of_le hbsucc_le⟩ = ((b + 1 : ℕ) : ℤ) := by
        simpa [hsucc_ne, hsucc_pre] using hD_succ
      rw [hDs, hDb]
      right
      omega
    · have hsucc_ne : b + 1 ≠ 0 := by omega
      have hsucc_to_p : b + 2 ≤ p := by omega
      have hDs :
          aoyagiLemma4IncrementPrefix ell M m H
            ⟨b + 1, Nat.lt_succ_of_le hbsucc_le⟩ =
              ((alpha - 1 : ℕ) : ℤ) := by
        simpa [hsucc_ne, hsucc_pre, hsucc_to_p] using hD_succ
      rw [hDs, hDb]
      right
      omega
  · have halpha_le_current : alpha ≤ b + 1 := by omega
    by_cases hflat : b + 2 ≤ p
    · have hDb :
          aoyagiLemma4IncrementPrefix ell M m H
            ⟨b, Nat.lt_succ_of_le hb_le⟩ =
              ((alpha - 1 : ℕ) : ℤ) := by
        by_cases hb0 : b = 0
        · have halpha_eq : alpha = 1 := by omega
          simpa [hb0, halpha_eq] using hD_b
        · have hb_to_p : b + 1 ≤ p := by omega
          simpa [hb0, hrise_first, hb_to_p] using hD_b
      have hsucc_ne : b + 1 ≠ 0 := by omega
      have hsucc_not_pre : ¬ b + 3 ≤ alpha := by omega
      have hDs :
          aoyagiLemma4IncrementPrefix ell M m H
            ⟨b + 1, Nat.lt_succ_of_le hbsucc_le⟩ =
              ((alpha - 1 : ℕ) : ℤ) := by
        simpa [hsucc_ne, hsucc_not_pre, hflat] using hD_succ
      rw [hDs, hDb]
      left
      omega
    · have hpost_start : p ≤ b + 1 := by omega
      by_cases hrise_second : b + 1 ≤ p + (a - alpha)
      · have hDb :
            aoyagiLemma4IncrementPrefix ell M m H
              ⟨b, Nat.lt_succ_of_le hb_le⟩ =
                ((alpha + b - p : ℕ) : ℤ) := by
          by_cases hb_to_p : b + 1 ≤ p
          · have hb0_false : b ≠ 0 := by omega
            have hprefix :
                aoyagiLemma4IncrementPrefix ell M m H
                  ⟨b, Nat.lt_succ_of_le hb_le⟩ =
                    ((alpha - 1 : ℕ) : ℤ) := by
              simpa [hb0_false, hrise_first, hb_to_p] using hD_b
            have hcast :
                ((alpha - 1 : ℕ) : ℤ) =
                  ((alpha + b - p : ℕ) : ℤ) := by
              omega
            rw [hprefix, hcast]
          · have hb0_false : b ≠ 0 := by omega
            have hb_post : b ≤ p + (a - alpha) := by omega
            simpa [hb0_false, hrise_first, hb_to_p, hb_post] using hD_b
        have hsucc_ne : b + 1 ≠ 0 := by omega
        have hsucc_not_pre : ¬ b + 3 ≤ alpha := by omega
        have hDs :
            aoyagiLemma4IncrementPrefix ell M m H
              ⟨b + 1, Nat.lt_succ_of_le hbsucc_le⟩ =
                ((alpha + (b + 1) - p : ℕ) : ℤ) := by
          simpa [hsucc_ne, hsucc_not_pre, hflat, hrise_second] using hD_succ
        rw [hDs, hDb]
        right
        omega
      · have hDs :
            aoyagiLemma4IncrementPrefix ell M m H
              ⟨b + 1, Nat.lt_succ_of_le hbsucc_le⟩ = (a : ℤ) := by
          have hsucc_ne : b + 1 ≠ 0 := by omega
          have hsucc_not_pre : ¬ b + 3 ≤ alpha := by omega
          simpa [hsucc_ne, hsucc_not_pre, hflat, hrise_second] using hD_succ
        have hDb :
            aoyagiLemma4IncrementPrefix ell M m H
              ⟨b, Nat.lt_succ_of_le hb_le⟩ = (a : ℤ) := by
          by_cases hb_post : b ≤ p + (a - alpha)
          · have hb0_false : b ≠ 0 := by omega
            have hb_not_to_p : ¬ b + 1 ≤ p := by omega
            have hprefix :
                aoyagiLemma4IncrementPrefix ell M m H
                  ⟨b, Nat.lt_succ_of_le hb_le⟩ =
                    ((alpha + b - p : ℕ) : ℤ) := by
              simpa [hb0_false, hrise_first, hb_not_to_p, hb_post] using hD_b
            have hcast : ((alpha + b - p : ℕ) : ℤ) = (a : ℤ) := by
              omega
            rw [hprefix, hcast]
          · have hb0_false : b ≠ 0 := by omega
            have hb_not_to_p : ¬ b + 1 ≤ p := by omega
            simpa [hb0_false, hrise_first, hb_not_to_p, hb_post] using hD_b
        rw [hDs, hDb]
        left
        omega

end Aoyagi
end DLN
end DLNFibre
