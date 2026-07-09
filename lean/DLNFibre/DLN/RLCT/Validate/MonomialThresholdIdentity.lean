import DLNFibre.DLN.RLCT.Validate.RouteMSJMonomialLower

/-!
# `DLNFibre.DLN.RLCT.Validate.MonomialThresholdIdentity` — the S2-FREE monomial-threshold IDENTITY

**Thread `genm-decites2`, STAGE A of the S2 de-citation.** The weighted-monomial RLCT threshold
equals the per-axis minimum, PROVEN (no `monomial_rlct`):

    monomialThreshold d k h = ⨅_j axisRatio (h j) (k j).

This is the *threshold conjunct* `(monomial_rlct d k h).1` of the cited S2 axiom, now discharged
from Mathlib. The two directions:

* **finiteness (`≤`/lower)** — `⨅ axisRatio ≤ monomialThreshold` — is BANKED, S2-free, in
  `RouteMSJMonomialLower.iInf_axisRatio_le_monomialThreshold` (below the per-axis minimum every
  chart converges).
* **divergence (`≥`/upper)** — `monomialThreshold ≤ ⨅ axisRatio` — is built HERE: any `c'` in the
  integrability down-set must lie below every per-axis ratio, because an axis `j` with
  `axisRatio (h j) (k j) < c'` has one-variable exponent `h_j − 2 k_j c' ≤ −1`, and the box integral
  then diverges (`Case222Cover.monomialIntegrand_lintegral_box_eq_top_of_axis`, the S2-free
  sub-box + 1-D `rpow`-divergence core), contradicting integrability.

`le_antisymm` of the two gives `monomialThreshold_eq_iInf_axisRatio` — the both-directions equality
that `monomial_rlct.1` supplied, now PROVEN and S2-FREE.

Axiom-clean `[propext, Classical.choice, Quot.sound]`: no `monomial_rlct`, no `cited_aoyagi_dln`, no
`sorryAx`. Only the *order conjunct* `(monomial_rlct d k h).2` (the pole-order `monomialOrderAnalytic
= monomialOrder`, needing meromorphic continuation Lean lacks) genuinely still needs the citation;
that is Stage B and is untouched here.
-/

namespace DLNFibre.DLN.RLCT

open MeasureTheory Set
open scoped ENNReal BigOperators

/-- **`axisRatio h 0 = ⊤`.** A `k = 0` axis is a spectator (the function is a unit in that
direction): `(h+1)/(2·0) = (h+1)/0 = ⊤`. -/
theorem axisRatio_k_zero_eq_top (h : ℕ) : axisRatio h 0 = ⊤ := by
  rw [axisRatio, Nat.cast_zero, mul_zero,
    ENNReal.div_zero (by positivity : ((h : ℝ≥0∞) + 1) ≠ 0)]

/-- **Exponent bound from a binding ratio.** If `k ≠ 0` and the per-axis ratio is at-or-below `c'`
(`axisRatio h k ≤ ofReal c'`), the one-variable exponent `(h : ℝ) − 2 k c'` is `≤ −1` (the 1-D
`rpow`-divergence condition). The arithmetic core of `Case222Cover.exists_binding_axis`, factored out
S2-free (it never touches `monomial_rlct`). -/
theorem exp_le_neg_one_of_axisRatio_le {h k : ℕ} {c' : ℝ} (hc'nn : 0 ≤ c') (hk : k ≠ 0)
    (hle : axisRatio h k ≤ ENNReal.ofReal c') :
    (h : ℝ) - 2 * (k : ℝ) * c' ≤ -1 := by
  unfold axisRatio at hle
  have hbne0 : (2 * (k : ℝ≥0∞)) ≠ 0 := by
    simp only [ne_eq, mul_eq_zero, not_or]; exact ⟨by norm_num, by exact_mod_cast hk⟩
  have hbnetop : (2 * (k : ℝ≥0∞)) ≠ ∞ := by finiteness
  rw [ENNReal.div_le_iff_le_mul (Or.inl hbne0) (Or.inl hbnetop)] at hle
  have h2k : (2 * (k : ℝ≥0∞)) = ENNReal.ofReal (2 * (k : ℝ)) := by
    rw [ENNReal.ofReal_mul (by norm_num)]; congr 1
    · simp [ENNReal.ofReal_ofNat]
    · rw [ENNReal.ofReal_natCast]
  rw [h2k, ← ENNReal.ofReal_mul hc'nn] at hle
  have hh1 : ((h : ℝ≥0∞) + 1) = ENNReal.ofReal ((h : ℝ) + 1) := by
    rw [ENNReal.ofReal_add (by positivity) (by norm_num)]; congr 1
    · rw [ENNReal.ofReal_natCast]
    · simp
  rw [hh1, ENNReal.ofReal_le_ofReal_iff (by positivity)] at hle
  nlinarith [hle]

/-- **The S2-FREE monomial-threshold divergence (upper) bound.** `monomialThreshold d k h ≤
⨅_j axisRatio (h j) (k j)`, proved constructively (no `monomial_rlct`): every `c'` in the
integrability down-set lies `≤` every per-axis ratio, since an axis `j` with `axisRatio (h j) (k j) <
c'` has exponent `h_j − 2 k_j c' ≤ −1`, forcing the box integral to `⊤`
(`monomialIntegrand_lintegral_box_eq_top_of_axis`) — contradicting the down-set membership. -/
theorem monomialThreshold_le_iInf_axisRatio (d : ℕ) (k h : Fin d → ℕ) :
    monomialThreshold d k h ≤ ⨅ j, axisRatio (h j) (k j) := by
  apply sSup_le
  rintro c ⟨c', rfl, hint⟩
  rw [le_iInf_iff]
  intro j
  rcases Nat.eq_zero_or_pos (k j) with hk0 | hkpos
  · rw [hk0, axisRatio_k_zero_eq_top]; exact le_top
  · by_contra hlt
    push_neg at hlt
    -- `hlt : axisRatio (h j) (k j) < (c' : ℝ≥0∞)`
    have hkne : k j ≠ 0 := hkpos.ne'
    have hle : axisRatio (h j) (k j) ≤ ENNReal.ofReal (c' : ℝ) := by
      rw [ENNReal.ofReal_coe_nnreal]; exact hlt.le
    have hexp : (h j : ℝ) - 2 * (k j : ℝ) * (c' : ℝ) ≤ -1 :=
      exp_le_neg_one_of_axisRatio_le c'.coe_nonneg hkne hle
    -- box divergence over the unit box contradicts integrability
    have hbox := monomialIntegrand_lintegral_box_eq_top_of_axis d k h (c' : ℝ) j hexp (ε := 1) one_pos
    have hdiv : ∫⁻ u in unitBox d, ENNReal.ofReal (monomialIntegrand d k h (c' : ℝ) u) = ⊤ := by
      rw [← hbox]
      refine setLIntegral_congr_fun (MeasurableSet.univ_pi (fun _ => measurableSet_Icc)) ?_
      intro u _
      exact congrArg ENNReal.ofReal (abs_of_nonneg (monomialIntegrand_nonneg' d k h (c' : ℝ) u)).symm
    have hfin : ∫⁻ u in unitBox d, ENNReal.ofReal (monomialIntegrand d k h (c' : ℝ) u) < ⊤ :=
      (hasFiniteIntegral_iff_ofReal
        (ae_of_all _ (fun u => monomialIntegrand_nonneg' d k h (c' : ℝ) u))).mp hint.2
    rw [hdiv] at hfin
    exact lt_irrefl ⊤ hfin

/-- **The S2-FREE monomial-threshold IDENTITY** (the discharged `(monomial_rlct d k h).1`).
`monomialThreshold d k h = ⨅_j axisRatio (h j) (k j)`, PROVEN with no `monomial_rlct`: `le_antisymm`
of the divergence bound (`monomialThreshold_le_iInf_axisRatio`, here) and the banked finiteness bound
(`iInf_axisRatio_le_monomialThreshold`, `RouteMSJMonomialLower`). This is the both-directions equality
the S2 threshold conjunct supplied; the λ-path consumers re-point to this. -/
theorem monomialThreshold_eq_iInf_axisRatio (d : ℕ) (k h : Fin d → ℕ) :
    monomialThreshold d k h = ⨅ j, axisRatio (h j) (k j) :=
  le_antisymm (monomialThreshold_le_iInf_axisRatio d k h)
    (iInf_axisRatio_le_monomialThreshold d k h)

end DLNFibre.DLN.RLCT
