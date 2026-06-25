import DLNFibre.DLN.RLCT.Foundations.Rlct
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# `DLNFibre.DLN.RLCT.Foundations.S1SmoothBlock` — the general-`n` smooth block

The regular-coordinate contribution L2 consumes: a nondegenerate quadratic block `∑ᵢ xᵢ²` on `ℝⁿ`
has RLCT `n/2`. This is the general-`n` extension of `S1Additive.smoothBlock1D_rlct` (the `n = 1`
case), needed by L2 **regardless** of the disjoint-block additivity strategy (the regular block's
RLCT is `n/2` either way; the 12th finding showed the *additive* combination is the subtle part, not
this value).

## The radial route (no Mathlib-gap)
Earlier this was flagged as a Mathlib-gap (no local `‖x‖^{−a}`-near-`0` integrability lemma). It is
not a gap: Mathlib's `MeasureTheory.integrable_fun_norm_addHaar` reduces integrability of a radial
function `f(‖x‖)` on `ℝⁿ` to integrability of `y ↦ y^{n−1}·f(y)` on `Ioi 0`. Truncating `f` to
a ball localises this to the neighbourhood the RLCT needs, and the surviving `1`-D fact is standard
`rpow` integrability `intervalIntegral.integrableOn_Ioo_rpow_iff`.

Stated on `M = EuclideanSpace ℝ (Fin n)`, where the ambient `volume` **is** the additive Haar
measure (`integrable_fun_norm_addHaar`'s hypothesis) and `‖x‖² = ∑ᵢ xᵢ²` (`EuclideanSpace.norm_eq`),
so no measure-isomorphism bridge is needed. (`n = 0` is itself a corner: the empty sum is `≡ 0`, so
the RLCT is `⊤`, not `0/2 = 0`; the theorem is stated for `n = m + 1 ≥ 1`.)
-/

namespace DLNFibre.DLN.RLCT

open MeasureTheory Set Real Metric
open scoped ENNReal Topology

/-! ## The truncated `1`-D radial integrand -/

/-- The `1`-D radial integrand after the addHaar reduction (`f` truncated to `[0, R)`): for `R > 0`,
`(if y < R then y^s else 0)` is integrable on `Ioi 0` **iff** `−1 < s`. The function is supported on
`Ioo 0 R` (where it is `y^s`, governed by `intervalIntegral.integrableOn_Ioo_rpow_iff`) and `0` on
`Ici R`. -/
theorem oneDimTrunc_iff (R s : ℝ) (hR : 0 < R) :
    IntegrableOn (fun y : ℝ => if y < R then y ^ s else 0) (Ioi 0) volume ↔ -1 < s := by
  constructor
  · intro h
    have hsub : Ioo (0:ℝ) R ⊆ Ioi 0 := fun y hy => hy.1
    have hr := h.mono_set hsub
    have heq : EqOn (fun y : ℝ => if y < R then y ^ s else 0) (fun y : ℝ => y ^ s) (Ioo 0 R) :=
      fun y hy => by simp [if_pos hy.2]
    rw [integrableOn_congr_fun heq measurableSet_Ioo,
      intervalIntegral.integrableOn_Ioo_rpow_iff hR] at hr
    exact hr
  · intro hs
    have hsplit : Ioi (0:ℝ) = Ioo 0 R ∪ Ici R := by
      ext y; simp only [mem_Ioi, mem_union, mem_Ioo, mem_Ici]
      constructor
      · intro hy; rcases le_or_gt R y with h | h
        · exact Or.inr h
        · exact Or.inl ⟨hy, h⟩
      · rintro (⟨h1, _⟩ | h1)
        · exact h1
        · linarith
    rw [hsplit]
    apply IntegrableOn.union
    · have heq : EqOn (fun y : ℝ => if y < R then y ^ s else 0) (fun y : ℝ => y ^ s) (Ioo 0 R) :=
        fun y hy => by simp [if_pos hy.2]
      rw [integrableOn_congr_fun heq measurableSet_Ioo]
      exact (intervalIntegral.integrableOn_Ioo_rpow_iff hR).mpr hs
    · have heq : EqOn (fun y : ℝ => if y < R then y ^ s else 0) (fun _ : ℝ => (0:ℝ)) (Ici R) := by
        intro y hy; simp only [mem_Ici] at hy; simp [if_neg (not_lt.mpr hy)]
      rw [integrableOn_congr_fun heq measurableSet_Ici]
      exact integrableOn_zero

/-! ## The ball-localised radial power integrability -/

/-- **The local radial power law.** On `EuclideanSpace ℝ (Fin (m+1))`, `‖x‖^s` is integrable on the
ball `ball 0 R` (`R > 0`) **iff** `−(m+1) < s`. The keystone: truncate `f = |·|^s` to `[0,R)` so
`f∘‖·‖` vanishes off the ball, apply `integrable_fun_norm_addHaar` (`volume` is the Haar measure on
`EuclideanSpace`), and read off the surviving `1`-D condition via `oneDimTrunc_iff` (the radial
Jacobian shifts the exponent `s ↦ m + s`, so `−1 < m + s ⟺ −(m+1) < s`). -/
theorem radial_ball_iff (m : ℕ) (R s : ℝ) (hR : 0 < R) :
    IntegrableOn (fun x : EuclideanSpace ℝ (Fin (m+1)) => ‖x‖ ^ s) (ball 0 R) volume
      ↔ -(m+1 : ℝ) < s := by
  set g : ℝ → ℝ := fun t => if t < R then |t| ^ s else 0 with hg
  have hagree_ball : EqOn (fun x : EuclideanSpace ℝ (Fin (m+1)) => g ‖x‖)
      (fun x => ‖x‖ ^ s) (ball 0 R) := by
    intro x hx; simp only [hg, mem_ball_zero_iff] at hx ⊢
    rw [if_pos hx, abs_of_nonneg (norm_nonneg _)]
  have hagree_compl : EqOn (fun x : EuclideanSpace ℝ (Fin (m+1)) => g ‖x‖)
      (fun _ => (0:ℝ)) (ball 0 R)ᶜ := by
    intro x hx; simp only [hg, mem_compl_iff, mem_ball_zero_iff, not_lt] at hx ⊢
    rw [if_neg (by linarith : ¬ ‖x‖ < R)]
  -- (1) ball-integrability of `‖x‖^s` ⟺ global integrability of the truncated `g∘‖·‖`.
  have step1 : IntegrableOn (fun x : EuclideanSpace ℝ (Fin (m+1)) => ‖x‖ ^ s) (ball 0 R) volume
      ↔ Integrable (fun x : EuclideanSpace ℝ (Fin (m+1)) => g ‖x‖) volume := by
    rw [← integrableOn_univ, ← union_compl_self (ball (0:EuclideanSpace ℝ (Fin (m+1))) R)]
    constructor
    · intro h
      refine IntegrableOn.union ?_ ?_
      · exact h.congr_fun hagree_ball.symm measurableSet_ball
      · exact (integrableOn_zero).congr_fun hagree_compl.symm measurableSet_ball.compl
    · intro h
      exact (h.mono_set subset_union_left).congr_fun hagree_ball measurableSet_ball
  rw [step1]
  -- (2) the addHaar radial reduction.
  have key := integrable_fun_norm_addHaar (E := EuclideanSpace ℝ (Fin (m+1))) (volume) (f := g)
  rw [show Module.finrank ℝ (EuclideanSpace ℝ (Fin (m+1))) = m+1 from by simp] at key
  rw [key]
  -- (3) the `1`-D side: `y^m • g y = (if y < R then y^{m+s} else 0)` on `Ioi 0`.
  have h1deq : EqOn (fun y : ℝ => y ^ (m+1 - 1) • g y)
      (fun y : ℝ => if y < R then y ^ ((m:ℝ) + s) else 0) (Ioi 0) := by
    intro y hy
    simp only [hg, smul_eq_mul, Nat.add_sub_cancel, mem_Ioi] at hy ⊢
    rw [abs_of_pos hy]
    by_cases h : y < R
    · simp only [if_pos h]
      rw [← Real.rpow_natCast y m, ← Real.rpow_add hy]
    · simp [if_neg h]
  rw [integrableOn_congr_fun h1deq measurableSet_Ioi, oneDimTrunc_iff R _ hR]
  constructor <;> intro h <;> linarith

/-! ## The general-`n` smooth block -/

/-- The admissibility predicate for the `n`-D smooth block `∑ᵢ xᵢ²` (`n = m+1`), in the
open-neighbourhood form: for `c' : NNReal`, some open `Ω ∋ 0` carries `|∑ᵢ xᵢ²|^{−c'}·1` integrably
**iff** `c' < (m+1)/2`. The integrand is `‖x‖^{−2c'}` (`EuclideanSpace.norm_eq`), so this is
`radial_ball_iff` at `s = −2c'` (`−(m+1) < −2c' ⟺ c' < (m+1)/2`); forward shrinks an arbitrary open
`Ω ∋ 0` to a `ball 0 ε`, reverse uses `ball 0 1`. -/
theorem smoothBlockND_admissible_iff (m : ℕ) (c' : NNReal) :
    (∃ Ω : Set (EuclideanSpace ℝ (Fin (m+1))), IsOpen Ω ∧ (0 : EuclideanSpace ℝ (Fin (m+1))) ∈ Ω ∧
        IntegrableOn (fun x => |∑ i, x i ^ 2| ^ (-(c' : ℝ)) * (1 : ℝ)) Ω volume)
      ↔ (c' : ℝ) < (m + 1) / 2 := by
  -- the integrand is `‖x‖^{−2c'}`.
  have hrw : (fun x : EuclideanSpace ℝ (Fin (m+1)) => |∑ i, x i ^ 2| ^ (-(c' : ℝ)) * (1 : ℝ))
      = fun x => ‖x‖ ^ (-(2 * (c' : ℝ))) := by
    funext x
    rw [mul_one]
    have hnorm : ∑ i, x i ^ 2 = ‖x‖ ^ 2 := by
      rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
      congr 1; ext i; rw [Real.norm_eq_abs, sq_abs]
    rw [hnorm, abs_of_nonneg (by positivity), ← Real.rpow_natCast ‖x‖ 2,
      ← Real.rpow_mul (norm_nonneg _)]
    ring_nf
  rw [hrw]
  constructor
  · rintro ⟨Ω, hΩopen, h0, hint⟩
    -- shrink `Ω` to a `ball 0 ε`, apply `radial_ball_iff`.
    obtain ⟨ε, hεpos, hball⟩ := Metric.isOpen_iff.1 hΩopen 0 h0
    have hr := hint.mono_set hball
    rw [radial_ball_iff m ε _ hεpos] at hr
    -- `−(m+1) < −2c' ⟹ c' < (m+1)/2`.
    have : 2 * (c' : ℝ) < (m + 1) := by linarith
    linarith
  · intro hc
    -- witness `ball 0 1`; `radial_ball_iff` needs `−(m+1) < −2c'`.
    refine ⟨ball 0 1, isOpen_ball, mem_ball_self one_pos, ?_⟩
    rw [radial_ball_iff m 1 _ one_pos]
    have : 2 * (c' : ℝ) < (m + 1) := by linarith
    linarith

/-- **The smooth block, general `n = m+1 ≥ 1`.** `rlctAtOn (fun x : EuclideanSpace ℝ (Fin (m+1)) =>
∑ᵢ xᵢ²) 0 = (m+1)/2`: the regular-block RLCT L2 sums up (one `½` per regular coordinate). The
admissible-exponent set is the coerced `{c' : NNReal | c' < (m+1)/2}`
(`smoothBlockND_admissible_iff`), whose `sSup` in `ℝ≥0∞` is `(m+1)/2`. Axiom-free (only
`propext`/`Classical.choice`/`Quot.sound`). Generalises `S1Additive.smoothBlock1D_rlct`
(the `m = 0` case). -/
theorem smoothBlockND_rlct (m : ℕ) :
    rlctAtOn (fun x : EuclideanSpace ℝ (Fin (m+1)) => ∑ i, x i ^ 2)
        (0 : EuclideanSpace ℝ (Fin (m+1))) = ((m + 1) / 2 : ℝ≥0∞) := by
  unfold rlctAtOn weightedThreshold
  have hset : { c : ℝ≥0∞ | ∃ c' : NNReal, c = (c' : ℝ≥0∞) ∧
        ∃ Ω : Set (EuclideanSpace ℝ (Fin (m+1))), IsOpen Ω ∧
          {(0 : EuclideanSpace ℝ (Fin (m+1)))} ⊆ Ω ∧
          IntegrableOn (fun x => |∑ i, x i ^ 2| ^ (-(c' : ℝ)) * (1 : ℝ)) Ω volume }
      = { c : ℝ≥0∞ | ∃ c' : NNReal, c = (c' : ℝ≥0∞) ∧ (c' : ℝ) < (m + 1) / 2 } := by
    ext c; constructor
    · rintro ⟨c', rfl, Ω, hΩopen, h0, hint⟩
      exact ⟨c', rfl, (smoothBlockND_admissible_iff m c').1 ⟨Ω, hΩopen, h0 rfl, hint⟩⟩
    · rintro ⟨c', rfl, hc⟩
      obtain ⟨Ω, hΩopen, h0, hint⟩ := (smoothBlockND_admissible_iff m c').2 hc
      exact ⟨c', rfl, Ω, hΩopen, by simpa using h0, hint⟩
  rw [hset]
  -- `sSup {c' : NNReal | c' < (m+1)/2}` coerced to `ℝ≥0∞` is `(m+1)/2`.
  apply le_antisymm
  · apply sSup_le; rintro c ⟨c', rfl, hc⟩
    rw [show ((m + 1) / 2 : ℝ≥0∞) = (((m + 1) / 2 : NNReal) : ℝ≥0∞) by
      rw [ENNReal.coe_div (by norm_num)]; push_cast; rfl]
    rw [ENNReal.coe_le_coe, ← NNReal.coe_le_coe]; push_cast; linarith
  · apply le_of_forall_lt_imp_le_of_dense
    intro q hq
    have hqfin : q ≠ ⊤ := by intro h; rw [h] at hq; simp at hq
    apply le_sSup
    refine ⟨q.toNNReal, (ENNReal.coe_toNNReal hqfin).symm, ?_⟩
    have hqt : q.toReal < ((m + 1) / 2 : ℝ) := by
      have hfin : ((m + 1) / 2 : ℝ≥0∞) ≠ ⊤ := by
        rw [show ((m + 1) / 2 : ℝ≥0∞) = (((m + 1) / 2 : NNReal) : ℝ≥0∞) by
          rw [ENNReal.coe_div (by norm_num)]; push_cast; rfl]
        exact ENNReal.coe_ne_top
      have := (ENNReal.toReal_lt_toReal hqfin hfin).2 hq
      rw [ENNReal.toReal_div] at this
      simpa using this
    simpa using hqt

end DLNFibre.DLN.RLCT
