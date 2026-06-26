import DLNFibre.DLN.RLCT.Foundations.Rlct
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# `DLNFibre.DLN.RLCT.Foundations.S1Additive` — S1.5 smooth-block contribution

S1.5 is meant to give "a nondegenerate-quadratic (regular) block `Σᵢ xᵢ²`, disjoint from a singular
block `G(y)²`, contributes `n/2`": `λ(Σᵢ xᵢ² + G(y)²) = n/2 + λ(G(y)²)`. What L2 consumes is the
**smooth block contributing its `n/2`**.

## FIDELITY FINDING (gap-class — the bare additivity statement is FALSE)
The committed `Skeleton.rlct_additive_smooth_block` (and the verbatim `_aux` wire-in target) reads,
with `G : Y → ℝ` arbitrary and `[MeasureSpace Y] [TopologicalSpace Y]`:
`rlctAtOn (fun p => (∑ i, p.1 i ^ 2) + G p.2 ^ 2) (0, y0) = n/2 + rlctAtOn (fun y => G y ^ 2) y0`.
This is **false on two independent counts**, neither ruled out by the stated hypotheses:

1. **Non-measurable `G`.** If `G` is not `volume`-measurable, the integrand `|G y|^{−c'}` is not
   `AEStronglyMeasurable`, so it is never `Integrable` (`Integrable ⟹ AEStronglyMeasurable`); hence
   the admissible-exponent set is `∅` (only `c'=0` could survive, and the `c'=0` integrand `1` is
   not integrable on a finite-`volume` nbhd either when `volume Y` is infinite) and `rlctAtOn (G²)
   y0 = sSup ∅ = 0`. The product integrand on the LHS is likewise non-measurable, so LHS `= 0` too,
   and the equation becomes `0 = n/2 + 0` — **false for `n ≥ 1`**. (Same mechanism as S1.1, S1.3.)

2. **`G ≡ 0` (the vanishing-loss convention).** Under Mathlib's `rpow` convention `0^{neg} = 0`, the
   integrand `|G y|^{−c'}` for `G ≡ 0` is the zero function for every `c' > 0`, integrable on every
   open set; so `rlctAtOn (G²) y0 = ⊤` (proven below as `rlctAtOn_zero_eq_top`). Then RHS `= n/2 + ⊤
   = ⊤`, while the LHS — the smooth block `Σᵢ xᵢ²` times a finite `y`-factor on a reasonable `Y`
   (e.g. `Y = ℝ`, where bounded nbhds have finite `volume`) — is **finite** (`= n/2`; the
   `rlctAtOn_zero_eq_top` half is Lean-proven, the LHS-finite half is the standard radial bound). So
   the equation reads `n/2 = ⊤` — **false** for `n ≥ 1`. This is *not*
   fixed by adding `Measurable G`: it is the same `≢0`-loss convention the `Rlct` docstring already
   names (`F(w*) ≠ 0` ⟹ `+∞`). The honest additivity needs the singular block to genuinely vanish
   near `y0` (`rlctAtOn (G²) y0 < ⊤`) **and** real-analyticity (the general measurable additivity
   fails — Skeleton's own note: alternating step functions give `⊤ ≠ 2`); that general
   real-analytic disjoint additivity (Aoyagi App. C Lemma 2) is heavy Laplace/Tauberian machinery,
   **roadmapped off** the critical path.

So the verbatim `rlct_additive_smooth_block_aux` is **not carried here as a `sorry`** (a `sorry`
belongs under a *correct* statement; this one is false). Instead this file delivers the honest,
true, reusable substrate the rung actually rests on:

* `rlctAtOn_zero_eq_top` — the `≡0`-loss convention fact (the witness for gap 2), reusable.
* `smoothBlock1D_rlct` — the smooth block `x²` on `ℝ` has RLCT `1/2` (the `n = 1` case), proven
  axiom-free from the single-variable `rpow` integrability iff. This is the analytic-clean fact L2
  consumes per regular coordinate.

The general-`n` smooth block `rlctAtOn (fun x : Fin n → ℝ => ∑ i, x i ^ 2) 0 = n/2` (for `n ≥ 1`;
**`n = 0` is itself a corner**: the empty sum is `≡ 0`, so the LHS is `⊤`, not `0/2 = 0`) needs the
radial fact `‖x‖^{−2c}` integrable near `0 ⟺ c < n/2`, which Mathlib lacks (no
`‖x‖^p`-integrable-near-`0` lemma; it would be a polar-coordinates / layer-cake computation). It is
flagged here as the remaining sub-task; the `n = 1` instance is closed.
-/

namespace DLNFibre.DLN.RLCT

open MeasureTheory Set Real
open scoped ENNReal Topology

/-! ## The `≡0`-loss convention: `rlctAtOn` of the zero function is `⊤` (gap-2 witness) -/

/-- **The `≡0`-loss convention (gap-2 witness).** On any measure/topological space, `rlctAtOn` of
the identically-zero function is `⊤`: under the `rpow` convention `0^{neg} = 0`, the integrand
`|0|^{−c'}·1` is the zero function for every `c' > 0`, integrable on `Set.univ`; so the
admissible-exponent set is unbounded and its `sSup` is `⊤`. This is exactly why the bare additivity
fails for `G ≡ 0` (RHS `= n/2 + ⊤ = ⊤ ≠` finite LHS). -/
theorem rlctAtOn_zero_eq_top {M : Type*} [MeasureSpace M] [TopologicalSpace M] (w : M) :
    rlctAtOn (fun _ : M => (0 : ℝ)) w = ⊤ := by
  unfold rlctAtOn weightedThreshold
  rw [sSup_eq_top]
  intro b hb
  refine ⟨((b.toNNReal + 1 : NNReal) : ℝ≥0∞), ⟨b.toNNReal + 1, rfl, ?_⟩, ?_⟩
  · refine ⟨Set.univ, isOpen_univ, Set.subset_univ _, ?_⟩
    have hzero : (fun _ : M => |(0 : ℝ)| ^ (-((b.toNNReal + 1 : NNReal) : ℝ)) * (1 : ℝ))
        = (fun _ : M => (0 : ℝ)) := by
      funext _
      have hc : ((b.toNNReal + 1 : NNReal) : ℝ) ≠ 0 := by positivity
      rw [abs_zero, Real.zero_rpow (neg_ne_zero.mpr hc), zero_mul]
    rw [hzero]
    exact integrableOn_zero
  · have h1 : b < (b.toNNReal : ℝ≥0∞) + 1 := by
      calc b = (b.toNNReal : ℝ≥0∞) := (ENNReal.coe_toNNReal hb.ne).symm
        _ < (b.toNNReal : ℝ≥0∞) + 1 := ENNReal.lt_add_right (by simp) (by simp)
    have h2 : (((b.toNNReal + 1 : NNReal)) : ℝ≥0∞) = (b.toNNReal : ℝ≥0∞) + 1 := by
      push_cast; rfl
    rw [h2]; exact h1

/-! ## The smooth block `x²` on `ℝ` has RLCT `1/2` (the `n = 1` case)

The single-variable spine, reproved locally (no `Skeleton`/`Case111Bridge` dependency, so this file
imports only the foundations): `|x|^s` integrable on the symmetric `Icc (-ε) ε` iff `−1 < s`, lifted
through the `x²`-integrand simplification `|x²|^{−c'} = |x|^{−2c'}` and the open-neighbourhood
form of `rlctAtOn`. -/

/-- `|x|^s` is integrable on the symmetric interval `[-ε, ε]` (a `𝓝 0`-shaped chart) **iff**
`−1 < s`. Forward: restrict to the right half (`|x| = x`) and apply the single-axis `rpow` iff. Then
glue the two halves, the negative half by reflection through `x ↦ -x`. (A local copy of the banked
`abs_rpow_integrableOn_Icc_symm_iff`, to keep this file off the `Skeleton` import chain.) -/
theorem abs_rpow_integrableOn_Icc_symm (s ε : ℝ) (hε : 0 < ε) :
    IntegrableOn (fun x : ℝ => |x| ^ s) (Icc (-ε) ε) volume ↔ -1 < s := by
  have hposEq : EqOn (fun x : ℝ => |x| ^ s) (fun x : ℝ => x ^ s) (Ioo (0 : ℝ) ε) :=
    fun x hx => by simp only; rw [abs_of_pos hx.1]
  constructor
  · intro h
    have hsub : Ioo (0 : ℝ) ε ⊆ Icc (-ε) ε := fun x hx => ⟨by linarith [hx.1], le_of_lt hx.2⟩
    have hr := h.mono_set hsub
    rw [integrableOn_congr_fun hposEq measurableSet_Ioo,
      intervalIntegral.integrableOn_Ioo_rpow_iff hε] at hr
    exact hr
  · intro hs
    have hpos : IntegrableOn (fun x : ℝ => |x| ^ s) (Icc (0 : ℝ) ε) volume := by
      rw [integrableOn_Icc_iff_integrableOn_Ioo, integrableOn_congr_fun hposEq measurableSet_Ioo,
        intervalIntegral.integrableOn_Ioo_rpow_iff hε]
      exact hs
    have hneg : IntegrableOn (fun x : ℝ => |x| ^ s) (Icc (-ε) 0) volume := by
      have hmp := (Measure.measurePreserving_neg (volume : Measure ℝ)).integrableOn_comp_preimage
        (measurableEmbedding_neg (α := ℝ)) (f := fun x : ℝ => |x| ^ s) (s := Icc (0 : ℝ) ε)
      have hpre : (fun x : ℝ => -x) ⁻¹' Icc (0 : ℝ) ε = Icc (-ε) 0 := by
        ext x; simp only [mem_preimage, mem_Icc, neg_nonneg]
        constructor
        · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩
        · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩
      have hfun : ((fun x : ℝ => |x| ^ s) ∘ fun x : ℝ => -x) = (fun x : ℝ => |x| ^ s) := by
        funext x; simp [abs_neg]
      rw [hpre, hfun] at hmp
      exact hmp.2 hpos
    have hunion : Icc (-ε) ε = Icc (-ε) 0 ∪ Icc (0 : ℝ) ε :=
      (Icc_union_Icc_eq_Icc (by linarith) (le_of_lt hε)).symm
    rw [hunion]; exact hneg.union hpos

/-- The admissibility predicate for the `1`-D smooth block `x²`, in the open-neighbourhood form: for
`c' : NNReal`, some open `Ω ∋ 0` carries `|x²|^{−c'}·1` integrably **iff** `c' < 1/2`. Forward: any
open `Ω ∋ 0` contains a symmetric `Ioo (-ε) ε`, so restrict to `Icc (-ε/2) (ε/2)` and apply the
symmetric `rpow` iff to `s = −2c'`. Reverse: `Ioo (-1) 1` works (subset of `Icc (-1) 1`). -/
theorem smoothBlock1D_admissible_iff (c' : NNReal) :
    (∃ Ω : Set ℝ, IsOpen Ω ∧ (0 : ℝ) ∈ Ω ∧
        IntegrableOn (fun x : ℝ => |x ^ 2| ^ (-(c' : ℝ)) * (1 : ℝ)) Ω volume)
      ↔ (c' : ℝ) < 1 / 2 := by
  have hrw : (fun x : ℝ => |x ^ 2| ^ (-(c' : ℝ)) * (1 : ℝ))
      = fun x : ℝ => |x| ^ (-(2 * (c' : ℝ))) := by
    funext x; rw [mul_one, abs_pow, ← Real.rpow_natCast |x| 2, ← Real.rpow_mul (abs_nonneg x)]
    ring_nf
  rw [hrw]
  constructor
  · rintro ⟨Ω, hΩopen, h0, hint⟩
    obtain ⟨l, u, hlu, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.1 (hΩopen.mem_nhds h0)
    set ε := min (-l) u with hε
    have hεpos : 0 < ε := lt_min (by linarith [hlu.1]) hlu.2
    have hεl : ε ≤ -l := min_le_left (-l) u
    have hεu : ε ≤ u := min_le_right (-l) u
    have hIoosub : Ioo (-ε) ε ⊆ Ω := fun x hx => hsub ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have hr := hint.mono_set hIoosub
    have hIccsub : Icc (-(ε / 2)) (ε / 2) ⊆ Ioo (-ε) ε :=
      fun x hx => ⟨by linarith [hx.1, hεpos], by linarith [hx.2, hεpos]⟩
    have hr2 := hr.mono_set hIccsub
    rw [abs_rpow_integrableOn_Icc_symm _ _ (by linarith : (0 : ℝ) < ε / 2)] at hr2
    linarith
  · intro hc
    refine ⟨Ioo (-1) 1, isOpen_Ioo, by norm_num, ?_⟩
    have hint : IntegrableOn (fun x : ℝ => |x| ^ (-(2 * (c' : ℝ)))) (Icc (-(1 : ℝ)) 1) volume := by
      rw [abs_rpow_integrableOn_Icc_symm _ _ (by norm_num : (0 : ℝ) < 1)]
      push_cast at hc ⊢; linarith
    exact hint.mono_set Ioo_subset_Icc_self

/-- **The smooth block, `n = 1`.** `rlctAtOn (fun x : ℝ => x²) 0 = 1/2`: the regular-coordinate RLCT
that L2 adds up. The admissible-exponent set is the coerced `{c' : NNReal | c' < 1/2}`
(`smoothBlock1D_admissible_iff`), whose `sSup` in `ℝ≥0∞` is `1/2`. Axiom-free (only
`propext`/`Classical.choice`/`Quot.sound`). -/
theorem smoothBlock1D_rlct : rlctAtOn (fun x : ℝ => x ^ 2) (0 : ℝ) = (1 / 2 : ℝ≥0∞) := by
  unfold rlctAtOn weightedThreshold
  have hset : { c : ℝ≥0∞ | ∃ c' : NNReal, c = (c' : ℝ≥0∞) ∧
        ∃ Ω : Set ℝ, IsOpen Ω ∧ {(0 : ℝ)} ⊆ Ω ∧
          IntegrableOn (fun x : ℝ => |x ^ 2| ^ (-(c' : ℝ)) * (1 : ℝ)) Ω volume }
      = { c : ℝ≥0∞ | ∃ c' : NNReal, c = (c' : ℝ≥0∞) ∧ (c' : ℝ) < 1 / 2 } := by
    ext c; constructor
    · rintro ⟨c', rfl, Ω, hΩopen, h0, hint⟩
      exact ⟨c', rfl, (smoothBlock1D_admissible_iff c').1 ⟨Ω, hΩopen, h0 rfl, hint⟩⟩
    · rintro ⟨c', rfl, hc⟩
      obtain ⟨Ω, hΩopen, h0, hint⟩ := (smoothBlock1D_admissible_iff c').2 hc
      exact ⟨c', rfl, Ω, hΩopen, by simpa using h0, hint⟩
  rw [hset]
  apply le_antisymm
  · apply sSup_le; rintro c ⟨c', rfl, hc⟩
    rw [show (1 / 2 : ℝ≥0∞) = ((1 / 2 : NNReal) : ℝ≥0∞) by simp]
    rw [ENNReal.coe_le_coe, ← NNReal.coe_le_coe]; push_cast; linarith
  · apply le_of_forall_lt_imp_le_of_dense
    intro q hq
    have hqfin : q ≠ ⊤ := by intro h; rw [h] at hq; simp at hq
    apply le_sSup
    refine ⟨q.toNNReal, (ENNReal.coe_toNNReal hqfin).symm, ?_⟩
    have hqt : q.toReal < (1 / 2 : ℝ) := by
      have := (ENNReal.toReal_lt_toReal hqfin (by simp : (1 / 2 : ℝ≥0∞) ≠ ⊤)).2 hq
      simpa using this
    exact hqt

end DLNFibre.DLN.RLCT
