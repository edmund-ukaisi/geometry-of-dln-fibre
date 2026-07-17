import DLNFibre.DLN.RLCT.Validate.RouteMSJResolution
import DLNFibre.DLN.RLCT.Validate.RouteMSJDecoratedCharge
import DLNFibre.DLN.RLCT.Validate.RouteMSJQBoxCore
import DLNFibre.DLN.RLCT.Validate.RouteMSchurCorankSlabD

/-!
# `DLNFibre.DLN.RLCT.Validate.RouteMSJFrontCollapse` — the front-collapse rank-sector atom (§1)

**Thread `genm-lane1-shell`, the Lane-1 native heart** (d1design `d1-atom-spec.md §1`). The single
genuinely-new native object the `d≤1` arm of `innerCorankDescent_lt_top` funnels to: reduce the
pivot-energy box integral `∫ (frobSq (F · prod(tailChain M) A'))^{−c'}` (over `F ∈ wingFrontBox`) to
the plain one-shorter IH `hIH(redChain s M)` by recombining `F` with the first tail layer `A₁` into
`W = F·A₁`, collapsing `(t, M₁, M₂) → (t, M₂) = redChain t M`, per the source-incidence `(r,s)` atlas
(`min_s [ (M₀−s)(M₁−s) + minAdm(redChain s M) ] = minAdm M`, d1design 0/5292).

## Status

The a=0 wide BOUNDED base (`M₂ ≤ M₁−M₀`) is LANDED sorry-free via the Gram–Schmidt route, with NO
Cauchy–Binet: `frontCollapse_wide_bounded_lt_top` (`RouteMSJFrontCollapseWide`), built on
`fixedF_wide_cov_bound` (`RouteMSJFrontCoV`) + `front_gram_qbox_lt_top` + `redChain_box_lt_top`. The
square extension `[F;S]` (`Core.exists_ortho_complement_rows`) yields the free-`F` Gram `det(F·Fᵀ)`
(`det_gram_fromRows_of_orthonormal`), fed to the banked Wishart `qbox_lintegral_lt_top` — sidestepping
the Cauchy–Binet / coarea primitives Mathlib v4.29 lacks (an earlier framing had these as the wall).

The atom `frontCollapseRankSector_lt_top` still carries the dispatch `sorry`; the remaining arms fill
it — LOG (`M₂ = M₁−M₀+1`, δ-fold), b=0 tall, POWER (`M₂ ≥ M₁−M₀+2`, the `(r,s)` atlas, general-κ) —
each gated on a pen-and-paper route pin (as the a=0 base was).

This module holds the shared bricks: `wingFrontBox` / `leadingBlock` + measurability; the both-wings
saturated charge (`peelCharge_min_eq_zero`, `saturated_threshold`); the reduced-chain box finiteness
(`redChain_box_lt_top`); the block-Gram-det identity; and the front-Gram qbox density factor.
-/

namespace DLNFibre.DLN.RLCT

open MeasureTheory
open scoped ENNReal BigOperators Matrix

variable {L : ℕ}

/-- **The leading `t×t` block** of a front matrix `F : M₀×M₁`, `t = min(M₀,M₁)` — the block whose
invertibility makes `F` full rank `t` (the CoV-enabling condition). -/
def leadingBlock (M : Fin (L + 1 + 1 + 1) → ℕ) (F : Fin (M 0) → Fin (M 1) → ℝ) :
    Matrix (Fin (min (M 0) (M 1))) (Fin (min (M 0) (M 1))) ℝ :=
  Matrix.of (fun i j => F (Fin.castLE (min_le_left _ _) i) (Fin.castLE (min_le_right _ _) j))

/-- **The wing front-box.** All entries in `[−1,1]` and the leading `t×t` block invertible (full rank
`t = min(M₀,M₁)`). Covers both wings: `F` wide (`M₀ ≤ M₁`, the `a=0` case) or tall (`M₀ ≥ M₁`, `b=0`). -/
def wingFrontBox (M : Fin (L + 1 + 1 + 1) → ℕ) : Set (Fin (M 0) → Fin (M 1) → ℝ) :=
  {F | (∀ i j, F i j ∈ Set.Icc (-1 : ℝ) 1) ∧ IsUnit (leadingBlock M F)}

/-- **THE ATOM (§1) — the front-collapse rank-sector finiteness.** For a `≥ 3`-width chain `M`, GIVEN
the plain one-shorter strong IH `hIH`, below the geometric threshold (`c' < ½·minAdm M`), the
front-factor box integral over `wingFrontBox M × paramsBoxM(tailChain M)` is finite. Reduces (per
d1design §1) via the source-incidence `(r,s)` atlas to `hIH(redChain s M)` at charge
`N_s = (M₀−s)(M₁−s)`, with `min_s[N_s + minAdm(redChain s M)] = minAdm M`. The dispatch `sorry` is
filled arm-by-arm: the a=0 wide bounded regime is LANDED (`frontCollapse_wide_bounded_lt_top`,
`RouteMSJFrontCollapseWide`); LOG / b=0 / POWER remain. -/
theorem frontCollapseRankSector_lt_top (M : Fin (L + 1 + 1 + 1) → ℕ)
    (hIH : ∀ M' : Fin (L + 1 + 1) → ℕ, RouteMBoxThresholdFinite M')
    (c' : NNReal) (hc' : (c' : ℝ) < (minAdm M : ℝ) / 2) :
    (∫⁻ F in wingFrontBox M,
        ∫⁻ A' in paramsBoxM (tailChain M) 1,
          ENNReal.ofReal ((frobSq (rmatMul F (prod (tailChain M) A'))) ^ (-(c' : ℝ)))) < ⊤ := by
  sorry

/-- **The saturated-cut charge is zero (LANDED, green, BOTH wings).** At the saturated cut
`u = min(M₀,M₁)`, `peelCharge M u = (M₀−u)(M₁−u) = 0` — for a wide front (`M₀≤M₁`, `u=M₀`, the a=0
factor vanishes) OR a tall front (`M₁≤M₀`, `u=M₁`, the b=0 factor vanishes). This is exactly the
saturated-shell (`a=0`/`b=0`) wing regime the front-collapse targets. -/
theorem peelCharge_min_eq_zero (M : Fin (L + 1 + 1 + 1) → ℕ) :
    peelCharge M (min (M 0) (M 1)) = 0 := by
  simp only [peelCharge]
  rcases le_total (M 0) (M 1) with h | h
  · rw [min_eq_left h]; simp
  · rw [min_eq_right h]; simp

/-- **The saturated reduction threshold (LANDED, green, BOTH wings).** At the saturated cut
`u = min(M₀,M₁)` the front-collapse to `redChain u M` carries NO charge (`peelCharge M u = 0`), so the
sub-threshold `c' < ½·minAdm M` transfers UNCHANGED to `c' < ½·minAdm(redChain u M)` (the reduced-chain
RLCT the plain IH consumes). Covers the `a=0` wide wing and the `b=0` tall wing in one statement. This
is the charge arithmetic the wing slices close on. -/
theorem saturated_threshold (M : Fin (L + 1 + 1 + 1) → ℕ)
    (c' : NNReal) (hc' : (c' : ℝ) < (minAdm M : ℝ) / 2) :
    (c' : ℝ) < (minAdm (redChain (min (M 0) (M 1)) M) : ℝ) / 2 := by
  have hu : min (M 0) (M 1) ≤ min (M 0) (M 1) := le_rfl
  have hle := minAdm_le_peelCharge_add_redChain M (min (M 0) (M 1)) hu
  rw [peelCharge_min_eq_zero M, Nat.zero_add] at hle
  have hcast : (minAdm M : ℝ) ≤ (minAdm (redChain (min (M 0) (M 1)) M) : ℝ) := by exact_mod_cast hle
  linarith

/-- **(N1a) `wingFrontBox` is measurable** — the entry-box (a finite intersection of coordinate
Icc-preimages) intersected with the leading-block non-singular locus `{det ≠ 0}` (det a continuous
function of the entries). The measurability the sector cover / CoV plumbing consumes. -/
theorem measurableSet_wingFrontBox (M : Fin (L + 1 + 1 + 1) → ℕ) :
    MeasurableSet (wingFrontBox M) := by
  have hbox : MeasurableSet {F : Fin (M 0) → Fin (M 1) → ℝ |
      ∀ i j, F i j ∈ Set.Icc (-1 : ℝ) 1} := by
    have hrw : {F : Fin (M 0) → Fin (M 1) → ℝ | ∀ i j, F i j ∈ Set.Icc (-1 : ℝ) 1}
        = ⋂ i, ⋂ j, {F : Fin (M 0) → Fin (M 1) → ℝ | F i j ∈ Set.Icc (-1 : ℝ) 1} := by
      ext F; simp only [Set.mem_iInter, Set.mem_setOf_eq]
    rw [hrw]
    exact MeasurableSet.iInter (fun i => MeasurableSet.iInter (fun j =>
      measurableSet_Icc.preimage ((measurable_pi_apply j).comp (measurable_pi_apply i))))
  have hdet : Measurable (fun F : Fin (M 0) → Fin (M 1) → ℝ => (leadingBlock M F).det) := by
    refine Continuous.measurable ?_
    refine Continuous.matrix_det ?_
    refine continuous_matrix (fun i j => ?_)
    simp only [leadingBlock, Matrix.of_apply]
    exact (continuous_apply _).comp (continuous_apply _)
  have hunit : {F : Fin (M 0) → Fin (M 1) → ℝ | IsUnit (leadingBlock M F)}
      = {F | (leadingBlock M F).det ≠ 0} := by
    ext F
    simp only [Set.mem_setOf_eq, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
  have hns : MeasurableSet {F : Fin (M 0) → Fin (M 1) → ℝ | IsUnit (leadingBlock M F)} := by
    rw [hunit]
    exact (hdet (measurableSet_singleton 0)).compl
  exact hbox.inter hns

/-- **The reduced-chain box finiteness the front-collapse reduces to (LANDED, green, route-independent).**
At the saturated cut `u = min(M₀,M₁)`, the plain IH `hIH` closes the reduced chain `redChain u M` at the
UNSHIFTED exponent `c'` (no charge, `saturated_threshold`). This is the finiteness target the absorption
CoV `(F, A₁) ↦ W` reduces the front-factor box integral to (up to the bounded pushforward density) — the
`hIH`-side of the reduction, independent of the CB-vs-GS density-bound route. -/
theorem redChain_box_lt_top (M : Fin (L + 1 + 1 + 1) → ℕ)
    (hIH : ∀ M' : Fin (L + 1 + 1) → ℕ, RouteMBoxThresholdFinite M')
    (c' : NNReal) (hc' : (c' : ℝ) < (minAdm M : ℝ) / 2) :
    routeMLayerBoxIntegral (redChain (min (M 0) (M 1)) M) (c' : ℝ) 1 < ⊤ :=
  hIH (redChain (min (M 0) (M 1)) M) c' (saturated_threshold M c' hc')

/-- **The block-Gram-det identity (LANDED, green — the "elementary, NOT Cauchy-Binet" core).** For a
front `F : m×n` extended by a residual `S : k×n` orthonormal to `F`'s row space (`S·Fᵀ = 0`,
`S·Sᵀ = 1`), the stacked Gram determinant collapses to the front Gram:
`det([F;S]·[F;S]ᵀ) = det(F·Fᵀ)`. The off-diagonal blocks (`S·Fᵀ`) vanish, so the block-Gram is
block-triangular with diagonal `(F·Fᵀ, 1)` — `det_fromBlocks_zero₂₁`, no minor sum. This is what makes
`|det[F;S]| = det(F·Fᵀ)^{1/2}` (the square-CoV Jacobian) reachable WITHOUT Cauchy-Binet: the front Gram
`det(F·Fᵀ)` (a FREE-`F` Gram) then feeds `qbox_lintegral_lt_top` directly. -/
theorem det_gram_fromRows_of_orthonormal {m k n : ℕ}
    (F : Matrix (Fin m) (Fin n) ℝ) (S : Matrix (Fin k) (Fin n) ℝ)
    (hSF : S * Fᵀ = 0) (hSS : S * Sᵀ = 1) :
    ((Matrix.fromRows F S) * (Matrix.fromRows F S)ᵀ).det = (F * Fᵀ).det := by
  rw [Matrix.transpose_fromRows, Matrix.fromRows_mul_fromCols, hSF, hSS,
    Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, mul_one]

/-- **The front-Gram qbox finiteness (LANDED, green — the "first factor", `M₂≤b`).** The free-`F` front
Gram integral `∫_{F ∈ box} det(F·Fᵀ)^{−M₂/2}` is finite whenever `M₀ ≤ M₁` and `M₂ < M₁ − M₀ + 1`
(i.e. `M₂ ≤ M₁ − M₀ = b`, the bounded regime). The entry box `[−1,1]^{M₀×M₁}` sits inside the column-ball
`colBallMat M₀ M₁ M₀` (each column norm² `≤ M₀`), so this reduces to the banked
`bRowGram_colBall_lt_top` (= `qbox_lintegral_lt_top` transported by `rowsEquiv`). This is the density
factor the GS-route square-CoV produces (Jacobian reciprocal `det(F·Fᵀ)^{−M₂/2}`, via
`det_gram_fromRows_of_orthonormal`) — closed WITHOUT Cauchy-Binet. -/
theorem front_gram_qbox_lt_top {M₀ M₁ : ℕ} (M₂ : ℕ) (hle : M₀ ≤ M₁)
    (hbnd : (M₂ : ℝ) < (M₁ : ℝ) - M₀ + 1) :
    (∫⁻ F in matBox M₀ M₁ 1,
        ENNReal.ofReal ((Matrix.of F * (Matrix.of F)ᵀ).det ^ (-(M₂ : ℝ) / 2))) < ⊤ :=
  lt_of_le_of_lt (lintegral_mono_set CorankSlabD.box_subset_colBall)
    (CorankSlabD.bRowGram_colBall_lt_top (n := M₀) hle (a := (M₂ : ℝ)) hbnd)

end DLNFibre.DLN.RLCT
