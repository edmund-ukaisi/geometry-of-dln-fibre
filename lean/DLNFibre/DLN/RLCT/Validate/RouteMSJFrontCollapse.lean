import DLNFibre.DLN.RLCT.Validate.RouteMSJResolution
import DLNFibre.DLN.RLCT.Validate.RouteMSJDecoratedCharge
import DLNFibre.DLN.RLCT.Validate.RouteMSJQBoxCore

/-!
# `DLNFibre.DLN.RLCT.Validate.RouteMSJFrontCollapse` — the front-collapse rank-sector atom (§1)

**Thread `genm-lane1-shell`, the Lane-1 native heart** (d1design `d1-atom-spec.md` §1). This module
builds `frontCollapseRankSector_lt_top`: the single genuinely-new native object the `d≤1` arm of
`innerCorankDescent_lt_top` funnels to. It reduces the pivot-energy term
`frobSq((of F)·prod(tailChain M) A')^{−c'}` to the plain one-shorter IH `hIH(redChain s M)` by
recombining the front `F` with the first tail layer `A₁` into `W = F·A₁`, collapsing
`(t, M₁, M₂) → (t, M₂) = redChain t M`.

## Status (STATEMENTS-FIRST skeleton + the reachability linchpin)

This is the SPECIFY phase: the exact Lean contract (the atom + the wide `a=0` slice) is pinned and
typechecks; the genuinely-green arithmetic (the `a=0` charge, `peelCharge = 0`) is landed. The analytic
core (the absorption change-of-variables `(F, A₁) ↦ W`) is NOT filled — see the linchpin below.

## The reachability linchpin (Lane-1 build recon, 2026-07-17)

Even the cleanest sub-case — WIDE `a=0`, BOUNDED density (`M₂ ≤ M₁ − M₀`, d1design's base case) — is
reachable in principle via the multi-dominant-minor cover + per-chart affine CoV + the banked Wishart
`qbox_lintegral_lt_top`, BUT its linchpin is **Cauchy–Binet** (`det(F·Fᵀ) = ∑_σ (det F_σ)²`, the sum
over `t×t` minors), which is **ABSENT from Mathlib v4.29 and from our codebase**. Cauchy–Binet is what
turns the per-chart `|det F_σ|^{−M₂}` (divergent alone — d1design's TRAP: `∫|det F_σ|^{−M₂}` diverges
for `M₂ ≥ 1`) into the convergent Gram integral `det(F·Fᵀ)^{−M₂/2}` on the `σ`-dominant chart, via
`det(F·Fᵀ) ≤ (#minors)·(det F_σ)²`. Mathlib also has NO coarea formula (only
`map_linearMap_addHaar_eq_smul_addHaar`, the single-invertible-map CoV). So the front-collapse
absorption CoV — which `RouteMSJQBoxCore`'s scope note ALSO carries as an unbuilt interface — needs
either Cauchy–Binet or coarea built first. The `(r,s)` source-incidence atlas of the power case
(`M₂ ≥ M₁ − M₀ + 2`) is a further layer on top.

**CLASSIFY: EXPENSIVE-TRANSCRIPTION, linchpinned on a MISSING Mathlib primitive (Cauchy–Binet).** The
math is settled (d1design certified 0/5292 on the charge); the cost is building Cauchy–Binet + the
multi-chart CoV assembly + qbox dim-match — a multi-brick effort, staged below.

## Sub-lemma decomposition (d1design N1–N5 + the linchpin)

- **(CB)** Cauchy–Binet corollary — the dominant-minor Gram bound (the linchpin; MISSING, build first).
- **(N1)** the finite dominant-minor cover of `wingFrontBox` (measurable, covers off a null boundary).
- **(N2)** the per-chart affine CoV `(A₁)_σ ↦ W = F·A₁` (raw-`Pi`, `mulLeftₚ` pattern, diamond guard).
- **(N3)** the per-sector Jacobian (bounded case: constant `|det F_σ|^{−M₂}`; power case: the monomial
  `|det DΦ| = u(ξ)·∏|z_j|^{ν_j−1}` — d1design supplies at exact widths).
- **(N4)** the integral-level sector replacement → plain `hIH(redChain s M)` at charge `N_s`.
- **(N5)** null-boundary removal + the finite sector sum (`ENNReal.sum_lt_top`).
-/

namespace DLNFibre.DLN.RLCT

open MeasureTheory
open scoped ENNReal BigOperators

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
d1design §1) via the joint source-incidence `(r,s)` atlas to `hIH(redChain s M)` at charge
`N_s = (M₀−s)(M₁−s)`, with `min_s[N_s + minAdm(redChain s M)] = minAdm M`. NOT filled — the absorption
CoV is linchpinned on Cauchy–Binet (module header). -/
theorem frontCollapseRankSector_lt_top (M : Fin (L + 1 + 1 + 1) → ℕ)
    (hIH : ∀ M' : Fin (L + 1 + 1) → ℕ, RouteMBoxThresholdFinite M')
    (c' : NNReal) (hc' : (c' : ℝ) < (minAdm M : ℝ) / 2) :
    (∫⁻ F in wingFrontBox M,
        ∫⁻ A' in paramsBoxM (tailChain M) 1,
          ENNReal.ofReal ((frobSq (rmatMul F (prod (tailChain M) A'))) ^ (-(c' : ℝ)))) < ⊤ := by
  sorry

/-- **The `a=0` wide reduction threshold (LANDED, green).** For the wide wing (`M₀ ≤ M₁`), the
saturated cut is `u = M₀`, where `peelCharge M M₀ = (M₀−M₀)(M₁−M₀) = 0` — so the front-collapse to
`redChain M₀ M` carries NO charge, and the sub-threshold `c' < ½·minAdm M` transfers UNCHANGED to
`c' < ½·minAdm(redChain M₀ M)` (the reduced-chain RLCT the IH consumes). This is the charge arithmetic
the `a=0` slice closes on. -/
theorem wide_a0_threshold (M : Fin (L + 1 + 1 + 1) → ℕ) (hwide : M 0 ≤ M 1)
    (c' : NNReal) (hc' : (c' : ℝ) < (minAdm M : ℝ) / 2) :
    (c' : ℝ) < (minAdm (redChain (M 0) M) : ℝ) / 2 := by
  have hu : M 0 ≤ min (M 0) (M 1) := by omega
  have hzero : peelCharge M (M 0) = 0 := by
    simp [peelCharge]
  have hle := minAdm_le_peelCharge_add_redChain M (M 0) hu
  rw [hzero, Nat.zero_add] at hle
  have hcast : (minAdm M : ℝ) ≤ (minAdm (redChain (M 0) M) : ℝ) := by exact_mod_cast hle
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

end DLNFibre.DLN.RLCT
