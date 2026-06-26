import DLNFibre.DLN.RLCT.Validate.MatMulFibre
import DLNFibre.DLN.RLCT.Validate.RouteMExtraction
import DLNFibre.DLN.RLCT.Validate.RouteMLayerSplit
import DLNFibre.DLN.RLCT.Validate.Case222CoverGETail

/-!
# `DLNFibre.DLN.RLCT.Validate.RouteMSchur` — the general-`M` R1 hfin Schur/radial ladder

The rank-stratified R1 hfin (upper-bound finiteness) ladder for the general-`M` `routeMCore`, validated
on the smallest binding corank-2 case `(3,3,4)` (depth-2, one nested minor-pivot level). The design is the
build-ready cover certificate
`expeditions/2026-06-20-aoyagi-full/threads/28-hfin-recStep-spec/L32a-cover-cert.md` §4, with four NEW
targets in dependency order:

* **N1 `radialDelta_loss_factor`** — degree-2 homogeneity of the determinantal core under the radial
  blow-up scale: `frobSq ((a•R)·S) = a²·frobSq (R·S)`. Pure `ring` (this file, PROVED).
* **N2 `schur_minorPivot_split`** — on the minor-invertible open neighbourhood `{det M11 ≠ 0}`, the
  disjoint Morse ⊕ Schur-complement split + the Schur determinant identity. The `r = 2` case is
  `ring`-clean (rank-1 split); `r ≥ 3` is the block-Gauss det-1 bookkeeping.
* **N3 `radial_loss_chart_lt_top`** — per-chart finiteness, threshold `min(r²/2, inner)`, wiring N1 + the
  existing `g5_pivotNode` change-of-variables + the a-axis 1-D monomial.
* **N4 `routeMCore_threshold_lt_top`** — the WellFounded-on-corank recursion assembly summing N3 over the
  `r²` charts; discharges `hfin`. Validated on `(3,3,4)` depth-2 first.

The cover wall (the `r²`-chart radial-`Δ` atlas) IS the existing `argmaxCellOn`/`pivotBlowupOn` infra at
the `r²` Δ-entry level (cert VERDICT) — reused verbatim, not rebuilt.

## S2-hygiene
The hfin CONCLUSION is proven S2-FREE (Morse leaves `radial_morse_dominates_lt_top`, the a-divisor 1-D
monomial, Tonelli, Schur splits, radial Jacobian dets). `monomial_rlct` enters ONLY the leaf-sum
hypothesis side of `hfin` — the SAME S2 use the headline already rides. No NEW axiom.
-/

namespace DLNFibre.DLN.RLCT

open MeasureTheory Set
open scoped ENNReal BigOperators

/-! ## N1 — the radial-blow-up degree-2 homogeneity (PROVED, `ring`)

On a radial-blow-up chart `Δ = a·R`, the determinantal core `frobSq (Δ·S) = frobSq ((a•R)·S)` factors as
`a²·frobSq (R·S)`: the scale `a` pulls out of the matrix product with degree 2 (one power per side of the
square). This is the integrand identity the per-chart change-of-variables consumes
(`L32a-cover-cert.md` §4 N1; sympy-pinned `L32a_cover_334.py` Part C, the `a`-degree is exactly 2). -/

/-- `(a•R)·S` entrywise is `a·(R·S)`: the scalar pulls through the raw matrix product. -/
theorem rmatMul_smul_left {r p : ℕ} (a : ℝ) (R : Fin r → Fin r → ℝ) (S : Fin r → Fin p → ℝ) :
    rmatMul (fun i k => a * R i k) S = fun i j => a * rmatMul R S i j := by
  funext i j
  unfold rmatMul
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  ring

/-- **N1 — `radialDelta_loss_factor`.** The degree-2 homogeneity of the determinantal core under the
radial blow-up scale: `frobSq ((a•R)·S) = a²·frobSq (R·S)`. The scale `a` is the radial coordinate of
the `Δ`-blow-up `Δ = a·R`; the loss core `frobSq (Δ·S)` carries it with degree exactly 2. Proved by
the entrywise `rmatMul_smul_left` + the `frobSq` sum-of-squares + `ring`. -/
theorem radialDelta_loss_factor {r p : ℕ} (a : ℝ) (R : Fin r → Fin r → ℝ) (S : Fin r → Fin p → ℝ) :
    frobSq (rmatMul (fun i k => a * R i k) S) = a ^ 2 * frobSq (rmatMul R S) := by
  rw [rmatMul_smul_left]
  unfold frobSq
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  ring

/-! ## N2 — the rank-stratified Schur split on the minor-invertible neighbourhood

At a corank-`r` cell the binding core is `frobSq (R·S)`. The rank recursion covers the inner `R`-space by
`j×j`-minor-invertible OPEN neighbourhoods `{det M11 ≠ 0}` (a nested `argmaxCellOn` over minors, NOT exact
rank strata — those are measure-zero and illegal as integration domains, cert §3, Codex Q3). On each, a
block-Gauss det-1 normal form splits `frobSq (R·S)` into a disjoint Morse block ⊕ the Schur-complement
core, and the Schur determinant identity `det R = det M11 · det Sc` makes the residual singularity
`{det R = 0} ∩ {det M11 ≠ 0} = {det Sc = 0}` carried entirely by `Sc` (an exact corank-`(r−j)` block).

The binding `(3,3,4)` corank-2 core (`r = 2`, `p = 4`) terminates after ONE rank drop: the rank-1 stratum
is the `ring`-clean outer-product split `frobSq (R·S) = (∑ col²)·frobSq (row·S)` below (N2a). The general
`r ≥ 3` block-Gauss det-1 bookkeeping (the coupling Gram is the rank-`j` Gram, positive-definite on the
bounded chart) is the precisely-named skeleton `schur_minorPivot_split` (N2b). -/

/-- **N2a — the `r = 2` rank-1 outer-product split (PROVED, `ring`).** On the rank-1 stratum of a `2×2`
residual `R` with pivoted column `col = (1, c)` and row `row = (1, b)` (so `R i k = col i · row k`, an
outer product), the determinantal core factors as the Morse coefficient `∑ col²` (the bounded-below
`1 + c²` unit) times the corank-1 reduced core `frobSq (row·S)`, where `row·S` is the single residual
linear form. This is the `(3,3,4)` corank-2 recursion's terminal rank-drop leaf; sympy-pinned
(`L32a_schur_r3.py`, the `r = 2` rank-1 identity `‖R·S‖² = (1+c²)·‖row·S‖²`). -/
theorem rankOne_outerProduct_split {p : ℕ} (col : Fin 2 → ℝ) (row : Fin 2 → ℝ)
    (S : Fin 2 → Fin p → ℝ) :
    frobSq (rmatMul (fun i k => col i * row k) S)
      = (∑ i, (col i) ^ 2) * frobSq (rmatMul (fun (_ : Fin 1) k => row k) S) := by
  unfold frobSq rmatMul
  -- LHS: ∑_{i<2} ∑_{j<p} (∑_{k<2} col i · row k · S k j)²
  --    = ∑_{i<2} (col i)² · ∑_{j<p} (∑_{k<2} row k · S k j)²  (pull col i out of the inner k-sum)
  -- RHS: (∑_{i<2} (col i)²) · ∑_{_<1} ∑_{j<p} (∑_{k<2} row k · S k j)²
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  -- the single `_ : Fin 1` index collapses the RHS outer sum to one term
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, one_smul, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  -- pointwise: (∑_k col i · row k · S k j)² = (col i)² · (∑_k row k · S k j)²
  rw [show (∑ k, col i * row k * S k j) = col i * (∑ k, row k * S k j) by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun k _ => by ring)]
  ring

/-- **N2b — `schur_minorPivot_split` (general `r`, SKELETON, correct statement + `sorry`).** On the
**bounded complete-pivoting cell** (`|R a b| ≤ 1` and the top-left `j×j` minor `M11` is a max-modulus
`j×j` minor — `minorpivot-cert.md` R2's cell), the disjoint Morse ⊕ Schur-complement TWO-SIDED bounded
comparison with **UNIFORM** constants (NOT raw equality — the non-orthogonal block-Gauss row-op is absorbed
into the bounded constants; cert §3, `L32a_disjoint_split.py`).

Three soundness pins, each load-bearing (reviewer/Codex-checked):
1. **Constants quantified BEFORE `R, S`** — else re-choosing `c₀,c₁` per `(R,S)` makes any comparison
   trivially true (the vacuity gap). The bounded complete-pivoting cell is what MAKES uniform `c₀,c₁`
   exist (numerically confirmed: over all `R` with merely `det M11 ≠ 0` the ratio `‖R·S‖²/D` is
   UNbounded; the shear ratios `M21·M11⁻¹ ≤ 1` only on the max-modulus-minor cell — `minorpivot-cert.md`
   R2). Hence the cell hypotheses `hbd`, `hpivot` are REQUIRED, not decorative.
2. **The Morse block is `P := (R·S)_top`** (the top `j` rows of `R·S`), NOT `S_top` — the det-1 S-shear
   `S' = U⁻¹·S` makes the disjoint top block `M11·S'_top = (R·S)_top` (`L32a_disjoint_split.py`).
   `Q := S_bot` (the bottom `r−j` rows of `S`); `P, Q` are DISJOINT and DETERMINED by `R, S`.
3. **`Sc` structurally PINNED** to the genuine Schur complement `M22 − M21·M11⁻¹·M12` (not merely by its
   determinant — closes the `r−j ≥ 2` freedom).

    c₀·(frobSq (R·S)_top + frobSq (Sc·S_bot)) ≤ frobSq (R·S) ≤ c₁·(frobSq (R·S)_top + frobSq (Sc·S_bot)).

The `(3,3,4)` corank-2 (`r = 2`) rank-1 case is the `ring`-clean equality `rankOne_outerProduct_split`
above. The general `r ≥ 3` block-Gauss det-1 normal form `L·R·U = diag(M11, Sc)` (positive-definite
rank-`j` coupling Gram) is the remaining matrix algebra — the MEDIUM-risk gap, de-risked in
`minorpivot-cert.md` (R1–R4; pp-r1-genM-2 on-call for the `r ≥ 3` det-1 bookkeeping). -/
theorem schur_minorPivot_split {r p : ℕ} (j : ℕ) (hj : j ≤ r) :
    ∃ (c₀ c₁ : ℝ), 0 < c₀ ∧ 0 < c₁ ∧
      ∀ (R : Matrix (Fin r) (Fin r) ℝ) (S : Fin r → Fin p → ℝ),
        -- the bounded complete-pivoting cell (REQUIRED for uniform constants — see pin 1)
        (∀ a b, |R a b| ≤ 1) →
        (∀ (I J : Fin j → Fin r),
          |(R.submatrix I J).det| ≤ |(Matrix.of (fun a b : Fin j =>
            R ⟨a, lt_of_lt_of_le a.2 hj⟩ ⟨b, lt_of_lt_of_le b.2 hj⟩)).det|) →
        (Matrix.of (fun a b : Fin j =>
            R ⟨a, lt_of_lt_of_le a.2 hj⟩ ⟨b, lt_of_lt_of_le b.2 hj⟩)).det ≠ 0 →
        ∃ (Sc : Matrix (Fin (r - j)) (Fin (r - j)) ℝ),
          -- `Sc` = the GENUINE Schur complement `M22 − M21·M11⁻¹·M12` (pin 3). Blocks:
          -- M22 : (r−j)×(r−j), M21 : (r−j)×j, M11⁻¹ : j×j, M12 : j×(r−j).
          Sc = (Matrix.of (fun a b : Fin (r - j) =>
                  R ⟨j + a, by omega⟩ ⟨j + b, by omega⟩))
                - (Matrix.of (fun (a : Fin (r - j)) (b : Fin j) =>
                      R ⟨j + a, by omega⟩ ⟨b, lt_of_lt_of_le b.2 hj⟩))
                  * (Matrix.of (fun a b : Fin j =>
                      R ⟨a, lt_of_lt_of_le a.2 hj⟩ ⟨b, lt_of_lt_of_le b.2 hj⟩))⁻¹
                  * (Matrix.of (fun (a : Fin j) (b : Fin (r - j)) =>
                      R ⟨a, lt_of_lt_of_le a.2 hj⟩ ⟨j + b, by omega⟩)) ∧
          -- the Schur determinant identity (a consequence of pin 3 + `det M11 ≠ 0`)
          R.det = (Matrix.of (fun a b : Fin j =>
              R ⟨a, lt_of_lt_of_le a.2 hj⟩ ⟨b, lt_of_lt_of_le b.2 hj⟩)).det * Sc.det ∧
          -- the two-sided UNIFORM comparison with `P := (R·S)_top`, `Q := S_bot` (pin 2)
          c₀ * (frobSq (fun a : Fin j => rmatMul (fun x y => R x y) S ⟨a, lt_of_lt_of_le a.2 hj⟩)
                  + frobSq (rmatMul (fun a b => Sc a b)
                      (fun a : Fin (r - j) => S ⟨j + a, by omega⟩)))
            ≤ frobSq (rmatMul (fun a b => R a b) S) ∧
          frobSq (rmatMul (fun a b => R a b) S)
            ≤ c₁ * (frobSq (fun a : Fin j => rmatMul (fun x y => R x y) S ⟨a, lt_of_lt_of_le a.2 hj⟩)
                  + frobSq (rmatMul (fun a b => Sc a b)
                      (fun a : Fin (r - j) => S ⟨j + a, by omega⟩))) := by
  sorry

/-! ## N3 — the per-chart finiteness: the a-axis radial divisor (PROVED) + the chart-integral (SKELETON)

On a single radial-`Δ`-blow-up entry-chart `p` of the corank-`r` core `frobSq (Δ·S)`, the per-chart
integral is finite for `c'` below the per-chart threshold `min(r²/2, inner)` (cert §2, Q4): the radial
Jacobian `|a|^{r²−1}` (`pivotBlowupOnDeriv_det`) × the N1 factor `a²·frobSq (R·S)` gives an `a`-axis
divisor `∫ |a|^{(r²−1)−2c'} da < ∞ ⟺ c' < r²/2`, Tonelli-separate from the inner `(R,S)`-integral (which
N2 + the recursion bounds). The threshold is a MINIMUM (both Tonelli factors must be finite, no
double-count of the two Tonelli roles — cert §2). The a-axis divisor itself (N3a) is the elementary 1-D
monomial; the full per-chart wiring through `g5_pivotNode` (N3b) is the remaining assembly. -/

/-- **N3a — the radial a-axis divisor finiteness (PROVED).** The `a`-axis factor of a radial-`Δ`-blow-up
chart: `∫_{[−T,T]} |a|^{(r²−1)−2c'} da < ⊤` for `c' < r²/2` — the radial Jacobian `|a|^{r²−1}` against the
N1 degree-2 scale `(a²·…)^{−c'} = |a|^{−2c'}·…`. The exponent `(r²−1)−2c' > −1 ⟺ c' < r²/2` is the a-axis
threshold of the per-chart MIN (cert §2, `L32a_joint_threshold.py`). Proved from the existing 1-D monomial
atom `abs_rpow_lintegral_Icc_lt_top`. The S2-FREE radial divisor the per-chart c-o-v consumes. -/
theorem radial_aAxis_divisor_lt_top (r : ℕ) (hr : 1 ≤ r) (T : ℝ) (hT : 0 < T)
    (c' : ℝ) (hc' : c' < (r ^ 2 : ℝ) / 2) :
    ∫⁻ a in Set.Icc (-T) T, ENNReal.ofReal (|a| ^ ((r ^ 2 : ℝ) - 1 - 2 * c')) < ⊤ := by
  apply abs_rpow_lintegral_Icc_lt_top T hT ((r ^ 2 : ℝ) - 1 - 2 * c')
  -- (r² − 1) − 2c' > −1  ⟺  c' < r²/2
  linarith [hc']

/-- **N3b — `radial_loss_chart_lt_top` (SKELETON, faithful per-chart statement).** The per-chart
finiteness on a radial-`Δ`-blow-up entry-chart: for the corank-`r` core `frobSq (Δ·S)` with `Δ = a·R` (the
radial scale `a` ∈ `[−T,T]`, the angular `R` over the bounded matrix box `matBox r r T`, the free block `S`
fixed), the radial-Jacobian-weighted integral `∫_a ∫_R |a|^{r²−1}·frobSq((a•R)·S)^{−c'}` is finite for
`c'` below the per-chart threshold `min(r²/2, inner)`. By N1 (`radialDelta_loss_factor`) the integrand
factors `|a|^{r²−1}·(a²·frobSq(R·S))^{−c'} = |a|^{(r²−1)−2c'}·frobSq(R·S)^{−c'}`, Tonelli-separating the
a-axis divisor (N3a, PROVED, finite ⟺ `c' < r²/2`) from the inner `R`-integral (bounded by the minor-pivot
Schur recursion N2). SKELETON (`sorry`) — the Tonelli split + the inner-N2 plug; the a-axis factor is N3a,
the homogeneity is N1. The radial change-of-variables onto this chart from `Δ`-coords is the existing
`g5_pivotNode`/`pivotBlowupOnDeriv_det` infra (cert §4 N3, reused verbatim in N4). -/
theorem radial_loss_chart_lt_top {r p : ℕ} (hr : 1 ≤ r) (T : ℝ) (hT : 0 < T)
    (c' : ℝ) (hc0 : 0 ≤ c') (hc' : c' < (r ^ 2 : ℝ) / 2) (S : Fin r → Fin p → ℝ)
    (hSfin : ∫⁻ R in matBox r r T,
        ENNReal.ofReal ((frobSq (rmatMul R S)) ^ (-c')) < ⊤) :
    ∫⁻ a in Set.Icc (-T) T, ∫⁻ R in matBox r r T,
        ENNReal.ofReal (|a| ^ ((r ^ 2 - 1 : ℕ) : ℝ)
          * (frobSq (rmatMul (fun i k => a * R i k) S)) ^ (-c')) < ⊤ := by
  -- N1: the integrand factors `|a|^{(r²−1)−2c'} · frobSq(R·S)^{−c'}` (a.e. in `a`, off `{a=0}`).
  -- Tonelli-separates the a-axis divisor (N3a) from the inner R-integral (`hSfin`).
  have hrw : ∀ a : ℝ, a ≠ 0 → ∀ R : Fin r → Fin r → ℝ,
      ENNReal.ofReal (|a| ^ ((r ^ 2 - 1 : ℕ) : ℝ)
          * (frobSq (rmatMul (fun i k => a * R i k) S)) ^ (-c'))
        = ENNReal.ofReal (|a| ^ ((r ^ 2 : ℝ) - 1 - 2 * c'))
          * ENNReal.ofReal ((frobSq (rmatMul R S)) ^ (-c')) := by
    intro a ha R
    rw [radialDelta_loss_factor a R S]
    -- (|a|^{r²−1}) · ((a²·F)^{−c'}) = |a|^{(r²−1)−2c'} · F^{−c'}, with F = frobSq(R·S) ≥ 0
    have hF : (0 : ℝ) ≤ frobSq (rmatMul R S) := frobSq_nonneg _
    have haa : (0 : ℝ) < |a| := abs_pos.2 ha
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    -- the r²−1 nat-cast exponent equals the real r²−1
    have hge : 1 ≤ r ^ 2 := Nat.one_le_iff_ne_zero.2 (by positivity)
    have hpow : |a| ^ (((r ^ 2 - 1 : ℕ)) : ℝ) = |a| ^ ((r : ℝ) ^ 2 - 1) := by
      congr 1; push_cast [Nat.cast_sub hge]; ring
    -- (a²·F)^{−c'} = |a|^{−2c'} · F^{−c'}
    have hsplit : (a ^ 2 * frobSq (rmatMul R S)) ^ (-c')
        = |a| ^ (-(2 * c')) * (frobSq (rmatMul R S)) ^ (-c') := by
      rw [Real.mul_rpow (by positivity) hF]
      congr 1
      rw [show (a ^ 2 : ℝ) = |a| ^ (2 : ℕ) by rw [sq_abs], ← Real.rpow_natCast |a| 2,
        ← Real.rpow_mul (abs_nonneg a)]
      norm_num
    rw [hpow, hsplit, ← mul_assoc, ← Real.rpow_add haa]
    ring_nf
  -- abbreviate the inner R-integral constant `C := ∫_R frobSq(R·S)^{−c'}` (finite by `hSfin`)
  set C : ℝ≥0∞ := ∫⁻ R in matBox r r T, ENNReal.ofReal ((frobSq (rmatMul R S)) ^ (-c')) with hC
  -- rewrite the outer integrand a.e. (off the null `{a = 0}`) and pull the a-factor out of the inner ∫
  have hae : (fun a => ∫⁻ R in matBox r r T,
        ENNReal.ofReal (|a| ^ ((r ^ 2 - 1 : ℕ) : ℝ)
          * (frobSq (rmatMul (fun i k => a * R i k) S)) ^ (-c')))
      =ᵐ[volume.restrict (Set.Icc (-T) T)]
      (fun a => ENNReal.ofReal (|a| ^ ((r ^ 2 : ℝ) - 1 - 2 * c')) * C) := by
    have haa0 : ∀ᵐ a : ℝ, a ≠ 0 := by
      rw [ae_iff]; simp [Real.volume_singleton]
    refine (ae_restrict_of_ae haa0).mono (fun a ha => ?_)
    -- rewrite each R-integrand via N1 (`hrw`), then pull the a-constant `ofReal(exp_a)` out of ∫_R
    calc ∫⁻ R in matBox r r T,
            ENNReal.ofReal (|a| ^ ((r ^ 2 - 1 : ℕ) : ℝ)
              * (frobSq (rmatMul (fun i k => a * R i k) S)) ^ (-c'))
        = ∫⁻ R in matBox r r T,
            ENNReal.ofReal (|a| ^ ((r ^ 2 : ℝ) - 1 - 2 * c'))
              * ENNReal.ofReal ((frobSq (rmatMul R S)) ^ (-c')) :=
          lintegral_congr (fun R => hrw a ha R)
      _ = ENNReal.ofReal (|a| ^ ((r ^ 2 : ℝ) - 1 - 2 * c'))
            * ∫⁻ R in matBox r r T, ENNReal.ofReal ((frobSq (rmatMul R S)) ^ (-c')) :=
          lintegral_const_mul' _ _ (ENNReal.ofReal_ne_top)
      _ = ENNReal.ofReal (|a| ^ ((r ^ 2 : ℝ) - 1 - 2 * c')) * C := by rw [hC]
  rw [lintegral_congr_ae hae]
  -- pull the constant `C` out of the a-integral: `∫_a (|a|^exp · C) = (∫_a |a|^exp) · C`
  rw [lintegral_mul_const' C _ hSfin.ne]
  -- product of finites: N3a (a-axis divisor) × C (the inner R-integral, `hSfin`)
  exact ENNReal.mul_lt_top (radial_aAxis_divisor_lt_top r hr T hT c' hc') hSfin

/-! ## N4 — the hfin conclusion = the general-`M` finiteness (SKELETON, correct statement + `sorry`)

The WellFounded-on-corank recursion assembly: cover `routeMBaseNbhd M` by `recStep` over the `r²` radial-`Δ`
pivot charts, on each apply the radial c-o-v (N3), stratify by the minor-pivot Schur split (N2), peel the
Morse block (`radial_morse_dominates_lt_top`), and RECURSE on the corank-`(r−j)` Schur-complement core
(WellFounded measure = corank, strictly decreasing), terminating at the Morse/monomial leaves (depth ≤ r).
This discharges `hfin` (the `routeMLayerCover_of_atoms` field). Mirrors `myF222_threshold_lt_top'` at scale
`r²` with depth ≤ r. Validated on `(3,3,4)` (corank-2, ONE nested minor-pivot level) FIRST.

S2-FREE conclusion (Morse leaves, a-divisor 1-D monomial, Tonelli, Schur splits); `monomial_rlct` enters
only the leaf-sum hypothesis side, the same S2 use the headline already rides. No NEW axiom. -/

/-- **N4 — `routeMCore_threshold_lt_top` (SKELETON, the hfin conclusion).** For `c' < ½·minAdm M`,
`∫⁻_{routeMBaseNbhd M} |routeMCore M x|^{−c'} < ⊤`. The general-`M` analog of
`routeMCore_M4422_threshold_lt_top`, via the rank-stratified radial-Schur recursion (N1–N3 + the
WellFounded-on-corank `recStep` assembly). Directly discharges the `hfin` field of
`routeMLayerCover_of_atoms` (given the leaf-sum ⟹ `c' < ½·minAdm` premise reduction). SKELETON (`sorry`) —
the depth-`r` measure-theoretic cover assembly (cert §4 N4, the HIGH-risk long pole); validate on `(3,3,4)`
depth-2 first. -/
theorem routeMCore_threshold_lt_top {L : ℕ} (M : Fin (L + 1) → ℕ) (c' : NNReal)
    (hc' : (c' : ℝ) < (minAdm M : ℝ) / 2) :
    ∫⁻ x in routeMBaseNbhd M, ENNReal.ofReal (|routeMCore M x| ^ (-(c' : ℝ))) < ⊤ := by
  sorry

end DLNFibre.DLN.RLCT
