import DLNFibre.DLN.RLCT.Validate.Case222Resolution

/-!
# `DLNFibre.DLN.RLCT.Validate.Case222Block` — the `(2,2,2)` ≥-direction cover (route R)

The `≥` direction of the `(2,2,2)` cover needs every one of the 24 leaves finite below `⨅ = 3/2`.

**Route R (the recursion route, validated here).** Rather than 24 bespoke composite charts (route C),
generate ALL leaves from the GATED `g5_pivotNode` by 3-deep recursion. The recursion driver is
`recStep`: a chart-domain summand `∫⁻_{L} h` re-covers as a finite sum over the next blow-up's active
cells, via `∫⁻_{L} h = ∫⁻_univ (L.indicator h)` (`setLIntegral_indicator`) + `g5_pivotNode active univ`
(`univ_ae_cover`). The unblock is `univ_ae_cover`: `univ =ᵐ ⋃ argmaxCellOn active` holds for ANY
nonempty `active` (the uncovered `{all active = 0}` slice is a codim-≥1 null subspace), so each
recursion level needs only the always-true `univ` cover — NOT the bounded-domain `=ᵐ` cover that
earlier appeared to wall (box-vs-argmax). This reuses gated infra only (`g5_pivotNode`, `pivotBlowupOn`,
`argmaxCellOn_cover`, `coordZero_null`); no bespoke `step2D`/`step3` composite charts.

Also recorded: the step-2 δ-pivot lift identities (`tailLift_step2D_apply`/`_det`) — the δ-branch
factorisation backbone. (The step-2 δ-cell of the cover is `pivotBlowupOn {1,2,3} 3`, gated; these
`tailLift step2D` lemmas pin the explicit form used for the leaf factorisation.)
-/

open MeasureTheory Set
open scoped BigOperators ENNReal
namespace DLNFibre.DLN.RLCT

/-! ## The route-R recursion driver (indicator-on-univ + `g5_pivotNode`)

The ≥-cover (route R, 2026-06-21) generates all 24 leaves from the GATED `g5_pivotNode` by 3-deep
recursion, WITHOUT bespoke composite charts. The key unblock: `g5_pivotNode active univ` only needs
`univ =ᵐ ⋃ argmaxCellOn active`, which holds for ANY nonempty `active` (the uncovered
`{all active = 0}` slice is a null codim-≥1 subspace). To recurse INTO a chart-domain summand `Lp`
(which is NOT `univ`), rewrite `∫⁻_{Lp} h = ∫⁻_univ (Lp.indicator h)` (`setLIntegral_indicator`) and
apply `g5_pivotNode active2 univ` to the whole-space integrand. The wall I earlier flagged
(box-vs-argmax) was an artifact of recursing the *bounded domain*; the indicator-on-univ recursion
side-steps it. -/

/-- **The generalised univ-cover** (route-R foundation): `univ` is covered up to null by the active
argmax cells, for ANY nonempty `active`. The complement `{∀ j ∈ active, y j = 0}` of the union is a
codim-≥1 null subspace (`coordZero_null p` for any `p ∈ active`). -/
theorem univ_ae_cover {N : ℕ} (active : Finset (Fin N)) (p : Fin N) (hp : p ∈ active) :
    (univ : Set (Fin N → ℝ)) =ᵐ[volume] ⋃ q ∈ active, argmaxCellOn active q := by
  rw [← argmaxCellOn_cover]
  symm
  rw [Filter.eventuallyEq_univ, mem_ae_iff]
  have hsub : {y : Fin N → ℝ | ∃ j ∈ active, y j ≠ 0}ᶜ ⊆ {y | y p = 0} := by
    intro y hy
    simp only [mem_compl_iff, mem_setOf_eq, not_exists, not_and, not_not] at hy
    exact hy p hp
  exact measure_mono_null hsub (coordZero_null p)

/-- **The route-R single recursion step.** A chart-domain integral `∫⁻_{L} h` re-covers as a finite
sum over the active₂ cells, via `∫⁻_{L} h = ∫⁻_univ (L.indicator h)` (`setLIntegral_indicator`) and
`g5_pivotNode active₂ univ` (`univ_ae_cover`). The reusable recursion unit: each application descends
one blow-up level, reusing only GATED infra (`g5_pivotNode`, `pivotBlowupOn`). -/
theorem recStep {N : ℕ} (active : Finset (Fin N)) (p : Fin N) (hp : p ∈ active)
    (L : Set (Fin N → ℝ)) (hL : MeasurableSet L) (h : (Fin N → ℝ) → ℝ≥0∞) :
    ∫⁻ x in L, h x
      = ∑ q ∈ active, ∫⁻ x in chartDomOn active q \ pivotZeroOn q,
          ENNReal.ofReal |(pivotBlowupOnDeriv active q x).det|
            * L.indicator h (pivotBlowupOn active q x) := by
  have heq : ∫⁻ x in L, h x = ∫⁻ x in univ, L.indicator h x := by
    rw [setLIntegral_indicator hL h, Set.inter_univ]
  rw [heq]
  exact g5_pivotNode active univ (univ_ae_cover active p hp) (L.indicator h)

/-- **The step-2 δ-pivot spectator-lift, explicit.** `tailLift step2D u = ![u0, u1, u2·u3, u2·u4, u2,
u5, u6, u7]` — the pivot value `u2` lands at the `δ`-slot (slot 4); the off-pivot products `u2·u3`,
`u2·u4` sit at slots 2, 3 (NOT a vanilla `pivotBlowupOn`, whose pivot value would stay at slot 2). -/
theorem tailLift_step2D_apply (u : Fin 8 → ℝ) :
    tailLift step2D u = ![u 0, u 1, u 2 * u 3, u 2 * u 4, u 2, u 5, u 6, u 7] := by
  funext i
  fin_cases i <;> rfl

/-- The step-2 δ-pivot lift Jacobian determinant: `|det| = |u2|²` (same `{2,3,4}`-pivot block as the
E-pivot branch — the determinant of a `card−1 = 2` blow-up; the pivot output-slot relabel does not
change `|det|`). -/
theorem tailLift_step2D_det (u : Fin 8 → ℝ) :
    (pivotBlowupOnDeriv ({2, 3, 4} : Finset (Fin 8)) 2 u).det = (u 2) ^ 2 :=
  tailLift_step2E_det u

/-! ## Route-R level-2 cell factorisations (the leaf-weight inputs)

The step-2 `g5_pivotNode {1,2,3}` produces three cells, one per pivot `p ∈ {1,2,3}` of the resolved
coords `(t1,E,F0,δ,q,G,H)`. These lemmas pin the residual factorisation on each — the leaf-weight
monomial·unit the ≥-cover consumes. The E-pivot (`p=1`) is the gated `resolvedForm_step2E` /
`step2E_unit_ge_one`; here are the F0-pivot (`p=2`, the other unit leaf) and the δ-pivot (`p=3`, the
block branch). -/

/-- **Step-2 δ-cell factorisation.** `resolvedForm (pivotBlowupOn {1,2,3} 3 z) = z3² · block`, where
`block = z1² + z2² + (z4·z1 + z5)² + (z4·z2 + z6)²` vanishes at the centre — the block branch (needs
step-3). The cover's δ-cell residual (cf. the gated `resolvedForm_step2D`, same block, pivot at `z3`
rather than the hand-def `step2D`'s `z1`). -/
theorem resolvedForm_pivotDelta (z : Fin 7 → ℝ) :
    resolvedForm (pivotBlowupOn ({1, 2, 3} : Finset (Fin 7)) 3 z)
      = (z 3) ^ 2 * ((z 1) ^ 2 + (z 2) ^ 2 + (z 4 * z 1 + z 5) ^ 2 + (z 4 * z 2 + z 6) ^ 2) := by
  rw [show pivotBlowupOn ({1, 2, 3} : Finset (Fin 7)) 3 z
        = ![z 0, z 3 * z 1, z 3 * z 2, z 3, z 4, z 5, z 6] from by
      funext i; unfold pivotBlowupOn; fin_cases i <;> simp [Matrix.cons_val]]
  unfold resolvedForm
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Fin.isValue]
  ring

/-- **Step-2 F0-cell factorisation (the other UNIT leaf).** `resolvedForm (pivotBlowupOn {1,2,3} 2 z)
= z2² · U'`, with `U' = 1 + z1² + (z4·z1·z3̂ + …)` a sum of `1` and squares (`≥ 1`) — the F0-pivot
unit leaf, symmetric to the E-pivot (`step2E_unit_ge_one`). -/
theorem resolvedForm_pivotF0 (z : Fin 7 → ℝ) :
    resolvedForm (pivotBlowupOn ({1, 2, 3} : Finset (Fin 7)) 2 z)
      = (z 2) ^ 2 * (1 + (z 1) ^ 2 + (z 4 * z 1 + z 3 * z 5) ^ 2 + (z 4 + z 3 * z 6) ^ 2) := by
  rw [show pivotBlowupOn ({1, 2, 3} : Finset (Fin 7)) 2 z
        = ![z 0, z 2 * z 1, z 2, z 2 * z 3, z 4, z 5, z 6] from by
      funext i; unfold pivotBlowupOn; fin_cases i <;> simp [Matrix.cons_val]]
  unfold resolvedForm
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Fin.isValue]
  ring

/-- The F0-cell residual `U' = 1 + z1² + (z4·z1 + z3·z5)² + (z4 + z3·z6)² ≥ 1` — the F0-unit-leaf
nonvanishing input (`0 < a`, `a = 1`) to `integrableOn_monomial_mul_unit_iff` (symmetric to
`step2E_unit_ge_one`). -/
theorem pivotF0_unit_ge_one (z : Fin 7 → ℝ) :
    (1 : ℝ) ≤ 1 + (z 1) ^ 2 + (z 4 * z 1 + z 3 * z 5) ^ 2 + (z 4 + z 3 * z 6) ^ 2 := by
  nlinarith [sq_nonneg (z 1), sq_nonneg (z 4 * z 1 + z 3 * z 5), sq_nonneg (z 4 + z 3 * z 6)]

end DLNFibre.DLN.RLCT
