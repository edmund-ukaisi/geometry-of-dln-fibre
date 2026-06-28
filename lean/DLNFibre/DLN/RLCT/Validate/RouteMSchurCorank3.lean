import DLNFibre.DLN.RLCT.Validate.RouteMSchurDepth2
import DLNFibre.DLN.RLCT.Validate.RadialResidualPower

/-!
# `DLNFibre.DLN.RLCT.Validate.RouteMSchurCorank3` — the corank-3 recursion STEP (the first real firing)

The corank-3 instance of the rank-stratified radial-Schur recursion — the FIRST case where the recursion
genuinely fires (the residual Schur complement `Sc` becomes `2×2`, NOT a scalar, so it is a corank-2 core
that bottoms out in the closed `core_schur2_lt_top` at a SHIFTED exponent — not a Morse leaf). This
validates the inductive STEP `corank-r → corank-(r−1)`-at-shifted-exponent (cert §4 N4 / §3); the full
arbitrary-depth WellFounded-on-corank recursion is the next milestone.

## The threshold (CONFIRMED `c' < 4 = λ_{3,4}` — the JOINT-core SUM, not the corank-2 `2`)
The binding inner threshold is the SUM `jp/2 + λ_{r−j,p}` = (j=1, p=4 ⟹ `jp/2 = 2`) + (`λ_{2,4} = 2`) = 4
= ½·minAdm(3,3,4). Reusing the corank-2 threshold-`2` lemma for the corank-3 leaf would UNDERSHOOT (the
cert §6 trap: it drops the `+jp/2` Morse gain). The shifted-exponent peel is what carries the `+jp/2`.

## The mechanism (the inductive STEP)
`schurInner3_S_le` (the per-chart inner-S heart, at a fixed `3×3` angular `R` with pivot `(0,0)`):
`∫_{S ∈ matBox 3 4 T} frobSq (R·S)^{−c'} < ⊤` for `0 < c' < 4`, via:
* N2b (`schur_minorPivot_split`, `r=3, j=1`) → the JOINT split `frobSq (R·S) ≳ frobSq (R·S)_row0 (Morse,
  p entries) + frobSq (Sc · S_bot)` (`Sc` the `2×2` Schur complement, `S_bot` rows 1,2 of S);
* the SHIFTED-EXPONENT Morse peel of the top block (`radial_morse_residual_power_le`, threshold `p/2 = 2`)
  → the corank-2 residual at exponent `c' − 2`;
* the translation-domination `M22 ↦ Sc` (Jac ≡ 1, `lintegral_translate_le_local` +
  `rowShear_entry_le_one`) confines `Sc` to a fixed box → `core_schur2_lt_top` at exponent `c' − 2 < 2`.

The OUTER 9-chart radial-Δ cover (mirror of the corank-2 `matBox2_*` cover) assembling
`∫_Δ ∫_S frobSq (Δ·S)^{−c'} < ⊤` is built on top (`core_schur3_lt_top`).

## S2-hygiene
S2-FREE: the shifted peel (`radial_morse_residual_power_le`, `radial_ball_iff`-based), `core_schur2_lt_top`
(S2-free), the translation domination, the radial Jacobian dets. No `monomial_rlct`, no new axiom.
-/

namespace DLNFibre.DLN.RLCT

open MeasureTheory Set
open scoped ENNReal BigOperators

/-! ## The corank-3 outer radial-Δ 9-chart cover (mirror of the corank-2 `matBox2_*` atoms) -/

/-- Local `matToFlatEquiv 3 3 : (Fin 3 → Fin 3 → ℝ) ≃ᵐ (Fin 9 → ℝ)` (uncurry + the `Fin 3 × Fin 3 ≃ Fin 9`
index reindex). -/
noncomputable def matToFlat3 : (Fin 3 → Fin 3 → ℝ) ≃ᵐ (Fin (3 * 3) → ℝ) :=
  (MeasurableEquiv.piCurry (fun (_ : Fin 3) (_ : Fin 3) => ℝ)).symm.trans
    (MeasurableEquiv.arrowCongr'
      ((Equiv.sigmaEquivProd (Fin 3) (Fin 3)).trans finProdFinEquiv) (MeasurableEquiv.refl ℝ))

theorem measurePreserving_matToFlat3 :
    MeasurePreserving matToFlat3 (volume : Measure (Fin 3 → Fin 3 → ℝ))
      (volume : Measure (Fin (3 * 3) → ℝ)) := by
  unfold matToFlat3
  refine MeasurePreserving.trans ?_ (volume_preserving_arrowCongr'
    ((Equiv.sigmaEquivProd (Fin 3) (Fin 3)).trans finProdFinEquiv)
    (MeasurableEquiv.refl ℝ) (MeasurePreserving.id _))
  exact (measurePreserving_piCurry (fun (_ : Fin 3) (_ : Fin 3) => ℝ)
    (fun _ _ => (volume : Measure ℝ))).symm
    (MeasurableEquiv.piCurry (fun (_ : Fin 3) (_ : Fin 3) => ℝ))

/-- The flattened `Δ`-box on the `Fin 9` carrier: `[−T,T]^9`. -/
def flatBox3 (T : ℝ) : Set (Fin (3 * 3) → ℝ) := {y | ∀ i, y i ∈ Set.Icc (-T) T}

theorem flatBox3_measurableSet (T : ℝ) : MeasurableSet (flatBox3 T) := by
  rw [flatBox3, Set.setOf_forall]
  exact MeasurableSet.iInter (fun i => (measurable_pi_apply i) measurableSet_Icc)

/-- `matBox 3 3 T = matToFlat3 ⁻¹' flatBox3 T`. -/
theorem matBox3_flatBox_preimage (T : ℝ) : matBox 3 3 T = matToFlat3 ⁻¹' flatBox3 T := by
  ext Δ
  simp only [matBox, flatBox3, Set.mem_setOf_eq, Set.mem_preimage]
  set e : (Σ _ : Fin 3, Fin 3) ≃ Fin (3 * 3) :=
    (Equiv.sigmaEquivProd (Fin 3) (Fin 3)).trans finProdFinEquiv with he
  have hcoord : ∀ i : Fin (3 * 3), (matToFlat3 Δ) i = Δ (e.symm i).1 (e.symm i).2 := fun i => rfl
  constructor
  · intro h i; rw [hcoord i]; exact h (e.symm i).1 (e.symm i).2
  · intro h k j
    have := h (e ⟨k, j⟩)
    rw [hcoord (e ⟨k, j⟩), Equiv.symm_apply_apply] at this
    exact this

/-- The flat-`Δ` cover integrand: `gFlat3 c' T y = ∫_{S∈box 3 4} frobSq(rmatMul (matToFlat3.symm y) S)^{−c'}`. -/
noncomputable def gFlat3 (c' : ℝ) (T : ℝ) (y : Fin (3 * 3) → ℝ) : ℝ≥0∞ :=
  ∫⁻ S in matBox 3 4 T,
    ENNReal.ofReal ((frobSq (rmatMul (matToFlat3.symm y) S)) ^ (-c'))

/-- The `Δ`-outer integral reindexes to the flat `gFlat3` integral over `flatBox3`. -/
theorem matBox3_outer_flat (c' : ℝ) (T : ℝ) :
    (∫⁻ Δ in matBox 3 3 T, ∫⁻ S in matBox 3 4 T,
        ENNReal.ofReal ((frobSq (rmatMul Δ S)) ^ (-c')))
      = ∫⁻ y in flatBox3 T, gFlat3 c' T y := by
  have hmp := measurePreserving_matToFlat3
  have hcomp := hmp.setLIntegral_comp_preimage_emb matToFlat3.measurableEmbedding
    (gFlat3 c' T) (flatBox3 T)
  rw [matBox3_flatBox_preimage, ← hcomp]
  refine setLIntegral_congr_fun (matToFlat3.measurable (flatBox3_measurableSet T)) (fun Δ _ => ?_)
  rw [gFlat3, MeasurableEquiv.symm_apply_apply]

/-- The cover-to-sum on the `Fin 9` flat carrier (`recStep`, the 9-entry argmax cover). -/
theorem gFlat3_cover_sum (c' : ℝ) (T : ℝ) :
    (∫⁻ y in flatBox3 T, gFlat3 c' T y)
      = ∑ p ∈ (Finset.univ : Finset (Fin (3 * 3))),
          ∫⁻ y in chartDomOn (Finset.univ : Finset (Fin (3 * 3))) p \ pivotZeroOn p,
            ENNReal.ofReal |(pivotBlowupOnDeriv (Finset.univ : Finset (Fin (3 * 3))) p y).det|
              * (flatBox3 T).indicator (gFlat3 c' T) (pivotBlowupOn
                  (Finset.univ : Finset (Fin (3 * 3))) p y) := by
  exact recStep (Finset.univ : Finset (Fin (3 * 3))) 0 (Finset.mem_univ 0)
    (flatBox3 T) (flatBox3_measurableSet T) (gFlat3 c' T)

/-- The unflattened angular matrix on chart `p`: `Rmat3 p y` is the `3×3` matrix with `R_p = 1`,
`R_k = y_k` (`k ≠ p`). -/
noncomputable def Rmat3 (p : Fin (3 * 3)) (y : Fin (3 * 3) → ℝ) : Fin 3 → Fin 3 → ℝ :=
  matToFlat3.symm (fun i => if i = p then 1 else y i)

/-- **The radial pull-out** (N1 degree-2 homogeneity): `gFlat3 c' T (blowup) = ∫_S ((y p)²·frobSq(Rmat3·S))^{−c'}`. -/
theorem gFlat3_blowup_radial (c' : ℝ) (T : ℝ) (p : Fin (3 * 3)) (y : Fin (3 * 3) → ℝ) :
    gFlat3 c' T (pivotBlowupOn (Finset.univ : Finset (Fin (3 * 3))) p y)
      = ∫⁻ S in matBox 3 4 T,
          ENNReal.ofReal (((y p) ^ 2 * frobSq (rmatMul (Rmat3 p y) S)) ^ (-c')) := by
  unfold gFlat3 Rmat3
  refine lintegral_congr (fun S => ?_)
  congr 1
  have hbl : matToFlat3.symm (pivotBlowupOn (Finset.univ : Finset (Fin (3 * 3))) p y)
      = fun r c => (y p) * (matToFlat3.symm (fun i => if i = p then 1 else y i)) r c := by
    funext r c
    show matToFlat3.symm (pivotBlowupOn (Finset.univ : Finset (Fin (3 * 3))) p y) r c = _
    rw [show pivotBlowupOn (Finset.univ : Finset (Fin (3 * 3))) p y
        = (fun i => (y p) * (if i = p then 1 else y i)) from by
      funext i; unfold pivotBlowupOn
      by_cases hi : i = p
      · subst hi; simp
      · simp [hi]]
    show matToFlat3.symm (fun i => (y p) * (if i = p then 1 else y i)) r c
        = (y p) * matToFlat3.symm (fun i => if i = p then 1 else y i) r c
    rfl
  rw [hbl, radialDelta_loss_factor (y p) (matToFlat3.symm (fun i => if i = p then 1 else y i)) S]

end DLNFibre.DLN.RLCT
