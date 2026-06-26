import DLNFibre.DLN.RLCT.Validate.Case222Cover

/-!
# `DLNFibre.DLN.RLCT.Validate.RouteMCoverLemmas` — abstract cover-fact reductions (fm3)

The reusable, atlas-construction-agnostic reductions for the two `IsRouteMCover` integral facts. They
take ABSTRACT data `(F, U, ι, d, k, h)` (NOT the Route-M atlas — so they bank independently of the
`routeStep` dispatcher) and reduce the cover facts to FINITENESS + DIVERGENCE atoms:

- `coverLe_scaling` : the `ℝ≥0∞` building block — `A < ⊤ ∧ B ≠ 0 ⟹ ∃ C < ⊤, A ≤ C·B`.
- `routeM_coverLe_of_finiteness` : the `cover_le` field shape, from (a) below-threshold `∫⁻_U |F|^{−c'}
  < ⊤` and (b) the leaf-sum RHS `≠ 0`. The bridge consumes `cover_le` ONLY for the `≥`-leg finiteness
  transfer (`mul_lt_top`), so a finite prefactor `C(c')` — produced here abstractly — suffices; NO
  explicit per-node change-of-variables is needed for `cover_le` (Codex g206, verified vs `RouteMBridge`).
- `routeM_coverGeDiv_of_boxDiverges` : the `cover_ge_div` field shape, from an `ε`-uniform box
  divergence `∫⁻_{[−ε,ε]^N} |F|^{−c'} = ⊤` (the same content as `rlctAtOn_le_of_box_diverges`'s
  hypothesis, repackaged to the `¬ IntegrableOn` form the bridge's `≤`-leg negates).

These are the analytic SKELETON; the consumer (the `(2,2,2)` instance, or the general atlas) supplies
the finiteness atom (banked `myF222_threshold_lt_top'`) and the divergence atom (banked
`monomialIntegrand_lintegral_box_eq_top` / the `(2,2,2)` `≤`-half box-divergence).
-/

open MeasureTheory
open scoped BigOperators ENNReal
namespace DLNFibre.DLN.RLCT

/-- **The `cover_le` scaling building block.** If `A < ⊤` and `B ≠ 0`, there is a finite `C` with
`A ≤ C·B`: take `C = A/B` when `B ≠ ⊤` (`div_mul_cancel`), or `C = 1` when `B = ⊤` (`A ≤ ⊤`). Pure
`ℝ≥0∞`. This is what lets `cover_le` carry the irreducible `a^{−c'}·2^d` normalization slack as a
per-`c'` finite prefactor (the bridge uses it only for the `≥`-leg finiteness transfer). -/
theorem coverLe_scaling {A B : ℝ≥0∞} (hA : A < ⊤) (hB : B ≠ 0) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ A ≤ C * B := by
  rcases eq_or_ne B ⊤ with hBtop | hBfin
  · exact ⟨1, by simp, by rw [hBtop, ENNReal.mul_top (by norm_num)]; exact le_top⟩
  · exact ⟨A / B, ENNReal.div_lt_top hA.ne hB, by rw [ENNReal.div_mul_cancel hB hBfin]⟩

/-- **The `cover_le` field, from finiteness.** Abstract over `(F, U, ι, d, k, h)`: if (a) the leaf-sum
RHS is `≠ 0` for every `c'`, and (b) whenever the leaf-sum is FINITE the `U`-integral `∫⁻_U |F|^{−c'}`
is finite (the below-threshold finiteness), then the `IsRouteMCover.cover_le` shape holds. Two cases:
the leaf-sum `= ⊤` ⟹ `C = 1` (`A ≤ ⊤`); the leaf-sum `< ⊤` ⟹ `A < ⊤` by (b), then `coverLe_scaling`.
This is the exact `cover_le` field — the bridge uses it only for the `≥`-leg finiteness transfer, so
the finite per-`c'` prefactor produced here suffices; no per-node change-of-variables needed. -/
theorem routeM_coverLe_of_finiteness {N : ℕ} (F : (Fin N → ℝ) → ℝ) (U : Set (Fin N → ℝ))
    {ι : Type} [Fintype ι] (d : ι → ℕ) (k h : (i : ι) → Fin (d i) → ℕ)
    (hpos : ∀ c' : NNReal,
      (∑ i : ι, ∫⁻ y in unitBox (d i),
          ENNReal.ofReal (monomialIntegrand (d i) (k i) (h i) (c' : ℝ) y)) ≠ 0)
    (hfin : ∀ c' : NNReal,
      (∑ i : ι, ∫⁻ y in unitBox (d i),
          ENNReal.ofReal (monomialIntegrand (d i) (k i) (h i) (c' : ℝ) y)) < ⊤ →
      ∫⁻ x in U, ENNReal.ofReal (|F x| ^ (-(c' : ℝ))) < ⊤) :
    ∀ c' : NNReal, ∃ C : ℝ≥0∞, C < ⊤ ∧
      ∫⁻ x in U, ENNReal.ofReal (|F x| ^ (-(c' : ℝ)))
        ≤ C * ∑ i : ι, ∫⁻ y in unitBox (d i),
            ENNReal.ofReal (monomialIntegrand (d i) (k i) (h i) (c' : ℝ) y) := by
  intro c'
  set B := ∑ i : ι, ∫⁻ y in unitBox (d i),
      ENNReal.ofReal (monomialIntegrand (d i) (k i) (h i) (c' : ℝ) y) with hB
  rcases eq_or_ne B ⊤ with hBtop | hBfin
  · exact ⟨1, by simp, by rw [hBtop, ENNReal.mul_top (by norm_num)]; exact le_top⟩
  · exact coverLe_scaling (hfin c' (lt_top_iff_ne_top.2 hBfin)) (hpos c')

/-- **The `cover_ge_div` field, from an `ε`-uniform box divergence.** Abstract over `(F, U, ι, d, k, h)`:
if, whenever some leaf threshold is `≤ c'`, the `U`-integral over EVERY box `[−ε, ε]^N` is `⊤`, then no
open `Ω ∋ 0` is admissible for `c'` — `IntegrableOn (|F|^{−c'}·1) Ω` would force `∫⁻_Ω < ⊤`, hence
`∫⁻_{cubeBox ε} < ⊤` on a sub-cube (`cubeBox_subset_of_isOpen` + `lintegral_mono_set`), contradicting
the divergence. This is the `IsRouteMCover.cover_ge_div` shape; the inner argument is exactly the body
of `rlctAtOn_le_of_box_diverges` (the `≤`-direction localisation), repackaged to the `¬ IntegrableOn`
form the bridge's `≤`-leg negates. The `ε`-uniform divergence atom is the genuine analytic content the
consumer supplies (`monomialIntegrand_lintegral_box_eq_top` per binding leaf, transported to `F`). -/
theorem routeM_coverGeDiv_of_boxDiverges {N : ℕ} (F : (Fin N → ℝ) → ℝ)
    {ι : Type} [Fintype ι] (d : ι → ℕ) (k h : (i : ι) → Fin (d i) → ℕ)
    (hdiv : ∀ c' : NNReal, (∃ i : ι, monomialThreshold (d i) (k i) (h i) ≤ (c' : ℝ≥0∞)) →
      ∀ ε > 0, ∫⁻ x in cubeBox N ε, ENNReal.ofReal (|F x| ^ (-(c' : ℝ))) = ⊤) :
    ∀ c' : NNReal, (∃ i : ι, monomialThreshold (d i) (k i) (h i) ≤ (c' : ℝ≥0∞)) →
      ∀ Ω : Set (Fin N → ℝ), IsOpen Ω → (0 : Fin N → ℝ) ∈ Ω →
        ¬ IntegrableOn (fun x => |F x| ^ (-(c' : ℝ)) * (fun _ => (1 : ℝ)) x) Ω volume := by
  intro c' hbind Ω hΩopen h0 hint
  -- strip the trivial weight; `|F|^{−c'}` is integrable on `Ω`
  have hintF : IntegrableOn (fun w => |F w| ^ (-(c' : ℝ))) Ω volume := by
    simpa only [mul_one] using hint
  -- extract a cube `[−ε, ε]^N ⊆ Ω`
  obtain ⟨ε, hε, hsub⟩ := cubeBox_subset_of_isOpen hΩopen h0
  -- `∫⁻_Ω ofReal|F|^{−c'} < ⊤` (finite-integral of the nonneg integrand)
  have hΩfin : ∫⁻ x in Ω, ENNReal.ofReal (|F x| ^ (-(c' : ℝ))) ∂volume < ⊤ := by
    rw [← hasFiniteIntegral_iff_ofReal (ae_of_all _ (fun x => Real.rpow_nonneg (abs_nonneg _) _))]
    exact hintF.2
  -- monotone over `cubeBox N ε ⊆ Ω`, contradicting the ε-divergence
  have hbox : ∫⁻ x in cubeBox N ε, ENNReal.ofReal (|F x| ^ (-(c' : ℝ))) ∂volume < ⊤ :=
    lt_of_le_of_lt (lintegral_mono_set hsub) hΩfin
  rw [hdiv c' hbind ε hε] at hbox
  exact lt_irrefl _ hbox

end DLNFibre.DLN.RLCT
