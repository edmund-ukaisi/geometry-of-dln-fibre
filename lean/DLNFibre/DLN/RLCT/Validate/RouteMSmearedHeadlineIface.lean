import DLNFibre.DLN.RLCT.Validate.RouteMSmearedBoxDiv
import DLNFibre.DLN.RLCT.Validate.RouteMSmearedContract

/-!
# `RouteMSmearedHeadlineIface` — the contract interface for the smeared headline (honest ceiling)

The honest-ceiling interface (Codex `headline-path-answer` §4): specializes the BANKED radial-MP contract
(`routeMCore_box_diverges_smearedContract`) to the BANKED source box `smearedSubBox p δ`, so the smeared
box-divergence headline reduces to NAMED chart-geometry hypotheses — no `sorry`, no re-derived measure
theory. The contract's weighted divergence `hSdiv` is supplied by the BANKED
`smearedSubBox_weighted_diverges` (this file's sibling, the axis-peel engine on the real source box).

The remaining gaps, made precise as the interface's hypotheses:
* `hmp`/`hemb` — `ψ` (shear∘reshape) is measure-preserving + a measurable embedding (banked
  `measurePreserving_shearM` + the reshape; assembled per family);
* `hRderiv`/`hRinj`/`hRdet` — the radial blow-up `R`'s C¹ / injectivity / determinant `|u p|^h` (generic
  `pivotBlowupOn` facts);
* `hSpre` — the containment `smearedSubBox p δ ⊆ (ψ∘R)⁻¹(cubeBox ε)` (FIELD A, per family);
* `hSdiv` — the weighted divergence (FIELD B; produced by `smearedSubBox_weighted_diverges` from the
  peeled rate + `U`-positivity — the chart-eval transported to the contract's `routeMCore (ψ (R ·))` form).

So the full headline is exactly: factorization/rate transport (→ `hSdiv` via the banked engine) +
containment (`hSpre`) + the chart's MP/embedding/radial facts.
-/

open MeasureTheory
open scoped ENNReal BigOperators

namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-- **The smeared box-divergence headline on `smearedSubBox` (the contract, specialized).** The achiever
box integral `∫_{cubeBox N ε} |routeMCore|^{−c'} = ⊤` from the chart facts (`ψ` MP + embedding, `R` radial
C¹/injective/`|det| = |u p|^h`), the containment `smearedSubBox p δ ⊆ (ψ∘R)⁻¹(cubeBox ε)`, and the weighted
divergence `hSdiv` on `smearedSubBox p δ` (supplied by `smearedSubBox_weighted_diverges`). The contract
specialized to the banked source box. -/
theorem routeMCore_box_diverges_on_smearedSubBox (M : Fin (L + 1) → ℕ)
    (ψ R : (Fin (routeMAmbient M) → ℝ) → (Fin (routeMAmbient M) → ℝ))
    (D : (Fin (routeMAmbient M) → ℝ) → (Fin (routeMAmbient M) → ℝ) →L[ℝ] (Fin (routeMAmbient M) → ℝ))
    (p : Fin (routeMAmbient M)) (h : ℕ) (c' ε δ : ℝ)
    (hmp : MeasurePreserving ψ (volume : Measure (Fin (routeMAmbient M) → ℝ)) volume)
    (hemb : MeasurableEmbedding ψ)
    (hSpre : smearedSubBox p δ ⊆ (fun u => ψ (R u)) ⁻¹' (cubeBox (routeMAmbient M) ε))
    (hRderiv : ∀ u ∈ smearedSubBox p δ, HasFDerivWithinAt R (D u) (smearedSubBox p δ) u)
    (hRinj : Set.InjOn R (smearedSubBox p δ))
    (hRdet : ∀ u ∈ smearedSubBox p δ, |(D u).det| = |u p| ^ h)
    (hSdiv : (∫⁻ u in smearedSubBox p δ, ENNReal.ofReal (|u p| ^ h)
      * ENNReal.ofReal (|routeMCore M (ψ (R u))| ^ (-c'))) = ⊤) :
    ∫⁻ x in cubeBox (routeMAmbient M) ε,
      ENNReal.ofReal (|routeMCore M x| ^ (-c')) = ⊤ :=
  routeMCore_box_diverges_smearedContract M ψ R D p h hmp hemb c' ε
    (smearedSubBox p δ) (measurableSet_smearedSubBox p δ) hSpre hRderiv hRinj hRdet hSdiv

/-- **The contract's `hSdiv` from the peeled quadratic rate** (the bridge into
`routeMCore_box_diverges_on_smearedSubBox`). For a pivot `p : Fin (n+1)`, the weighted divergence on
`smearedSubBox p δ` follows from the peeled rate `routeMCore M (ψ (R (insertNth p z y))) = z²·Uy y`
(`Uy` measurable + positive on the rest box) and `(h:ℝ) − 2c' ≤ −1`. Reconciles the contract's `ℕ`-power
weight `|u p|^h` with the engine's `ℝ`-power via `Real.rpow_natCast`, and combines the two `ofReal`s. -/
theorem hSdiv_of_peeled_rate {n : ℕ} (M : Fin (L + 1) → ℕ) (hN : routeMAmbient M = n + 1)
    (ψ R : (Fin (routeMAmbient M) → ℝ) → (Fin (routeMAmbient M) → ℝ))
    (p : Fin (n + 1)) (h : ℕ) (c' δ : ℝ) (Uy : (Fin n → ℝ) → ℝ)
    (hδ : 0 < δ) (hUmeas : Measurable Uy) (hexp : (h : ℝ) - 2 * c' ≤ -1)
    (W : (Fin (n + 1) → ℝ) → ℝ)
    (hW : ∀ u : Fin (n + 1) → ℝ, W u = routeMCore M (ψ (R (hN ▸ u))))
    (hRate : ∀ z ∈ Set.Ioo (0:ℝ) δ,
      ∀ y ∈ Set.univ.pi (fun _ : Fin n => Set.Icc (-δ) δ),
        W (Fin.insertNth p z y) = z ^ 2 * Uy y)
    (hUpos : ∀ y ∈ Set.univ.pi (fun _ : Fin n => Set.Icc (-δ) δ), 0 < Uy y) :
    (∫⁻ u in smearedSubBox p δ, ENNReal.ofReal (|u p| ^ h)
      * ENNReal.ofReal (|W u| ^ (-c'))) = ⊤ := by
  -- combine the two `ofReal`s (`|u p|^h ≥ 0`) and convert `ℕ`-power to `ℝ`-power
  have hcomb : (∫⁻ u in smearedSubBox p δ, ENNReal.ofReal (|u p| ^ h)
      * ENNReal.ofReal (|W u| ^ (-c')))
      = ∫⁻ u in smearedSubBox p δ,
          ENNReal.ofReal (|u p| ^ (h : ℝ) * |W u| ^ (-c')) := by
    refine lintegral_congr_ae (Filter.Eventually.of_forall (fun u => ?_))
    simp only
    rw [← Real.rpow_natCast |u p| h, ← ENNReal.ofReal_mul (by positivity)]
  rw [hcomb]
  exact smearedSubBox_weighted_diverges p δ (h : ℝ) c' W Uy hδ hUmeas hexp hRate hUpos

end DLNFibre.DLN.RLCT
