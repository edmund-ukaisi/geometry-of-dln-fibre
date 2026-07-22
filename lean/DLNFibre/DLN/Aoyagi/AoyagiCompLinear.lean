import DLNFibre.DLN.Aoyagi.MonumentAtlas

/-!
# `DLN.Aoyagi.AoyagiCompLinear` — `AffineOn`/`HomogeneousDeg1On` survive a support-LINEAR map (SEAT-L3T2)

The N_p faithful shear (`canonNormalizationOf`) WRITES the support layer `sl = S+1` (component (ii), the
deeper recoord `A_{S+1}·Q₁⁻¹`), degree-1-LINEAR in the layer-`sl` coords. So the pre-N_p
`…_comp_of_fixing` (which assumed the step map FIXES layer `sl`) no longer applies at `ℓ = sl`; the step
shifts to a `comp_of_linear` variant: `AffineOn`/`HomogeneousDeg1On` survive composition with a map `σ`
that is HOMOGENEOUS-LINEAR on the block `X` (with `X`-free coefficients) and preserves off-`X` agreement.

Decoupled (imports only `MonumentAtlas`) so it verifies independently of the slot's re-wire; consumed by
both the slot descent arms' clause-2 (`MultiAffineStepWire`) and the homogeneity induction
(`MultiAffineHomogWire`).
-/

open MeasureTheory Set
open DLNFibre.Core DLNFibre.Core.Aoyagi

namespace DLNFibre.DLN.Aoyagi

variable {D : ℕ}

/-- **`AffineOn` survives a support-linear map.** If `σ` is homogeneous-`X`-linear on the block `X`
(`σ u x = ∑_{j∈X} C u x j · u j`, coefficients `C` reading no `X`-coord) and preserves off-`X` agreement,
then `g ∘ σ` is `AffineOn` on `X`: constant part `a ∘ σ`, and the `X`-linear part absorbs `σ`'s linear
action (`b'_j = ∑_x b_x(σ·)·C · x j`). -/
theorem affineOn_comp_of_linear
    (g : (Fin D → ℝ) → ℝ) (X : Finset (Fin D))
    (σ : (Fin D → ℝ) → (Fin D → ℝ))
    (C : (Fin D → ℝ) → Fin D → Fin D → ℝ)
    (hagree : ∀ u v : Fin D → ℝ, (∀ s, s ∉ X → u s = v s) → ∀ s, s ∉ X → σ u s = σ v s)
    (hlin : ∀ u, ∀ x ∈ X, σ u x = ∑ j ∈ X, C u x j * u j)
    (hC : ∀ x ∈ X, ∀ j ∈ X, IgnoresCoords (fun u => C u x j) X Set.univ)
    (hg : AffineOn g X Set.univ) :
    AffineOn (fun u => g (σ u)) X Set.univ := by
  obtain ⟨a, b, ha_ign, hb_ign, hrepr⟩ := hg
  refine ⟨fun u => a (σ u), fun j u => ∑ x ∈ X, b x (σ u) * C u x j, ?_, ?_, ?_⟩
  · -- constant part `a ∘ σ` ignores `X`
    exact (ignoresCoords_univ_iff_agree _ X).mpr (fun u v hag =>
      (ignoresCoords_univ_iff_agree a X).mp ha_ign (σ u) (σ v) (hagree u v hag))
  · -- each coefficient `∑_x b_x(σ·)·C·x j` ignores `X`
    intro j hj
    refine (ignoresCoords_univ_iff_agree _ X).mpr (fun u v hag => ?_)
    refine Finset.sum_congr rfl (fun x hx => ?_)
    rw [(ignoresCoords_univ_iff_agree (b x) X).mp (hb_ign x hx) (σ u) (σ v) (hagree u v hag),
      (ignoresCoords_univ_iff_agree _ X).mp (hC x hx j hj) u v hag]
  · -- representation: absorb `σ`'s linear action, swap the sums
    intro u _
    show g (σ u) = a (σ u) + ∑ j ∈ X, (∑ x ∈ X, b x (σ u) * C u x j) * u j
    rw [hrepr (σ u) (Set.mem_univ _)]
    congr 1
    rw [Finset.sum_congr rfl (fun x hx => by rw [hlin u x hx, Finset.mul_sum])]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    ring

/-- **`HomogeneousDeg1On` survives a support-linear map.** `AffineOn` via `affineOn_comp_of_linear`;
the vanishing clause because a homogeneous-`X`-linear `σ` maps "every `X`-coord zero" to itself
(`σ u x = ∑_j C u x j · 0 = 0`), so `g (σ u) = 0` by `g`'s vanishing. -/
theorem homogeneousDeg1On_comp_of_linear
    (g : (Fin D → ℝ) → ℝ) (X : Finset (Fin D))
    (σ : (Fin D → ℝ) → (Fin D → ℝ))
    (C : (Fin D → ℝ) → Fin D → Fin D → ℝ)
    (hagree : ∀ u v : Fin D → ℝ, (∀ s, s ∉ X → u s = v s) → ∀ s, s ∉ X → σ u s = σ v s)
    (hlin : ∀ u, ∀ x ∈ X, σ u x = ∑ j ∈ X, C u x j * u j)
    (hC : ∀ x ∈ X, ∀ j ∈ X, IgnoresCoords (fun u => C u x j) X Set.univ)
    (hg : HomogeneousDeg1On g X Set.univ) :
    HomogeneousDeg1On (fun u => g (σ u)) X Set.univ := by
  refine ⟨affineOn_comp_of_linear g X σ C hagree hlin hC hg.1, ?_⟩
  intro u _ hu
  refine hg.2 (σ u) (Set.mem_univ _) (fun x hx => ?_)
  rw [hlin u x hx]
  exact Finset.sum_eq_zero (fun j hj => by rw [hu j hj, mul_zero])

end DLNFibre.DLN.Aoyagi
