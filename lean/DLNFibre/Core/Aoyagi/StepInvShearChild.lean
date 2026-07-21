import DLNFibre.Core.Aoyagi.PrincipalInv
import DLNFibre.Core.Aoyagi.BlockDivision

/-!
# `Core.Aoyagi.StepInvShearChild` — the δ=1 child `StepInv` under FIX-A (SEAT-L4, THE WALL)

The δ-agnostic heart of the coupled Case-1 step, proved abstractly against the elder's FIX-A +
FIX-RESID rulings so it instantiates unchanged at the fold's concrete data (arch-C's amended defs):

* **FIX-A** — the step map is `σ = blockBlowupMap center pivot ∘ sh` (blow-up OUTERMOST, thread-34's
  order), with the shear `sh` KEEPING the pivot (`hsh_pivot : ∀ u, sh u pivot = u pivot`). Then each
  center coordinate of `σ` gains the pivot factor structurally (`blockBlowupMap_shear_center_eq`).
* **FIX-RESID** — the child dominant gains `u_pivot` (δ=1) and the child residual is the STRICT
  TRANSFORM (the `blockBlowupCoordQuot` combination), so the `u_pivot` balances and the witness law
  is `q' = q∘σ` (NO division on the witness).

`hsupp` is the ideal-membership `SupportedOn`: `resid j u = ∑_{i∈center} c j i u · u i` (the
residual is a center-coordinate combination — Aoyagi's residual IS the center block). No
`ContinuousOn` on `resid'` is needed (`StepInv` requires it only of the witness `q'`).
-/

open MeasureTheory Set Filter Topology RLCT

namespace DLNFibre.Core.Aoyagi

variable {M D nR : ℕ}

/-- **The δ=0 child `StepInv` (pure pullback).** When the child dominant does NOT gain the pivot
factor (δ=0), the child `StepInv` is the plain pullback along ANY origin-fixing continuous step map
`σ`: `b' = b∘σ`, `resid'ⱼ = residⱼ∘σ`, `q' = q∘σ`. No divisibility / shear hypothesis needed. -/
theorem stepInv_delta0_pullback_child
    {F : Fin M → (Fin D → ℝ) → ℝ} {g : (Fin D → ℝ) → (Fin D → ℝ)} {b : (Fin D → ℝ) → ℝ}
    {resid : Fin nR → (Fin D → ℝ) → ℝ} {q : Fin M → Fin nR → (Fin D → ℝ) → ℝ}
    {V : Set (Fin D → ℝ)} {σ : (Fin D → ℝ) → (Fin D → ℝ)}
    (hStep : StepInv F g b resid q V) (hσ_cont : Continuous σ) (hσ0 : σ 0 = 0) :
    StepInv F (fun u ↦ g (σ u)) (fun u ↦ b (σ u)) (fun j u ↦ resid j (σ u))
      (fun i j u ↦ q i j (σ u)) (σ ⁻¹' V) := by
  refine ⟨fun i j ↦ (hStep.1 i j).comp hσ_cont.continuousOn (fun u hu ↦ hu), fun i ↦ ?_,
    fun u hu i ↦ ?_⟩
  · have h1 : (F i ∘ fun u ↦ g (σ u)) 0 = (F i ∘ g) (σ 0) := rfl
    rw [h1, hσ0]; exact hStep.2.1 i
  · exact hStep.2.2 (σ u) hu i

/-- **The δ=1 child `StepInv` (FIX-A + FIX-RESID).** From a parent `StepInv` whose residual is a
center-coordinate combination (`hsupp`), a pivot-keeping shear `sh`, and the blow-up-outermost step
map `σ = blockBlowupMap center pivot ∘ sh`, the child `StepInv` holds with dominant `b' =
u_pivot·(b∘σ)`, residual the STRICT TRANSFORM `resid'_j = ∑_{i∈center}(c_ji∘σ)·quot_i(sh ·)`, and
witness `q' = q∘σ`. -/
theorem stepInv_delta1_shear_child
    {F : Fin M → (Fin D → ℝ) → ℝ} {g : (Fin D → ℝ) → (Fin D → ℝ)} {b : (Fin D → ℝ) → ℝ}
    {resid : Fin nR → (Fin D → ℝ) → ℝ} {q : Fin M → Fin nR → (Fin D → ℝ) → ℝ}
    {V : Set (Fin D → ℝ)} {center : Finset (Fin D)} {pivot : Fin D}
    {sh : (Fin D → ℝ) → (Fin D → ℝ)} {c : Fin nR → Fin D → (Fin D → ℝ) → ℝ}
    (hStep : StepInv F g b resid q V)
    (hsupp : ∀ (j : Fin nR), ∀ u ∈ V, resid j u = ∑ i ∈ center, c j i u * u i)
    (hsh_cont : Continuous sh) (hsh0 : sh 0 = 0) (hsh_pivot : ∀ u, sh u pivot = u pivot) :
    StepInv F (fun u ↦ g (blockBlowupMap center pivot (sh u)))
      (fun u ↦ u pivot * b (blockBlowupMap center pivot (sh u)))
      (fun j u ↦ ∑ i ∈ center, c j i (blockBlowupMap center pivot (sh u))
        * blockBlowupCoordQuot pivot i (sh u))
      (fun i j u ↦ q i j (blockBlowupMap center pivot (sh u)))
      ((fun u ↦ blockBlowupMap center pivot (sh u)) ⁻¹' V) := by
  set σ : (Fin D → ℝ) → (Fin D → ℝ) := fun u ↦ blockBlowupMap center pivot (sh u) with hσ
  have hσ_cont : Continuous σ := (continuous_blockBlowupMap center pivot).comp hsh_cont
  have hσ0 : σ 0 = 0 := by
    rw [hσ]; simp only; rw [hsh0, blockBlowupMap_zero]
  have hmaps : Set.MapsTo σ (σ ⁻¹' V) V := fun u hu ↦ hu
  refine ⟨fun i j ↦ ?_, fun i ↦ ?_, fun u hu i ↦ ?_⟩
  · -- q' = q∘σ continuous on the child region
    exact (hStep.1 i j).comp hσ_cont.continuousOn hmaps
  · -- child S3: (F i ∘ (g∘σ)) 0 = (F i∘g)(σ 0) = (F i∘g) 0 = 0
    have h1 : (F i ∘ fun u ↦ g (σ u)) 0 = (F i ∘ g) (σ 0) := rfl
    rw [h1, hσ0]; exact hStep.2.1 i
  · -- the divisibility factorization at u ∈ σ⁻¹V
    have hσu : σ u ∈ V := hu
    -- resid_j(σu) = u_pivot · resid'_j(u)   (the strict-transform division, FIX-A)
    have hres : ∀ j, resid j (σ u)
        = u pivot * ∑ i ∈ center, c j i (σ u) * blockBlowupCoordQuot pivot i (sh u) := by
      intro j
      rw [hsupp j (σ u) hσu, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i' hi' ↦ ?_)
      have hbb : σ u i' = u pivot * blockBlowupCoordQuot pivot i' (sh u) :=
        blockBlowupMap_shear_center_eq center pivot hi' sh hsh_pivot u
      rw [hbb]; ring
    have hstepσ := hStep.2.2 (σ u) hσu i
    -- rewrite the parent factorization at σu, substitute hres, reassemble
    show (F i ∘ fun u ↦ g (σ u)) u
      = ∑ j, q i j (σ u) * ((u pivot * b (σ u))
          * ∑ i' ∈ center, c j i' (σ u) * blockBlowupCoordQuot pivot i' (sh u))
    have hlhs : (F i ∘ fun u ↦ g (σ u)) u = (F i ∘ g) (σ u) := rfl
    rw [hlhs, hstepσ]
    refine Finset.sum_congr rfl (fun j _ ↦ ?_)
    rw [hres j]; ring

end DLNFibre.Core.Aoyagi
