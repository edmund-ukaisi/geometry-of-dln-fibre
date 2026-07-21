import DLNFibre.Core.Aoyagi.PathAtoms
import DLNFibre.Core.Aoyagi.BlockDivision

/-!
# `Core.Aoyagi.Case2RefuteProbe` — the gate witness for the `hshear_center` alignment field

**seat-w0l3, L3 stop-on-suspect (2026-07-21).** The concrete construction that refuted the
free-`shearφ` form of `case2_preserves_stepInv` at a δ=1 case-2 edge with a NON-trivial spectator, and
that the elder-ruled `hshear_center` alignment field (placement (i), the third `TreeEdge` shear
proof-field) now KILLS at construction (the edge becomes untypeable).

## The construction

Ambient `Fin D` with three DISTINCT coordinates `p` (pivot), `c` (a non-pivot center member), `s` (a
SPECTATOR, `s ∉ center`). Center `S = {p, c}`. The shear displacement injects the spectator's squared
value into the center coordinate `c`:

  `refuteφ s c := fun w ↦ Pi.single c ((w s) ^ 2)`.

This φ is ADMISSIBLE under the OLD shear fields — `jacDet (blockShear (refuteφ s c)) ≡ 1` (a single
nilpotent off-diagonal `∂/∂w_s`, `c ≠ s`; via the W0 `jacDet_blockShear` at keep-set `{s}`) and
`refuteφ 0 = 0`. But after the block-center blow-up the spectator SURVIVES (`blockBlowupMap` fixes
`w_s`), so along `{w_p = 0}` the shear injects `(w_s)^2 ≠ 0` into the center coordinate `c ∈ S`:

  `refuteφ (blockBlowupMap S p u)` at `u_p = 0`, `u_s = 1`, reads `c ↦ ((u_s)^2) = 1 ≠ 0`.

So `foldResid p j ∘ (blockShear φ ∘ blockBlowupMap S p)` fails to vanish on `{u_p = 0}`, breaking the
`u_p`-divisibility that the δ=1 child `StepInv` needs (`b' = u_p · (foldB ∘ σ)` forces the LHS
divisible by `u_p`; here it is not). The full `¬ (∃ child q)` is heavy (a continuous-function
non-membership); it is documented, the ADMISSIBILITY + the exact `hshear_center` VIOLATION are the
kernel-checked content here.

## The fix kills it at construction

`hshear_center pivot center φ := ∀ u, u pivot = 0 → ∀ i ∈ center, φ (blockBlowupMap center pivot u) i
= 0` (the elder-ruled field, pivot-inclusive). `refuteφ_violates_hshear_center` below exhibits the
witness `u` with `u pivot = 0` yet `refuteφ (blockBlowupMap S p u) c ≠ 0`, `c ∈ S` — so an edge
carrying `refuteφ` cannot supply the field, i.e. the whole refutation family is UNTYPEABLE under the
amended `TreeEdge` (death-at-construction, the strongest death). This file is the regression witness
that the amended statement excludes exactly this construction.
-/

open MeasureTheory Set Filter Topology RLCT

namespace DLNFibre.Core.Aoyagi

variable {D : ℕ}

/-- The refuting shear displacement: inject the spectator `s`'s squared value into the center
coordinate `c`. -/
def refuteφ (s c : Fin D) : (Fin D → ℝ) → (Fin D → ℝ) :=
  fun w ↦ Pi.single c ((w s) ^ 2)

/-- `refuteφ` fixes the origin. -/
theorem refuteφ_zero (s c : Fin D) : refuteφ s c 0 = 0 := by
  simp [refuteφ]

/-- **Admissibility (old fields): `jacDet (blockShear (refuteφ s c)) ≡ 1`.** The displacement keeps and
reads only the spectator coordinate `s` (`c ≠ s`), so `blockShear` is unipotent with det ≡ 1 — the W0
`jacDet_blockShear` at keep-set `{s}`. So a free `shearφ := refuteφ s c` satisfies `hshear`. -/
theorem jacDet_blockShear_refuteφ (s c : Fin D) (hsc : s ≠ c) (u : Fin D → ℝ) :
    jacDet (blockShear (refuteφ s c)) u = 1 := by
  refine jacDet_blockShear (refuteφ s c) (fun i ↦ i = s) ?_ ?_ ?_ u
  · -- differentiable: `w ↦ Pi.single c ((w s)^2)` is a polynomial map
    refine differentiable_pi.mpr (fun i ↦ ?_)
    by_cases hi : i = c
    · have : (fun w : Fin D → ℝ ↦ refuteφ s c w i) = fun w ↦ (w s) ^ 2 := by
        funext w; simp [refuteφ, Pi.single_apply, hi]
      rw [this]; exact ((differentiable_apply s).pow 2)
    · have : (fun w : Fin D → ℝ ↦ refuteφ s c w i) = fun _ ↦ (0 : ℝ) := by
        funext w; simp [refuteφ, Pi.single_apply, hi]
      rw [this]; exact differentiable_const 0
  · -- hkeep: for a kept coord `i = s`, the displacement vanishes (`s ≠ c`)
    intro w i hi
    have hic : i ≠ c := by rw [hi]; exact hsc
    simp [refuteφ, Pi.single_apply, hic]
  · -- hread: the displacement reads only the kept coord `s`
    intro w v hwv
    funext i
    simp only [refuteφ, Pi.single_apply]
    rw [hwv s rfl]

/-- **The `hshear_center` VIOLATION** (the death-at-construction witness): with `S` the center, `p` the
pivot, `c ∈ S` a non-pivot member and `s ∉ S` a spectator, there is a `u` with `u p = 0` yet
`refuteφ s c (blockBlowupMap S p u) c ≠ 0`. So no edge carrying `refuteφ s c` can supply the elder's
`hshear_center` field — the refutation family is untypeable under the amended `TreeEdge`. -/
theorem refuteφ_violates_hshear_center {S : Finset (Fin D)} {p c s : Fin D}
    (hp : p ∈ S) (hc : c ∈ S) (hs : s ∉ S) (hcp : c ≠ p) (hsp : s ≠ p) :
    ∃ u : Fin D → ℝ, u p = 0 ∧ refuteφ s c (blockBlowupMap S p u) c ≠ 0 := by
  refine ⟨Pi.single s 1, ?_, ?_⟩
  · -- (Pi.single s 1) p = 0  since p ≠ s
    exact Pi.single_eq_of_ne (Ne.symm hsp) 1
  · -- refuteφ reads the spectator, which the blow-up fixes at value 1
    have hspec := blockBlowupMap_spectator_eq S hp hs (Pi.single (s : Fin D) (1 : ℝ))
    have hc' : refuteφ s c (blockBlowupMap S p (Pi.single s 1)) c
        = (blockBlowupMap S p (Pi.single s 1) s) ^ 2 := by
      simp [refuteφ, Pi.single_apply]
    rw [hc', hspec]; simp

end DLNFibre.Core.Aoyagi
