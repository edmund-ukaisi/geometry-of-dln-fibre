import DLNFibre.Core.Aoyagi.PathAtoms

/-!
SEAT-L4 — THE WALL checkpoint, kernel witness: a FREE `ed.shearφ` breaks the case12 δ=1 divisibility.

`φbad` writes the SPECTATOR coord `2` into the CENTER coord `1`. It is a LEGAL `ed.shearφ`
(`jacDet (blockShear φbad) = 1`, `φbad 0 = 0`), yet the center coordinate `1`, pulled back through
`stepMap = blockShear φbad ∘ blockBlowupMap {0,1} 0` (the render's shear-AFTER-blowup order), is NOT
divisible by the pivot coordinate `u 0` — it equals the spectator value at `u 0 = 0`. So a
center-supported residual (`SupportedOn {0,1}`, e.g. `w ↦ w 1`) pulls back OUT of `⟨u_pivot⟩`, and the
δ=1 child `StepInv` (whose `foldB` carries the extra `u_pivot`) has no witness. STOP-ON-SUSPECT.
-/

open DLNFibre.Core.Aoyagi Set

/-- The free shear displacement: put the spectator coord `2` into the center coord `1`. -/
noncomputable def φbad : (Fin 3 → ℝ) → (Fin 3 → ℝ) := fun w ↦ fun i ↦ if i = 1 then w 2 else 0

/-- `φbad` fixes the origin. -/
example : φbad 0 = 0 := by funext i; simp [φbad]

/-- `blockShear φbad` has Jacobian determinant `1` — so `φbad` is a LEGAL `ed.shearφ` (`hshear`). -/
example : ∀ u, jacDet (blockShear φbad) u = 1 := by
  intro u
  refine jacDet_blockShear φbad (fun i ↦ i ≠ 1) ?_ ?_ ?_ u
  · refine differentiable_pi.mpr (fun i ↦ ?_)
    by_cases hi : i = 1
    · simp only [φbad, hi, if_true]; exact (differentiable_apply 2)
    · simp only [φbad, hi, if_false]; exact differentiable_const 0
  · intro u i hi; simp [φbad, hi]
  · intro u v huv; funext i
    by_cases hi : i = 1
    · simp only [φbad, hi, if_true]; exact huv 2 (by decide)
    · simp [φbad, hi]

/-- `w ↦ w 1` is `SupportedOn {0,1}` (a center coordinate — ideal-membership form). -/
example : SupportedOn (fun (_ : Fin 1) (w : Fin 3 → ℝ) ↦ w 1) ({0, 1} : Finset (Fin 3)) Set.univ := by
  refine ⟨fun _ i w ↦ if i = 1 then 1 else 0, fun j i ↦ continuousOn_const, fun j u _ ↦ ?_⟩
  simp [Finset.sum_pair (show (0 : Fin 3) ≠ 1 by decide)]

/-- **The break, kernel-checked:** the center coord `1` pulled back through the render's
`stepMap = blockShear φbad ∘ blockBlowupMap {0,1} 0` is NOT divisible by the pivot coord `u 0`
(no quotient `c`) — it is the spectator value `5` at a point with `u 0 = 0`. -/
example :
    ¬ ∃ c : (Fin 3 → ℝ) → ℝ, ∀ u : Fin 3 → ℝ,
      (blockShear φbad (blockBlowupMap ({0, 1} : Finset (Fin 3)) 0 u)) 1 = u 0 * c u := by
  rintro ⟨c, hc⟩
  have h := hc ![0, 7, 5]
  simp [blockShear, φbad, blockBlowupMap] at h
