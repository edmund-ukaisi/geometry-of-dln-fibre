import DLNFibre.Core.Aoyagi.PrincipalInv
open DLNFibre.Core.Aoyagi

/- (item 1) S3 non-vacuity: the root StepInv witness now needs a VANISHING family (F i 0 = 0). -/
example {M D : ℕ} (F : Fin M → (Fin D → ℝ) → ℝ) (V : Set (Fin D → ℝ))
    (hF0 : ∀ i, F i 0 = 0) :
    StepInv F id (fun _ => 1) F (fun i j _ => if i = j then (1:ℝ) else 0) V := by
  refine ⟨fun i j => continuousOn_const, ?_, ?_⟩
  · intro i; simpa using hF0 i
  · intro u hu i
    simp only [Function.comp_apply, id_eq, one_mul]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji; rw [if_neg (fun h => hji h.symm), zero_mul]
    · intro h; exact absurd (Finset.mem_univ i) h

/- (item 5, L7 geometric kernel) A single-pivot blow-up image MISSES a neighbourhood direction:
   the point (0, ε) with ε ≠ 0 is not in the image of blowupMap 0 — so a single-pivot chart cannot
   cover any ball around 0, however large its domain. This is why a wrong-pivot atlas satisfying
   FoldProduced (which does NOT constrain the step maps σ) can still fail L7's cover. -/
example (ε : ℝ) (hε : ε ≠ 0) : (![0, ε] : Fin 2 → ℝ) ∉ Set.range (blowupMap (0 : Fin 2)) := by
  rintro ⟨w, hw⟩
  have h0 : w 0 = 0 := by have := congrFun hw 0; simpa [blowupMap] using this
  have h1 : w 0 * w 1 = ε := by have := congrFun hw 1; simpa [blowupMap] using this
  rw [h0, zero_mul] at h1
  exact hε h1.symm
