import DLNFibre.Core.Aoyagi.PrincipalInv
open DLNFibre.Core.Aoyagi

/- (s2) The `∀ _branch : Bool` quantifier COLLAPSES: a single StepInvChild discharges the
   branch-quantified conclusion. So Case1Preservation does NOT force two distinct children
   (1(1) vs 1(2)); one child, ignoring branch, satisfies it. -/
example {M D : ℕ} (F : Fin M → (Fin D → ℝ) → ℝ) (g : (Fin D → ℝ) → (Fin D → ℝ))
    (V : Set (Fin D → ℝ)) (h : StepInvChild F g V) : ∀ _branch : Bool, StepInvChild F g V :=
  fun _ => h

/- (soundness) `terminal_bezout` (TerminalBezout) is FALSE as stated: it concludes 0 ∈ V' ⊆ V
   but never assumes 0 ∈ V. Counterexample: V = {u | 0 < u 0} (open, 0 ∉ V). -/
example : ¬ TerminalBezout := by
  intro hTB
  have hstep : StepInv (M := 1) (D := 1) (fun _ _ => 1) id (fun _ => 1)
      (fun _ : Fin 1 => 1) (fun _ _ _ => 1) {u : Fin 1 → ℝ | 0 < u 0} := by
    refine ⟨fun i j => continuousOn_const, ?_⟩
    intro u hu i; simp
  obtain ⟨V', r, hopen, h0V', hsub, hprin⟩ :=
    hTB hstep 0 (fun _ => 1) continuousAt_const (by norm_num)
      (by intro u hu; simp)
  have : (0 : Fin 1 → ℝ) ∈ {u : Fin 1 → ℝ | 0 < u 0} := hsub h0V'
  simp at this
