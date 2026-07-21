import DLNFibre.Core.Aoyagi.PrincipalInv
import DLNFibre.DLN.Aoyagi.MonumentAtlas
open DLNFibre.Core.Aoyagi
open scoped Topology

/- (a) FIX 1 CONFIRMED: the old counterexample V={u|0<u 0} is now BLOCKED — the new `0 ∈ V`
   hypothesis is exactly the unprovable obligation (0 0 = 0, not > 0). We leave that lone goal
   to show the rejection reason is the region hypothesis, nothing else. -/
example : ¬ TerminalBezout := by
  intro hTB
  have hstep : StepInv (M := 1) (D := 1) (fun _ _ => 1) id (fun _ => 1)
      (fun _ : Fin 1 => 1) (fun _ _ _ => 1) {u : Fin 1 → ℝ | 0 < u 0} :=
    ⟨fun i j => continuousOn_const, by intro u hu i; simp⟩
  -- Supplying IsOpen V is fine; the NEW `0 ∈ V` obligation is `(0:Fin 1→ℝ) ∈ {u|0<u 0}` = `0 < 0`.
  obtain ⟨V', r, hopen, h0V', hsub, hprin⟩ :=
    hTB (isOpen_lt continuous_const (continuous_apply 0))
        (show (0 : Fin 1 → ℝ) ∈ {u : Fin 1 → ℝ | 0 < u 0} by
          simp only [Set.mem_setOf_eq, Pi.zero_apply]; sorry)  -- ← UNPROVABLE: 0 < 0
        hstep 0 (fun _ => 1) continuousOn_const (by norm_num) (by intro u hu; simp)
  exact absurd (hsub h0V') (by simp)

/- (c) FIX 3 CONFIRMED: the two branch b'-laws are jointly UNSATISFIABLE by one witness, so the
   `fun _ => h` collapse is DEAD — the ∀branch existential genuinely needs two distinct children. -/
example : ¬ ∃ b' : (Fin 1 → ℝ) → ℝ,
    (∀ u, b' u = (u 0) ^ (if true then 0 else 1) * (fun _ : Fin 1 → ℝ => (1:ℝ)) u) ∧
    (∀ u, b' u = (u 0) ^ (if false then 0 else 1) * (fun _ : Fin 1 → ℝ => (1:ℝ)) u) := by
  rintro ⟨b', ht, hf⟩
  have e1 : b' (fun _ => 2) = 1 := by have := ht (fun _ => 2); simpa using this
  have e2 : b' (fun _ => 2) = 2 := by have := hf (fun _ => 2); simpa using this
  rw [e1] at e2; norm_num at e2
