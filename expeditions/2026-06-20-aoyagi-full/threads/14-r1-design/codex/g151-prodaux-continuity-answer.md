**Strategy**  
Rewrite the continuity goal for the transported layer with `e1` and `e2` before transporting the proof. In other words, prove `Continuous layer` by normalizing the whole goal with `simpa only [e1, e2, eq_mpr_eq_cast, cast_eq] using continuous_apply ...`; after that the casted layer is just the coordinate projection `fun A => A ⟨k, hkL⟩`. Then multiply by the induction hypothesis and use `Continuous.congr` with the definitional recursive equation for `prodAux`.

```lean
theorem continuous_prodAux (H : Fin (L + 1) → ℕ) (k : ℕ) (hk : k < L + 1) :
    Continuous (fun A : Params H => prodAux H A k hk) := by
  revert hk
  induction k with
  | zero =>
      intro hk
      simpa [prodAux] using
        (continuous_const :
          Continuous (fun _ : Params H =>
            (1 : Matrix (Fin (H 0)) (Fin (H 0)) ℝ)))
  | succ k ih =>
      intro hk
      have hk' : k < L + 1 := Nat.lt_of_succ_lt hk
      have hkL : k < L := Nat.lt_of_succ_lt_succ hk
      have e1 : (⟨k, hk'⟩ : Fin (L + 1)) = (⟨k, hkL⟩ : Fin L).castSucc := by
        apply Fin.ext
        simp [Fin.castSucc]
      have e2 : (⟨k + 1, hk⟩ : Fin (L + 1)) = (⟨k, hkL⟩ : Fin L).succ := by
        apply Fin.ext
        simp [Fin.succ]

      let layer : Params H →
          Matrix (Fin (H ⟨k, hk'⟩)) (Fin (H ⟨k + 1, hk⟩)) ℝ :=
        fun A =>
          ((by
            rw [e1, e2]
            exact A ⟨k, hkL⟩) :
            Matrix (Fin (H ⟨k, hk'⟩)) (Fin (H ⟨k + 1, hk⟩)) ℝ)

      have hLayer : Continuous layer := by
        dsimp [layer]
        simpa only [e1, e2, eq_mpr_eq_cast, cast_eq] using
          (continuous_apply ⟨k, hkL⟩ :
            Continuous (fun A : Params H => A ⟨k, hkL⟩))

      have hMul : Continuous (fun A : Params H =>
          prodAux H A k hk' * layer A) :=
        (ih hk').matrix_mul hLayer

      exact hMul.congr fun A => by
        dsimp [layer]
        rfl
```

No unverified lemma names here: `continuous_apply`, `Continuous.matrix_mul`, `Continuous.congr` are in your confirmed list; `eq_mpr_eq_cast` and `cast_eq` are core/mathlib cast simplifiers present at this pin. I did not run Lean, per your grounding rule.