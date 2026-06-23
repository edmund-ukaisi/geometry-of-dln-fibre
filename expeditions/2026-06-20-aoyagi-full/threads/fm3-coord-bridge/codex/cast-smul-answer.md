**Ranking, v4.29**

1. **(c) HEq `prodAux_step`**: most robust. Avoids commuting smul through transport.
2. **(b) `Matrix.ext` entrywise**: possible, but noisy; no `Matrix.cast_apply` found locally.
3. **(a) simp cast/smul**: not robust as stated. I do **not** find stock `cast_smul`, `smul_cast`, or `Matrix.cast_apply` in this mathlib. Confirmed useful names: `eq_mpr_eq_cast`, `cast_heq_iff_heq`, `heq_of_eqRec_eq`, `Matrix.mul_smul`, `Matrix.smul_mul`.

Use (c). Put `prodAux_step` near `prodAux` or locally:

```lean
private theorem prodAux_step (H : Fin (L + 1) → ℕ) (A : Params H)
    (k : ℕ) (hk : k + 1 < L + 1)
    (Mstep : Matrix (Fin (H ⟨k, Nat.lt_of_succ_lt hk⟩)) (Fin (H ⟨k + 1, hk⟩)) ℝ)
    (hheq : HEq (A ⟨k, Nat.lt_of_succ_lt_succ hk⟩) Mstep) :
    prodAux H A (k + 1) hk =
      prodAux H A k (Nat.lt_of_succ_lt hk) * Mstep := by
  rw [prodAux]
  congr 1
  rw [eq_comm]
  apply eq_of_heq
  exact hheq.symm.trans (heq_of_eqRec_eq rfl rfl)
```

In the `s = k` branch, replace the stuck cast goal with:

```lean
let Mstep : Matrix (Fin (H ⟨k, hk'⟩)) (Fin (H ⟨k + 1, hk⟩)) ℝ := by
  have e1 : (⟨k, hk'⟩ : Fin (L + 1)) = (⟨k, hkL⟩ : Fin L).castSucc := by
    apply Fin.ext
    simp [Fin.castSucc]
  have e2 : (⟨k + 1, hk⟩ : Fin (L + 1)) = (⟨k, hkL⟩ : Fin L).succ := by
    apply Fin.ext
    simp [Fin.succ]
  rw [e1, e2]
  exact A ⟨k, hkL⟩

have hM : HEq (A ⟨k, hkL⟩) Mstep := by
  dsimp [Mstep]
  exact heq_of_eqRec_eq rfl rfl

have hMscaled :
    HEq ((scaleLayer H c s A) ⟨k, hkL⟩) (c • Mstep) := by
  rw [hlayer]
  cases hM
  rfl

rw [prodAux_step H (scaleLayer H c s A) k hk (c • Mstep) hMscaled,
    prodAux_step H A k hk Mstep hM,
    ihk, one_smul, Matrix.mul_smul]
```

The important idiom is: name the transported layer as `Mstep`, prove `HEq` once, instantiate the scaled successor with `c • Mstep`, then `Matrix.mul_smul` applies without seeing any casts.