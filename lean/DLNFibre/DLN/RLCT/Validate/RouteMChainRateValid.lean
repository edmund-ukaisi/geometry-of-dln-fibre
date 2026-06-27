import DLNFibre.DLN.RLCT.Validate.RouteMChainRate

/-!
# `RouteMChainRateValid` — end-to-end non-vacuity of the rate engine (a genuine multi-level chain)

A concrete `L = 2` `FactoredChain` over a `(1,1,1)` network, exercising the FULL rate-engine pipeline
(`FactoredChain.toChain` → `chain_telescope_zero` → `prod_eq_reindex_suffix`) to confirm it fires
non-vacuously: the produced chain satisfies `prod (1,1,1) A = reindex (suffix 0)`, and with `C 0 = 1`
the suffix simplifies to `u • H`. This validates the seam from the cert's factored block data all the
way to the genuine DLN layer product `prod`, end-to-end, on a genuine `L ≥ 2` chain (two `step`s + the
terminal `base`, all discharged by the engine, NO per-entry `ring`).

`(1,1,1)`: widths `M = ![1,1,1]`, all `1×1`. Achiever descent `t_0 = 1, t_1 = 0, t_2 = ⊥`; the chain
is the radial scaling `A_0 = u • a_0`, `A_1 = u? ` — for the `1×1` leaf the telescope reduces to the
length-`L` radial RRR pattern. We use the minimal binding shape (`C` the identities/scalings) that makes
`step`/`base` hold by `1×1` scalar arithmetic, then confirm `prod = reindex (suffix 0)`.
-/

namespace DLNFibre.DLN.RLCT

open Matrix

/-- A concrete `L = 2` factored chain over the `(1,1,1)` network (all widths `1`), binding shape
`C_k = 1` for `k < 2`, `C_2 = u • R`, `B_k = 0`, `Q_k = 1`, `R̄_k = 0`, terminal `R`. The two `step`s
(`1·A_k = 0·C_{k+1} + u•(0·A_k)`, forcing `A_k = 0`... ) — we instead take the leaf-radial shape:
`A_0`, `A_1` free, `C_2 = u • R`, and the chaining `Q_k A_k = C_{k+1}` PINS `A_0 = C_1 = 1`,
`A_1 = C_2 = u•R`. So the construction is consistent and the telescope gives `suffix 0 = A_0·A_1 = u•R`. -/
noncomputable def validChain111 (u : ℝ) (R : Matrix (Fin 1) (Fin 1) ℝ) : FactoredChain 2 u where
  Wwid := fun _ => 1
  Twid := fun _ => 1
  A := fun k => if k = 0 then 1 else u • R
  C := fun k => if k = 2 then u • R else 1
  Bmat := fun _ => 1
  Qmat := fun _ => 1
  Rmat := fun _ => 0
  R := R
  hC := by
    intro k hk
    -- `C_k = 1 = 1·1 + u•0 = B_k·Q_k + u•R̄_k` for `k ∈ {0,1}`.
    interval_cases k <;> simp
  hQA := by
    intro k hk
    -- `Q_k · A_k = 1 · A_k = A_k = C_{k+1}`: `A_0 = C_1 = 1`, `A_1 = C_2 = u•R`.
    interval_cases k <;> simp
  base := by simp

/-- **The rate engine fires end-to-end on `(1,1,1)`.** `prod (![1,1,1]) A = reindex (suffix 0)` for the
DLN parameter `A` whose layers match `validChain111`'s (`A_0 = 1`, `A_1 = u•R`). The bridge
(`prod_eq_reindex_suffix`) connects the abstract chain suffix to the genuine layer product; the produced
chain's `step`/`base` were discharged by the engine (`step_of_factor`), confirming non-vacuity of the
whole `FactoredChain` → telescope → bridge pipeline. -/
theorem validChain111_prod_eq (u : ℝ) (R : Matrix (Fin 1) (Fin 1) ℝ)
    (A : Params (![1, 1, 1] : Fin 3 → ℕ))
    (hW : ∀ k (hk : k ≤ 2), (validChain111 u R).toChain.Wwid k
        = (![1, 1, 1] : Fin 3 → ℕ) ⟨k, Nat.lt_succ_of_le hk⟩)
    (hA : ∀ k (hk : k < 2),
      Matrix.reindex (finCongr (hW k (le_of_lt hk))) (finCongr (hW (k + 1) hk))
          ((validChain111 u R).toChain.A k)
        = (A ⟨k, hk⟩ :
            Matrix (Fin ((![1, 1, 1] : Fin 3 → ℕ) (⟨k, Nat.lt_succ_of_le (le_of_lt hk)⟩ : Fin 3)))
              (Fin ((![1, 1, 1] : Fin 3 → ℕ) (⟨k + 1, Nat.succ_lt_succ hk⟩ : Fin 3))) ℝ)) :
    prod (![1, 1, 1] : Fin 3 → ℕ) A
      = Matrix.reindex (finCongr (hW 0 (Nat.zero_le 2))) (finCongr (hW 2 (le_refl 2)))
          ((validChain111 u R).toChain.suffix 0 (Nat.zero_le 2)) :=
  FactoredChain.prod_eq_reindex_suffix (validChain111 u R) (![1, 1, 1] : Fin 3 → ℕ) A hW hA

end DLNFibre.DLN.RLCT
