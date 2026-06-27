import DLNFibre.DLN.RLCT.Validate.RouteMGenChain

/-!
# `RouteMGenChartId` — the ∀M chart identity `routeMCore M (φ u) = u²·V` (via the engine)

The general-`M` chart identity, consuming `chainOfMt` (`RouteMGenChain`). For any `M : Fin (L+1) → ℕ`,
descent path `t`, block data `B`, and the identity-boundary condition `C 0 = 1` (which the achiever block
data supplies — `Bmat 0 = 1`, `Rmat 0 = 0`, `chainQ` at `c_0 = 0` is `I`), the chart parameter
`chartParamsGen` (the chain's layers reindexed to `M`) satisfies the RATE identity `prod M (chartParams)
= u • H`, hence `dlnLoss M 0 (chartParams) = u²·V` and `routeMCore M (φ u) = u²·V` with
`φ := paramsEquivFlat M ∘ chartParams`, `V := ‖H‖²`. NO per-entry `ring` — the rate engine does the
telescoping.

This is the **∀M chart identity** (the rate factor of the achiever box-divergence atom). The
identity-boundary `C 0 = 1` is carried as an explicit hypothesis `hC0` — the same `prod = u•H` shape the
suffix bridge consumes; the per-`M` achiever block data discharges it.

* `chartParamsGen` — the chain's layers as a genuine `Params M`.
* `prod_chartParamsGen_eq` — `prod M (chartParams) = u • H` (the ∀M rate identity, given `hC0`).
* `dlnLoss_chartParamsGen` / `routeMCore_phiGen` — the ∀M loss / chart identities `= u²·V`.

Axiom-clean `[propext, Classical.choice, Quot.sound]` (pure matrix algebra; no analysis).
-/

namespace DLNFibre.DLN.RLCT

open Matrix

variable {L : ℕ}

/-! ## The chart parameter (the chain's layers, reindexed to `M`) -/

/-- **The chart parameter** `chartParamsGen : Params M` — the chain's layer `A s.val`, reindexed from the
ambient `Wext`-widths to the genuine `M`-widths (`Wext M s.val = M s.castSucc`, `Wext M (s.val+1) =
M s.succ`, both `rfl`-after-`Wext_apply`). -/
noncomputable def chartParamsGen (u : ℝ) (M t : Fin (L + 1) → ℕ) (B : GenBlk M t)
    (hle : ∀ k, k < L → Text M t (k + 1) ≤ Wext M k) : Params M := fun s =>
  Matrix.reindex
    (finCongr (show Wext M s.val = M s.castSucc by rw [Wext_apply M s.val (by omega)]; rfl))
    (finCongr (show Wext M (s.val + 1) = M s.succ by rw [Wext_apply M (s.val + 1) (by omega)]; rfl))
    ((chainOfMt u M t B hle).toChain.A s.val)

/-- The width match `hW`: `Wwid k = M ⟨k,_⟩` (`= M k`) for `k ≤ L`. -/
theorem hWgen (u : ℝ) (M t : Fin (L + 1) → ℕ) (B : GenBlk M t)
    (hle : ∀ k, k < L → Text M t (k + 1) ≤ Wext M k) :
    ∀ k (hk : k ≤ L), (chainOfMt u M t B hle).toChain.Wwid k = M ⟨k, Nat.lt_succ_of_le hk⟩ := by
  intro k hk
  show Wext M k = M ⟨k, Nat.lt_succ_of_le hk⟩
  rw [Wext_apply M k (by omega)]

/-- The layer match `hA`: the chain's layer `A k`, reindexed by the width equalities, IS
`chartParamsGen ⟨k,_⟩` — by construction (`chartParamsGen` is `reindex (A k)`; the reindexes agree
value-wise since every `finCongr`/composite is the `Fin.cast` value-preserving map). -/
theorem hAgen (u : ℝ) (M t : Fin (L + 1) → ℕ) (B : GenBlk M t)
    (hle : ∀ k, k < L → Text M t (k + 1) ≤ Wext M k) :
    ∀ k (hk : k < L),
      Matrix.reindex (finCongr (hWgen u M t B hle k (le_of_lt hk)))
          (finCongr (hWgen u M t B hle (k + 1) hk))
          ((chainOfMt u M t B hle).toChain.A k)
        = (chartParamsGen u M t B hle ⟨k, hk⟩ :
            Matrix (Fin (M (⟨k, Nat.lt_succ_of_le (le_of_lt hk)⟩ : Fin (L + 1))))
              (Fin (M (⟨k + 1, Nat.succ_lt_succ hk⟩ : Fin (L + 1)))) ℝ) := by
  intro k hk
  unfold chartParamsGen
  rw [Matrix.reindex_apply, Matrix.reindex_apply]
  ext i j
  simp only [Matrix.submatrix_apply, finCongr_symm, finCongr_apply, Fin.cast_eq_self]
  rfl

/-! ## The ∀M rate identity `prod = u • H` (given the identity-boundary `C 0 = 1`) -/

/-- **The ∀M rate identity** `prod M (chartParams) = u • H` (`H := reindex (Hmat 0)`). The suffix bridge
gives `prod = reindex (suffix 0)`; the identity-boundary `hC0 : C 0 = 1` makes `C 0 · suffix 0 = suffix 0`,
so `telescope_zero` reads `suffix 0 = u • Hmat 0`, and `u` pulls through the reindex. -/
theorem prod_chartParamsGen_eq (u : ℝ) (M t : Fin (L + 1) → ℕ) (B : GenBlk M t)
    (hle : ∀ k, k < L → Text M t (k + 1) ≤ Wext M k)
    (hC0 : (chainOfMt u M t B hle).toChain.C 0
        * (chainOfMt u M t B hle).toChain.suffix 0 (Nat.zero_le L)
      = (chainOfMt u M t B hle).toChain.suffix 0 (Nat.zero_le L)) :
    prod M (chartParamsGen u M t B hle)
      = u • Matrix.reindex (finCongr (hWgen u M t B hle 0 (Nat.zero_le L)))
          (finCongr (hWgen u M t B hle L (le_refl L)))
          ((chainOfMt u M t B hle).toChain.Hmat 0 (Nat.zero_le L)) := by
  set c := chainOfMt u M t B hle with hc
  have hbridge := FactoredChain.prod_eq_reindex_suffix c M (chartParamsGen u M t B hle)
    (hWgen u M t B hle) (hAgen u M t B hle)
  rw [hbridge]
  have hsuf : c.toChain.suffix 0 (Nat.zero_le L) = u • c.toChain.Hmat 0 (Nat.zero_le L) := by
    have ht := c.telescope_zero
    rwa [hC0] at ht
  rw [hsuf, Matrix.reindex_apply, Matrix.reindex_apply]
  exact (congrFun (congrFun (Matrix.submatrix_smul u (c.toChain.Hmat 0 (Nat.zero_le L))) _) _)

/-! ## The ∀M loss / chart identities `= u²·V` -/

/-- The telescoped quotient `Hr := reindex (Hmat 0)` (the `H` of `prod = u • H`). -/
noncomputable def HrGen (u : ℝ) (M t : Fin (L + 1) → ℕ) (B : GenBlk M t)
    (hle : ∀ k, k < L → Text M t (k + 1) ≤ Wext M k) :
    Matrix (Fin (M 0)) (Fin (M (Fin.last L))) ℝ :=
  Matrix.reindex (finCongr (hWgen u M t B hle 0 (Nat.zero_le L)))
    (finCongr (hWgen u M t B hle L (le_refl L)))
    ((chainOfMt u M t B hle).toChain.Hmat 0 (Nat.zero_le L))

/-- The unit factor `V = ‖Hr‖²` (the `u`-free factor of `F = u²·V`). -/
noncomputable def VvalGen (u : ℝ) (M t : Fin (L + 1) → ℕ) (B : GenBlk M t)
    (hle : ∀ k, k < L → Text M t (k + 1) ≤ Wext M k) : ℝ :=
  ∑ i, ∑ j, (HrGen u M t B hle i j) ^ 2

/-- **The ∀M loss factorization** `dlnLoss M 0 (chartParams) = u²·V` (given `hC0`). Each product entry is
`u·(Hr entry)` (the rate identity), so the squared Frobenius norm is `u²·V`. NO per-entry `ring`. -/
theorem dlnLoss_chartParamsGen (u : ℝ) (M t : Fin (L + 1) → ℕ) (B : GenBlk M t)
    (hle : ∀ k, k < L → Text M t (k + 1) ≤ Wext M k)
    (hC0 : (chainOfMt u M t B hle).toChain.C 0
        * (chainOfMt u M t B hle).toChain.suffix 0 (Nat.zero_le L)
      = (chainOfMt u M t B hle).toChain.suffix 0 (Nat.zero_le L)) :
    dlnLoss M 0 (chartParamsGen u M t B hle)
      = u ^ 2 * VvalGen u M t B hle := by
  unfold dlnLoss
  simp only [Matrix.sub_apply, Matrix.zero_apply, sub_zero]
  rw [show prod M (chartParamsGen u M t B hle) = u • HrGen u M t B hle from
        prod_chartParamsGen_eq u M t B hle hC0,
      VvalGen, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Matrix.smul_apply, smul_eq_mul]
  ring

/-- **The genuine achiever flat chart** `phiGen := paramsEquivFlat M ∘ chartParams`. -/
noncomputable def phiGen (u : ℝ) (M t : Fin (L + 1) → ℕ) (B : GenBlk M t)
    (hle : ∀ k, k < L → Text M t (k + 1) ≤ Wext M k) : Fin (routeMAmbient M) → ℝ :=
  paramsEquivFlat M (chartParamsGen u M t B hle)

/-- **The ∀M chart identity** `routeMCore M (φ u) = u²·V` (given `hC0`). The soundness-critical
`F ∘ φ = u²·V` for arbitrary `M`, established THROUGH the rate engine. -/
theorem routeMCore_phiGen (u : ℝ) (M t : Fin (L + 1) → ℕ) (B : GenBlk M t)
    (hle : ∀ k, k < L → Text M t (k + 1) ≤ Wext M k)
    (hC0 : (chainOfMt u M t B hle).toChain.C 0
        * (chainOfMt u M t B hle).toChain.suffix 0 (Nat.zero_le L)
      = (chainOfMt u M t B hle).toChain.suffix 0 (Nat.zero_le L)) :
    routeMCore M (phiGen u M t B hle) = u ^ 2 * VvalGen u M t B hle := by
  rw [routeMCore, phiGen, MeasurableEquiv.symm_apply_apply,
    dlnLoss_chartParamsGen u M t B hle hC0]

end DLNFibre.DLN.RLCT
