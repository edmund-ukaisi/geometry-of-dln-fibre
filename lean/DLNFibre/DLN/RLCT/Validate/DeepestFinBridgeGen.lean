import DLNFibre.DLN.RLCT.Validate.DeepestPsiSplitGenLeftCol
import DLNFibre.DLN.RLCT.Validate.DeepestSplitReindex

/-!
# `DLNFibre.DLN.RLCT.Validate.DeepestFinBridgeGen` — the `Fin`-side product bridge (#120 `hstep2`, Item 1)

The general-`L` bridge from the DLN framed layer product `prod H A` (an `L`-factor `prodAux` fold over the
`Fin (H ·)` widths, cast-laden through the `finCongr` succ-steps) to the **network-free abstract chain**
`partProd (deepestChain H r hr A)` of `DeepestPsiSplitGenMoved`/`DeepestSchurRecursion` (a cast-free `ℕ`-indexed
fold of `r ⊕ (·−r)`-blocked matrices). This is the "identify each framed layer with the abstract
`r ⊕ (H s − r)` block form" step of the cert §6 build order: once the DLN product reindexes to the
abstract `partProd`, the banked reg-preservation `regBlocks_movedC` (Invariant A, both halves) transfers
to the DLN framed product — the algebraic heart of the concrete `hsub3reg`.

## What is banked here (pure `Matrix` algebra, sorry-free)

* `reindex_mul_split_gen` — the shared-middle cancel with **arbitrary** target block types (the
  `DeepestBlockDecomp.reindex_mul_split` freed of its `Fin r ⊕ Fin (· − r)` middle shape, so the abstract
  chain's `Fin r ⊕ Fin (deepestChainWidth · − r)` middle applies).
* `reindex_prodAux_eq_partProd` — the **core fold bridge**: for any `A : Params H` and every prefix length
  `k ≤ L`, `reindex (rThr 0) (deepestChainCol k) (prodAux H A k) = partProd (deepestChain H r hr A) k`. Induction on `k`,
  peeling the last layer with `prodAux_succ` + `reindex_mul_split_gen`; the succ-step layer-match is the
  `finCongr`-composition collapse. This is the sole cast-grind of the bridge, isolated once.
* `reindex_prod_eq_partProd` — the `k = L` specialization on the full product `prod H A`.
* `reindexECol_regBlocks_eq_of_chain_movedC` — the **conditional transport**: given the abstract move
  identity `deepestChain … Aψ = movedC (deepestChain … Aq) (Z0edit0 …)` and the unit hypotheses on the base chain,
  the three reg-residual blocks (`{11,12,21}`) of the reindexed DLN products agree. Combines the bridge
  with the banked `regBlocks_movedC`. This isolates the remaining geometric content of `hsub3reg` to
  exactly the move identity (the concrete `psiSplitRawGen` design, Item 2) and the last-column
  pivot-split reconciliation (`deepestChainCol L` vs `pivotThresholdSplit … J`, discharged at `J = frontEmbed`).

## Status
Pure `Matrix`/`Ring`/`Equiv` algebra over `ℝ`; no `deepestSplit` analysis. The `IsUnit` hypotheses on the
base chain's pivots / partial pivots / pivot-mix, and the abstract move identity, are carried as explicit
hypotheses (they hold near the deepest point, where every pivot is `I`). Axiom footprint
`[propext, Classical.choice, Quot.sound]`.
-/

open Matrix
namespace DLNFibre.DLN.RLCT

set_option linter.unusedSectionVars false

variable {L : ℕ}

/-! ## The abstract chain of a DLN parameter tuple (`deepestChain`) -/

/-- The width family extended to all of `ℕ`, defeq to `H` at index `0`, via a `min`-clamp. -/
noncomputable def deepestChainWidth (H : Fin (L + 1) → ℕ) (s : ℕ) : ℕ :=
  H ⟨min s L, Nat.lt_succ_of_le (min_le_right s L)⟩

/-- `deepestChainWidth` at a layer's `castSucc` index (`s < L`) is the running input width. -/
theorem deepestChainWidth_castSucc (H : Fin (L + 1) → ℕ) (s : ℕ) (hs : s < L) :
    H (⟨s, hs⟩ : Fin L).castSucc = deepestChainWidth H s :=
  congrArg H (Fin.ext (by simp only [Fin.val_castSucc]; omega))

/-- `deepestChainWidth` at a layer's `succ` index (`s < L`) is the running output width. -/
theorem deepestChainWidth_succ (H : Fin (L + 1) → ℕ) (s : ℕ) (hs : s < L) :
    H (⟨s, hs⟩ : Fin L).succ = deepestChainWidth H (s + 1) :=
  congrArg H (Fin.ext (by simp only [Fin.val_succ]; omega))

/-- `deepestChainWidth` at an index `k ≤ L` is `H ⟨k, ·⟩` (the clamp is vacuous). -/
theorem H_eq_deepestChainWidth (H : Fin (L + 1) → ℕ) (k : ℕ) (hk : k < L + 1) :
    H ⟨k, hk⟩ = deepestChainWidth H k :=
  congrArg H (Fin.ext (by simp only []; omega))

/-- `r ≤ deepestChainWidth H s` for the reduced-rank splits (from the DLN rank bound `hr`). -/
theorem r_le_deepestChainWidth (H : Fin (L + 1) → ℕ) (r : ℕ) (hr : ∀ s : Fin (L + 1), r ≤ H s) (s : ℕ) :
    r ≤ deepestChainWidth H s := hr _

/-- The per-index `r ⊕ (· − r)` threshold split at the extended width `deepestChainWidth H s`. -/
noncomputable def deepestChainSplit (H : Fin (L + 1) → ℕ) (r : ℕ) (hr : ∀ s : Fin (L + 1), r ≤ H s) (s : ℕ) :
    Fin (deepestChainWidth H s) ≃ Fin r ⊕ Fin (deepestChainWidth H s - r) :=
  rThresholdSplit r (deepestChainWidth H s) (r_le_deepestChainWidth H r hr s)

/-- The column split of `prodAux H A k` at index `k ≤ L`: cast `H ⟨k,·⟩` to `deepestChainWidth H k`, then split. -/
noncomputable def deepestChainCol (H : Fin (L + 1) → ℕ) (r : ℕ) (hr : ∀ s : Fin (L + 1), r ≤ H s)
    (k : ℕ) (hk : k < L + 1) : Fin (H ⟨k, hk⟩) ≃ Fin r ⊕ Fin (deepestChainWidth H k - r) :=
  (finCongr (H_eq_deepestChainWidth H k hk)).trans (deepestChainSplit H r hr k)

/-- The `s`-th layer of `A`, recast to the `deepestChainWidth` running widths (junk `0` beyond the last layer). -/
noncomputable def deepestChainLayer (H : Fin (L + 1) → ℕ) (A : Params H) (s : ℕ) :
    Matrix (Fin (deepestChainWidth H s)) (Fin (deepestChainWidth H (s + 1))) ℝ :=
  if hs : s < L then
    Matrix.reindex (finCongr (deepestChainWidth_castSucc H s hs)) (finCongr (deepestChainWidth_succ H s hs)) (A ⟨s, hs⟩)
  else 0

/-- **The abstract chain of `A`**: layer `s` is the DLN layer reindexed into `r ⊕ (deepestChainWidth · − r)` block
shape. Feeds the `DeepestPsiSplitGenMoved` / `DeepestSchurRecursion` `partProd`/`movedC` framework. -/
noncomputable def deepestChain (H : Fin (L + 1) → ℕ) (r : ℕ) (hr : ∀ s : Fin (L + 1), r ≤ H s)
    (A : Params H) (s : ℕ) :
    Matrix (Fin r ⊕ Fin (deepestChainWidth H s - r)) (Fin r ⊕ Fin (deepestChainWidth H (s + 1) - r)) ℝ :=
  Matrix.reindex (deepestChainSplit H r hr s) (deepestChainSplit H r hr (s + 1)) (deepestChainLayer H A s)

/-! ## The general shared-middle split and the fold bridge -/

/-- **Shared-middle reindex split, arbitrary target types.** `DeepestBlockDecomp.reindex_mul_split`
freed of the `Fin r ⊕ Fin (· − r)` middle shape (needs only `[Fintype μ]` for the contracted product). -/
theorem reindex_mul_split_gen {a b c : ℕ} {ρ μ γ : Type*} [Fintype μ]
    (eR : Fin a ≃ ρ) (eMid : Fin c ≃ μ) (eC : Fin b ≃ γ)
    (G0 : Matrix (Fin a) (Fin c) ℝ) (G1 : Matrix (Fin c) (Fin b) ℝ) :
    Matrix.reindex eR eC (G0 * G1)
      = Matrix.reindex eR eMid G0 * Matrix.reindex eMid eC G1 := by
  simp only [Matrix.reindex_apply]
  rw [Matrix.submatrix_mul_equiv G0 G1 eR.symm eMid.symm eC.symm]

/-- **The core fold bridge** (all prefix lengths). For any `A : Params H` and `k ≤ L`, the reindexed
running product `reindex (rThr 0) (deepestChainCol k) (prodAux H A k)` equals the abstract `partProd (deepestChain …) k`.
Induction on `k`: base is `reindex e e 1 = 1`; the succ-step peels the last layer (`prodAux_succ` +
`reindex_mul_split_gen`) and matches the layer via the `finCongr`-composition collapse. -/
theorem reindex_prodAux_eq_partProd (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (A : Params H) :
    ∀ (k : ℕ) (hk : k < L + 1),
      Matrix.reindex (rThresholdSplit r (H 0) (hr 0)) (deepestChainCol H r hr k hk) (prodAux H A k hk)
        = partProd (deepestChain H r hr A) k := by
  intro k
  induction k with
  | zero =>
      intro hk
      have hrfl : deepestChainCol H r hr 0 hk = rThresholdSplit r (H 0) (hr 0) := rfl
      rw [hrfl, Matrix.reindex_apply]
      exact Matrix.submatrix_one_equiv (rThresholdSplit r (H 0) (hr 0)).symm
  | succ k ih =>
      intro hk
      have hk' : k < L + 1 := Nat.lt_of_succ_lt hk
      have hkL : k < L := Nat.lt_of_succ_lt_succ hk
      have e1 : H (⟨k, hk'⟩ : Fin (L + 1)) = H ((⟨k, hkL⟩ : Fin L).castSucc) := rfl
      have e2 : H (⟨k + 1, hk⟩ : Fin (L + 1)) = H ((⟨k, hkL⟩ : Fin L).succ) := rfl
      rw [prodAux_succ H A k hk e1 e2,
        reindex_mul_split_gen (rThresholdSplit r (H 0) (hr 0)) (deepestChainCol H r hr k hk')
          (deepestChainCol H r hr (k + 1) hk), ih hk']
      change _ = partProd (deepestChain H r hr A) k * deepestChain H r hr A k
      congr 1
      rw [deepestChain, deepestChainLayer, dif_pos hkL]
      simp only [Matrix.reindex_apply, Matrix.submatrix_submatrix]
      congr 1

/-- **The full-product bridge** (`k = L`). `reindex (rThr 0) (deepestChainCol L) (prod H A) = partProd (deepestChain …) L`.
The `k = L` case of `reindex_prodAux_eq_partProd`, unfolding `prod = prodAux … L`. -/
theorem reindex_prod_eq_partProd (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (A : Params H) :
    Matrix.reindex (rThresholdSplit r (H 0) (hr 0)) (deepestChainCol H r hr L (Nat.lt_succ_self L))
        (prod H A)
      = partProd (deepestChain H r hr A) L :=
  reindex_prodAux_eq_partProd H r hr A L (Nat.lt_succ_self L)

/-! ## The conditional block-transport (bridge + banked `regBlocks_movedC`) -/

/-- **Transport of Invariant A to the DLN products** (conditional on the abstract move identity). Let
`Aq Aψ : Params H`. If the abstract chain of `Aψ` is the joint move of the abstract chain of `Aq`
(`deepestChain … Aψ = movedC (deepestChain … Aq) (Z0edit0 (deepestChain … Aq) L)` — the concrete `psiSplitRawGen`
design), and the base chain satisfies the pivot/partial-pivot/pivot-mix unit hypotheses, then the three
reg-residual blocks (`{11,12,21}`) of the reindexed DLN products agree. The banked `regBlocks_movedC`
supplies the block-equalities on the abstract side; `reindex_prod_eq_partProd` transports them to the
`reindex (rThr 0) (deepestChainCol L)` form the DLN reg-energy reads. -/
theorem reindexECol_regBlocks_eq_of_chain_movedC (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (Aq Aψ : Params H)
    (hmove : deepestChain H r hr Aψ = movedC (deepestChain H r hr Aq) (Z0edit0 (deepestChain H r hr Aq) L))
    (hP : ∀ k, IsUnit (partProd (deepestChain H r hr Aq) k).toBlocks₁₁)
    (hA : ∀ k, IsUnit (deepestChain H r hr Aq k).toBlocks₁₁)
    (hN : ∀ k, IsUnit (nMix (deepestChain H r hr Aq) k)) :
    (Matrix.reindex (rThresholdSplit r (H 0) (hr 0)) (deepestChainCol H r hr L (Nat.lt_succ_self L))
        (prod H Aψ)).toBlocks₁₁
      = (Matrix.reindex (rThresholdSplit r (H 0) (hr 0)) (deepestChainCol H r hr L (Nat.lt_succ_self L))
          (prod H Aq)).toBlocks₁₁
    ∧ (Matrix.reindex (rThresholdSplit r (H 0) (hr 0)) (deepestChainCol H r hr L (Nat.lt_succ_self L))
        (prod H Aψ)).toBlocks₁₂
      = (Matrix.reindex (rThresholdSplit r (H 0) (hr 0)) (deepestChainCol H r hr L (Nat.lt_succ_self L))
          (prod H Aq)).toBlocks₁₂
    ∧ (Matrix.reindex (rThresholdSplit r (H 0) (hr 0)) (deepestChainCol H r hr L (Nat.lt_succ_self L))
        (prod H Aψ)).toBlocks₂₁
      = (Matrix.reindex (rThresholdSplit r (H 0) (hr 0)) (deepestChainCol H r hr L (Nat.lt_succ_self L))
          (prod H Aq)).toBlocks₂₁ := by
  obtain ⟨h11, h12, h21⟩ := regBlocks_movedC (deepestChain H r hr Aq) L hP hA hN hL
  rw [reindex_prod_eq_partProd H r hr Aψ, reindex_prod_eq_partProd H r hr Aq, hmove]
  exact ⟨h11, h12, h21⟩

end DLNFibre.DLN.RLCT
