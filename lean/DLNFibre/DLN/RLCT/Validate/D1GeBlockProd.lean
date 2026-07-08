import DLNFibre.DLN.RLCT.Validate.DeepestFinBridgeGen
import DLNFibre.DLN.RLCT.Validate.D1L2PhiExpl

/-!
# `DLNFibre.DLN.RLCT.Validate.D1GeBlockProd` — piece (ii): block-layer-product ↔ DLN `prod` bridge

The general-`L`, general-pivot analogue of `blockFlatEquiv_L2_mul` (`D1L2PhiExpl`): the ordered
of the block-reindexed layers equals the pivot-reindexed multiplication map `prod H v`. It is the
`sumSplit (ι ·)` (common-pivot) analogue of the achiever-side `reindex_prodAux_eq_partProd`
(`DeepestFinBridgeGen`, which uses the first-`r` threshold split), and reuses that file's cast-free
width bookkeeping (`deepestChainWidth`, `deepestChainLayer`) and shared-middle cancel
(`reindex_mul_split_gen`) verbatim — only the per-vertex split changes.

For an arbitrary injective per-vertex pivot family `ι : (s : Fin (L+1)) → Fin r → Fin (H s)` (as
supplied by `exists_common_pivot_gen`, piece (i)), the DLN product reindexed by `sumSplit (ι ·)`
becomes the cast-free `partProd` fold of the block chain `genChain`:

* `genPivotN` / `genPivotN_inj` — the `ℕ`-extended pivot family (the actual `ι` on `s ≤ L`, the
  first-`r` injection `Fin.castLE` past the last layer — never read by `partProd … L`, present only
  for totality), and its injectivity.
* `genChainSplit` / `genChainCol` — the per-index split `Fin (dcw s) ≃ Fin r ⊕ Fin (dcw s − r)`
  (`sumSplit (ι ·)` symm) and the `prodAux`-column split.
* `genChain` — the block chain: layer `s` is `deepestChainLayer` (the DLN layer recast to running
  widths, pivot-independent) reindexed by `genChainSplit` at both vertices.
* `reindex_prodAux_eq_genPartProd` — the **core fold bridge** (`k ≤ L`):
  `reindex (genChainCol 0) (genChainCol k) (prodAux H v k) = partProd (genChain …) k`. Induction on
  `k`, peeling the last layer (`prodAux_succ` + `reindex_mul_split_gen`); the succ-step layer
  is the `finCongr`-composition collapse. The sole cast-grind, isolated once.
* `reindex_prod_eq_genPartProd` — the `k = L` full-product specialisation on `prod H v`.

Pure `Matrix`/`Equiv` algebra over `ℝ`; no analysis. Takes only `hι` (injectivity); invertibility
of the pivot minors is a separate downstream fact (piece (i)).
-/

open Matrix
namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-! ## The `ℕ`-extended common-pivot family and its block chain -/

/-- The common-pivot family extended to all of `ℕ`: the actual `ι ⟨s,·⟩` recast to the running
width `deepestChainWidth H s` for `s ≤ L`, the first-`r` `Fin.castLE` past the last layer. -/
noncomputable def genPivotN (H : Fin (L + 1) → ℕ) (r : ℕ) (hr : ∀ s : Fin (L + 1), r ≤ H s)
    (ι : (s : Fin (L + 1)) → Fin r → Fin (H s)) (s : ℕ) : Fin r → Fin (deepestChainWidth H s) :=
  if hs : s < L + 1 then
    (finCongr (H_eq_deepestChainWidth H s hs)) ∘ (ι ⟨s, hs⟩)
  else
    Fin.castLE (r_le_deepestChainWidth H r hr s)

/-- `genPivotN` is injective at every index (`hι` on the pivot branch, `Fin.castLE` on the tail). -/
theorem genPivotN_inj (H : Fin (L + 1) → ℕ) (r : ℕ) (hr : ∀ s : Fin (L + 1), r ≤ H s)
    (ι : (s : Fin (L + 1)) → Fin r → Fin (H s)) (hι : ∀ s, Function.Injective (ι s)) (s : ℕ) :
    Function.Injective (genPivotN H r hr ι s) := by
  unfold genPivotN
  split
  · exact (finCongr _).injective.comp (hι _)
  · exact Fin.castLE_injective _

/-- The per-index block split `Fin (dcw s) ≃ Fin r ⊕ Fin (dcw s − r)` placing the pivot indices
`genPivotN … s` in the left summand (`sumSplit`-symm). -/
noncomputable def genChainSplit (H : Fin (L + 1) → ℕ) (r : ℕ) (hr : ∀ s : Fin (L + 1), r ≤ H s)
    (ι : (s : Fin (L + 1)) → Fin r → Fin (H s)) (hι : ∀ s, Function.Injective (ι s)) (s : ℕ) :
    Fin (deepestChainWidth H s) ≃ Fin r ⊕ Fin (deepestChainWidth H s - r) :=
  (sumSplit (genPivotN H r hr ι s) (genPivotN_inj H r hr ι hι s)).symm

/-- The column split of `prodAux H v k` at `k ≤ L`: recast `H ⟨k,·⟩` to `deepestChainWidth H k`,
then split. -/
noncomputable def genChainCol (H : Fin (L + 1) → ℕ) (r : ℕ) (hr : ∀ s : Fin (L + 1), r ≤ H s)
    (ι : (s : Fin (L + 1)) → Fin r → Fin (H s)) (hι : ∀ s, Function.Injective (ι s))
    (k : ℕ) (hk : k < L + 1) : Fin (H ⟨k, hk⟩) ≃ Fin r ⊕ Fin (deepestChainWidth H k - r) :=
  (finCongr (H_eq_deepestChainWidth H k hk)).trans (genChainSplit H r hr ι hι k)

/-- **The block chain of `v` at the common pivot `ι`**: layer `s` is the DLN layer recast to the
running widths (`deepestChainLayer`, pivot-independent) reindexed into `r ⊕ (dcw · − r)` blocks by
`genChainSplit` at both vertices. Feeds `partProd` / `blockSchur`. -/
noncomputable def genChain (H : Fin (L + 1) → ℕ) (r : ℕ) (hr : ∀ s : Fin (L + 1), r ≤ H s)
    (ι : (s : Fin (L + 1)) → Fin r → Fin (H s)) (hι : ∀ s, Function.Injective (ι s))
    (v : Params H) (s : ℕ) :
    Matrix (Fin r ⊕ Fin (deepestChainWidth H s - r))
      (Fin r ⊕ Fin (deepestChainWidth H (s + 1) - r)) ℝ :=
  Matrix.reindex (genChainSplit H r hr ι hι s) (genChainSplit H r hr ι hι (s + 1))
    (deepestChainLayer H r v s)

/-! ## The fold bridge -/

/-- **The core fold bridge** (all prefix lengths `k ≤ L`). For any injective pivot family `ι` and
any `v : Params H`, the reindexed product `reindex (genChainCol 0) (genChainCol k) (prodAux H v k)`
equals the abstract `partProd (genChain …) k`. Induction on `k`: base is `reindex e e 1 = 1`; the
succ-step peels the last layer (`prodAux_succ` + `reindex_mul_split_gen`) and matches the layer via
`finCongr`-composition collapse. The `sumSplit (ι ·)` analogue of `reindex_prodAux_eq_partProd`. -/
theorem reindex_prodAux_eq_genPartProd (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (ι : (s : Fin (L + 1)) → Fin r → Fin (H s))
    (hι : ∀ s, Function.Injective (ι s)) (v : Params H) :
    ∀ (k : ℕ) (hk : k < L + 1),
      Matrix.reindex (sumSplit (ι 0) (hι 0)).symm (genChainCol H r hr ι hι k hk)
          (prodAux H v k hk)
        = partProd (genChain H r hr ι hι v) k := by
  intro k
  induction k with
  | zero =>
      intro hk
      have hcol0 : genChainCol H r hr ι hι 0 hk = (sumSplit (ι 0) (hι 0)).symm := rfl
      rw [hcol0, Matrix.reindex_apply]
      exact Matrix.submatrix_one_equiv (sumSplit (ι 0) (hι 0))
  | succ k ih =>
      intro hk
      have hk' : k < L + 1 := Nat.lt_of_succ_lt hk
      have hkL : k < L := Nat.lt_of_succ_lt_succ hk
      have e1 : H (⟨k, hk'⟩ : Fin (L + 1)) = H ((⟨k, hkL⟩ : Fin L).castSucc) := rfl
      have e2 : H (⟨k + 1, hk⟩ : Fin (L + 1)) = H ((⟨k, hkL⟩ : Fin L).succ) := rfl
      rw [prodAux_succ H v k hk e1 e2,
        reindex_mul_split_gen (sumSplit (ι 0) (hι 0)).symm
          (genChainCol H r hr ι hι k hk') (genChainCol H r hr ι hι (k + 1) hk), ih hk']
      change _ = partProd (genChain H r hr ι hι v) k * genChain H r hr ι hι v k
      congr 1
      simp only [genChain, deepestChainLayer, dif_pos hkL, Matrix.reindex_apply,
        Matrix.submatrix_submatrix]
      congr 1

/-- **The full-product bridge** (`k = L`). `reindex (genChainCol 0) (genChainCol L) (prod H v)
= partProd (genChain …) L`. The `k = L` case of `reindex_prodAux_eq_genPartProd`, unfolding
`prod = prodAux … L`. This is the general-`L`, general-pivot lift of `blockFlatEquiv_L2_mul`. -/
theorem reindex_prod_eq_genPartProd (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (ι : (s : Fin (L + 1)) → Fin r → Fin (H s))
    (hι : ∀ s, Function.Injective (ι s)) (v : Params H) :
    Matrix.reindex (sumSplit (ι 0) (hι 0)).symm
        (genChainCol H r hr ι hι L (Nat.lt_succ_self L)) (prod H v)
      = partProd (genChain H r hr ι hι v) L :=
  reindex_prodAux_eq_genPartProd H r hr ι hι v L (Nat.lt_succ_self L)

/-- **The block corner is the prefix pivot minor.** The `(1,1)` block of the partial-product chain
exactly the prefix-product minor `exists_common_pivot_gen` (piece (i)) makes invertible:
`(partProd (genChain …) k).toBlocks₁₁ = (prodAux H v k).submatrix (ι 0) (ι ⟨k, hk⟩)`. This is glue
turning piece (i)'s `det ≠ 0` into `IsUnit (partProd …).toBlocks₁₁` (the `hPart` the Schur telescope
reads). Via `reindex_prodAux_eq_genPartProd`, then `sumSplit_inl` on both index families (the column
`finCongr` cancels its `genPivotN` recast). -/
theorem genPartProd_toBlocks₁₁ (H : Fin (L + 1) → ℕ) (r : ℕ) (hr : ∀ s : Fin (L + 1), r ≤ H s)
    (ι : (s : Fin (L + 1)) → Fin r → Fin (H s)) (hι : ∀ s, Function.Injective (ι s)) (v : Params H)
    (k : ℕ) (hk : k < L + 1) :
    (partProd (genChain H r hr ι hι v) k).toBlocks₁₁
      = (prodAux H v k hk).submatrix (ι 0) (ι ⟨k, hk⟩) := by
  rw [← reindex_prodAux_eq_genPartProd H r hr ι hι v k hk]
  funext a b
  simp only [Matrix.toBlocks₁₁, Matrix.of_apply, Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.symm_symm]
  congr 1
  -- column: `(genChainCol k).symm (inl b) = ι ⟨k,hk⟩ b`, the `genPivotN` recast cancels `finCongr`.
  rw [genChainCol, genChainSplit]
  simp only [Equiv.symm_trans_apply, Equiv.symm_symm, sumSplit_inl]
  rw [genPivotN, dif_pos hk]
  simp only [Function.comp_apply, finCongr_symm, finCongr_apply, Fin.cast_cast, Fin.cast_eq_self]

end DLNFibre.DLN.RLCT
