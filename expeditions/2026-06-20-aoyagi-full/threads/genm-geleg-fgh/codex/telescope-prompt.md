<task>
Lean 4 + Mathlib (v4.29). I am proving a "reduced-factor telescope" lemma for a general-L deep-linear-network
Schur-chart residual. I need the CLEANEST proof route + the slickest Lean idiom for one sub-lemma (a
block-diagonal Equiv construction). Give me a concrete plan I can implement; illustrative Lean is welcome but
I will build it locally.

## The exact definitions (all already in the codebase, verbatim)

`Matrix.reindex e₁ e₂ M = M.submatrix e₁.symm e₂.symm` (standard Mathlib). `M.toBlocks₂₂ a b = M (Sum.inr a) (Sum.inr b)`.

```
-- sumSplit σ hσ : (Fin r ⊕ Fin (n - r)) ≃ Fin n, places the injection σ's image in the left summand.
noncomputable def sumSplit {r n : ℕ} (σ : Fin r → Fin n) (hσ : Function.Injective σ) :
    Fin r ⊕ Fin (n - r) ≃ Fin n :=
  (Equiv.sumCongr (Equiv.ofInjective σ hσ)
      (Fintype.equivOfCardEq ...)).trans (Equiv.Set.sumCompl (Set.range σ))
-- Only lemma available: sumSplit_inl : sumSplit σ hσ (Sum.inl a) = σ a.  (No sumSplit_inr / range lemma.)

-- deepestChainWidth H s : ℕ,  with H_eq_deepestChainWidth : H ⟨k, hk⟩ = deepestChainWidth H k (k < L+1),
-- deepestChainWidth_castSucc : H (⟨s,hs⟩:Fin L).castSucc = deepestChainWidth H s  (s < L),
-- deepestChainWidth_succ    : H (⟨s,hs⟩:Fin L).succ     = deepestChainWidth H (s+1) (s < L).

-- genPivotN H r hr ι s : Fin r → Fin (deepestChainWidth H s) := (for s < L+1)
--   (finCongr (H_eq_deepestChainWidth H s hs)) ∘ (ι ⟨s, hs⟩)         [ι : (v:Fin(L+1)) → Fin r → Fin (H v), injective]
-- genChainSplit H r hr ι hι s : Fin (deepestChainWidth H s) ≃ Fin r ⊕ Fin (deepestChainWidth H s - r) :=
--   (sumSplit (genPivotN H r hr ι s) (genPivotN_inj ...)).symm

-- rowEq (s : Fin L) : (Fin r ⊕ Fin (H s.castSucc - r)) ≃ (Fin r ⊕ Fin (deepestChainWidth H s.val - r)) :=
--   (sumSplit (ι s.castSucc) (hι s.castSucc)).trans
--     ((finCongr (deepestChainWidth_castSucc H s.val s.isLt)).trans (genChainSplit H r hr ι hι s.val))
-- colEq (s : Fin L) : (Fin r ⊕ Fin (H s.succ - r)) ≃ (Fin r ⊕ Fin (deepestChainWidth H (s.val+1) - r)) :=
--   (sumSplit (ι s.succ) (hι s.succ)).trans
--     ((finCongr (deepestChainWidth_succ H s.val s.isLt)).trans (genChainSplit H r hr ι hι (s.val+1)))

-- blockToChainGen H r hr ι hι (P : BlockParamsGen H r) (s : ℕ) :
--     Matrix (Fin r ⊕ Fin (deepestChainWidth H s - r)) (Fin r ⊕ Fin (deepestChainWidth H (s+1) - r)) ℝ :=
--   if h : s < L then Matrix.reindex (rowEq ⟨s,h⟩) (colEq ⟨s,h⟩) (P ⟨s,h⟩) else 0
-- (BlockParamsGen H r := ∀ s : Fin L, Matrix (Fin r ⊕ Fin (H s.castSucc - r)) (Fin r ⊕ Fin (H s.succ - r)) ℝ)

-- blockDiagProd Q : (k:ℕ) → Matrix (Fin (n 0)) (Fin (n k)) ℝ  -- n s := deepestChainWidth H s - r
--   | 0 => 1  | k+1 => blockDiagProd Q k * (Q k).toBlocks₂₂
-- blockDiagProd_congr : (∀ t < k, Q t = Q' t) → blockDiagProd Q k = blockDiagProd Q' k  [available]

-- prod (H') (A : Params H') : Matrix (Fin (H' 0)) (Fin (H' (Fin.last L))) ℝ := prodAux H' A L (lt_succ_self L)
-- prodAux H' A : (k:ℕ) → (hk : k < L+1) → Matrix (Fin (H' 0)) (Fin (H' ⟨k,hk⟩)) ℝ
--   | 0,_ => 1  | k+1, hk => prodAux H' A k _ * (cast of A ⟨k, hkL⟩)   -- Params H' = ∀ s:Fin L, Matrix (Fin(H' s.castSucc))(Fin(H' s.succ))
```

## The lemma I want (the "telescope")

For `B : BlockParamsGen H r`, with `H' := fun s => H s - r`:
```
blockDiagProd (blockToChainGen H r hr ι hι B) L
    = Matrix.reindex e0 eL (prod H' (fun s => (B s).toBlocks₂₂))
```
for the appropriate ENDPOINT equivs `e0 : Fin (H' 0) ≃ Fin (deepestChainWidth H 0 - r)` and
`eL : Fin (H' (Fin.last L)) ≃ Fin (deepestChainWidth H L - r)`. (`fun s => (B s).toBlocks₂₂ : Params H'`.)
Ultimately I only need the SUM-OF-SQUARES consequence
`∑ a b, (blockDiagProd (blockToChainGen … B) L a b)^2 = ∑ i j, (prod H' (fun s => (B s).toBlocks₂₂) i j)^2`,
so any reindex bijection at the endpoints is fine (sum-of-squares is reindex-invariant; I have `sum_sq_reindex_gen`).

## What I have worked out (verify or correct)

1. `rowEq s` and `colEq s` are BLOCK-DIAGONAL: `rowEq s (Sum.inl k) = Sum.inl k` (provable: `sumSplit_inl`
   makes the pivot go to `ι`, `finCongr` matches `genPivotN`'s finCongr up to proof-irrelevance, then
   `genChainSplit = (sumSplit genPivotN).symm` sends the pivot back to `inl k`). An equiv `α⊕β ≃ α⊕γ` fixing
   `inl` must send `inr` to `inr` (injectivity). So `rowEq s = Equiv.sumCongr (Equiv.refl (Fin r)) (rowInr s)`
   for an induced `rowInr s : Fin (H s.castSucc - r) ≃ Fin (deepestChainWidth H s.val - r)`.
2. MIDDLE CANCELLATION: `colEq s` and `rowEq (s+1 : Fin L)` are the SAME equiv (both use vertex `s+1`:
   `ι s.succ = ι (s+1).castSucc`, same finCongr target `deepestChainWidth H (s+1)`, same `genChainSplit (s+1)`).
   So the induced `colInr s = rowInr (s+1)`, giving telescoping middle cancellation.
3. For block-diagonal `e_row = sumCongr refl u`, `e_col = sumCongr refl w`:
   `(Matrix.reindex e_row e_col M).toBlocks₂₂ = Matrix.reindex u w (M.toBlocks₂₂)`  (should be `simp`/`Equiv.sumCongr_symm` + defn).
4. Bridging `blockDiagProd` (ℕ-indexed, widths `deepestChainWidth H s - r`) to `prodAux H'` (Fin-indexed,
   widths `H' ⟨k,·⟩ = H ⟨k,·⟩ - r`) needs a cast-tracking induction like the existing `reindex_prodAux_eq_genPartProd`.

## Output contract

Give me, in this order, terse and concrete:

1. VERDICT on the 4-step route: is it correct and the cleanest? If there is a materially simpler route
   (e.g. avoid naming `rowInr` as an Equiv; or prove the sum-of-squares directly by an induction that never
   builds the endpoint equivs; or a Mathlib lemma that gives "equiv fixing inl ⟹ sumCongr refl _" directly),
   name it and say why it's less work.
2. The CLEANEST Lean idiom to get `rowInr s` as an `Equiv` from "`rowEq s` fixes `inl`" — i.e. the
   block-diagonal decomposition `e = Equiv.sumCongr (Equiv.refl α) e'`. Is there a Mathlib helper
   (`Equiv.sumCongr`-inverse, `Equiv.sumComm`, `Equiv.Sum.*`, subtype tricks)? If not, the ~10-line explicit
   construction (toFun/invFun via `Sum.getRight`? plus the injectivity fact), stated concretely.
3. The recommended STATEMENT + induction shape for the telescope so the endpoint casts stay isolated (mirror
   `reindex_prodAux_eq_genPartProd`: induct on prefix length `k ≤ L`, peel `blockDiagProd _ (k+1) = _ * (Q k)₂₂`
   and `prodAux _ (k+1) = _ * (layer)`, cancel the middle). Should I state it at general `k ≤ L` with
   `deepestChainCol`-style column equivs, or is there a shortcut given I only need `k = L` and only the sum?
4. Any TRAP you foresee (proof-irrelevance mismatches between the two finCongrs; `prodAux`'s `Fin ⟨k,hk⟩`
   cast e1/e2; `deepestChainWidth H L` vs `H (Fin.last L)` defeq).

Keep it under ~500 words. Flag inference vs certainty.
</task>
