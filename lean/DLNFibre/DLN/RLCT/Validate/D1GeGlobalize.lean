import DLNFibre.DLN.RLCT.Validate.D1GeChartGlobal
import DLNFibre.DLN.RLCT.Validate.D1GeBlockModel

/-!
# `DLNFibre.DLN.RLCT.Validate.D1GeGlobalize` — piece (iii) rung 8: general-`L` chart globalisation

The final rung of the general-`L` corner-elimination chart. Assembles the banked chain-level algebra
(`schurChartRawGen` + `schurChartRawInvGen` + `recoverProductGen`, `D1GeChart`) with the block model
(`blockFlatEquivGen`, `D1GeBlockModel`) into:

* `schurChart_global_gen` — the general-`L` port of `schurChart_global` (`D1L2PhiExpl`): a global
  `ContDiff ℝ 2` chart `Φ` on the flat space, fixing `0`, with an invertible derivative there,
  agreeing near `0` with the block-conjugated Schur reparametrisation. Uses the finite-dimensional
  LEFT-inverse route (`derivEquiv_of_left_inverse`, `Ψ∘Φ =ᶠ id` only).
* `schur_loss_germ_gen_at_pivot` — the general-`L` port of `schur_loss_germ_L2_at_pivot`: in the
chart
  coordinates the flat-shifted loss equals the block-chart Frobenius readout `schurReadoutF_gen ∘ Φ`
  near the flat origin.

The bridge `chainToBlockGen`/`blockToChainGen` (`BlockParamsGen H r`, `Fin L`/`H` widths ↔ the
`ℕ`-indexed `deepestChainWidth` chain the algebra reads) is built here as a per-slot
`Matrix.reindex`
by the composite equiv `rowEq`/`colEq`; by construction `blockToChainGen (blockFlatEquivGen x)`
coincides with the banked `genChain` on the first `L` slots (`blockToChainGen_blockFlatEquivGen`),
letting `reindex_prod_eq_genPartProd` feed the germ.
-/

open Matrix Filter
open scoped Topology
namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-! ## Rung 8a — the block ↔ chain reindex bridge -/

/-- A reindex-composition identity: `reindex e₁ e₂ (reindex f₁ f₂ M) = reindex (f₁.trans e₁)
(f₂.trans e₂) M`. Combines two successive `Matrix.reindex`es into one. -/
theorem reindex_reindex {l m l' m' l'' m'' : Type*}
    (f₁ : l ≃ l') (f₂ : m ≃ m') (e₁ : l' ≃ l'') (e₂ : m' ≃ m'')
    (M : Matrix l m ℝ) :
    Matrix.reindex e₁ e₂ (Matrix.reindex f₁ f₂ M)
      = Matrix.reindex (f₁.trans e₁) (f₂.trans e₂) M := by
  simp only [Matrix.reindex_apply, Matrix.submatrix_submatrix]
  rfl

/-- The per-vertex-input reindex `rowEq s : Fin r ⊕ Fin (H s.castSucc − r) ≃ Fin r ⊕ Fin
(deepestChainWidth H s.val − r)`: place the pivot `ι s.castSucc` in the left block (`sumSplit`),
recast the width `H s.castSucc → deepestChainWidth H s.val` (`finCongr`), then the chain's block
split
`genChainSplit`. Chosen so `blockToChainGen ∘ blockFlatEquivGen` lands on `genChain`. -/
noncomputable def rowEq (H : Fin (L + 1) → ℕ) (r : ℕ) (hr : ∀ s : Fin (L + 1), r ≤ H s)
    (ι : (s : Fin (L + 1)) → Fin r → Fin (H s)) (hι : ∀ s, Function.Injective (ι s)) (s : Fin L) :
    Fin r ⊕ Fin (H s.castSucc - r) ≃ Fin r ⊕ Fin (deepestChainWidth H s.val - r) :=
  (sumSplit (ι s.castSucc) (hι s.castSucc)).trans
    ((finCongr (deepestChainWidth_castSucc H s.val s.isLt)).trans
      (genChainSplit H r hr ι hι s.val))

/-- The per-vertex-output reindex `colEq s`, analogous to `rowEq` at the `succ` vertex. -/
noncomputable def colEq (H : Fin (L + 1) → ℕ) (r : ℕ) (hr : ∀ s : Fin (L + 1), r ≤ H s)
    (ι : (s : Fin (L + 1)) → Fin r → Fin (H s)) (hι : ∀ s, Function.Injective (ι s)) (s : Fin L) :
    Fin r ⊕ Fin (H s.succ - r) ≃ Fin r ⊕ Fin (deepestChainWidth H (s.val + 1) - r) :=
  (sumSplit (ι s.succ) (hι s.succ)).trans
    ((finCongr (deepestChainWidth_succ H s.val s.isLt)).trans
      (genChainSplit H r hr ι hι (s.val + 1)))

/-- **`blockToChainGen`** — the block-param → `ℕ`-chain bridge: slot `s < L` is `P ⟨s,·⟩` reindexed
by `rowEq`/`colEq` into the `deepestChainWidth` chain widths; slots `≥ L` (never read by the
`L`-layer algebra) are `0`. -/
noncomputable def blockToChainGen (H : Fin (L + 1) → ℕ) (r : ℕ) (hr : ∀ s : Fin (L + 1), r ≤ H s)
    (ι : (s : Fin (L + 1)) → Fin r → Fin (H s)) (hι : ∀ s, Function.Injective (ι s))
    (P : BlockParamsGen H r) (s : ℕ) :
    Matrix (Fin r ⊕ Fin (deepestChainWidth H s - r))
      (Fin r ⊕ Fin (deepestChainWidth H (s + 1) - r)) ℝ :=
  if h : s < L then
    Matrix.reindex (rowEq H r hr ι hι ⟨s, h⟩) (colEq H r hr ι hι ⟨s, h⟩) (P ⟨s, h⟩)
  else 0

/-- **`chainToBlockGen`** — the `ℕ`-chain → block-param bridge: slot `s : Fin L` is `D s.val`
reindexed back by `(rowEq s)⁻¹`/`(colEq s)⁻¹`. Left/right inverse of `blockToChainGen` on the first
`L` slots. -/
noncomputable def chainToBlockGen (H : Fin (L + 1) → ℕ) (r : ℕ) (hr : ∀ s : Fin (L + 1), r ≤ H s)
    (ι : (s : Fin (L + 1)) → Fin r → Fin (H s)) (hι : ∀ s, Function.Injective (ι s))
    (D : (s : ℕ) → Matrix (Fin r ⊕ Fin (deepestChainWidth H s - r))
      (Fin r ⊕ Fin (deepestChainWidth H (s + 1) - r)) ℝ) :
    BlockParamsGen H r :=
  fun s => Matrix.reindex (rowEq H r hr ι hι s).symm (colEq H r hr ι hι s).symm (D s.val)

/-- **Round trip R1** — `chainToBlockGen ∘ blockToChainGen = id` on `BlockParamsGen H r`. -/
theorem chainToBlockGen_blockToChainGen (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (ι : (s : Fin (L + 1)) → Fin r → Fin (H s))
    (hι : ∀ s, Function.Injective (ι s)) (P : BlockParamsGen H r) :
    chainToBlockGen H r hr ι hι (blockToChainGen H r hr ι hι P) = P := by
  funext s
  simp only [chainToBlockGen, blockToChainGen, dif_pos s.isLt, Fin.eta]
  rw [← Matrix.reindex_symm, Equiv.symm_apply_apply]

/-- **Round trip R2** — `blockToChainGen ∘ chainToBlockGen = id` on the first `L` chain slots. -/
theorem blockToChainGen_chainToBlockGen (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (ι : (s : Fin (L + 1)) → Fin r → Fin (H s))
    (hι : ∀ s, Function.Injective (ι s))
    (D : (s : ℕ) → Matrix (Fin r ⊕ Fin (deepestChainWidth H s - r))
      (Fin r ⊕ Fin (deepestChainWidth H (s + 1) - r)) ℝ) (s : ℕ) (hs : s < L) :
    blockToChainGen H r hr ι hι (chainToBlockGen H r hr ι hι D) s = D s := by
  simp only [blockToChainGen, chainToBlockGen, dif_pos hs]
  rw [← Matrix.reindex_symm, Equiv.apply_symm_apply]

/-- **`chainToBlockGen` reads only the first `L` chain slots.** -/
theorem chainToBlockGen_congr (H : Fin (L + 1) → ℕ) (r : ℕ) (hr : ∀ s : Fin (L + 1), r ≤ H s)
    (ι : (s : Fin (L + 1)) → Fin r → Fin (H s)) (hι : ∀ s, Function.Injective (ι s))
    (D D' : (s : ℕ) → Matrix (Fin r ⊕ Fin (deepestChainWidth H s - r))
      (Fin r ⊕ Fin (deepestChainWidth H (s + 1) - r)) ℝ) (h : ∀ s, s < L → D s = D' s) :
    chainToBlockGen H r hr ι hι D = chainToBlockGen H r hr ι hι D' := by
  funext s
  simp only [chainToBlockGen, h s.val s.isLt]

/-- **KEY relation.** `blockToChainGen (blockFlatEquivGen x)` coincides with the banked chain
`genChain` (at the flat-inverse of `x`) on the first `L` slots — both are the `sumSplit (ι ·)`
reindex of the same layer. Lets `reindex_prod_eq_genPartProd` feed the germ. -/
theorem blockToChainGen_blockFlatEquivGen (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (ι : (s : Fin (L + 1)) → Fin r → Fin (H s))
    (hι : ∀ s, Function.Injective (ι s)) (x : Fin (flatDim H) → ℝ) (s : ℕ) (hs : s < L) :
    blockToChainGen H r hr ι hι (blockFlatEquivGen H r ι hι x) s
      = genChain H r hr ι hι ((paramsEquivFlatLinear H).symm x) s := by
  have hrow : (sumSplit (ι (⟨s, hs⟩ : Fin L).castSucc) (hι _)).symm.trans
        (rowEq H r hr ι hι ⟨s, hs⟩)
      = (finCongr (deepestChainWidth_castSucc H s hs)).trans (genChainSplit H r hr ι hι s) := by
    rw [rowEq, ← Equiv.trans_assoc, Equiv.symm_trans_self, Equiv.refl_trans]
  have hcol : (sumSplit (ι (⟨s, hs⟩ : Fin L).succ) (hι _)).symm.trans
        (colEq H r hr ι hι ⟨s, hs⟩)
      = (finCongr (deepestChainWidth_succ H s hs)).trans (genChainSplit H r hr ι hι (s + 1)) := by
    rw [colEq, ← Equiv.trans_assoc, Equiv.symm_trans_self, Equiv.refl_trans]
  simp only [blockToChainGen, dif_pos hs]
  rw [blockFlatEquivGen_apply, reindex_reindex, genChain, deepestChainLayer, dif_pos hs,
    reindex_reindex, hrow, hcol]

/-! ## Rung 8a — congruences for the chain-level algebra (reads only the first `L` slots) -/

section Congr
variable {r₀ : ℕ} {n : ℕ → ℕ}

/-- `blockDiagProd Q k` reads only chain slots `< k`. -/
theorem blockDiagProd_congr
    (Q Q' : (s : ℕ) → Matrix (Fin r₀ ⊕ Fin (n s)) (Fin r₀ ⊕ Fin (n (s + 1))) ℝ) (k : ℕ)
    (h : ∀ t, t < k → Q t = Q' t) : blockDiagProd Q k = blockDiagProd Q' k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [blockDiagProd, blockDiagProd, ih (fun t ht => h t (by omega)), h k (by omega)]

/-- `recoverProductGen Q last` reads only chain slots `≤ last`. -/
theorem recoverProductGen_congr
    (Q Q' : (s : ℕ) → Matrix (Fin r₀ ⊕ Fin (n s)) (Fin r₀ ⊕ Fin (n (s + 1))) ℝ) (last : ℕ)
    (h : ∀ k, k ≤ last → Q k = Q' k) :
    recoverProductGen Q last = recoverProductGen Q' last := by
  simp only [recoverProductGen, h last le_rfl, h 0 (Nat.zero_le _),
    blockDiagProd_congr Q Q' (last + 1) (fun t ht => h t (by omega))]

/-- `invLayerSucc Q t` reads only chain slots `t`, `t+1`. -/
theorem invLayerSucc_congr
    (Q Q' : (s : ℕ) → Matrix (Fin r₀ ⊕ Fin (n s)) (Fin r₀ ⊕ Fin (n (s + 1))) ℝ) (t : ℕ)
    (ht : Q t = Q' t) (ht1 : Q (t + 1) = Q' (t + 1)) :
    invLayerSucc Q t = invLayerSucc Q' t := by
  simp only [invLayerSucc, ht, ht1]

/-- `schurChartRawInvGen Q last s` (for `s ≤ last`) reads only chain slots `≤ last`. -/
theorem schurChartRawInvGen_congr
    (Q Q' : (s : ℕ) → Matrix (Fin r₀ ⊕ Fin (n s)) (Fin r₀ ⊕ Fin (n (s + 1))) ℝ) (last : ℕ)
    (h : ∀ t, t ≤ last → Q t = Q' t) :
    ∀ s, s ≤ last → schurChartRawInvGen Q last s = schurChartRawInvGen Q' last s := by
  rintro (_ | t) hs
  · simp only [schurChartRawInvGen, h 0 (Nat.zero_le _), h last le_rfl,
      partProd_congr (fun u => invLayerSucc Q u) (fun u => invLayerSucc Q' u) last
        (fun u hu => invLayerSucc_congr Q Q' u (h u (by omega)) (h (u + 1) (by omega)))]
  · exact invLayerSucc_congr Q Q' t (h t (by omega)) (h (t + 1) (by omega))

end Congr

/-! ## Rung 8b — smoothness of the INVERSE chain map (`schurChartRawInvGen`)

The general-`L` analogue of `contDiffAt_schurChartRawInv` (`D1L2PhiExpl`), needed so the left
inverse
`Ψ` of the chart is differentiable at the base point (the hypothesis `hΨ'` of
`derivEquiv_of_left_inverse`). The inverse chain map is again `+`/`∗`/`⁻¹` in the input blocks, so
its
entries are `ContDiffAt` where the prefix pivots `(C x₀ k).toBlocks₁₁` are invertible. -/

section InvSmooth
variable {𝕏 : Type*} [NormedAddCommGroup 𝕏] [NormedSpace ℝ 𝕏] {r₀ : ℕ} {n : ℕ → ℕ}

/-- `ContDiffAt` version of `contDiff_gen_partProd_entry`: only the layers `< k` need be
`ContDiffAt`
(the invLayer chain has inverses, so it is not globally `ContDiff`). -/
theorem contDiffAt_gen_partProd_entry
    (C : 𝕏 → (s : ℕ) → Matrix (Fin r₀ ⊕ Fin (n s)) (Fin r₀ ⊕ Fin (n (s + 1))) ℝ) {x₀ : 𝕏} :
    ∀ (k : ℕ), (∀ s, s < k → ∀ i j, ContDiffAt ℝ (⊤ : ℕ∞) (fun x => C x s i j) x₀) →
      ∀ i j, ContDiffAt ℝ (⊤ : ℕ∞) (fun x => (partProd (C x) k) i j) x₀ := by
  intro k
  induction k with
  | zero => intro _ i j; simp only [partProd]; exact contDiffAt_const
  | succ k ih =>
      intro hC i j
      change ContDiffAt ℝ (⊤ : ℕ∞) (fun x => (partProd (C x) k * C x k) i j) x₀
      exact SchurChartC2.contDiffAt_matrix_mul_entry
        (fun a b => ih (fun s hs => hC s (by omega)) a b) (fun a b => hC k (by omega) a b) i j

/-- **Each `invLayerSucc` entry is `ContDiffAt`** where the two prefix pivots `(C x₀ t)₁₁`,
`(C x₀ (t+1))₁₁` are invertible. -/
theorem contDiffAt_invLayerSucc_entry
    (C : 𝕏 → (s : ℕ) → Matrix (Fin r₀ ⊕ Fin (n s)) (Fin r₀ ⊕ Fin (n (s + 1))) ℝ)
    (hC : ∀ s i j, ContDiff ℝ (⊤ : ℕ∞) (fun x => C x s i j)) (t : ℕ) {x₀ : 𝕏}
    (hp1 : ((C x₀ t).toBlocks₁₁).det ≠ 0) (hp2 : ((C x₀ (t + 1)).toBlocks₁₁).det ≠ 0)
    (a : Fin r₀ ⊕ Fin (n (t + 1))) (b : Fin r₀ ⊕ Fin (n (t + 1 + 1))) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun x => (invLayerSucc (C x) t) a b) x₀ := by
  have hinv1 : ∀ i j, ContDiffAt ℝ (⊤ : ℕ∞) (fun x => ((C x t).toBlocks₁₁)⁻¹ i j) x₀ := fun i j =>
    SchurChartC2.contDiffAt_matrix_inv_entry_of_det_ne_zero
      (fun i' j' => hC t (Sum.inl i') (Sum.inl j')) hp1 i j
  have hinv2 : ∀ i j, ContDiffAt ℝ (⊤ : ℕ∞) (fun x => ((C x (t + 1)).toBlocks₁₁)⁻¹ i j) x₀ :=
    fun i j => SchurChartC2.contDiffAt_matrix_inv_entry_of_det_ne_zero
      (fun i' j' => hC (t + 1) (Sum.inl i') (Sum.inl j')) hp2 i j
  -- `E = R + D · pt2⁻¹ · qt2` entry (the eliminated `(2,2)` factor).
  have hE : ∀ k l, ContDiffAt ℝ (⊤ : ℕ∞)
      (fun x => ((C x (t + 1)).toBlocks₂₂
        + (C x (t + 1)).toBlocks₂₁ * ((C x (t + 1)).toBlocks₁₁)⁻¹
          * (C x (t + 1)).toBlocks₁₂) k l) x₀ := fun k l =>
    ((hC (t + 1) (Sum.inr k) (Sum.inr l)).contDiffAt).add
      (SchurChartC2.contDiffAt_matrix_mul_entry
        (fun i m => SchurChartC2.contDiffAt_matrix_mul_entry
          (fun i' m' => (hC (t + 1) (Sum.inr i') (Sum.inl m')).contDiffAt) hinv2 i m)
        (fun m j => (hC (t + 1) (Sum.inl m) (Sum.inr j)).contDiffAt) k l)
  rcases a with a | a <;> rcases b with b | b
  · simp only [invLayerSucc, Matrix.fromBlocks_apply₁₁]
    exact SchurChartC2.contDiffAt_matrix_mul_entry hinv1
      (fun k j => ((hC (t + 1) (Sum.inl k) (Sum.inl j)).contDiffAt).sub
        (SchurChartC2.contDiffAt_matrix_mul_entry
          (fun k' l => (hC t (Sum.inl k') (Sum.inr l)).contDiffAt)
          (fun l j' => (hC (t + 1) (Sum.inr l) (Sum.inl j')).contDiffAt) k j)) a b
  · simp only [invLayerSucc, Matrix.fromBlocks_apply₁₂]
    exact SchurChartC2.contDiffAt_matrix_mul_entry hinv1
      (fun k j => ((hC (t + 1) (Sum.inl k) (Sum.inr j)).contDiffAt).sub
        (SchurChartC2.contDiffAt_matrix_mul_entry
          (fun k' l => (hC t (Sum.inl k') (Sum.inr l)).contDiffAt) hE k j)) a b
  · simp only [invLayerSucc, Matrix.fromBlocks_apply₂₁]
    exact (hC (t + 1) (Sum.inr a) (Sum.inl b)).contDiffAt
  · simp only [invLayerSucc, Matrix.fromBlocks_apply₂₂]
    exact hE a b

/-- **Each `schurChartRawInvGen` entry is `ContDiffAt`** on slots `s ≤ last`, where all prefix
pivots
`(C x₀ k).toBlocks₁₁` (`k ≤ last`) are invertible. Slot `t+1` is `invLayerSucc`; slot `0` assembles
the front factor `D0` from the reduced-layer telescope `γ` and the pivots. -/
theorem contDiffAt_schurChartRawInvGen_entry
    (C : 𝕏 → (s : ℕ) → Matrix (Fin r₀ ⊕ Fin (n s)) (Fin r₀ ⊕ Fin (n (s + 1))) ℝ)
    (hC : ∀ s i j, ContDiff ℝ (⊤ : ℕ∞) (fun x => C x s i j)) (last : ℕ) {x₀ : 𝕏}
    (hpiv : ∀ k, k ≤ last → ((C x₀ k).toBlocks₁₁).det ≠ 0) (s : ℕ) (hs : s ≤ last)
    (a : Fin r₀ ⊕ Fin (n s)) (b : Fin r₀ ⊕ Fin (n (s + 1))) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun x => (schurChartRawInvGen (C x) last s) a b) x₀ := by
  match s, hs with
  | t + 1, hs =>
      have heq : (fun x => (schurChartRawInvGen (C x) last (t + 1)) a b)
          = fun x => (invLayerSucc (C x) t) a b := rfl
      rw [heq]
      exact contDiffAt_invLayerSucc_entry C hC t (hpiv t (by omega)) (hpiv (t + 1) (by omega)) a b
  | 0, _ =>
      have hinvp : ∀ k, k ≤ last → ∀ i j, ContDiffAt ℝ (⊤ : ℕ∞)
          (fun x => ((C x k).toBlocks₁₁)⁻¹ i j) x₀ := fun k hk i j =>
        SchurChartC2.contDiffAt_matrix_inv_entry_of_det_ne_zero
          (fun i' j' => hC k (Sum.inl i') (Sum.inl j')) (hpiv k hk) i j
      have hγ : ∀ i j, ContDiffAt ℝ (⊤ : ℕ∞)
          (fun x => (partProd (fun u => invLayerSucc (C x) u) last) i j) x₀ :=
        contDiffAt_gen_partProd_entry (fun x u => invLayerSucc (C x) u) last
          (fun u hu i j => contDiffAt_invLayerSucc_entry C hC u (hpiv u (by omega))
            (hpiv (u + 1) (by omega)) i j)
      -- `ellL − R0·γ` entry (the front numerator).
      have hnum : ∀ i k, ContDiffAt ℝ (⊤ : ℕ∞)
          (fun x => ((C x 0).toBlocks₂₁
            - (C x 0).toBlocks₂₂ * (partProd (fun u => invLayerSucc (C x) u) last).toBlocks₂₁)
            i k) x₀ := fun i k =>
        ((hC 0 (Sum.inr i) (Sum.inl k)).contDiffAt).sub
          (SchurChartC2.contDiffAt_matrix_mul_entry
            (fun i' l => (hC 0 (Sum.inr i') (Sum.inr l)).contDiffAt)
            (fun l k' => hγ (Sum.inr l) (Sum.inl k')) i k)
      -- `D0 = (ellL − R0·γ)·pL⁻¹·p1` entry.
      have hD0 : ∀ i j, ContDiffAt ℝ (⊤ : ℕ∞)
          (fun x => (((C x 0).toBlocks₂₁
              - (C x 0).toBlocks₂₂ * (partProd (fun u => invLayerSucc (C x) u) last).toBlocks₂₁)
              * ((C x last).toBlocks₁₁)⁻¹ * (C x 0).toBlocks₁₁) i j) x₀ := fun i j =>
        SchurChartC2.contDiffAt_matrix_mul_entry
          (fun i' k => SchurChartC2.contDiffAt_matrix_mul_entry hnum (hinvp last le_rfl) i' k)
          (fun k j' => (hC 0 (Sum.inl k) (Sum.inl j')).contDiffAt) i j
      rcases a with a | a <;> rcases b with b | b
      · simp only [schurChartRawInvGen, Matrix.fromBlocks_apply₁₁]
        exact (hC 0 (Sum.inl a) (Sum.inl b)).contDiffAt
      · simp only [schurChartRawInvGen, Matrix.fromBlocks_apply₁₂]
        exact (hC 0 (Sum.inl a) (Sum.inr b)).contDiffAt
      · simp only [schurChartRawInvGen, Matrix.fromBlocks_apply₂₁]
        exact hD0 a b
      · simp only [schurChartRawInvGen, Matrix.fromBlocks_apply₂₂]
        exact ((hC 0 (Sum.inr a) (Sum.inr b)).contDiffAt).add
          (SchurChartC2.contDiffAt_matrix_mul_entry
            (fun i k => SchurChartC2.contDiffAt_matrix_mul_entry hD0 (hinvp 0 (Nat.zero_le _)) i k)
            (fun k j => (hC 0 (Sum.inl k) (Sum.inr j)).contDiffAt) a b)

end InvSmooth

/-! ## Rung 8b — the block-param self-map and its left inverse -/

/-- **The corner-elimination chart as a `BlockParamsGen` self-map**: bridge to the chain, run the
banked `schurChartRawGen`, bridge back. The general-`L` analogue of `schurChartRaw`. -/
noncomputable def schurChartRawSelfGen (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (ι : (s : Fin (L + 1)) → Fin r → Fin (H s))
    (hι : ∀ s, Function.Injective (ι s)) (P : BlockParamsGen H r) : BlockParamsGen H r :=
  chainToBlockGen H r hr ι hι (schurChartRawGen (blockToChainGen H r hr ι hι P) L)

/-- **The chart self-map has a left inverse on the prefix-pivot domain.** With every prefix pivot
`(partProd (blockToChainGen u) k).toBlocks₁₁` (`k ≤ L = last+1`) invertible, the chain-level inverse
`schurChartRawInvGen`, bridged back, recovers `u` — the `Ψ∘Φ = id` half. Composes R1/R2, the chain
congruences, and the banked `schurChartRawInvGen_schurChartRawGen`. -/
theorem leftInverse_selfGen {last : ℕ} (H : Fin (last + 1 + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (last + 1 + 1), r ≤ H s) (ι : (s : Fin (last + 1 + 1)) → Fin r → Fin (H s))
    (hι : ∀ s, Function.Injective (ι s)) (u : BlockParamsGen H r)
    (hPart : ∀ k, k ≤ last + 1 →
      Invertible (partProd (blockToChainGen H r hr ι hι u) k).toBlocks₁₁) :
    chainToBlockGen H r hr ι hι
        (schurChartRawInvGen
          (blockToChainGen H r hr ι hι (schurChartRawSelfGen H r hr ι hι u)) last)
      = u := by
  have hE := schurChartRawInvGen_schurChartRawGen (blockToChainGen H r hr ι hι u) last hPart
  have key : ∀ s, s ≤ last →
      schurChartRawInvGen
          (blockToChainGen H r hr ι hι (schurChartRawSelfGen H r hr ι hι u)) last s
        = blockToChainGen H r hr ι hι u s := by
    intro s hs
    simp only [schurChartRawSelfGen]
    rw [schurChartRawInvGen_congr _ (schurChartRawGen (blockToChainGen H r hr ι hι u) (last + 1))
        last (fun t _ => blockToChainGen_chainToBlockGen H r hr ι hι _ t (by omega)) s hs]
    exact hE s hs
  rw [chainToBlockGen_congr H r hr ι hι _ (blockToChainGen H r hr ι hι u)
      (fun s hs => key s (Nat.lt_succ_iff.mp hs))]
  exact chainToBlockGen_blockToChainGen H r hr ι hι u

/-! ## Rung 8c — the loss readout and germ -/

/-- `paramsEquivFlatLinear.symm` and `paramsEquivFlat.symm` agree as functions (general `L`; the
`D1HChartRank` lemma is `L = 2`-only, same proof). -/
theorem paramsEquivFlatLinear_symm_coe_gen (H : Fin (L + 1) → ℕ) :
    ⇑(paramsEquivFlatLinear H).symm = ⇑(paramsEquivFlat H).symm := by
  funext x; apply (paramsEquivFlat H).injective
  rw [(paramsEquivFlat H).apply_symm_apply]
  have hx : (paramsEquivFlat H) ((paramsEquivFlatLinear H).symm x)
      = (paramsEquivFlatLinear H) ((paramsEquivFlatLinear H).symm x) := by
    rw [paramsEquivFlatLinear_coe]
  rw [hx, (paramsEquivFlatLinear H).apply_symm_apply]

/-- **Frobenius sum reindex-invariance** (general row/column equivs): `∑ᵢⱼ ((M − B) i j)² =
∑_{a,bb} ((reindex e₀ e₁ M − reindex e₀ e₁ B) a bb)²`. General-`L` analogue of `sum_sq_reindex`. -/
theorem sum_sq_reindex_gen {n₀ n₁ : ℕ} {ρ₀ ρ₁ : Type*} [Fintype ρ₀] [Fintype ρ₁]
    (M B : Matrix (Fin n₀) (Fin n₁) ℝ) (e₀ : Fin n₀ ≃ ρ₀) (e₁ : Fin n₁ ≃ ρ₁) :
    (∑ i, ∑ j, ((M - B) i j) ^ 2)
      = ∑ a : ρ₀, ∑ bb : ρ₁,
          ((Matrix.reindex e₀ e₁ M - Matrix.reindex e₀ e₁ B) a bb) ^ 2 := by
  rw [← Equiv.sum_comp e₀.symm (fun i => ∑ j, ((M - B) i j) ^ 2)]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [← Equiv.sum_comp e₁.symm (fun j => ((M - B) (e₀.symm a) j) ^ 2)]
  refine Finset.sum_congr rfl (fun bb _ => ?_)
  simp only [Matrix.sub_apply, Matrix.reindex_apply, Matrix.submatrix_apply]

/-- **The post-chart Frobenius loss readout** (general `L`). From the chart OUTPUT
`blockFlatEquivGen
x + C`, `recoverProductGen` (via the bridge) rebuilds the reindexed product; `F` is the squared
Frobenius distance to the reindexed target `Br`. General-`L` analogue of `schurReadoutF_L2`. -/
noncomputable def schurReadoutF_gen {last : ℕ} (H : Fin (last + 1 + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (last + 1 + 1), r ≤ H s) (ι : (s : Fin (last + 1 + 1)) → Fin r → Fin (H s))
    (hι : ∀ s, Function.Injective (ι s)) (C : BlockParamsGen H r)
    (Br : Matrix (Fin r ⊕ Fin (deepestChainWidth H 0 - r))
      (Fin r ⊕ Fin (deepestChainWidth H (last + 1) - r)) ℝ) :
    (Fin (flatDim H) → ℝ) → ℝ :=
  fun x =>
    ∑ a : Fin r ⊕ Fin (deepestChainWidth H 0 - r),
      ∑ bb : Fin r ⊕ Fin (deepestChainWidth H (last + 1) - r),
        ((recoverProductGen (blockToChainGen H r hr ι hι (blockFlatEquivGen H r ι hι x + C)) last
          - Br) a bb) ^ 2

/-! ## Rung 8b — the globalised chart `schurChart_global_gen` -/

section Global
open scoped Matrix.Norms.Elementwise

-- Repeatedly `whnf`-ing the dependent `Fin (deepestChainWidth ·)` block widths through the banked
-- chart-entry `ContDiffAt` lemmas exceeds the default heartbeats (as in the L = 2 `D1L2PhiExpl`).
set_option maxHeartbeats 1000000 in
/-- **The general-`L` globalised corner-elimination chart.** The port of `schurChart_global`
(`D1L2PhiExpl`): from a base block-param `P₀` with every prefix pivot `(partProd (blockToChainGen
P₀)
k).toBlocks₁₁` (`k ≤ L`) nonsingular, there is a global `ContDiff ℝ 2` chart `Φ` on the flat space,
fixing `0`, with an invertible derivative at `0`, agreeing near `0` with the block-conjugated Schur
reparametrisation `blockFlatEquivGen⁻¹ ∘ (schurChartRawSelfGen (· + P₀) − schurChartRawSelfGen P₀)`.
Invertible derivative via the finite-dimensional LEFT-inverse route `derivEquiv_of_left_inverse`. -/
theorem schurChart_global_gen (H : Fin (L + 1) → ℕ) (r : ℕ) (hr : ∀ s : Fin (L + 1), r ≤ H s)
    (ι : (s : Fin (L + 1)) → Fin r → Fin (H s)) (hι : ∀ s, Function.Injective (ι s)) (hL : 1 ≤ L)
    (P₀ : BlockParamsGen H r)
    (hPart : ∀ k, k ≤ L → ((partProd (blockToChainGen H r hr ι hι P₀) k).toBlocks₁₁).det ≠ 0) :
    ∃ (Φ : (Fin (flatDim H) → ℝ) → (Fin (flatDim H) → ℝ))
      (f' : (Fin (flatDim H) → ℝ) ≃L[ℝ] (Fin (flatDim H) → ℝ)),
      ContDiff ℝ 2 Φ ∧
      HasFDerivAt Φ (f' : (Fin (flatDim H) → ℝ) →L[ℝ] (Fin (flatDim H) → ℝ))
        (0 : Fin (flatDim H) → ℝ) ∧
      Φ (0 : Fin (flatDim H) → ℝ) = 0 ∧
      Φ =ᶠ[𝓝 (0 : Fin (flatDim H) → ℝ)] fun w =>
        (blockFlatEquivGen H r ι hι).symm
          (schurChartRawSelfGen H r hr ι hι ((blockFlatEquivGen H r ι hι) w + P₀)
            - schurChartRawSelfGen H r hr ι hι P₀) := by
  classical
  obtain ⟨last, rfl⟩ : ∃ last, L = last + 1 := ⟨L - 1, by omega⟩
  set b := blockFlatEquivGen H r ι hι with hbdef
  set Cbase := schurChartRawSelfGen H r hr ι hι P₀ with hCdef
  set Φraw : (Fin (flatDim H) → ℝ) → (Fin (flatDim H) → ℝ) :=
    fun w => b.symm (schurChartRawSelfGen H r hr ι hι (b w + P₀) - Cbase) with hΦrawdef
  set Ψraw : (Fin (flatDim H) → ℝ) → (Fin (flatDim H) → ℝ) :=
    fun w => b.symm (chainToBlockGen H r hr ι hι
      (schurChartRawInvGen (blockToChainGen H r hr ι hι (b w + Cbase)) last) - P₀) with hΨrawdef
  have hle2 : (2 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
    rw [show (2 : WithTop ℕ∞) = ((2 : ℕ∞) : WithTop ℕ∞) from rfl]
    exact WithTop.coe_le_coe.mpr le_top
  have hb0 : b (0 : Fin (flatDim H) → ℝ) = 0 := map_zero b
  -- entrywise `ContDiff` of the bridged chain `w ↦ blockToChainGen (b w + Q₀)`.
  have hb_entry : ∀ (s' : Fin (last + 1)) i' j',
      ContDiff ℝ (⊤ : ℕ∞) (fun w => (b w) s' i' j') := fun s' i' j' =>
    (contDiff_apply_apply (𝕜 := ℝ) (n := (⊤ : ℕ∞)) (E := ℝ) i' j').comp
      ((ContinuousLinearMap.proj s').contDiff.comp b.contDiff)
  have hCentryOf : ∀ (Q₀ : BlockParamsGen H r) (s : ℕ) i j,
      ContDiff ℝ (⊤ : ℕ∞) (fun w => (blockToChainGen H r hr ι hι (b w + Q₀)) s i j) := by
    intro Q₀ s i j
    by_cases h : s < last + 1
    · have heq : (fun w => (blockToChainGen H r hr ι hι (b w + Q₀)) s i j)
          = fun w => (b w) ⟨s, h⟩ ((rowEq H r hr ι hι ⟨s, h⟩).symm i)
                ((colEq H r hr ι hι ⟨s, h⟩).symm j)
              + (Q₀ ⟨s, h⟩) ((rowEq H r hr ι hι ⟨s, h⟩).symm i)
                ((colEq H r hr ι hι ⟨s, h⟩).symm j) := by
        funext w
        simp only [blockToChainGen, dif_pos h, Matrix.reindex_apply, Matrix.submatrix_apply,
          Pi.add_apply, Matrix.add_apply]
      rw [heq]; exact (hb_entry ⟨s, h⟩ _ _).add contDiff_const
    · have heq : (fun w => (blockToChainGen H r hr ι hι (b w + Q₀)) s i j) = fun _ => (0 : ℝ) := by
        funext w; simp only [blockToChainGen, dif_neg h, Matrix.zero_apply]
      rw [heq]; exact contDiff_const
  -- `Φraw 0 = 0`.
  have hbP0 : b (0 : Fin (flatDim H) → ℝ) + P₀ = P₀ := by rw [hb0, zero_add]
  have hΦraw0 : Φraw 0 = 0 := by
    simp only [hΦrawdef]; rw [hbP0, ← hCdef, sub_self, map_zero]
  -- ContDiffAt of the forward self-map at `0`.
  have hself : ContDiffAt ℝ (⊤ : ℕ∞) (fun w => schurChartRawSelfGen H r hr ι hι (b w + P₀)) 0 := by
    refine contDiffAt_pi.mpr (fun s =>
      contDiffAt_pi.mpr (fun a => contDiffAt_pi.mpr (fun bb => ?_)))
    have heq : (fun w => schurChartRawSelfGen H r hr ι hι (b w + P₀) s a bb)
        = fun w => (schurChartRawGen (blockToChainGen H r hr ι hι (b w + P₀)) (last + 1) s.val)
            ((rowEq H r hr ι hι s) a) ((colEq H r hr ι hι s) bb) := by
      funext w
      simp only [schurChartRawSelfGen, chainToBlockGen, Matrix.reindex_apply,
        Matrix.submatrix_apply, Equiv.symm_symm]
    rw [heq]
    exact contDiffAt_schurChartRawGen_entry (fun w => blockToChainGen H r hr ι hι (b w + P₀))
      (hCentryOf P₀) last s.val
      (by
          change ((partProd (blockToChainGen H r hr ι hι (b 0 + P₀)) (s.val + 1)).toBlocks₁₁).det
            ≠ 0
          rw [hbP0]; exact hPart (s.val + 1) (by omega))
      ((rowEq H r hr ι hι s) a) ((colEq H r hr ι hι s) bb)
  -- prefix pivots at `Cbase` (via R2 + the chart readback).
  have hbC : b (0 : Fin (flatDim H) → ℝ) + Cbase = Cbase := by rw [hb0, zero_add]
  have hpivCbase : ∀ k, k ≤ last →
      ((blockToChainGen H r hr ι hι (b 0 + Cbase) k).toBlocks₁₁).det ≠ 0 := by
    intro k hk
    rw [hbC, hCdef]
    simp only [schurChartRawSelfGen]
    rw [blockToChainGen_chainToBlockGen H r hr ι hι
        (schurChartRawGen (blockToChainGen H r hr ι hι P₀) (last + 1)) k (by omega),
      schurChartRawGen_toBlocks₁₁]
    exact hPart (k + 1) (by omega)
  -- ContDiffAt of the inverse self-map at `0`.
  have hΨself : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun w => chainToBlockGen H r hr ι hι
        (schurChartRawInvGen (blockToChainGen H r hr ι hι (b w + Cbase)) last)) 0 := by
    refine contDiffAt_pi.mpr (fun s =>
      contDiffAt_pi.mpr (fun a => contDiffAt_pi.mpr (fun bb => ?_)))
    have heq : (fun w => chainToBlockGen H r hr ι hι
          (schurChartRawInvGen (blockToChainGen H r hr ι hι (b w + Cbase)) last) s a bb)
        = fun w => (schurChartRawInvGen (blockToChainGen H r hr ι hι (b w + Cbase)) last s.val)
            ((rowEq H r hr ι hι s) a) ((colEq H r hr ι hι s) bb) := by
      funext w
      simp only [chainToBlockGen, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm]
    rw [heq]
    exact contDiffAt_schurChartRawInvGen_entry (fun w => blockToChainGen H r hr ι hι (b w + Cbase))
      (hCentryOf Cbase) last hpivCbase s.val (by omega)
      ((rowEq H r hr ι hι s) a) ((colEq H r hr ι hι s) bb)
  -- `Φraw`, `Ψraw` are `ContDiffAt ⊤` at `0`.
  have hΦraw_cda : ContDiffAt ℝ (⊤ : ℕ∞) Φraw 0 :=
    (b.symm.contDiff.contDiffAt).comp 0 (hself.sub contDiffAt_const)
  have hΨraw_cda : ContDiffAt ℝ (⊤ : ℕ∞) Ψraw 0 :=
    (b.symm.contDiff.contDiffAt).comp 0 (hΨself.sub contDiffAt_const)
  -- the invertibility germ (all prefix pivots nonzero near `0`).
  have hdet_cont : ∀ k, Continuous
      (fun w => ((partProd (blockToChainGen H r hr ι hι (b w + P₀)) k).toBlocks₁₁).det) := fun k =>
    (SchurChartC2.contDiff_matrix_det_of_entries (A := fun w =>
        (partProd (blockToChainGen H r hr ι hι (b w + P₀)) k).toBlocks₁₁)
      (fun i j => contDiff_gen_partProd_entry (fun w => blockToChainGen H r hr ι hι (b w + P₀))
        (hCentryOf P₀) k (Sum.inl i) (Sum.inl j))).continuous
  have hdomDet : ∀ᶠ w in 𝓝 (0 : Fin (flatDim H) → ℝ), ∀ k ∈ Finset.range (last + 2),
      ((partProd (blockToChainGen H r hr ι hι (b w + P₀)) k).toBlocks₁₁).det ≠ 0 := by
    rw [Filter.eventually_all_finset]
    intro k hk
    have hval : ((partProd (blockToChainGen H r hr ι hι (b 0 + P₀)) k).toBlocks₁₁).det ≠ 0 := by
      rw [hbP0]; exact hPart k (by simp only [Finset.mem_range] at hk; omega)
    exact (hdet_cont k).continuousAt.eventually_ne hval
  -- the raw left-inverse germ `Ψraw ∘ Φraw =ᶠ id`.
  have hΨΦraw : (Ψraw ∘ Φraw) =ᶠ[𝓝 (0 : Fin (flatDim H) → ℝ)] id := by
    filter_upwards [hdomDet] with w hw
    have hInv : ∀ k, k ≤ last + 1 →
        Invertible (partProd (blockToChainGen H r hr ι hι (b w + P₀)) k).toBlocks₁₁ := fun k hk =>
      Matrix.invertibleOfIsUnitDet _
        (isUnit_iff_ne_zero.mpr (hw k (Finset.mem_range.mpr (by omega))))
    have key := leftInverse_selfGen H r hr ι hι (b w + P₀) hInv
    have e1 : b (Φraw w) + Cbase = schurChartRawSelfGen H r hr ι hι (b w + P₀) := by
      simp only [hΦrawdef, ContinuousLinearEquiv.apply_symm_apply]; abel
    change Ψraw (Φraw w) = id w
    simp only [hΨrawdef, id_eq]
    rw [e1, key, add_sub_cancel_right, ContinuousLinearEquiv.symm_apply_apply]
  -- bump-globalise `Φraw` to a global `ContDiff ℝ 2` map.
  obtain ⟨uu, hu_nhds, hΦraw_cdon⟩ := (hΦraw_cda.of_le hle2).contDiffOn le_rfl (by simp)
  obtain ⟨V, hVu, hVopen, hV0⟩ := mem_nhds_iff.mp hu_nhds
  obtain ⟨Φg, hΦg_cd, hΦg_eq⟩ :=
    exists_contDiff_eventuallyEq_of_contDiffOn (n := (2 : ℕ∞)) hVopen hV0 (hΦraw_cdon.mono hVu)
  have hΦg0 : Φg 0 = 0 := by rw [hΦg_eq.self_of_nhds]; exact hΦraw0
  have hΦg' : HasFDerivAt Φg (fderiv ℝ Φg 0) 0 :=
    ((hΦg_cd.differentiable (by norm_num)) 0).hasFDerivAt
  have hΨraw' : HasFDerivAt Ψraw (fderiv ℝ Ψraw 0) 0 :=
    (hΨraw_cda.differentiableAt (by simp)).hasFDerivAt
  have hΨΦ : (Ψraw ∘ Φg) =ᶠ[𝓝 (0 : Fin (flatDim H) → ℝ)] id := by
    filter_upwards [hΦg_eq, hΨΦraw] with w hw hw2
    change Ψraw (Φg w) = id w
    rw [hw]; exact hw2
  obtain ⟨f', hf'⟩ := derivEquiv_of_left_inverse Φg Ψraw 0 (fderiv ℝ Φg 0) (fderiv ℝ Ψraw 0) hΦg'
    (by rw [hΦg0]; exact hΨraw') hΨΦ
  exact ⟨Φg, f', hΦg_cd, hf', hΦg0, hΦg_eq⟩

/-- Each entry of `w ↦ blockToChainGen (blockFlatEquivGen w + Q₀)` is `ContDiff` (affine in `w`). -/
theorem contDiff_b2cg_entry (H : Fin (L + 1) → ℕ) (r : ℕ) (hr : ∀ s : Fin (L + 1), r ≤ H s)
    (ι : (s : Fin (L + 1)) → Fin r → Fin (H s)) (hι : ∀ s, Function.Injective (ι s))
    (Q₀ : BlockParamsGen H r) (s : ℕ) (i j) :
    ContDiff ℝ (⊤ : ℕ∞)
      (fun w => (blockToChainGen H r hr ι hι (blockFlatEquivGen H r ι hι w + Q₀)) s i j) := by
  by_cases h : s < L
  · have heq : (fun w => (blockToChainGen H r hr ι hι (blockFlatEquivGen H r ι hι w + Q₀)) s i j)
        = fun w => (blockFlatEquivGen H r ι hι w) ⟨s, h⟩ ((rowEq H r hr ι hι ⟨s, h⟩).symm i)
              ((colEq H r hr ι hι ⟨s, h⟩).symm j)
            + (Q₀ ⟨s, h⟩) ((rowEq H r hr ι hι ⟨s, h⟩).symm i)
              ((colEq H r hr ι hι ⟨s, h⟩).symm j) := by
      funext w
      simp only [blockToChainGen, dif_pos h, Matrix.reindex_apply, Matrix.submatrix_apply,
        Pi.add_apply, Matrix.add_apply]
    rw [heq]
    exact (((contDiff_apply_apply (𝕜 := ℝ) (n := (⊤ : ℕ∞)) (E := ℝ) _ _).comp
      ((ContinuousLinearMap.proj (⟨s, h⟩ : Fin L)).contDiff.comp
        (blockFlatEquivGen H r ι hι).contDiff)).add contDiff_const)
  · have heq : (fun w => (blockToChainGen H r hr ι hι (blockFlatEquivGen H r ι hι w + Q₀)) s i j)
        = fun _ => (0 : ℝ) := by
      funext w; simp only [blockToChainGen, dif_neg h, Matrix.zero_apply]
    rw [heq]; exact contDiff_const

-- The four-step slice `rw` chain forces `whnf` of the reduced-width dependent types (as in the
-- L = 2 `D1L2SchurAssembly`), exceeding the default heartbeats.
set_option maxHeartbeats 1000000 in
/-- **The general-`L` Schur loss germ (pivot-parametric).** At a general optimal `v` with every
prefix pivot `(partProd (genChain …) k).toBlocks₁₁` (`k ≤ L`) nonsingular, the
`schurChart_global_gen`
chart `Φ` carries the flat-shifted loss to the block-chart Frobenius readout `schurReadoutF_gen`
near
the flat origin:

    lossFlatShift H B v =ᶠ[𝓝 0] fun w => schurReadoutF_gen … (Φ w).

Near `0`, `blockToChainGen (blockFlatEquivGen (Φ w) + C)` reduces (R2) to the forward chart output
on
the first `L` slots, so `recoverProductGen` recovers the reindexed product
(`recoverProductGen_schurChartRawGen`, then the KEY relation + `reindex_prod_eq_genPartProd`), and
`sum_sq_reindex_gen` identifies the readout with the loss. General-`L` port of
`schur_loss_germ_L2_at_pivot`; feeds the `∃Φ` chart-data consumer `d1ge_hAtV_of_explicit_chart_genL`
(after piece (iv) splits `schurReadoutF_gen` into `∑ p² + ∑ qₑ²`). -/
theorem schur_loss_germ_gen_at_pivot {last : ℕ} (H : Fin (last + 1 + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (last + 1 + 1), r ≤ H s)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last (last + 1)))) ℝ) (v : Params H)
    (ι : (s : Fin (last + 1 + 1)) → Fin r → Fin (H s)) (hι : ∀ s, Function.Injective (ι s))
    (hPart : ∀ k, k ≤ last + 1 →
      ((partProd (genChain H r hr ι hι v) k).toBlocks₁₁).det ≠ 0) :
    ∃ (Φ : (Fin (flatDim H) → ℝ) → (Fin (flatDim H) → ℝ))
      (f' : (Fin (flatDim H) → ℝ) ≃L[ℝ] (Fin (flatDim H) → ℝ)),
      ContDiff ℝ 2 Φ ∧
      HasFDerivAt Φ (f' : (Fin (flatDim H) → ℝ) →L[ℝ] (Fin (flatDim H) → ℝ))
        (0 : Fin (flatDim H) → ℝ) ∧
      Φ (0 : Fin (flatDim H) → ℝ) = 0 ∧
      lossFlatShift H B v =ᶠ[𝓝 (0 : Fin (flatDim H) → ℝ)]
        fun w => schurReadoutF_gen H r hr ι hι
          (schurChartRawSelfGen H r hr ι hι (blockFlatEquivGen H r ι hι ((paramsEquivFlat H) v)))
          (Matrix.reindex (sumSplit (ι 0) (hι 0)).symm
            (genChainCol H r hr ι hι (last + 1) (Nat.lt_succ_self _)) B) (Φ w) := by
  classical
  set P₀ := blockFlatEquivGen H r ι hι ((paramsEquivFlat H) v) with hP0def
  set Cbase := schurChartRawSelfGen H r hr ι hι P₀ with hCdef
  -- flat-inverse identity and the KEY chain-agreement at `v`.
  have hvv : (paramsEquivFlatLinear H).symm ((paramsEquivFlat H) v) = v := by
    rw [paramsEquivFlatLinear_symm_coe_gen]; exact (paramsEquivFlat H).symm_apply_apply v
  have hchain : ∀ t, t < last + 1 →
      blockToChainGen H r hr ι hι P₀ t = genChain H r hr ι hι v t := by
    intro t ht
    rw [hP0def, blockToChainGen_blockFlatEquivGen H r hr ι hι _ t ht, hvv]
  -- prefix-pivot dets at `blockToChainGen P₀` from `genChain`.
  have hPart' : ∀ k, k ≤ last + 1 →
      ((partProd (blockToChainGen H r hr ι hι P₀) k).toBlocks₁₁).det ≠ 0 := by
    intro k hk
    rw [partProd_congr (blockToChainGen H r hr ι hι P₀) (genChain H r hr ι hι v) k
        (fun t ht => hchain t (by omega))]
    exact hPart k hk
  obtain ⟨Φ, f', hΦcd, hΦ', hΦ0, hΦeq⟩ := schurChart_global_gen H r hr ι hι (by omega) P₀ hPart'
  refine ⟨Φ, f', hΦcd, hΦ', hΦ0, ?_⟩
  -- the invertibility germ (all prefix pivots nonzero near `0`).
  have hdet_cont : ∀ k, Continuous (fun w =>
      ((partProd (blockToChainGen H r hr ι hι (blockFlatEquivGen H r ι hι w + P₀))
        k).toBlocks₁₁).det) := fun k =>
    (SchurChartC2.contDiff_matrix_det_of_entries (A := fun w =>
        (partProd (blockToChainGen H r hr ι hι (blockFlatEquivGen H r ι hι w + P₀)) k).toBlocks₁₁)
      (fun i j => contDiff_gen_partProd_entry
        (fun w => blockToChainGen H r hr ι hι (blockFlatEquivGen H r ι hι w + P₀))
        (fun s i' j' => contDiff_b2cg_entry H r hr ι hι P₀ s i' j') k
        (Sum.inl i) (Sum.inl j))).continuous
  have hdomDet : ∀ᶠ w in 𝓝 (0 : Fin (flatDim H) → ℝ), ∀ k ∈ Finset.range (last + 2),
      ((partProd (blockToChainGen H r hr ι hι (blockFlatEquivGen H r ι hι w + P₀))
        k).toBlocks₁₁).det ≠ 0 := by
    rw [Filter.eventually_all_finset]
    intro k hk
    have hval : ((partProd (blockToChainGen H r hr ι hι
        (blockFlatEquivGen H r ι hι 0 + P₀)) k).toBlocks₁₁).det ≠ 0 := by
      rw [map_zero, zero_add]; exact hPart' k (by simp only [Finset.mem_range] at hk; omega)
    exact (hdet_cont k).continuousAt.eventually_ne hval
  filter_upwards [hΦeq, hdomDet] with w hΦw hw
  -- invertibility instances at this `w`.
  have hPartw : ∀ k, k ≤ last + 1 →
      Invertible (partProd (blockToChainGen H r hr ι hι
        (blockFlatEquivGen H r ι hι w + P₀)) k).toBlocks₁₁ := fun k hk =>
    Matrix.invertibleOfIsUnitDet _ (isUnit_iff_ne_zero.mpr (hw k (Finset.mem_range.mpr (by omega))))
  -- the reindexed-product identity from the chart output.
  have hrecov : recoverProductGen (blockToChainGen H r hr ι hι
        (blockFlatEquivGen H r ι hι (Φ w) + Cbase)) last
      = Matrix.reindex (sumSplit (ι 0) (hι 0)).symm
          (genChainCol H r hr ι hι (last + 1) (Nat.lt_succ_self _))
          (prod H ((paramsEquivFlatLinear H).symm (w + (paramsEquivFlat H) v))) := by
    have hbΦ : blockFlatEquivGen H r ι hι (Φ w) + Cbase
        = schurChartRawSelfGen H r hr ι hι (blockFlatEquivGen H r ι hι w + P₀) := by
      rw [hΦw, ContinuousLinearEquiv.apply_symm_apply]; abel
    have hshift : blockFlatEquivGen H r ι hι w + P₀
        = blockFlatEquivGen H r ι hι (w + (paramsEquivFlat H) v) := by rw [hP0def, ← map_add]
    rw [hbΦ,
      recoverProductGen_congr (blockToChainGen H r hr ι hι
          (schurChartRawSelfGen H r hr ι hι (blockFlatEquivGen H r ι hι w + P₀)))
        (schurChartRawGen (blockToChainGen H r hr ι hι (blockFlatEquivGen H r ι hι w + P₀))
          (last + 1)) last
        (fun k hk => by
          simp only [schurChartRawSelfGen]
          exact blockToChainGen_chainToBlockGen H r hr ι hι _ k (by omega)),
      recoverProductGen_schurChartRawGen _ last hPartw,
      partProd_congr (blockToChainGen H r hr ι hι (blockFlatEquivGen H r ι hι w + P₀))
        (genChain H r hr ι hι ((paramsEquivFlatLinear H).symm (w + (paramsEquivFlat H) v)))
        (last + 1) (fun t ht => by
          rw [hshift]
          exact blockToChainGen_blockFlatEquivGen H r hr ι hι
            (w + (paramsEquivFlat H) v) t (by omega)),
      ← reindex_prod_eq_genPartProd H r hr ι hι
        ((paramsEquivFlatLinear H).symm (w + (paramsEquivFlat H) v))]
  -- match both sides through `sum_sq_reindex_gen`.
  rw [lossFlatShift, dlnLoss, ← paramsEquivFlatLinear_symm_coe_gen]
  simp only [schurReadoutF_gen, hrecov]
  exact sum_sq_reindex_gen (prod H ((paramsEquivFlatLinear H).symm (w + (paramsEquivFlat H) v))) B
    (show Fin (H 0) ≃ Fin r ⊕ Fin (deepestChainWidth H 0 - r) from (sumSplit (ι 0) (hι 0)).symm)
    (genChainCol H r hr ι hι (last + 1) (Nat.lt_succ_self _))

end Global

end DLNFibre.DLN.RLCT
