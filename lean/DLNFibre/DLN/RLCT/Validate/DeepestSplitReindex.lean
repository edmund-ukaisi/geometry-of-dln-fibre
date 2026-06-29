import DLNFibre.DLN.RLCT.Validate.DeepestGaugeChart

/-!
# `DLNFibre.DLN.RLCT.Validate.DeepestSplitReindex` — obligation (i) of `deepest_gauge_construction`

The **`split`** field of `DeepestGaugeChart` (#44c obligation (i), crux2): the measure-preserving
gauge-slice coordinate reindex
`split : (Fin (flatDim H) → ℝ) ≃ₜ DeepestSplit H r nGauge`
with `split_mp` (measure-preserving) and `split_basepoint` (carries the flat image of the deepest
point to the split origin `0`). The other three obligations (`coreAbsorb` + its `rlct` peel +
`loss_squeeze`) are cobuild-sub34's; this module is the pure **measure/coordinate geometry**.

## The MP tension, resolved (g125 vs the structure field)

pp2's g125 cert flagged that the deepest-point regular-peel chart χ is **unit-Jacobian, NOT
measure-preserving** (`det = (1+w₀)²(w₄+1)`, intrinsic to the `S₁₁`-multiplication). That looks to
clash with `split_mp : MeasurePreserving split`. The reconciliation (cobuild-sub34's g157, 3-way
aligned): the unit-Jacobian content lives **entirely in `coreAbsorb`'s non-MP inter-layer unit**, so
`split` itself is a pure measure-preserving (`det = ±1`) **linear coordinate reindex**. g125's "no
det=±1 chart for the regular peel" is about the COMBINED peel (`split ∘ coreAbsorb`), not the bare
reindex.

## The dimension identity (the load-bearing combinatorial content, this file)

`flatDim H = deepestNReg H r + flatDim (deepestM H r) + nGauge` with
`nGauge = flatDim H − deepestNReg H r − flatDim (deepestM H r) ≥ 0`. Per layer,
`H_s·H_{s+1} − (H_s−r)(H_{s+1}−r) = r(H_s + H_{s+1} − r)`, so
`flatDim H − flatDim M = Σ_s r(H_s+H_{s+1}−r)`, and subtracting `nReg = r(H⁰+Hᴸ−r)` leaves
`r(2·Σ_{interior} H_i − (L−1)r) ≥ 0` (each interior `H_i ≥ r`, `L−1` of them) — so `nGauge ≥ 0`.
-/

open MeasureTheory Matrix
open scoped ENNReal BigOperators Topology
namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-! ## The per-layer block-count identity -/

/-- **Per-layer block count.** The full per-layer size minus the reduced (bottom-right) block equals
the regular-frame size `r(H_s + H_{s+1} − r)`: `H_s·H_{s+1} = (H_s−r)(H_{s+1}−r) + r(H_s+H_{s+1}−r)`,
given `r ≤ H_s` and `r ≤ H_{s+1}`. -/
theorem layer_block_count {a b r : ℕ} (ha : r ≤ a) (hb : r ≤ b) :
    a * b = (a - r) * (b - r) + r * (a + b - r) := by
  obtain ⟨a', rfl⟩ := Nat.exists_eq_add_of_le ha
  obtain ⟨b', rfl⟩ := Nat.exists_eq_add_of_le hb
  -- a = r + a', b = r + b'; (a−r)(b−r) = a'b', a+b−r = r+a'+b', so RHS = a'b' + r(r+a'+b').
  have hsub : r + a' + (r + b') - r = r + a' + b' := by omega
  simp only [Nat.add_sub_cancel_left, hsub]
  ring

/-- **The regular-frame total.** Summed over layers, the per-layer regular size
`r(H_s + H_{s+1} − r)` telescopes to `r(H⁰ + Hᴸ − r) + r(2·Σ_{interior} H_i − (L−1)r)` — i.e. it is
`deepestNReg H r` plus the nonnegative spectator surplus. We package the bound: `deepestNReg H r ≤
Σ_s r(H s.castSucc + H s.succ − r)` (each interior `H_i ≥ r` makes the surplus `≥ 0`). -/
theorem deepestNReg_le_layer_regular_sum (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) :
    deepestNReg H r ≤ ∑ s : Fin L, r * (H s.castSucc + H s.succ - r) := by
  -- Factor `r` out of both sides; reduce to `(H 0 + H last − r) ≤ Σ_s (H s.castSucc + H s.succ − r)`.
  unfold deepestNReg
  rw [← Finset.mul_sum]
  refine Nat.mul_le_mul_left r ?_
  -- Lower-bound the sum by the inner-term bound.  `H 0 = H (0:Fin L).castSucc` and
  -- `H last = H (Fin.last L) = H (last index of Fin L).succ`.
  obtain ⟨L', rfl⟩ : ∃ L', L = L' + 1 := ⟨L - 1, by omega⟩
  -- s₀ = first index, sₑ = last index of `Fin (L'+1)`.
  set s₀ : Fin (L' + 1) := 0 with hs₀
  set sₑ : Fin (L' + 1) := Fin.last L' with hsₑ
  have hcast₀ : (s₀.castSucc : Fin (L' + 2)) = 0 := by simp [hs₀]
  have hsuccₑ : (sₑ.succ : Fin (L' + 2)) = Fin.last (L' + 1) := by simp [hsₑ]
  -- Each summand is `≥ 0`; isolate the `s₀` and `sₑ` contributions.
  rcases Nat.eq_zero_or_pos L' with hL'0 | hLgt
  · -- L = 1 (L' = 0): single index `0 : Fin 1`, exact match `castSucc 0 = 0`, `succ 0 = last 1`.
    subst hL'0
    rw [Fin.sum_univ_one]
    have h0 : ((0 : Fin 1).castSucc : Fin 2) = 0 := by simp
    have he : ((0 : Fin 1).succ : Fin 2) = Fin.last 1 := by simp [Fin.last]
    rw [h0, he]
  · -- L ≥ 2 (L' ≥ 1): `s₀ ≠ sₑ`, isolate both terms; the rest is `≥ 0`.
    have hne : s₀ ≠ sₑ := by
      rw [hs₀, hsₑ]; intro h
      have := congrArg Fin.val h
      simp [Fin.last] at this; omega
    have hmem₀ : s₀ ∈ (Finset.univ : Finset (Fin (L' + 1))) := Finset.mem_univ _
    have hmemₑ : sₑ ∈ (Finset.univ.erase s₀) :=
      Finset.mem_erase.2 ⟨fun h => hne h.symm, Finset.mem_univ _⟩
    -- `Σ ≥ term(s₀) + term(sₑ)`.
    have hlb :
        (H s₀.castSucc + H s₀.succ - r) + (H sₑ.castSucc + H sₑ.succ - r)
          ≤ ∑ s : Fin (L' + 1), (H s.castSucc + H s.succ - r) := by
      rw [← Finset.add_sum_erase _ _ hmem₀]
      refine Nat.add_le_add_left ?_ _
      exact Finset.single_le_sum (f := fun s => H s.castSucc + H s.succ - r)
        (fun _ _ => Nat.zero_le _) hmemₑ
    refine le_trans ?_ hlb
    -- `H 0 + H last − r ≤ (H 0 + H s₀.succ − r) + (H sₑ.castSucc + H last − r)` (Nat, all `≥ r`).
    rw [hcast₀, hsuccₑ]
    have h1 : r ≤ H (0 : Fin (L' + 2)) := hr _
    have h2 : r ≤ H (Fin.last (L' + 1)) := hr _
    have h3 : r ≤ H s₀.succ := hr _
    have h4 : r ≤ H sₑ.castSucc := hr _
    omega

/-- **The flat-dimension identity** (the load-bearing combinatorial content of obligation (i)).
`flatDim H = deepestNReg H r + flatDim (deepestM H r) + nGauge`, where the spectator count
`nGauge = flatDim H − deepestNReg H r − flatDim (deepestM H r)` is `≥ 0`. The per-layer
`layer_block_count` gives `flatDim H = flatDim M + Σ_s r(H_s+H_{s+1}−r)`; then
`deepestNReg_le_layer_regular_sum` pins `nReg ≤` that sum, so the split is `nReg + flatDim M + (the
nonnegative remainder)`. -/
theorem flatDim_deepest_split (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) :
    flatDim H
      = deepestNReg H r + flatDim (deepestM H r)
          + (flatDim H - deepestNReg H r - flatDim (deepestM H r)) := by
  -- `flatDim H = flatDim M + Σ_s r(H_s+H_{s+1}−r)` via per-layer `layer_block_count`.
  have hflat : flatDim H
      = flatDim (deepestM H r) + ∑ s : Fin L, r * (H s.castSucc + H s.succ - r) := by
    rw [flatDim_eq, flatDim_eq, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun s _ => ?_
    have := layer_block_count (a := H s.castSucc) (b := H s.succ) (r := r)
      (hr s.castSucc) (hr s.succ)
    simpa [deepestM] using this
  -- `nReg ≤ Σ_s r(…)` so the difference is nonnegative; `omega` closes the `Nat.sub` rearrangement.
  have hle := deepestNReg_le_layer_regular_sum H r hr hL
  omega

/-! ## The role-respecting block split (the precision-pin: slots BY ROLE, not arbitrary)

The controller's precision pin (#64): the split's slots must be grouped BY ROLE — the core slot the
raw `T_s` blocks (`= FlatIdx (deepestM H r)`, forced by the slot type `Fin (flatDim (deepestM H r))`),
the regular slot the gauge pivots, spectators the rest — NOT an arbitrary `equivOfCardEq`. The
load-bearing piece is the **role-respecting index bijection** `FlatIdx H ≃ RegIdx ⊕ (FlatIdx (deepestM
H r) ⊕ GaugeIdx)`, where the middle summand is exactly the `T`-block entries `{(s,i,j) | r ≤ i ∧ r ≤
j}`. Building blocks below; the per-layer `r`-threshold row split is the atom. -/

/-- The per-vertex `r`-threshold split `Fin a ≃ Fin r ⊕ Fin (a − r)` (for `r ≤ a`): the first `r`
indices (the gauge/regular rows) and the last `a − r` (the reduced `T`-block rows). The atom of the
role-respecting block decomposition. -/
noncomputable def rThresholdSplit (r a : ℕ) (ha : r ≤ a) : Fin a ≃ Fin r ⊕ Fin (a - r) :=
  (finCongr (by omega : a = r + (a - r))).trans finSumFinEquiv.symm

/-! ## The B-pivot-twisted threshold split (PIN1, the shared-J column alignment)

`rThresholdSplit` always sends the FIRST `r` indices to the left block. PIN1's reg-slice fderiv
needs the LAST-interface column split to align with `B`'s actual pivot columns (so the `B22` block of
the boundary frame is invertible). `pivotThresholdSplit r a ha J` is the generalization: its left
block is exactly the `r` PIVOT columns `Set.range J` (in sorted order), the right block is the
complement. At the "first `r`" embedding `Fin.castLE` it reduces to `rThresholdSplit`
(`pivotThresholdSplit_castLE`), so the unpermuted / pivot-already-front path reuses existing proofs.
`J` is `B`-DETERMINED (the chosen pivot set), so there is no restriction on the rank-`r` target `B`. -/

/-- The pivot support: the image of the pivot embedding `J` as a finset of `Fin a` (cardinality `r`). -/
noncomputable def pivotSupport (r a : ℕ) (J : Fin r ↪ Fin a) : Finset (Fin a) :=
  Finset.univ.map J

/-- The pivot support has cardinality `r` (`J` injective). -/
theorem pivotSupport_card (r a : ℕ) (J : Fin r ↪ Fin a) :
    (pivotSupport r a J).card = r := by
  simp [pivotSupport]

/-- The complement of the pivot support has cardinality `a − r`. -/
theorem pivotSupport_compl_card (r a : ℕ) (ha : r ≤ a) (J : Fin r ↪ Fin a) :
    (pivotSupport r a J)ᶜ.card = a - r := by
  rw [Finset.card_compl, pivotSupport_card]; simp

/-- **The B-pivot-twisted threshold split** `Fin a ≃ Fin r ⊕ Fin (a − r)`: the left block enumerates
the `r` pivot columns `Set.range J` (sorted), the right block the complement. The `.symm` of
`finSumEquivOfFinset` on the pivot finset. The replacement for `rThresholdSplit r a` at the last
interface where the rank-`r` target's pivot columns need not sit first. -/
noncomputable def pivotThresholdSplit (r a : ℕ) (ha : r ≤ a) (J : Fin r ↪ Fin a) :
    Fin a ≃ Fin r ⊕ Fin (a - r) :=
  (finSumEquivOfFinset (pivotSupport_card r a J) (pivotSupport_compl_card r a ha J)).symm

/-- The left block of `pivotThresholdSplit` enumerates the pivot columns (sorted): its inverse on
`Sum.inl i` is the `i`-th smallest pivot column. -/
theorem pivotThresholdSplit_symm_inl (r a : ℕ) (ha : r ≤ a) (J : Fin r ↪ Fin a) (i : Fin r) :
    (pivotThresholdSplit r a ha J).symm (Sum.inl i)
      = (pivotSupport r a J).orderEmbOfFin (pivotSupport_card r a J) i := by
  rw [pivotThresholdSplit, Equiv.symm_symm, finSumEquivOfFinset_inl]

/-- The right block of `pivotThresholdSplit` enumerates the non-pivot columns (sorted complement). -/
theorem pivotThresholdSplit_symm_inr (r a : ℕ) (ha : r ≤ a) (J : Fin r ↪ Fin a)
    (i : Fin (a - r)) :
    (pivotThresholdSplit r a ha J).symm (Sum.inr i)
      = (pivotSupport r a J)ᶜ.orderEmbOfFin (pivotSupport_compl_card r a ha J) i := by
  rw [pivotThresholdSplit, Equiv.symm_symm, finSumEquivOfFinset_inr]

/-- **Every left-block index is a pivot column** — `(pivotThresholdSplit … J).symm (Sum.inl i)` lies in
`Set.range J`. The semantic fact the frame uses: the left block selects exactly the pivot columns. -/
theorem pivotThresholdSplit_symm_inl_mem_range (r a : ℕ) (ha : r ≤ a) (J : Fin r ↪ Fin a)
    (i : Fin r) :
    (pivotThresholdSplit r a ha J).symm (Sum.inl i) ∈ Set.range J := by
  rw [pivotThresholdSplit_symm_inl]
  have hmem := (pivotSupport r a J).orderEmbOfFin_mem (pivotSupport_card r a J) i
  simp only [pivotSupport, Finset.mem_map, Finset.mem_univ, true_and,
    Function.Embedding.coeFn_mk] at hmem
  obtain ⟨x, hx⟩ := hmem
  exact ⟨x, hx⟩

/-- **The pivot split at the "first `r`" embedding IS `rThresholdSplit`.** When `J = Fin.castLE` (the
unpermuted / pivot-already-front case), the sorted pivot set is `{0,…,r−1}` and the sorted complement
is `{r,…,a−1}`, so the pivot split coincides with the plain threshold split. Lets the existing
reachable-half proofs reuse verbatim on the unpermuted path. -/
theorem pivotThresholdSplit_castLE (r a : ℕ) (ha : r ≤ a) :
    pivotThresholdSplit r a ha ⟨Fin.castLE ha, Fin.castLE_injective ha⟩ = rThresholdSplit r a ha := by
  -- Compare the two `.symm`s on each arm (each lands on the explicit threshold formula).
  apply Equiv.symm_bijective.injective
  apply Equiv.ext
  intro x
  rcases x with i | i
  · -- inl: the sorted pivot set `{0,…,r−1}` orderEmbeds to `castLE`.
    rw [pivotThresholdSplit_symm_inl]
    have hcastLE : (rThresholdSplit r a ha).symm (Sum.inl i) = i.castLE ha := by
      unfold rThresholdSplit
      simp only [Equiv.symm_trans_apply, finCongr_symm, Equiv.symm_symm,
        finSumFinEquiv_apply_left, finCongr_apply]
      apply Fin.ext; simp [Fin.castLE, Fin.castAdd]
    rw [hcastLE]
    have h : (fun j : Fin r => j.castLE ha)
        = (pivotSupport r a ⟨Fin.castLE ha, Fin.castLE_injective ha⟩).orderEmbOfFin
            (pivotSupport_card r a _) := by
      apply Finset.orderEmbOfFin_unique
      · intro y
        simp only [pivotSupport, Finset.mem_map, Finset.mem_univ, true_and,
          Function.Embedding.coeFn_mk]
        exact ⟨y, rfl⟩
      · exact Fin.strictMono_castLE ha
    rw [← h]
  · -- inr: the sorted complement `{r,…,a−1}` orderEmbeds to `r + ·`.
    rw [pivotThresholdSplit_symm_inr]
    have hnat : (rThresholdSplit r a ha).symm (Sum.inr i) = ⟨r + i, by omega⟩ := by
      unfold rThresholdSplit
      simp only [Equiv.symm_trans_apply, finCongr_symm, Equiv.symm_symm,
        finSumFinEquiv_apply_right, finCongr_apply]
      apply Fin.ext; simp [Fin.natAdd]
    rw [hnat]
    have h : (fun j : Fin (a - r) => (⟨r + j, by omega⟩ : Fin a))
        = (pivotSupport r a ⟨Fin.castLE ha, Fin.castLE_injective ha⟩)ᶜ.orderEmbOfFin
            (pivotSupport_compl_card r a ha _) := by
      apply Finset.orderEmbOfFin_unique
      · intro y
        simp only [pivotSupport, Finset.mem_compl, Finset.mem_map, Finset.mem_univ, true_and,
          Function.Embedding.coeFn_mk, not_exists]
        intro z hz
        have hz2 : (z.castLE ha : ℕ) < r := z.isLt
        rw [Fin.ext_iff] at hz
        simp only [Fin.castLE] at hz
        omega
      · intro x y hxy
        simp only [Fin.lt_def]
        omega
    rw [← h]

/-- **The pivot-split P12 discriminating identity** (Stage B item-1, the cheapest discriminating
check; L1-soundness gate). For a row split `eR : Fin a ≃ Fin r ⊕ Fin (a−r)`, a (pivot) column split
`eJ : Fin b ≃ Fin r ⊕ Fin (b−r)` shared between the deviation insertion AND the read, and any frame
`Q : Matrix (Fin b)²`, the top-right (`P12`, `Fin r × Fin (b−r)`) block of the read of the
Y-deviation-conjugated `Q` is exactly `Y · (reindex eJ eJ Q).toBlocks₂₂`:

    (reindex eR eJ ((reindex eR.symm eJ.symm (fromBlocks 0 Y 0 0)) * Q)).toBlocks₁₂
      = Y * (reindex eJ eJ Q).toBlocks₂₂.

This is the certified `Y · B₂₂` shape (with `B₂₂ = (reindex eJ eJ Q).toBlocks₂₂`) PIN1's reg-slice
fderiv needs. CRITICAL (L1 vs L2): the SAME `eJ` appears on the `.symm` insertion side and the read
side; with the threshold `.succ` split on the insertion and `eJ` only on the outer read, the block
is the MIXED `Y · (reindex eThreshold eJ Q).toBlocks₂₂` — NOT this certified form (the documented L2
unsoundness). Proof: split the product at the middle index `eJ` (`submatrix_mul_equiv`), the outer
reindex cancels the inserted reindex, then `fromBlocks_multiply` on `fromBlocks 0 Y 0 0`. -/
theorem pivot_devY_read_toBlocks₁₂ {a b r : ℕ}
    (eR : Fin a ≃ Fin r ⊕ Fin (a - r)) (eJ : Fin b ≃ Fin r ⊕ Fin (b - r))
    (Y : Matrix (Fin r) (Fin (b - r)) ℝ) (Q : Matrix (Fin b) (Fin b) ℝ) :
    (Matrix.reindex eR eJ
        ((Matrix.reindex eR.symm eJ.symm (Matrix.fromBlocks 0 Y 0 0)) * Q)).toBlocks₁₂
      = Y * (Matrix.reindex eJ eJ Q).toBlocks₂₂ := by
  -- Split the product at the middle index `eJ`. Unfold every `reindex` to `submatrix`; with
  -- `Q = (reindex eJ eJ Q).submatrix eJ eJ`, the outer `submatrix _ eR.symm eJ.symm` of the product
  -- merges by `submatrix_mul_equiv` (middle `eJ`) into `fromBlocks 0 Y 0 0 * reindex eJ eJ Q`.
  have hsplit : Matrix.reindex eR eJ
        ((Matrix.reindex eR.symm eJ.symm (Matrix.fromBlocks 0 Y 0 0)) * Q)
      = (Matrix.fromBlocks (0 : Matrix (Fin r) (Fin r) ℝ) Y 0 0)
          * (Matrix.reindex eJ eJ Q) := by
    -- Rewrite `Q` as the round-trip `(reindex eJ eJ Q).submatrix eJ eJ` so the product is two
    -- submatrices sharing the middle index `eJ`.
    have hQ : Q = (Matrix.reindex eJ eJ Q).submatrix eJ eJ := by
      simp only [Matrix.reindex_apply, Matrix.submatrix_submatrix, Equiv.symm_comp_self,
        Matrix.submatrix_id_id]
    simp only [Matrix.reindex_apply, Equiv.symm_symm]
    conv_lhs => rw [hQ]
    rw [Matrix.submatrix_mul_equiv (Matrix.fromBlocks (0 : Matrix (Fin r) (Fin r) ℝ) Y 0 0)
        (Matrix.reindex eJ eJ Q) eR eJ eJ, Matrix.submatrix_submatrix,
      Equiv.self_comp_symm, Equiv.self_comp_symm, Matrix.submatrix_id_id]
    rfl
  rw [hsplit]
  -- `(fromBlocks 0 Y 0 0 * M).toBlocks₁₂ = Y · M.toBlocks₂₂`: expand `M` into its blocks, multiply.
  conv_lhs => rw [← Matrix.fromBlocks_toBlocks (Matrix.reindex eJ eJ Q)]
  rw [Matrix.fromBlocks_multiply, Matrix.toBlocks_fromBlocks₁₂]
  simp only [Matrix.zero_mul, zero_add]

/-- The per-layer entry split: a layer's entry index `Fin a × Fin b` (rows × cols) splits, by the
`r`-threshold on both, into the **three regular blocks** `(X = r×r) ⊕ (Y = r×(b−r)) ⊕ (Z = (a−r)×r)`
collected on the left, and the **reduced `T`-block** `MM = (a−r)×(b−r)` isolated on the right. The
`MM`-block is exactly the reduced-width layer entry (`a−r = M s.castSucc`, `b−r = M s.succ`), so its
`Σ`-collection is `FlatIdx (deepestM H r)` (the core slot). -/
noncomputable def layerEntrySplit (r a b : ℕ) (ha : r ≤ a) (hb : r ≤ b) :
    (Fin a × Fin b)
      ≃ ((Fin r × Fin r ⊕ Fin r × Fin (b - r)) ⊕ Fin (a - r) × Fin r)
          ⊕ (Fin (a - r) × Fin (b - r)) := by
  refine ((rThresholdSplit r a ha).prodCongr (rThresholdSplit r b hb)).trans ?_
  refine (Equiv.sumProdDistrib _ _ _).trans ?_
  refine ((Equiv.prodSumDistrib _ _ _).sumCongr (Equiv.prodSumDistrib _ _ _)).trans ?_
  exact (Equiv.sumAssoc _ _ _).symm

/-- `FlatIdx H ≃ Σ s, (Fin (H s.castSucc) × Fin (H s.succ))` — the layer-grouped entry form
(`sigmaAssoc` + the constant-fiber `sigmaEquivProd`). The intermediate for the role split. -/
noncomputable def flatIdxLayerProd (H : Fin (L + 1) → ℕ) :
    FlatIdx H ≃ Σ s : Fin L, (Fin (H s.castSucc) × Fin (H s.succ)) :=
  (Equiv.sigmaAssoc (fun (s : Fin L) (_ : Fin (H s.castSucc)) => Fin (H s.succ))).trans
    (Equiv.sigmaCongrRight fun s => Equiv.sigmaEquivProd (Fin (H s.castSucc)) (Fin (H s.succ)))

/-- The reg+gauge entry collection (the three `X/Y/Z` blocks summed over layers) — the complement of
the reduced `T`-core in `FlatIdx H`. -/
abbrev RegGaugeIdx (H : Fin (L + 1) → ℕ) (r : ℕ) : Type :=
  Σ s : Fin L,
    ((Fin r × Fin r ⊕ Fin r × Fin (H s.succ - r)) ⊕ Fin (H s.castSucc - r) × Fin r)

/-- **The role-respecting index split**: `FlatIdx H ≃ RegGaugeIdx H r ⊕ FlatIdx (deepestM H r)` — the
reg+gauge entries (`X/Y/Z`) and the reduced `T`-core (`= FlatIdx (deepestM)`), grouped BY ROLE. The core
slot is exactly the reduced-chain flat index (the precision pin: core = the `T_s` blocks). Per-layer
`layerEntrySplit` collected (`sigmaCongrRight`), then `sigmaSumDistrib` separates reg-gauge from the
`MM`-core, whose `Σ`-collection is `FlatIdx (deepestM H r)`. -/
noncomputable def roleSplitIdx (H : Fin (L + 1) → ℕ) (r : ℕ) (hr : ∀ s : Fin (L + 1), r ≤ H s) :
    FlatIdx H ≃ RegGaugeIdx H r ⊕ FlatIdx (deepestM H r) := by
  refine (flatIdxLayerProd H).trans ?_
  refine (Equiv.sigmaCongrRight fun (s : Fin L) =>
    layerEntrySplit r (H s.castSucc) (H s.succ) (hr s.castSucc) (hr s.succ)).trans ?_
  refine (Equiv.sigmaSumDistrib _ _).trans ?_
  refine Equiv.sumCongr (Equiv.refl _) ?_
  -- `Σ s, (Fin (M s.castSucc) × Fin (M s.succ)) ≃ FlatIdx (deepestM H r)`.
  refine (Equiv.sigmaCongrRight fun (s : Fin L) =>
    (Equiv.sigmaEquivProd (Fin (deepestM H r s.castSucc)) (Fin (deepestM H r s.succ))).symm).trans ?_
  exact (Equiv.sigmaAssoc
    (fun (s : Fin L) (_ : Fin (deepestM H r s.castSucc)) => Fin (deepestM H r s.succ))).symm

/-! ## The measure-preserving gauge-slice reindex -/

/-- The spectator (gauge) coordinate count: the flat directions left after the regular frame and the
reduced core. `nGauge = flatDim H − deepestNReg H r − flatDim (deepestM H r) ≥ 0` (the surplus from
`flatDim_deepest_split`). -/
abbrev deepestNGauge (H : Fin (L + 1) → ℕ) (r : ℕ) : ℕ :=
  flatDim H - deepestNReg H r - flatDim (deepestM H r)

/-- `card (RegGaugeIdx H r) = deepestNReg + deepestNGauge` — the reg+gauge entries number the
non-core flat directions (from `roleSplitIdx` being a bijection + the dimension identity). -/
theorem card_regGaugeIdx (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) :
    Fintype.card (RegGaugeIdx H r) = deepestNReg H r + deepestNGauge H r := by
  have hcard := Fintype.card_congr (roleSplitIdx H r hr)
  rw [Fintype.card_sum] at hcard
  have hfH : Fintype.card (FlatIdx H) = flatDim H := rfl
  have hfM : Fintype.card (FlatIdx (deepestM H r)) = flatDim (deepestM H r) := rfl
  rw [hfH, hfM] at hcard
  have hdim := flatDim_deepest_split H r hr hL
  unfold deepestNGauge
  omega

/-! ## The #120 explicit boundary-pivot packing (deriv-fm, #82-deriv)

The transparent replacement for the opaque `Fintype.equivFin` reg/gauge split: route the reg slot
explicitly onto the boundary generators `(X_first, Y_last, Z_first)`, so the reg-block derivative is `id`
by construction (g213/#91). `regResidualPack` (in `DeepestGaugeConstruction`) and `regGaugeIdxSplit`
(below) both factor through the SAME `regPivotFinEquiv`, so they cancel. -/

/-- **The boundary-pivot index type** — the residual blocks `(P11−I, P12, P21)` surviving the idempotent
sandwich: `(r×r) ⊕ ((r×M_L) ⊕ (M_0×r))`, the sum type `regResidualPack` targets, of card `deepestNReg`. -/
abbrev BoundaryPivotIdx (H : Fin (L + 1) → ℕ) (r : ℕ) : Type :=
  (Fin r × Fin r) ⊕ ((Fin r × Fin (H (Fin.last L) - r)) ⊕ (Fin (H 0 - r) × Fin r))

/-- **The card match** — `card BoundaryPivotIdx = deepestNReg` (the arithmetic `regResidualPack` proves:
`r² + r(H_L−r) + (H_0−r)r = r(H_0+H_L−r)`). -/
theorem card_boundaryPivotIdx (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) :
    Fintype.card (BoundaryPivotIdx H r) = deepestNReg H r := by
  simp only [BoundaryPivotIdx, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
  obtain ⟨a', ha'⟩ := Nat.le.dest (hr 0)
  obtain ⟨b', hb'⟩ := Nat.le.dest (hr (Fin.last L))
  unfold deepestNReg
  rw [← ha', ← hb']
  simp only [Nat.add_sub_cancel_left]
  rw [show r + a' + (r + b') - r = r + (a' + b') by omega]
  ring

/-- **The explicit pivot packing** `Fin (deepestNReg H r) ≃ BoundaryPivotIdx H r` — the TRANSPARENT
`finProdFinEquiv`/`finSumFinEquiv`/`finCongr` enumeration replacing the opaque `Fintype.equivFin`.
Computable (has `_apply` equation lemmas), so the cancellation reduces. -/
noncomputable def regPivotFinEquiv (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) :
    Fin (deepestNReg H r) ≃ BoundaryPivotIdx H r :=
  (finCongr (show deepestNReg H r
      = r * r + (r * (H (Fin.last L) - r) + (H 0 - r) * r) by
        obtain ⟨a', ha'⟩ := Nat.le.dest (hr 0)
        obtain ⟨b', hb'⟩ := Nat.le.dest (hr (Fin.last L))
        unfold deepestNReg
        rw [← ha', ← hb']
        simp only [Nat.add_sub_cancel_left]
        rw [show r + a' + (r + b') - r = r + (a' + b') by omega]
        ring)).trans
    (finSumFinEquiv.symm.trans
      (Equiv.sumCongr finProdFinEquiv.symm
        (finSumFinEquiv.symm.trans
          (Equiv.sumCongr finProdFinEquiv.symm finProdFinEquiv.symm))))

/-- The first layer index `⟨0,_⟩ : Fin L` (`0 < L` from `1 ≤ L`). -/
def firstLayer (hL : 1 ≤ L) : Fin L := ⟨0, by omega⟩

/-- The last layer `⟨L-1,_⟩ : Fin L`; `.succ` is `Fin.last L` (width `H (Fin.last L)`). -/
def lastLayer (hL : 1 ≤ L) : Fin L := ⟨L - 1, by omega⟩

/-- `(lastLayer hL).succ` has the same `H`-width as `Fin.last L` — the Y_last column cast. -/
theorem H_lastLayer_succ (H : Fin (L + 1) → ℕ) (hL : 1 ≤ L) :
    H ((lastLayer hL).succ) = H (Fin.last L) := by
  congr 1; apply Fin.ext; simp [lastLayer, Fin.succ, Fin.last]; omega

/-- **The boundary-generator routing** `BoundaryPivotIdx → RegGaugeIdx` (the reg-half target):
`X_first` ↦ layer-0 (0,0) entry, `Y_last` ↦ last-layer (0,1) entry, `Z_first` ↦ layer-0 (1,0) entry.
INJECTIVE (distinct layer-tag × sum-arm). -/
def regBoundaryToRegGauge (H : Fin (L + 1) → ℕ) (r : ℕ) (hL : 1 ≤ L) :
    BoundaryPivotIdx H r → RegGaugeIdx H r
  | Sum.inl (i, j) => ⟨firstLayer hL, Sum.inl (Sum.inl (i, j))⟩
  | Sum.inr (Sum.inl (i, j)) =>
      ⟨lastLayer hL, Sum.inl (Sum.inr (i, (finCongr (by rw [H_lastLayer_succ H hL])) j))⟩
  | Sum.inr (Sum.inr (i, j)) => ⟨firstLayer hL, Sum.inr (i, j)⟩

/-- A LEFT INVERSE of `regBoundaryToRegGauge` (total on `RegGaugeIdx`, inverting on the image). -/
def regGaugeDecode (H : Fin (L + 1) → ℕ) (r : ℕ) (hL : 1 ≤ L) :
    RegGaugeIdx H r → BoundaryPivotIdx H r
  | ⟨_, Sum.inl (Sum.inl (i, j))⟩ => Sum.inl (i, j)
  | ⟨s, Sum.inl (Sum.inr (i, j))⟩ =>
      if h : H s.succ - r = H (Fin.last L) - r then Sum.inr (Sum.inl (i, (finCongr h) j))
      else Sum.inl (i, i)
  | ⟨s, Sum.inr (i, j)⟩ =>
      if h : H s.castSucc - r = H 0 - r then Sum.inr (Sum.inr ((finCongr h) i, j))
      else Sum.inl (j, j)

/-- **`regBoundaryToRegGauge` is INJECTIVE** (the no-collapse fact) — via the left inverse `regGaugeDecode`
(`decode ∘ route = id`, per arm: X reads back, Y/Z fire their `dif` and the `finCongr` round-trip
collapses). The reg-half read is injective, so the `Σ_s δX_s` sandwich keeps `X_first` alone. -/
theorem regBoundaryToRegGauge_injective (H : Fin (L + 1) → ℕ) (r : ℕ) (hL : 1 ≤ L) :
    Function.Injective (regBoundaryToRegGauge H r hL) := by
  have hY : H (lastLayer hL).succ - r = H (Fin.last L) - r := by rw [H_lastLayer_succ H hL]
  have hZ : H ((firstLayer hL).castSucc) - r = H 0 - r := by
    have hc : (firstLayer hL).castSucc = (0 : Fin (L + 1)) := by
      apply Fin.ext; simp [firstLayer, Fin.castSucc, Fin.castAdd, Fin.castLE]
    rw [hc]
  refine Function.LeftInverse.injective (g := regGaugeDecode H r hL) (fun b => ?_)
  rcases b with ⟨i, j⟩ | ⟨i, j⟩ | ⟨i, j⟩
  · rfl
  · rw [regBoundaryToRegGauge, regGaugeDecode, dif_pos hY]
    exact congrArg (fun x => Sum.inr (Sum.inl (i, x))) (Fin.ext (by simp [finCongr_apply]))
  · rw [regBoundaryToRegGauge, regGaugeDecode, dif_pos hZ]
    exact congrArg (fun x => Sum.inr (Sum.inr (x, j))) (Fin.ext (by simp [finCongr_apply]))

/-- The boundary-generator EMBEDDING `BoundaryPivotIdx ↪ RegGaugeIdx` (from the routing + its injectivity).
The reg slot's image inside `RegGaugeIdx`. -/
def regBoundaryEmbed (H : Fin (L + 1) → ℕ) (r : ℕ) (hL : 1 ≤ L) :
    BoundaryPivotIdx H r ↪ RegGaugeIdx H r :=
  ⟨regBoundaryToRegGauge H r hL, regBoundaryToRegGauge_injective H r hL⟩

/-- The complement of the boundary image has `Nat.card` = `deepestNGauge` — `card RegGaugeIdx −
card BoundaryPivotIdx = (nReg + nGauge) − nReg = nGauge`. Stated with `Nat.card` to avoid a
statement-level `Fintype ↥…ᶜ` synth; the `Fintype` instances are produced locally via `Fintype.ofFinite`. -/
theorem card_compl_regBoundaryEmbed (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) :
    Nat.card (↥(Set.range (regBoundaryEmbed H r hL))ᶜ) = deepestNGauge H r := by
  classical
  haveI : Fintype (↥(Set.range (regBoundaryEmbed H r hL))) := Fintype.ofFinite _
  haveI : Fintype (↥(Set.range (regBoundaryEmbed H r hL))ᶜ) := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card]
  -- `range(embed) ≃ BoundaryPivotIdx` (ofInjective), so `card (range) = card BoundaryPivotIdx = nReg`.
  have hrange : Fintype.card (↥(Set.range (regBoundaryEmbed H r hL)))
      = Fintype.card (BoundaryPivotIdx H r) :=
    (Fintype.card_congr (Equiv.ofInjective _ (regBoundaryEmbed H r hL).injective)).symm
  -- `card (range) + card (rangeᶜ) = card RegGaugeIdx` via `sumCompl`.
  have htot : Fintype.card (↥(Set.range (regBoundaryEmbed H r hL)))
      + Fintype.card (↥(Set.range (regBoundaryEmbed H r hL))ᶜ) = Fintype.card (RegGaugeIdx H r) := by
    rw [← Fintype.card_sum]
    exact Fintype.card_congr (Equiv.Set.sumCompl _)
  rw [hrange, card_boundaryPivotIdx H r hr, card_regGaugeIdx H r hr hL] at htot
  omega

/-- **The reg-gauge index split** (the `eReg` of `deepestRoleIndexEquiv`, named for reuse):
`RegGaugeIdx H r ≃ Fin (deepestNReg H r) ⊕ Fin (deepestNGauge H r)` — the #120 EXPLICIT split: the
`Fin nReg` (reg) half routes onto the boundary generators via `regBoundaryToRegGauge ∘ regPivotFinEquiv`
(`regBoundaryEmbed`'s image, `≃ BoundaryPivotIdx ≃ Fin nReg`); the `Fin nGauge` (gauge) half is the
complement (its enumeration opaque — only the REG half needs the boundary alignment). So `regResidualPack
:= regPivotFinEquiv` and this split's reg-half SHARE `regPivotFinEquiv`, hence cancel (reg-block = id). -/
noncomputable def regGaugeIdxSplit (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) :
    RegGaugeIdx H r ≃ Fin (deepestNReg H r) ⊕ Fin (deepestNGauge H r) := by
  classical
  haveI : Fintype (↥(Set.range (regBoundaryEmbed H r hL))ᶜ) := Fintype.ofFinite _
  -- `RegGaugeIdx ≃ range(embed) ⊕ range(embed)ᶜ` (sumCompl), reg-half `≃ BoundaryPivotIdx ≃ Fin nReg`
  -- (the SHARED `regPivotFinEquiv`), gauge-half `≃ Fin nGauge` (opaque enum on the complement).
  refine (Equiv.Set.sumCompl (Set.range (regBoundaryEmbed H r hL))).symm.trans ?_
  refine Equiv.sumCongr ?_ ?_
  · exact (Equiv.ofInjective _ (regBoundaryEmbed H r hL).injective).symm.trans
      (regPivotFinEquiv H r hr).symm
  · refine (Fintype.equivFin _).trans (finCongr ?_)
    have := card_compl_regBoundaryEmbed H r hr hL
    rwa [Nat.card_eq_fintype_card] at this

/-- **The role-respecting `Fin`-index equivalence** (the precision-pin core): `Fin (flatDim H) ≃
Fin nReg ⊕ (Fin (flatDim (deepestM H r)) ⊕ Fin nGauge)`, where the MIDDLE summand is the reduced `T`-core
(`= FlatIdx (deepestM)`) and the outer/right are the reg/gauge entries — slots BY ROLE, NOT arbitrary.
**The reg/gauge half is `regGaugeIdxSplit`** (NOT the opaque `Fintype.equivFin`): the SAME explicit split
`regGaugeSlotEquiv` un-flattens through, so the concrete `deepestSplit` decode and the slot reads share
one enumeration and the `gaugeReadX/Y/Z (deepestSplit w) = raw-deviation` round-trip cancels definitionally
(the PIN2 unblock — the prior opaque `Fintype.equivFin` made that round-trip non-definitional). Built
from `roleSplitIdx` (the role split) + `regGaugeIdxSplit` (reg-gauge) + `Fintype.equivFin` on the core +
`sumAssoc` + `sumComm`. -/
noncomputable def deepestRoleIndexEquiv (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) :
    Fin (flatDim H)
      ≃ Fin (deepestNReg H r) ⊕ (Fin (flatDim (deepestM H r)) ⊕ Fin (deepestNGauge H r)) := by
  -- `Fin (flatDim H) ≃ FlatIdx H ≃ RegGaugeIdx ⊕ FlatIdx (deepestM)`.
  refine (Fintype.equivFin (FlatIdx H)).symm.trans ((roleSplitIdx H r hr).trans ?_)
  -- RegGaugeIdx ≃ Fin nReg ⊕ Fin nGauge VIA `regGaugeIdxSplit` (the explicit, shared enumeration);
  -- FlatIdx (deepestM) ≃ Fin (flatDim M).
  have eReg : RegGaugeIdx H r ≃ Fin (deepestNReg H r) ⊕ Fin (deepestNGauge H r) :=
    regGaugeIdxSplit H r hr hL
  have eCore : FlatIdx (deepestM H r) ≃ Fin (flatDim (deepestM H r)) :=
    Fintype.equivFin (FlatIdx (deepestM H r))
  refine (Equiv.sumCongr eReg eCore).trans ?_
  -- (Fin nReg ⊕ Fin nGauge) ⊕ Fin (flatDim M) ≃ Fin nReg ⊕ (Fin (flatDim M) ⊕ Fin nGauge).
  refine (Equiv.sumAssoc _ _ _).trans (Equiv.sumCongr (Equiv.refl _) (Equiv.sumComm _ _))

/-- **The reg-gauge SLOT bridge** (crux2 #78, for cobuild-sub34's `gaugeDecode` reshape). The split's
two opaque function-slots recombine to the LEGIBLE per-layer `RegGaugeIdx` coordinate function:
`(Fin nReg → ℝ) × (Fin nGauge → ℝ) ≃ₜ (RegGaugeIdx H r → ℝ)`. The producer reads off the per-layer
`X_s/Y_s/Z_s` matrix blocks from `RegGaugeIdx` (the per-layer `Σ`), so this bridge is the stepping
stone from the split's `Fin nReg ⊕ Fin nGauge` slots to that legible Sigma BEFORE the matrix-block
reshape. `(Homeomorph.sumPiEquivProdPi).symm` (joins the two slots into `Fin nReg ⊕ Fin nGauge → ℝ`)
then `(Homeomorph.piCongrLeft regGaugeIdxSplit).symm` (relabels along the index split). -/
noncomputable def regGaugeSlotEquiv (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) :
    ((Fin (deepestNReg H r) → ℝ) × (Fin (deepestNGauge H r) → ℝ)) ≃ₜ (RegGaugeIdx H r → ℝ) :=
  (Homeomorph.sumPiEquivProdPi (Fin (deepestNReg H r)) (Fin (deepestNGauge H r))
      (fun _ => ℝ)).symm.trans
    (Homeomorph.piCongrLeft (Y := fun _ => ℝ) (regGaugeIdxSplit H r hr hL)).symm

/-- **Obligation (i) — the gauge-slice MP reindex exists** (the `split` field of `DeepestGaugeChart`).
At the deepest point, a measure-preserving homeomorphism
`split : (Fin (flatDim H) → ℝ) ≃ₜ DeepestSplit H r nGauge` carrying the flat image of the deepest point
to the split origin `0`, with `nGauge = deepestNGauge H r`. Per g159: `split = translation by
−flatDeepest, then a coordinate reindex (an honest finite-index `Equiv`), then unpacking `⊕` into the
product`. MP via translation invariance (`measurePreserving_sub_right`) + `volume_preserving_arrowCongr'`
(relabel, det = ±1) + `volume_measurePreserving_sumPiEquivProdPi` (the product unpack).

**The reindex is ROLE-RESPECTING** (the controller's precision pin): it is `deepestRoleIndexEquiv`, NOT
an arbitrary `equivOfCardEq` — the **core slot** is exactly the reduced `T`-blocks `= FlatIdx (deepestM
H r)` (type-forced), the regular/spectator slots the gauge `X/Y/Z` entries. So the slots carry the role
semantics the absorptions consume (`coreAbsorb` reads the `T`-core, `regAbsorb` reads the gauge entries
for `E`); a wrong (arbitrary) grouping would break them. -/
theorem deepestSplit_exists (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L)
    (wstar : Fin (flatDim H) → ℝ) :
    ∃ split : (Fin (flatDim H) → ℝ) ≃ₜ DeepestSplit H r (deepestNGauge H r),
      MeasurePreserving split volume volume ∧ split wstar = 0 := by
  classical
  set nReg := deepestNReg H r
  set nM := flatDim (deepestM H r)
  set nG := deepestNGauge H r
  -- (1) The ROLE-RESPECTING finite-index partition (the precision pin): the middle slot is the reduced
  -- `T`-core (`= FlatIdx (deepestM)`), NOT an arbitrary `equivOfCardEq`. `deepestRoleIndexEquiv`.
  let eIdx : Fin (flatDim H) ≃ Fin nReg ⊕ (Fin nM ⊕ Fin nG) := deepestRoleIndexEquiv H r hr hL
  -- (2) translation (MP, sends wstar ↦ 0), (3) relabel, (4) unpack `⊕` into the product.
  let tHom : (Fin (flatDim H) → ℝ) ≃ₜ (Fin (flatDim H) → ℝ) := Homeomorph.subRight wstar
  let relabel : (Fin (flatDim H) → ℝ) ≃ₜ (Fin nReg ⊕ (Fin nM ⊕ Fin nG) → ℝ) :=
    Homeomorph.piCongrLeft (Y := fun _ => ℝ) eIdx
  let unpackInner : (Fin nM ⊕ Fin nG → ℝ) ≃ₜ ((Fin nM → ℝ) × (Fin nG → ℝ)) :=
    Homeomorph.sumPiEquivProdPi (Fin nM) (Fin nG) (fun _ => ℝ)
  let unpack : (Fin nReg ⊕ (Fin nM ⊕ Fin nG) → ℝ) ≃ₜ DeepestSplit H r nG :=
    (Homeomorph.sumPiEquivProdPi (Fin nReg) (Fin nM ⊕ Fin nG) (fun _ => ℝ)).trans
      (Homeomorph.prodCongr (Homeomorph.refl _) unpackInner)
  refine ⟨tHom.trans (relabel.trans unpack), ?_, ?_⟩
  · -- MP: translation ∘ relabel ∘ unpack, each MP, composite MP (coerce `trans` to `∘`).
    have hmp_t : MeasurePreserving tHom volume volume := measurePreserving_sub_right volume wstar
    have hmp_relabel : MeasurePreserving relabel volume volume :=
      volume_measurePreserving_piCongrLeft (fun _ => ℝ) eIdx
    have hmp_unpackOuter :
        MeasurePreserving
          (Homeomorph.sumPiEquivProdPi (Fin nReg) (Fin nM ⊕ Fin nG) (fun _ => ℝ))
          volume volume :=
      volume_measurePreserving_sumPiEquivProdPi (fun _ : Fin nReg ⊕ (Fin nM ⊕ Fin nG) => ℝ)
    have hmp_unpackInner : MeasurePreserving unpackInner volume volume :=
      volume_measurePreserving_sumPiEquivProdPi (fun _ : Fin nM ⊕ Fin nG => ℝ)
    have hmp_prod :
        MeasurePreserving
          (⇑(Homeomorph.prodCongr (Homeomorph.refl (Fin nReg → ℝ)) unpackInner))
          volume volume := by
      simpa [Homeomorph.prodCongr] using (MeasurePreserving.id _).prod hmp_unpackInner
    have hmp_unpack : MeasurePreserving unpack volume volume := by
      rw [show (⇑unpack) = (⇑(Homeomorph.prodCongr (Homeomorph.refl (Fin nReg → ℝ)) unpackInner))
            ∘ (⇑(Homeomorph.sumPiEquivProdPi (Fin nReg) (Fin nM ⊕ Fin nG) (fun _ => ℝ)))
          from rfl]
      exact hmp_prod.comp hmp_unpackOuter
    rw [show (⇑(tHom.trans (relabel.trans unpack)))
          = (⇑unpack) ∘ (⇑relabel) ∘ (⇑tHom) from rfl]
    exact (hmp_unpack.comp hmp_relabel).comp hmp_t
  · -- basepoint: subRight wstar sends wstar ↦ 0; relabel/unpack are linear, send 0 ↦ 0.
    show unpack (relabel (tHom wstar)) = 0
    have ht0 : tHom wstar = 0 := by simp [tHom]
    rw [ht0]
    -- `relabel 0 = 0`: `piCongrLeft` recasts a constant-`0` function (cast of `0` is `0`).
    have hr0 : relabel (0 : Fin (flatDim H) → ℝ) = 0 := by
      ext j
      show (Equiv.piCongrLeft (fun _ => ℝ) eIdx) (0 : Fin (flatDim H) → ℝ) j = 0
      rw [Equiv.piCongrLeft_apply_eq_cast]; simp
    rw [hr0]
    -- `unpack 0 = 0`: the outer `sumPiEquivProdPi` and `unpackInner` each split `0 ↦ (0, 0)`.
    have hunpack0 : unpack (0 : Fin nReg ⊕ (Fin nM ⊕ Fin nG) → ℝ) = 0 := by
      have houter0 :
          (Homeomorph.sumPiEquivProdPi (Fin nReg) (Fin nM ⊕ Fin nG) (fun _ => ℝ))
            (0 : Fin nReg ⊕ (Fin nM ⊕ Fin nG) → ℝ) = 0 := by
        apply Prod.ext <;> ext j <;> rfl
      have hinner0 : unpackInner (0 : Fin nM ⊕ Fin nG → ℝ) = 0 := by
        apply Prod.ext <;> ext j <;> rfl
      show (Homeomorph.prodCongr (Homeomorph.refl _) unpackInner)
          ((Homeomorph.sumPiEquivProdPi (Fin nReg) (Fin nM ⊕ Fin nG) (fun _ => ℝ)) 0) = 0
      rw [houter0]
      apply Prod.ext
      · show (Homeomorph.refl (Fin nReg → ℝ))
            (0 : (Fin nReg → ℝ) × (Fin nM ⊕ Fin nG → ℝ)).1 = 0
        rw [Prod.fst_zero]; rfl
      · show unpackInner (0 : (Fin nReg → ℝ) × (Fin nM ⊕ Fin nG → ℝ)).2 = 0
        rw [Prod.snd_zero, hinner0]
    exact hunpack0

end DLNFibre.DLN.RLCT
