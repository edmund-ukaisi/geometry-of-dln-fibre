import DLNFibre.DLN.RLCT.Validate.RouteMFlatLive

/-!
# `RouteMLayerGrade` — Route (b) b-0: layer grading `bLayer` + reader-boundary locality (VERIFY-1)

The cheapest discriminating kill-check for Route (b) (the fused-frame layer-filtration block-tri det),
done BEFORE building the general fused frame `Frame_M`/`DFrame_M`. F1 (composeFold-of-disjoint-factors)
is DEAD (the chain accumulator couples boundaries). Route (b) keeps the FULL fused matrix and exploits
that the coupling is DET-IRRELEVANT (it lives in the off-diagonal blocks of a LAYER-graded
block-triangular matrix; `BlockTriangular.det = ∏ diagonal-block dets`).

This module supplies the GRADING + the abstract ONE-SIDED-DEPENDENCY fact the block-triangularity rests
on, stated against the EXISTING decoder/readers (no new fused frame needed yet):

* `bLayer M t ha q` — the chain-layer/boundary a flat coordinate `q` belongs to:
  `(chartIdxEquiv … q).fst.val`.
* `readK_indep_of` / `readX_…` / `readN_…` / `readE_…` / `readW_…` — each boundary-`k` reader is
  INVARIANT under changing `x` only away from layer `k` (the off-block-vanishing at the reader level:
  the reader reads ONE slot, of layer `k`; `apply_symm_apply` + `chartIdxEquiv` injectivity).

**The VERIFY-1 verdict (the kill-check).** The chart's output layer `s` is `chartParamsGen ⟨s⟩ =
reindex (Agen s.val)`. `Cgen k = Bmat k·chainQ(N_k) + u·Rmat k` is NON-recursive (reads only GenBlk-index
`k`), and `Agen s = chainA(Nblk s, Wblk s, Cgen (s+1))` reads GenBlk-indices `{s, s+1}`. The decoder block
at GenBlk-index `(j+1)` reads chart-slot `⟨j⟩` (layer `j`); index `0` is the constant identity boundary.
So output layer `s` reads input layers `{s−1, s} ⊆ [0, s]` — NEVER a later layer. The dependency is
ONE-SIDED (LOWER-triangular under `bLayer`): `bLayer j > bLayer i ⟹ DFrame entry (i,j) = 0` (note: LOWER,
i.e. `toDual`, NOT the upper form the build-spec wrote — the GenBlk-index = chart-slot + 1 shift flips the
side; either way one-sided ⟹ det = ∏ diagonal blocks). NOT two-sided ⟹ Route (b) is SOUND. The diagonal
block at layer `s` (the within-layer Schur frame) reads boundary `s`'s `K`-block ALONE (VERIFY-2: `K_s`
single-layer ✓). See `item3-route-b-buildspec.md`.

Axiom-clean `[propext, Classical.choice, Quot.sound]` (finite equivalences; no analysis).
-/

namespace DLNFibre.DLN.RLCT

open scoped BigOperators

variable {L : ℕ}
variable {𝕜 : Type} [CommRing 𝕜]

/-! ## The layer grading -/

/-- **The layer grading** `bLayer M t ha q` — the chain-layer / boundary index `k : Fin L` that the
flat coordinate `q` belongs to, read off `chartIdxEquiv`'s `ChartIdx = Σ k : Fin L, …` first component.
The `LinearOrder ℕ` grading `Matrix.BlockTriangular.det` consumes (b-3). -/
noncomputable def bLayer (M : Fin (L + 1) → ℕ) (t : Fin (L + 1) → ℕ) (ha : StructAdm M t)
    (q : Fin (routeMAmbient M)) : ℕ :=
  ((chartIdxEquiv M (tDesc M t) ha.h0 ha.hc ha.hL) q).fst.val

/-- **`bLayer < L`** — every flat coordinate sits at a layer in `[0, L)` (the grading is `Fin L`-valued
under the hood). Confirms `bLayer` is the genuine boundary index, not a stray `ℕ`. -/
theorem bLayer_lt (M t : Fin (L + 1) → ℕ) (ha : StructAdm M t) (q : Fin (routeMAmbient M)) :
    bLayer M t ha q < L :=
  ((chartIdxEquiv M (tDesc M t) ha.h0 ha.hc ha.hL) q).fst.isLt

/-! ## Reader-boundary locality (the off-block-vanishing, at the reader level)

Each boundary-`k` reader reads `x` at exactly ONE flat slot, whose `bLayer` is `k` (the
`chartIdxEquiv.symm ⟨k, …⟩` round-trip). Hence if `x` and `y` agree on every coord of layer `k`, the
reader returns the same value — it is INVARIANT under any change away from layer `k`. This is the
∂(reader)/∂(off-layer coord) = 0 fact, the seed of the fused frame's off-block-vanishing. -/

variable (M t : Fin (L + 1) → ℕ) (ha : StructAdm M t)

/-- **The `K`-reader of boundary `k` is invariant under changing `x` away from layer `k`.** -/
theorem readK_indep_of (x y : Fin (routeMAmbient M) → 𝕜) (k : Fin L)
    (h : ∀ q, bLayer M t ha q = k.val → x q = y q) (i j : Fin (Text M t (k.val + 2))) :
    readK M t ha x k i j = readK M t ha y k i j := by
  rw [readK, readK]
  apply h
  rw [bLayer, Equiv.apply_symm_apply]

/-- **The `X`-reader of boundary `k` is invariant under changing `x` away from layer `k`.** -/
theorem readX_indep_of (x y : Fin (routeMAmbient M) → 𝕜) (k : Fin L)
    (h : ∀ q, bLayer M t ha q = k.val → x q = y q)
    (i : Fin (Text M t (k.val + 1) - Text M t (k.val + 2))) (j : Fin (Text M t (k.val + 2))) :
    readX M t ha x k i j = readX M t ha y k i j := by
  rw [readX, readX]
  apply h
  rw [bLayer, Equiv.apply_symm_apply]

/-- **The `N`-reader of boundary `k` is invariant under changing `x` away from layer `k`.** -/
theorem readN_indep_of (x y : Fin (routeMAmbient M) → 𝕜) (k : Fin L)
    (h : ∀ q, bLayer M t ha q = k.val → x q = y q)
    (i : Fin (Text M t (k.val + 2))) (j : Fin (Wext M (k.val + 1) - Text M t (k.val + 2))) :
    readN M t ha x k i j = readN M t ha y k i j := by
  rw [readN, readN]
  apply h
  rw [bLayer, Equiv.apply_symm_apply]

/-- **The `E`-reader of boundary `k` is invariant under changing `x` away from layer `k`.** -/
theorem readE_indep_of (x y : Fin (routeMAmbient M) → 𝕜) (k : Fin L)
    (h : ∀ q, bLayer M t ha q = k.val → x q = y q)
    (i : Fin (Text M t (k.val + 1) - Text M t (k.val + 2)))
    (j : Fin (Wext M (k.val + 1) - Text M t (k.val + 2))) :
    readE M t ha x k i j = readE M t ha y k i j := by
  rw [readE, readE]
  apply h
  rw [bLayer, Equiv.apply_symm_apply]

/-- **The lift `W`-reader of boundary `k` is invariant under changing `x` away from layer `k`.** -/
theorem readW_indep_of (x y : Fin (routeMAmbient M) → 𝕜) (k : Fin L) (hk : k.val + 1 < L)
    (h : ∀ q, bLayer M t ha q = k.val → x q = y q)
    (i : Fin (Wext M (k.val + 1) - Text M t (k.val + 2))) (j : Fin (Wext M (k.val + 2))) :
    readW M t ha x k hk i j = readW M t ha y k hk i j := by
  rw [readW, readW]
  apply h
  rw [bLayer, Equiv.apply_symm_apply]

/-! ## Decoder-block layer-locality (the off-block-vanishing, at the GenBlk-block level)

The structured decoder's interior block at GenBlk-index `(j+1)` is assembled from the boundary-`j`
readers (`Bmat = bmatStack(readK, readX)`, `Nblk = readN`, `Wblk = readW`, `Rmat = rmatPad(readE)`), so
it is INVARIANT under changing `x` away from layer `j`. Threads the reader-locality lemmas through the
block constructors. (The identity boundary `j = 0` blocks are constant, trivially invariant.) This is the
∂(block)/∂(off-layer coord) = 0 fact — the genuine kill-check content one index above the readers. -/

/-- **The structured decoder's `Bmat (j+1)` is invariant under changing `x` away from layer `j`.**
`bmatStack` of the layer-`j` `readK`/`readX`; the off-layer change leaves both readers fixed. -/
theorem genBlkFlatStruct_Bmat_indep_of (x y : Fin (routeMAmbient M) → ℝ) (j : ℕ) (hj : j < L)
    (h : ∀ q, bLayer M t ha q = j → x q = y q) :
    (genBlkFlatStruct M t ha x).Bmat (j + 1) = (genBlkFlatStruct M t ha y).Bmat (j + 1) := by
  have hK : readK M t ha x (⟨j, hj⟩ : Fin L) = readK M t ha y ⟨j, hj⟩ := by
    funext i jj; exact readK_indep_of M t ha x y ⟨j, hj⟩ h i jj
  have hX : readX M t ha x (⟨j, hj⟩ : Fin L) = readX M t ha y ⟨j, hj⟩ := by
    funext i jj; exact readX_indep_of M t ha x y ⟨j, hj⟩ h i jj
  simp only [genBlkFlatStruct, dif_pos hj, hK, hX]

/-- **The structured decoder's `Nblk (j+1)` is invariant under changing `x` away from layer `j`.** -/
theorem genBlkFlatStruct_Nblk_indep_of (x y : Fin (routeMAmbient M) → ℝ) (j : ℕ) (hj : j < L)
    (h : ∀ q, bLayer M t ha q = j → x q = y q) :
    (genBlkFlatStruct M t ha x).Nblk (j + 1) = (genBlkFlatStruct M t ha y).Nblk (j + 1) := by
  have hN : readN M t ha x (⟨j, hj⟩ : Fin L) = readN M t ha y ⟨j, hj⟩ := by
    funext i jj; exact readN_indep_of M t ha x y ⟨j, hj⟩ h i jj
  simp only [genBlkFlatStruct, dif_pos hj, hN]

/-- **The structured decoder's `Rmat (j+1)` is invariant under changing `x` away from layer `j`.** -/
theorem genBlkFlatStruct_Rmat_indep_of (x y : Fin (routeMAmbient M) → ℝ) (j : ℕ) (hj : j < L)
    (h : ∀ q, bLayer M t ha q = j → x q = y q) :
    (genBlkFlatStruct M t ha x).Rmat (j + 1) = (genBlkFlatStruct M t ha y).Rmat (j + 1) := by
  have hE : readE M t ha x (⟨j, hj⟩ : Fin L) = readE M t ha y ⟨j, hj⟩ := by
    funext i jj; exact readE_indep_of M t ha x y ⟨j, hj⟩ h i jj
  simp only [genBlkFlatStruct, dif_pos hj, hE]

/-- **The structured decoder's `Wblk (j+1)` is invariant under changing `x` away from layer `j`.** -/
theorem genBlkFlatStruct_Wblk_indep_of (x y : Fin (routeMAmbient M) → ℝ) (j : ℕ) (hj : j < L)
    (h : ∀ q, bLayer M t ha q = j → x q = y q) :
    (genBlkFlatStruct M t ha x).Wblk (j + 1) = (genBlkFlatStruct M t ha y).Wblk (j + 1) := by
  by_cases hk2 : j + 1 < L
  · have hW : readW M t ha x (⟨j, hj⟩ : Fin L) hk2 = readW M t ha y ⟨j, hj⟩ hk2 := by
      funext i jj; exact readW_indep_of M t ha x y ⟨j, hj⟩ hk2 h i jj
    simp only [genBlkFlatStruct, dif_pos hj, dif_pos hk2, hW]
  · simp only [genBlkFlatStruct, dif_pos hj, dif_neg hk2]

/-! ## The VERIFY-1 capstone: the chart layer `Agen s` reads ONLY layers `≤ s` (off-block-vanishing)

The decisive kill-check. `Agen s = chainA(Nblk s, Wblk s, Cgen (s+1))`, and `Cgen (s+1) = Bmat (s+1) ·
chainQ(Nblk (s+1)) + u·Rmat (s+1)`. The interior blocks at GenBlk-index `(j+1)` read only layer `j`
(the block-locality lemmas above); the identity-boundary blocks at index `0` are constant. So `Agen s`
reads GenBlk-indices `{s, s+1}` = layers `⊆ [0, s]` — NEVER a later layer. Stated as: if `x` and `y`
agree on every coord of layer `≤ s`, the layer-`s` chart parameter is unchanged. This is exactly
`∂(output layer s)/∂(input coord at layer > s) = 0` — the off-block-vanishing the fused frame
`DFrame_M`'s block-triangularity will state pointwise. SOUND (one-sided, lower-triangular). -/

/-- **VERIFY-1 (the kill-check): `Agen` of the structured chart at layer `s` reads only layers `≤ s`.**
If `x` and `y` agree on every coordinate at layer `≤ s`, then `Agen u … (genBlkFlatStruct … x) … s =
Agen … y … s`. The layer-`s` output depends on NO later layer — the dependency is one-sided
(lower-triangular under `bLayer`), so Route (b)'s block-triangular det is sound. -/
theorem Agen_genBlkFlatStruct_reads_le (u : ℝ) (x y : Fin (routeMAmbient M) → ℝ) (s : ℕ)
    (h : ∀ q, bLayer M t ha q ≤ s → x q = y q) :
    Agen u M t (genBlkFlatStruct M t ha x) (hleStruct M t ha) s
      = Agen u M t (genBlkFlatStruct M t ha y) (hleStruct M t ha) s := by
  by_cases hs : s < L
  · -- the five blocks `Agen s` reads: `Nblk s`, `Wblk s` (index `s`), and via `Cgen (s+1)`:
    -- `Bmat (s+1)`, `Nblk (s+1)`, `Rmat (s+1)` (index `s+1`).
    have hNs : (genBlkFlatStruct M t ha x).Nblk s = (genBlkFlatStruct M t ha y).Nblk s := by
      match s with
      | 0 => rfl
      | (j + 1) =>
        exact genBlkFlatStruct_Nblk_indep_of M t ha x y j (by omega)
          (fun q hq => h q (by omega))
    have hWs : (genBlkFlatStruct M t ha x).Wblk s = (genBlkFlatStruct M t ha y).Wblk s := by
      match s with
      | 0 => rfl
      | (j + 1) =>
        exact genBlkFlatStruct_Wblk_indep_of M t ha x y j (by omega)
          (fun q hq => h q (by omega))
    have hBs1 : (genBlkFlatStruct M t ha x).Bmat (s + 1) = (genBlkFlatStruct M t ha y).Bmat (s + 1) :=
      genBlkFlatStruct_Bmat_indep_of M t ha x y s hs (fun q hq => h q (by omega))
    have hNs1 : (genBlkFlatStruct M t ha x).Nblk (s + 1) = (genBlkFlatStruct M t ha y).Nblk (s + 1) :=
      genBlkFlatStruct_Nblk_indep_of M t ha x y s hs (fun q hq => h q (by omega))
    have hRs1 : (genBlkFlatStruct M t ha x).Rmat (s + 1) = (genBlkFlatStruct M t ha y).Rmat (s + 1) :=
      genBlkFlatStruct_Rmat_indep_of M t ha x y s hs (fun q hq => h q (by omega))
    -- assemble: `Agen s` and `Cgen (s+1)` agree because all the blocks they read agree.
    have hCs1 : Cgen u M t (genBlkFlatStruct M t ha x) (hleStruct M t ha) (s + 1)
        = Cgen u M t (genBlkFlatStruct M t ha y) (hleStruct M t ha) (s + 1) := by
      by_cases hs1 : s + 1 < L
      · simp only [Cgen, dif_pos hs1, hBs1, hNs1, hRs1]
      · -- the leaf `Cgen L = u • Rfin L`; `Rfin = fun _ => 0` on both decoders (constant).
        simp only [Cgen, dif_neg hs1,
          show (genBlkFlatStruct M t ha x).Rfin (s + 1) = (genBlkFlatStruct M t ha y).Rfin (s + 1)
            from rfl]
    simp only [Agen, dif_pos hs, hNs, hWs, hCs1]
  · simp only [Agen, dif_neg hs]

end DLNFibre.DLN.RLCT
