import DLNFibre.DLN.RLCT.Validate.RouteMChartSlots
import DLNFibre.DLN.RLCT.Validate.RouteMGenChartId
import DLNFibre.DLN.RLCT.Validate.RouteMGenFlatChart
import DLNFibre.DLN.RLCT.Validate.RouteMGenChainBridge

/-!
# `RouteMGenFlatStruct` — the STRUCTURED achiever-chart decoder (the item-3 unblock)

The structured flat decoder `genBlkFlatStruct`, replacing the diagnosed over-determined modular-hash
`genBlkFlat` (`RouteMGenFlatChart`). It reads the genuine FREE coordinates (the Schur-frame `K/X/N/E`
roles + the lift `W`, per boundary) from DISJOINT flat slots via the banked `chartIdxEquiv`
coordinatization (`RouteMChartSlots`), and DERIVES the `GenBlk` block data via the Schur-frame
structure: `Bmat (k+1) = [K ; X·K]` (`bmatStack`), `Rmat (k+1) = [[0,0],[0,E]]` (`rmatPad`), so
`C_{k+1} = Bmat·chainQ(N) + u·Rmat = [[K, KN],[XK, XKN + uE]]` (the Schur frame). The `K` block is kept
DIRECT (the LDU reparametrization is the job of the `composeFold` LDU factor, item 2 — matched in
item 3). The identity boundary `k = 0` is `Bmat 0 = I`, `Rmat 0 = 0`.

Indexing: GenBlk boundary `s = k+1` reads chart-slot `k` (the `s = k+1` form makes
`schurDim k = Text(k+1)·Wext(k+1)` `rfl`-clean — no `s−1`-through-`dite` HEq friction). The `t`-arity
bridge is `tDesc := fun j => Text M t (j+1)` (the ℕ→ℕ descent `schurDim`/`chartIdxEquiv` consume).

This module is the decoder + (next) its rate transfer (via the decoder-agnostic `routeMCore_phiGen`,
re-checking only `hC0`). The factored chart + item-3 map equality + the leafH summation build on it.

Axiom-clean `[propext, Classical.choice, Quot.sound]` (pure matrix algebra / finite equivalences).
-/

namespace DLNFibre.DLN.RLCT

open Matrix

variable {L : ℕ}

/-! ## The descent-bridge + the per-boundary admissibility hypotheses

`tDesc M t := fun j => Text M t (j+1)` is the ℕ→ℕ descent the slot API consumes (`Text(k+1)` at index
`k`). The structured decoder needs the achiever descent `Text(k+2) ≤ Text(k+1)` (strictly decreasing
`t`) for the `Bmat`/`Rmat` block splits — beyond the chain's `hle : Text(k+1) ≤ Wext k`. -/

/-- The ℕ→ℕ descent bridge `tDesc k = Text M t (k+1)` — what `schurDim`/`chartIdxEquiv`/`frameSplitEquiv`
read (the slot API is ℕ-indexed; `Text` is `Fin (L+1) → ℕ`-indexed). -/
def tDesc (M : Fin (L + 1) → ℕ) (t : Fin (L + 1) → ℕ) : ℕ → ℕ := fun j => Text M t (j + 1)

@[simp] theorem tDesc_apply (M t : Fin (L + 1) → ℕ) (j : ℕ) : tDesc M t j = Text M t (j + 1) := rfl

/-- `schurDim (tDesc) k = Text(k+1)·Wext(k+1)` — `rfl`-clean (the `s = k+1` indexing payoff). -/
theorem schurDim_tDesc (M t : Fin (L + 1) → ℕ) (k : ℕ) :
    schurDim M (tDesc M t) k = Text M t (k + 1) * Wext M (k + 1) := rfl

/-- Under `tDesc 0 = M 0` (the `h0` side condition), `Text 0 = Text 1` (the identity-boundary
square-ness for `Bmat 0 = I`). `tDesc 0 = Text 1` by `rfl`, so `Text 1 = M 0 = Text 0`. -/
theorem Text0_eq_Text1_struct (M t : Fin (L + 1) → ℕ) (hh0 : tDesc M t 0 = M 0) :
    Text M t 0 = Text M t 1 := by
  rw [Text_zero]; exact hh0.symm

/-! ## The bundled admissibility hypotheses

The structured decoder threads: the chart coordinatization side conditions (`h0`, `hc`, `hL` for
`chartIdxEquiv`) + the descent `hdesc k : Text(k+2) ≤ Text(k+1)` and `hub k : Text(k+2) ≤ Wext(k+1)`
(for the `frameSplitEquiv`/`bmatStack`/`rmatPad` block splits). Bundle them once. -/

/-- The structured decoder's admissibility bundle for `M`, `t`. -/
structure StructAdm (M : Fin (L + 1) → ℕ) (t : Fin (L + 1) → ℕ) : Prop where
  /-- `chartIdxEquiv` boundary: `tDesc 0 = M 0`. -/
  h0 : tDesc M t 0 = M 0
  /-- `chartIdxEquiv` upper bound: `tDesc (p+1) ≤ Wext (p+1)`. -/
  hc : ∀ p, tDesc M t (p + 1) ≤ Wext M (p + 1)
  /-- positive depth. -/
  hL : 0 < L
  /-- the achiever descent `Text(k+2) ≤ Text(k+1)` (`t` weakly decreasing). -/
  hdesc : ∀ k, Text M t (k + 2) ≤ Text M t (k + 1)
  /-- the residual-column bound `Text(k+2) ≤ Wext(k+1)`. -/
  hub : ∀ k, Text M t (k + 2) ≤ Wext M (k + 1)

/-! ## The matrix-block readers (K / X / N / E from the frame slot; W from the lift slot)

Each reader reads a role-block matrix from DISJOINT flat coords: inject the `(i,j)` matrix index by
`finProdFinEquiv`, place it in the right `frameSplitEquiv` sub-block, pull back through
`frameSplitEquiv.symm` to the `schurDim k` slot, then `chartIdxEquiv.symm ⟨k, Sum.inl ·⟩` and read `x`.
Disjoint by `chartIdxEquiv`'s injectivity + the role sub-block disjointness. -/

variable (M t : Fin (L + 1) → ℕ) (ha : StructAdm M t) (x : Fin (routeMAmbient M) → ℝ)

/-- Read the Schur-frame `K` block (`Text(k+2) × Text(k+2)`) of GenBlk boundary `s = k+1`. -/
noncomputable def readK (k : Fin L) (i j : Fin (Text M t (k.val + 2))) : ℝ :=
  x ((chartIdxEquiv M (tDesc M t) ha.h0 ha.hc ha.hL).symm
    ⟨k, Sum.inl ((frameSplitEquiv M t (k.val + 1) (ha.hdesc k.val) (ha.hub k.val)).symm
      (Sum.inl (Sum.inl (Sum.inl (finProdFinEquiv (i, j))))))⟩)

/-- Read the Schur-frame `X` block (`(Text(k+1)−Text(k+2)) × Text(k+2)`). -/
noncomputable def readX (k : Fin L)
    (i : Fin (Text M t (k.val + 1) - Text M t (k.val + 2))) (j : Fin (Text M t (k.val + 2))) : ℝ :=
  x ((chartIdxEquiv M (tDesc M t) ha.h0 ha.hc ha.hL).symm
    ⟨k, Sum.inl ((frameSplitEquiv M t (k.val + 1) (ha.hdesc k.val) (ha.hub k.val)).symm
      (Sum.inl (Sum.inl (Sum.inr (finProdFinEquiv (i, j))))))⟩)

/-- Read the Schur-frame `N` block (`Text(k+2) × (Wext(k+1)−Text(k+2))`). -/
noncomputable def readN (k : Fin L)
    (i : Fin (Text M t (k.val + 2))) (j : Fin (Wext M (k.val + 1) - Text M t (k.val + 2))) : ℝ :=
  x ((chartIdxEquiv M (tDesc M t) ha.h0 ha.hc ha.hL).symm
    ⟨k, Sum.inl ((frameSplitEquiv M t (k.val + 1) (ha.hdesc k.val) (ha.hub k.val)).symm
      (Sum.inl (Sum.inr (finProdFinEquiv (i, j)))))⟩)

/-- Read the Schur-frame `E` block (`(Text(k+1)−Text(k+2)) × (Wext(k+1)−Text(k+2))`). -/
noncomputable def readE (k : Fin L)
    (i : Fin (Text M t (k.val + 1) - Text M t (k.val + 2)))
    (j : Fin (Wext M (k.val + 1) - Text M t (k.val + 2))) : ℝ :=
  x ((chartIdxEquiv M (tDesc M t) ha.h0 ha.hc ha.hL).symm
    ⟨k, Sum.inl ((frameSplitEquiv M t (k.val + 1) (ha.hdesc k.val) (ha.hub k.val)).symm
      (Sum.inr (finProdFinEquiv (i, j))))⟩)

/-- Read the lift `W` block of GenBlk boundary `s = k+1` (`(Wext(k+1)−Text(k+2)) × Wext(k+2)`), from
the lift slot `liftDim k`. -/
noncomputable def readW (k : Fin L) (hk : k.val + 1 < L)
    (i : Fin (Wext M (k.val + 1) - Text M t (k.val + 2))) (j : Fin (Wext M (k.val + 2))) : ℝ :=
  x ((chartIdxEquiv M (tDesc M t) ha.h0 ha.hc ha.hL).symm
    ⟨k, Sum.inr ((liftSlotEquiv M (tDesc M t) k.val hk).symm (i, j))⟩)

/-! ## The structured decoder `genBlkFlatStruct`

Assembles the `GenBlk M t` from the readers: identity boundary `k = 0` (`Bmat 0 = reindex 1`,
`Rmat 0 = 0`); interior `k+1` (`Bmat (k+1) = bmatStack (readK) (readX)`,
`Rmat (k+1) = rmatPad (readE)`, `Nblk (k+1) = readN`, `Wblk (k+1) = readW`). Out-of-range `k` and the
`Nblk 0`/`Wblk 0` empty slots are filled with `0` (irrelevant — the identity boundary's `c_0 = 0`). -/

/-- The structured flat decoder `genBlkFlatStruct M t ha x : GenBlk M t` — reads the free
Schur/lift coords from disjoint slots (`readK/X/N/E/W`) and derives the `GenBlk` blocks via the
Schur frame (`bmatStack`/`rmatPad`), identity at `k = 0`. -/
noncomputable def genBlkFlatStruct : GenBlk M t where
  Bmat := fun k => match k with
    | 0 => Matrix.reindex (Equiv.refl _) (finCongr (Text0_eq_Text1_struct M t ha.h0))
        (1 : Matrix (Fin (Text M t 0)) (Fin (Text M t 0)) ℝ)
    | (k + 1) =>
      if hk : k < L then
        bmatStack M t (k + 1) (ha.hdesc k) (readK M t ha x ⟨k, hk⟩) (readX M t ha x ⟨k, hk⟩)
      else 0
  Nblk := fun k => match k with
    | 0 => 0
    | (k + 1) =>
      if hk : k < L then readN M t ha x ⟨k, hk⟩ else 0
  Wblk := fun k => match k with
    | 0 => 0
    | (k + 1) =>
      if hk : k < L then
        (if hk2 : k + 1 < L then readW M t ha x ⟨k, hk⟩ hk2 else 0) else 0
  Rmat := fun k => match k with
    | 0 => (0 : Matrix (Fin (Text M t 0)) (Fin (Wext M 0)) ℝ)
    | (k + 1) =>
      if hk : k < L then rmatPad M t (k + 1) (ha.hdesc k) (ha.hub k) (readE M t ha x ⟨k, hk⟩) else 0
  Rfin := fun _ => 0

/-! ## The rate transfer (the chain admissibility + the chart + the conditional rate)

The structured decoder feeds the decoder-agnostic rate engine `routeMCore_phiGen`. `hleStruct` derives
the chain admissibility from `StructAdm`; `Wext0_eq_Text1` is the identity-boundary `c_0 = 0`. The
chart `phiFlatStruct` and its rate `routeMCore = u²·V` follow from `routeMCore_phiGen` given `hC0`
(the identity-boundary `C 0 · suffix = suffix`; `Bmat 0 = reindex 1`, `Rmat 0 = 0`, `chainQ(N_0) = I`
at `c_0 = 0`). -/

/-- The chain admissibility `hle : Text(k+1) ≤ Wext k` for `chartParamsGen`, from `StructAdm`. -/
theorem hleStruct (M t : Fin (L + 1) → ℕ) (ha : StructAdm M t) :
    ∀ k, k < L → Text M t (k + 1) ≤ Wext M k := by
  intro k _
  match k with
  | 0 =>
    rw [show Wext M 0 = M 0 from by rw [Wext]; simp]
    have h := ha.h0; rw [tDesc_apply] at h; rw [h]
  | (k + 1) => exact ha.hub k

/-- The identity boundary has `c_0 = 0` (`Wext 0 = Text 1`, from `t_0 = M_0`). -/
theorem Wext0_eq_Text1 (M t : Fin (L + 1) → ℕ) (ha : StructAdm M t) : Text M t 1 = Wext M 0 := by
  have h := ha.h0; rw [tDesc_apply] at h
  rw [show Wext M 0 = M 0 from by rw [Wext]; simp, h]

/-- **The identity boundary `C 0 = 1`** (square `Text 0` type): `Bmat 0 · chainQ(N_0) + u·Rmat 0 =
(reindex 1)·(I at c_0=0) + 0 = 1`. The `chainQ` kept-column law (`chainQ_apply_castAdd`, every column a
kept column at `c_0 = 0`) + the `Text 0 = Text 1 = Wext 0` cast collapse. -/
theorem C0_eq_one (M t : Fin (L + 1) → ℕ) (ha : StructAdm M t) (u : ℝ) :
    (chainOfMt u M t (genBlkFlatStruct M t ha (fun _ => u)) (hleStruct M t ha)).toChain.C 0
      = (1 : Matrix (Fin (Text M t 0)) (Fin (Text M t 0)) ℝ) := by
  rw [chainOfMt_C_zero u M t _ (hleStruct M t ha) ha.hL,
    show (genBlkFlatStruct M t ha (fun _ => u)).Rmat 0 = 0 from rfl, smul_zero, add_zero]
  have h1W : Text M t 1 = Wext M 0 := Wext0_eq_Text1 M t ha
  have hBmat : (genBlkFlatStruct M t ha (fun _ => u)).Bmat 0
      = Matrix.reindex (Equiv.refl _) (finCongr (Text0_eq_Text1_struct M t ha.h0))
          (1 : Matrix (Fin (Text M t 0)) (Fin (Text M t 0)) ℝ) := rfl
  rw [hBmat]
  ext i j
  rw [Matrix.mul_apply, Finset.sum_eq_single (Fin.cast (Text0_eq_Text1_struct M t ha.h0) i)]
  · rw [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.refl_symm, Equiv.refl_apply,
      finCongr_symm, finCongr_apply, Fin.cast_cast, Fin.cast_eq_self, Matrix.one_apply_eq, one_mul]
    have hjcol : (j : Fin (Wext M 0)) = Fin.cast (genWidthEq M t (hleStruct M t ha) 0 ha.hL)
        (Fin.castAdd (Wext M 0 - Text M t (0 + 1)) (Fin.cast h1W.symm j)) := by
      apply Fin.ext; simp
    rw [hjcol, chainQ_apply_castAdd, Matrix.one_apply, Matrix.one_apply]
    by_cases h : (i : ℕ) = (j : ℕ)
    · rw [if_pos (by apply Fin.ext; simpa using h), if_pos (by apply Fin.ext; simpa using h)]
    · rw [if_neg (by intro hc; exact h (by simpa using congrArg Fin.val hc)),
        if_neg (by intro hc; exact h (by simpa using congrArg Fin.val hc))]
  · intro b _ hb
    rw [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.refl_symm, Equiv.refl_apply,
      finCongr_symm, finCongr_apply]
    rw [show (1 : Matrix (Fin (Text M t 0)) (Fin (Text M t 0)) ℝ) i
          (Fin.cast (Text0_eq_Text1_struct M t ha.h0).symm b) = 0 from by
      rw [Matrix.one_apply, if_neg]; intro hc; apply hb; rw [hc]; apply Fin.ext; simp]
    rw [zero_mul]
  · intro hi; exact absurd (Finset.mem_univ _) hi

/-- **`hC0` for the structured decoder** (unconditional): `C 0 · suffix 0 = suffix 0` (`C 0 = 1`). -/
theorem hC0_struct (M t : Fin (L + 1) → ℕ) (ha : StructAdm M t) (u : ℝ) :
    (chainOfMt u M t (genBlkFlatStruct M t ha (fun _ => u)) (hleStruct M t ha)).toChain.C 0
        * (chainOfMt u M t (genBlkFlatStruct M t ha (fun _ => u))
            (hleStruct M t ha)).toChain.suffix 0 (Nat.zero_le L)
      = (chainOfMt u M t (genBlkFlatStruct M t ha (fun _ => u))
          (hleStruct M t ha)).toChain.suffix 0 (Nat.zero_le L) := by
  rw [C0_eq_one M t ha u]
  exact Matrix.one_mul _

/-- **The structured flat chart** `phiFlatStruct := paramsEquivFlat ∘ chartParamsGen ∘ genBlkFlatStruct`
(binding pivot the radial `u`). -/
noncomputable def phiFlatStruct (M t : Fin (L + 1) → ℕ) (ha : StructAdm M t) (u : ℝ) :
    Fin (routeMAmbient M) → ℝ :=
  phiGen u M t (genBlkFlatStruct M t ha (fun _ => u)) (hleStruct M t ha)

/-- **The rate transfers to the structured chart** (UNCONDITIONAL): `routeMCore M (phiFlatStruct u) =
u²·VvalGen`, via the decoder-agnostic banked `routeMCore_phiGen` + the proven `hC0_struct`. The
structured decoder keeps the rate ∀M. -/
theorem routeMCore_phiFlatStruct (M t : Fin (L + 1) → ℕ) (ha : StructAdm M t) (u : ℝ) :
    routeMCore M (phiFlatStruct M t ha u)
      = u ^ 2 * VvalGen u M t (genBlkFlatStruct M t ha (fun _ => u)) (hleStruct M t ha) :=
  routeMCore_phiGen u M t (genBlkFlatStruct M t ha (fun _ => u)) (hleStruct M t ha)
    (hC0_struct M t ha u)

end DLNFibre.DLN.RLCT
