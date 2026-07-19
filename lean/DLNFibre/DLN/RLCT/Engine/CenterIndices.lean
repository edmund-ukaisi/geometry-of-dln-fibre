import DLNFibre.DLN.RLCT.Engine.EngineConstruction

/-!
# `DLNFibre.DLN.RLCT.Engine.CenterIndices` — the arithmetic center-coordinate selector (carrier)

The carrier's coordinate-layout piece (elder-gate9, tick-208): `centerIndices` maps a blow-up node's
residual-block index to its flat coordinate in `Fin (flatDim M)`, against the `FlatIdx` sigma encoding
(`ParamsFlat`: a flat coord is `(layer s, row i < M s.castSucc, col j < M s.succ)` = the `(i,j)` entry
of the `s`-th weight matrix). Coverage's `centerSplit`/`q_node` (or my `qNodeOf` assembly) is built
FROM this selector.

**Scope (elder-gate9 split):** the residual/d-block selector (case-2 + the case-1(2) d-family) is
PURE ARITHMETIC — built here. The case-1(1) `u`-pivot is an EXISTING divisor coordinate (ledger-tied,
held on the slot-stability page-check); `qNodeOf` takes the `u`-coordinate as a PARAMETER of the
case-1 shape so this arithmetic part does not block on it (tick-208).

Per-edge `d_center` counts (elder-gate9 amendment 1): case-1(1) edge = 1 (the `u`-pivot), case-1(2)
edge = `runLen·resCols` (the d-family), case-2 edge = `resRows·resCols`, rollover = 0. Node `d_center`
= the sum; NEVER emit the node total on the case-1(2) edge (double-counts `u`).
-/

namespace DLNFibre.DLN.RLCT.Engine

open DLNFibre.DLN.RLCT

variable {L : ℕ}

/-- **The flat coordinate of a matrix entry** `(s, i, j)` — the `(i,j)` entry of the `s`-th weight
matrix — as an index in `Fin (flatDim M)`, via the `FlatIdx` sigma re-index `paramsEquivFlat` uses. -/
noncomputable def flatCoordOf (M : Fin (L + 1) → ℕ) (s : Fin L)
    (i : Fin (M s.castSucc)) (j : Fin (M s.succ)) : Fin (flatDim M) :=
  Fintype.equivFin (FlatIdx M) ⟨⟨s, i⟩, j⟩

/-- **`flatCoordOf` is injective** — distinct matrix entries map to distinct flat coordinates
(`Fintype.equivFin` is an equiv; the `FlatIdx` sigma constructor is injective). The load-bearing fact
for the center selector's injectivity (⟹ the `centerSplit` reindex is a permutation). -/
theorem flatCoordOf_injective (M : Fin (L + 1) → ℕ) (s : Fin L)
    {i i' : Fin (M s.castSucc)} {j j' : Fin (M s.succ)}
    (h : flatCoordOf M s i j = flatCoordOf M s i' j') : i = i' ∧ j = j' := by
  unfold flatCoordOf at h
  have hsig : (⟨⟨s, i⟩, j⟩ : FlatIdx M) = ⟨⟨s, i'⟩, j'⟩ := (Fintype.equivFin (FlatIdx M)).injective h
  obtain ⟨hq, hj⟩ := Sigma.mk.inj_iff.mp hsig
  obtain ⟨_, hi⟩ := Sigma.mk.inj_iff.mp hq
  exact ⟨eq_of_heq hi, eq_of_heq hj⟩

/-- **The residual-block center selector** (elder-gate9, the arithmetic part): the `rows × cols`
sub-block at rows `[J, J+rows)` × cols `[J, J+cols)` of the layer-`s` weight matrix, flattened to
`Fin (rows*cols)`, mapped to its flat coordinates. The bounds `J+rows ≤ M s.castSucc` / `J+cols ≤ M
s.succ` (the reachability invariants `resRows = M(S)−J ≤ M s.castSucc` etc.) are hypotheses; on the
built tree's nodes they hold. Instantiate `rows,cols`: case-2 `= resRows,resCols`; case-1(2) d-family
`= runLen,resCols`. -/
noncomputable def resBlockCenterIndices (M : Fin (L + 1) → ℕ) (s : Fin L) (J rows cols : ℕ)
    (hrow : J + rows ≤ M s.castSucc) (hcol : J + cols ≤ M s.succ) :
    Fin (rows * cols) → Fin (flatDim M) :=
  fun k =>
    flatCoordOf M s
      ⟨J + (finProdFinEquiv.symm k).1, by have := (finProdFinEquiv.symm k).1.isLt; omega⟩
      ⟨J + (finProdFinEquiv.symm k).2, by have := (finProdFinEquiv.symm k).2.isLt; omega⟩

/-- **The residual-block selector is injective** — distinct block cells map to distinct flat
coordinates (`flatCoordOf` injective on `(i,j)` for fixed `s`; the `J+·` shift + `finProdFinEquiv`
injective). This is what makes `centerSplit`'s reindex a permutation. -/
theorem resBlockCenterIndices_injective (M : Fin (L + 1) → ℕ) (s : Fin L) (J rows cols : ℕ)
    (hrow : J + rows ≤ M s.castSucc) (hcol : J + cols ≤ M s.succ) :
    Function.Injective (resBlockCenterIndices M s J rows cols hrow hcol) := by
  intro k k' h
  unfold resBlockCenterIndices at h
  obtain ⟨hi, hj⟩ := flatCoordOf_injective M s h
  have hi' : (finProdFinEquiv.symm k).1 = (finProdFinEquiv.symm k').1 := by
    apply Fin.ext; have := Fin.mk.inj_iff.mp hi; omega
  have hj' : (finProdFinEquiv.symm k).2 = (finProdFinEquiv.symm k').2 := by
    apply Fin.ext; have := Fin.mk.inj_iff.mp hj; omega
  exact finProdFinEquiv.symm.injective (Prod.ext hi' hj')

end DLNFibre.DLN.RLCT.Engine
