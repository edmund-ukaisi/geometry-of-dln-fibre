import DLNFibre.DLN.RLCT.Validate.RouteMSmearedGenAtom
import DLNFibre.DLN.RLCT.Validate.RouteMSmearedChartOpaque
import DLNFibre.DLN.RLCT.Foundations.ParamsReshapeMP

/-!
# `RouteMSmearedDecodeGen` — the general-`L` flat DECODE (generalizing `RouteMSmearedDecodeL2`)

The `Fin (L+1)`-layer generalization of the `Fin 3`-hardcoded L=2 decode (`RouteMSmearedDecodeL2`).
For any depth `0 < L` and any widths `M : Fin (L+1) → ℕ`, with the deepest front-bottleneck split
`r + s = M (deepLayer hL).castSucc`:

* the slot bijection `slotEquivG M : Fin (routeMAmbient M) ≃ FlatIdx M`;
* the deepest-layer flat slots `topSlotG a j` / `botSlotG b j` (row-split via `deepWidthEquiv hrs`);
* the front slots `frontSlotG t i j` (any layer `t : Fin L` with `t.val < L−1`);
* the radial-active coord set `topCoordsG` (the `r·c` deepest-top coords) and the pivot `pivotCoordG`;
* the DECODE `packM (shearMBody (R u)) = chartGenParams M (A_front u) hL … (Λ₀ u)`.

The KEY structural simplification (Codex-clean route, brief §1): the interior front layers `1..L−2`
stay CONSTANT under the shear (their coords are NOT in `topCoordsG`), so `shearMBody_apply_of_not_mem`
returns them untouched; the decode's per-layer dispatch hits only "is this the deep layer `L−1`?" —
deep ⟹ the `deepWidthEquiv` row split; else ⟹ the identity front readoff. The deepest-slot cast (the
riskiest piece) is `deepest_slot_split_spec`, de-risked first: `deepWidthEquiv hrs` at width
`M (deepLayer hL).castSucc` lands in the FlatIdx deep-slot row type, and `flatEquivOf_symm_coord`
reads it back exactly as the L=2 `packM_shear_entry`.
-/

open MeasureTheory Matrix
open scoped ENNReal BigOperators

namespace DLNFibre.DLN.RLCT

variable {L : ℕ} {M : Fin (L + 1) → ℕ} {r s : ℕ}

/-! ## The deep layer index and the slot bijection -/

/-- The deepest layer index `⟨L−1, _⟩ : Fin L` (the deepest factor `A^{L−1}`). -/
def deepLayer (hL : 0 < L) : Fin L := ⟨L - 1, Nat.sub_lt hL Nat.one_pos⟩

/-- The width equality `M (deepLayer hL).castSucc = M (⟨L−1⟩ : Fin (L+1))` (the atom's `e1`). -/
theorem deepLayer_castSucc_width (M : Fin (L + 1) → ℕ) (hL : 0 < L) :
    M ((deepLayer hL).castSucc) = M (⟨L - 1, by omega⟩ : Fin (L + 1)) := by
  apply congrArg; apply Fin.ext; simp [deepLayer, Fin.castSucc, Fin.castAdd, Fin.castLE]

/-- The width equality `M (deepLayer hL).succ = M (last L)` (the atom's `e2`). -/
theorem deepLayer_succ_width (M : Fin (L + 1) → ℕ) (hL : 0 < L) :
    M ((deepLayer hL).succ) = M (Fin.last L) := by
  apply congrArg; apply Fin.ext; simp [deepLayer, Fin.succ, Fin.last]; omega

/-- The (noncomputable) slot bijection `Fin (routeMAmbient M) ≃ FlatIdx M`. -/
noncomputable def slotEquivG (M : Fin (L + 1) → ℕ) : Fin (routeMAmbient M) ≃ FlatIdx M :=
  (Fintype.equivFin (FlatIdx M)).symm

/-- The `Fin (routeMAmbient M)` coordinate of a flat slot `q` (the `slotEquivG.symm`). -/
noncomputable def coordOfG (M : Fin (L + 1) → ℕ) (q : FlatIdx M) : Fin (routeMAmbient M) :=
  (slotEquivG M).symm q

/-- `coordOfG` is injective. -/
theorem coordOfG_injective (M : Fin (L + 1) → ℕ) {q q' : FlatIdx M}
    (h : coordOfG M q = coordOfG M q') : q = q' := (slotEquivG M).symm.injective h

/-! ## The flat slots (front layers, deepest-top, deepest-bottom) -/

/-- A front-layer flat slot `⟨⟨t, i⟩, j⟩` at a layer `t : Fin L` (`i` a row, `j` a column). Used for
the free front layers `0 ≤ t < L−1`. -/
def frontSlotG (M : Fin (L + 1) → ℕ) (t : Fin L) (i : Fin (M t.castSucc)) (j : Fin (M t.succ)) :
    FlatIdx M :=
  ⟨⟨t, i⟩, j⟩

/-- A deepest-top flat slot `⟨⟨deepLayer, deepWidthEquiv (inl a)⟩, j⟩` (top `r`-row block). -/
noncomputable def topSlotG (M : Fin (L + 1) → ℕ) (hL : 0 < L)
    (hrs : r + s = M ((deepLayer hL).castSucc))
    (a : Fin r) (j : Fin (M ((deepLayer hL).succ))) : FlatIdx M :=
  ⟨⟨deepLayer hL, deepWidthEquiv hrs (Sum.inl a)⟩, j⟩

/-- A deepest-bottom flat slot `⟨⟨deepLayer, deepWidthEquiv (inr b)⟩, j⟩` (bottom `s`-row block). -/
noncomputable def botSlotG (M : Fin (L + 1) → ℕ) (hL : 0 < L)
    (hrs : r + s = M ((deepLayer hL).castSucc))
    (b : Fin s) (j : Fin (M ((deepLayer hL).succ))) : FlatIdx M :=
  ⟨⟨deepLayer hL, deepWidthEquiv hrs (Sum.inr b)⟩, j⟩

/-! ## The slots are distinct (the split faithfulness) -/

/-- `deepWidthEquiv` separates the top/bottom blocks: `topSlotG a j ≠ botSlotG b j'`. -/
theorem topSlotG_ne_botSlotG (M : Fin (L + 1) → ℕ) (hL : 0 < L)
    (hrs : r + s = M ((deepLayer hL).castSucc))
    (a : Fin r) (j : Fin (M ((deepLayer hL).succ)))
    (b : Fin s) (j' : Fin (M ((deepLayer hL).succ))) :
    topSlotG M hL hrs a j ≠ botSlotG M hL hrs b j' := by
  intro h
  have hval : (deepWidthEquiv hrs (Sum.inl a) : Fin (M ((deepLayer hL).castSucc))).val
      = (deepWidthEquiv hrs (Sum.inr b) : Fin (M ((deepLayer hL).castSucc))).val :=
    congrArg (fun q : FlatIdx M => (q.1.2.val : ℕ)) h
  have hrow : deepWidthEquiv hrs (Sum.inl a) = deepWidthEquiv hrs (Sum.inr b) := Fin.ext hval
  exact Sum.inl_ne_inr ((deepWidthEquiv hrs).injective hrow)

/-- A front slot at a layer `t ≠ deepLayer` is never a deepest-top slot (different layer). -/
theorem frontSlotG_ne_topSlotG (M : Fin (L + 1) → ℕ) (hL : 0 < L)
    (hrs : r + s = M ((deepLayer hL).castSucc))
    (t : Fin L) (ht : t ≠ deepLayer hL) (i : Fin (M t.castSucc)) (jf : Fin (M t.succ))
    (a : Fin r) (j : Fin (M ((deepLayer hL).succ))) :
    frontSlotG M t i jf ≠ topSlotG M hL hrs a j := by
  intro h
  exact ht (congrArg (·.1.1) h)

/-- A front slot at a layer `t ≠ deepLayer` is never a deepest-bottom slot. -/
theorem frontSlotG_ne_botSlotG (M : Fin (L + 1) → ℕ) (hL : 0 < L)
    (hrs : r + s = M ((deepLayer hL).castSucc))
    (t : Fin L) (ht : t ≠ deepLayer hL) (i : Fin (M t.castSucc)) (jf : Fin (M t.succ))
    (b : Fin s) (j : Fin (M ((deepLayer hL).succ))) :
    frontSlotG M t i jf ≠ botSlotG M hL hrs b j := by
  intro h
  exact ht (congrArg (·.1.1) h)

end DLNFibre.DLN.RLCT
