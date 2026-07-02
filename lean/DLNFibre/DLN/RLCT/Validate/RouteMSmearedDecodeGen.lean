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

/-! ## The chart components read off `u` at the flat slots -/

/-- **The front tuple** `frontTupleG u : Params M` — the identity readoff `A t i j =
u (coordOfG (frontSlotG t i j))` at EVERY layer `t`. (The deep layer `L−1` is overridden by
`chartGenParams`, so only the free front layers `0..L−2` matter downstream — their coords are all
`∉ topCoordsG`, hence shear-untouched.) -/
noncomputable def frontTupleG (M : Fin (L + 1) → ℕ) (u : Fin (routeMAmbient M) → ℝ) : Params M :=
  fun t i j => u (coordOfG M (frontSlotG M t i j))

/-- The deepest-top radial coords (`R`'s active set / the shear's Core slots): the `r·c` coords
`coordOfG (topSlotG a j)`. -/
noncomputable def topCoordsG (M : Fin (L + 1) → ℕ) (hL : 0 < L)
    (hrs : r + s = M ((deepLayer hL).castSucc)) : Finset (Fin (routeMAmbient M)) :=
  Finset.image
    (fun p : Fin r × Fin (M ((deepLayer hL).succ)) => coordOfG M (topSlotG M hL hrs p.1 p.2))
    Finset.univ

/-- The radial pivot coord (the `(0,0)` entry of the deepest-top block) — needs `0 < r`, `0 < M last`. -/
noncomputable def pivotCoordG (M : Fin (L + 1) → ℕ) (hL : 0 < L)
    (hrs : r + s = M ((deepLayer hL).castSucc)) (hr : 0 < r)
    (hc : 0 < M ((deepLayer hL).succ)) : Fin (routeMAmbient M) :=
  coordOfG M (topSlotG M hL hrs ⟨0, hr⟩ ⟨0, hc⟩)

/-- The radial pivot value `z = u (pivotCoordG)`. -/
noncomputable def zuG (M : Fin (L + 1) → ℕ) (hL : 0 < L)
    (hrs : r + s = M ((deepLayer hL).castSucc)) (hr : 0 < r) (hc : 0 < M ((deepLayer hL).succ))
    (u : Fin (routeMAmbient M) → ℝ) : ℝ :=
  u (pivotCoordG M hL hrs hr hc)

/-- The residual `S_bot b j = u (coordOfG (botSlotG b j))` (the free bottom block). -/
noncomputable def SbotuG (M : Fin (L + 1) → ℕ) (hL : 0 < L)
    (hrs : r + s = M ((deepLayer hL).castSucc)) (u : Fin (routeMAmbient M) → ℝ) :
    Matrix (Fin s) (Fin (M ((deepLayer hL).succ))) ℝ :=
  fun b j => u (coordOfG M (botSlotG M hL hrs b j))

/-- The angular UNIT block `H̄_unit a j`: the pivot entry `(⟨0⟩,⟨0⟩)` is fixed `= 1`, every other
deepest-top entry is the free coord `u (coordOfG (topSlotG a j))`. -/
noncomputable def HbarUnitG (M : Fin (L + 1) → ℕ) (hL : 0 < L)
    (hrs : r + s = M ((deepLayer hL).castSucc)) (hr : 0 < r) (hc : 0 < M ((deepLayer hL).succ))
    (u : Fin (routeMAmbient M) → ℝ) : Matrix (Fin r) (Fin (M ((deepLayer hL).succ))) ℝ :=
  fun a j => if coordOfG M (topSlotG M hL hrs a j) = pivotCoordG M hL hrs hr hc then 1
    else u (coordOfG M (topSlotG M hL hrs a j))

/-- **The atom-shaped split hypothesis** `r + s = M (⟨L−1⟩ : Fin (L+1))`, obtained from the
FlatIdx-natural `hrs : r + s = M (deepLayer hL).castSucc` by the width equality. The atom's
`chartGenParams`/`prod_chartGen_collapse`/`frontProd` all index by `M (⟨L−1⟩ : Fin (L+1))`, so this
is the single conversion point between the FlatIdx-natural split and the atom's split. -/
theorem hrsAtom_of_hrs (hL : 0 < L) (hrs : r + s = M ((deepLayer hL).castSucc)) :
    r + s = M (⟨L - 1, by omega⟩ : Fin (L + 1)) :=
  hrs.trans (deepLayer_castSucc_width M hL).symm

/-- The rank-block front columns `P₁ i k = frontProd i (deepWidthEquiv (inl k))` (atom-shaped `hrs`). -/
noncomputable def P1uG (M : Fin (L + 1) → ℕ) (hL : 0 < L)
    (hrs : r + s = M ((deepLayer hL).castSucc)) (u : Fin (routeMAmbient M) → ℝ) :
    Matrix (Fin (M 0)) (Fin r) ℝ :=
  fun i k => frontProd M (frontTupleG M u) hL i
    (deepWidthEquiv (hrsAtom_of_hrs hL hrs) (Sum.inl k))

/-- The residual front columns `P₂ i k = frontProd i (deepWidthEquiv (inr k))`. -/
noncomputable def P2uG (M : Fin (L + 1) → ℕ) (hL : 0 < L)
    (hrs : r + s = M ((deepLayer hL).castSucc)) (u : Fin (routeMAmbient M) → ℝ) :
    Matrix (Fin (M 0)) (Fin s) ℝ :=
  fun i k => frontProd M (frontTupleG M u) hL i
    (deepWidthEquiv (hrsAtom_of_hrs hL hrs) (Sum.inr k))

/-- The rational routing `Λ₀ = (P₁ᵀP₁)⁻¹P₁ᵀP₂` (the smeared shear coefficient). -/
noncomputable def Lam0uG (M : Fin (L + 1) → ℕ) (hL : 0 < L)
    (hrs : r + s = M ((deepLayer hL).castSucc)) (u : Fin (routeMAmbient M) → ℝ) :
    Matrix (Fin r) (Fin s) ℝ :=
  ((P1uG M hL hrs u).transpose * P1uG M hL hrs u)⁻¹ * (P1uG M hL hrs u).transpose * P2uG M hL hrs u

/-! ## `topCoordsG` membership + the radial blow-up `R` -/

/-- `coordOfG (topSlotG a j) ∈ topCoordsG`. -/
theorem coordOfG_topSlotG_mem (M : Fin (L + 1) → ℕ) (hL : 0 < L)
    (hrs : r + s = M ((deepLayer hL).castSucc)) (a : Fin r) (j : Fin (M ((deepLayer hL).succ))) :
    coordOfG M (topSlotG M hL hrs a j) ∈ topCoordsG M hL hrs := by
  rw [topCoordsG, Finset.mem_image]
  exact ⟨(a, j), Finset.mem_univ _, rfl⟩

/-- Membership in `topCoordsG` is exactly "is the `coordOfG` of some top slot". -/
theorem mem_topCoordsG_iff (M : Fin (L + 1) → ℕ) (hL : 0 < L)
    (hrs : r + s = M ((deepLayer hL).castSucc)) (m : Fin (routeMAmbient M)) :
    m ∈ topCoordsG M hL hrs ↔
      ∃ a : Fin r, ∃ j : Fin (M ((deepLayer hL).succ)), coordOfG M (topSlotG M hL hrs a j) = m := by
  rw [topCoordsG, Finset.mem_image]
  constructor
  · rintro ⟨⟨a, j⟩, _, h⟩; exact ⟨a, j, h⟩
  · rintro ⟨a, j, h⟩; exact ⟨(a, j), Finset.mem_univ _, h⟩

/-- `coordOfG (frontSlotG t i jf) ∉ topCoordsG` when `t ≠ deepLayer` (a front slot is not a top slot). -/
theorem coordOfG_frontSlotG_not_mem (M : Fin (L + 1) → ℕ) (hL : 0 < L)
    (hrs : r + s = M ((deepLayer hL).castSucc))
    (t : Fin L) (ht : t ≠ deepLayer hL) (i : Fin (M t.castSucc)) (jf : Fin (M t.succ)) :
    coordOfG M (frontSlotG M t i jf) ∉ topCoordsG M hL hrs := by
  rw [mem_topCoordsG_iff]
  rintro ⟨a, j, h⟩
  exact frontSlotG_ne_topSlotG M hL hrs t ht i jf a j (coordOfG_injective M h.symm)

/-- `coordOfG (botSlotG b j) ∉ topCoordsG` (a bottom slot is not a top slot). -/
theorem coordOfG_botSlotG_not_mem (M : Fin (L + 1) → ℕ) (hL : 0 < L)
    (hrs : r + s = M ((deepLayer hL).castSucc)) (b : Fin s) (j : Fin (M ((deepLayer hL).succ))) :
    coordOfG M (botSlotG M hL hrs b j) ∉ topCoordsG M hL hrs := by
  rw [mem_topCoordsG_iff]
  rintro ⟨a, j', h⟩
  exact topSlotG_ne_botSlotG M hL hrs a j' b j (coordOfG_injective M h)

/-- The radial blow-up `R := pivotBlowupOn (topCoordsG) pivotCoordG`: fixes the pivot, scales the
other deepest-top coords by the pivot, fixes the spectators (front + bottom). -/
noncomputable def RmapG (M : Fin (L + 1) → ℕ) (hL : 0 < L)
    (hrs : r + s = M ((deepLayer hL).castSucc)) (hr : 0 < r) (hc : 0 < M ((deepLayer hL).succ)) :
    (Fin (routeMAmbient M) → ℝ) → (Fin (routeMAmbient M) → ℝ) :=
  pivotBlowupOn (topCoordsG M hL hrs) (pivotCoordG M hL hrs hr hc)

/-- The pivot coord is in `topCoordsG`. -/
theorem pivotCoordG_mem (M : Fin (L + 1) → ℕ) (hL : 0 < L)
    (hrs : r + s = M ((deepLayer hL).castSucc)) (hr : 0 < r) (hc : 0 < M ((deepLayer hL).succ)) :
    pivotCoordG M hL hrs hr hc ∈ topCoordsG M hL hrs :=
  coordOfG_topSlotG_mem M hL hrs ⟨0, hr⟩ ⟨0, hc⟩

/-- `RmapG u m = u m` off `topCoordsG` (spectators: front + bottom; `pivot ∈ topCoordsG`). -/
theorem RmapG_spectator (M : Fin (L + 1) → ℕ) (hL : 0 < L)
    (hrs : r + s = M ((deepLayer hL).castSucc)) (hr : 0 < r) (hc : 0 < M ((deepLayer hL).succ))
    (u : Fin (routeMAmbient M) → ℝ) {m : Fin (routeMAmbient M)} (hm : m ∉ topCoordsG M hL hrs) :
    RmapG M hL hrs hr hc u m = u m := by
  have hmp : m ≠ pivotCoordG M hL hrs hr hc := fun h => hm (h ▸ pivotCoordG_mem M hL hrs hr hc)
  simp only [RmapG, pivotBlowupOn, if_neg hmp, if_neg hm]

/-- `RmapG u (coordOfG (topSlotG a j)) = zuG · HbarUnitG a j`. -/
theorem RmapG_topSlotG (M : Fin (L + 1) → ℕ) (hL : 0 < L)
    (hrs : r + s = M ((deepLayer hL).castSucc)) (hr : 0 < r) (hc : 0 < M ((deepLayer hL).succ))
    (u : Fin (routeMAmbient M) → ℝ) (a : Fin r) (j : Fin (M ((deepLayer hL).succ))) :
    RmapG M hL hrs hr hc u (coordOfG M (topSlotG M hL hrs a j))
      = zuG M hL hrs hr hc u * HbarUnitG M hL hrs hr hc u a j := by
  rw [RmapG, HbarUnitG, zuG, pivotBlowupOn]
  by_cases hpiv : coordOfG M (topSlotG M hL hrs a j) = pivotCoordG M hL hrs hr hc
  · rw [if_pos hpiv, if_pos hpiv, mul_one]
  · have hmem := coordOfG_topSlotG_mem M hL hrs a j
    rw [if_neg hpiv, if_pos hmem, if_neg hpiv]

/-! ## The front tuple / `S_bot` / `Λ₀` read only `topCoordsGᶜ` (shear-spectator coords) -/

/-- `frontTupleG v = frontTupleG w` if `v`, `w` agree off `topCoordsG` (the FRONT layers `t ≠ deepLayer`
read `frontSlotG` coords, all `∉ topCoordsG`; the deep layer of `frontTupleG` is overridden downstream
by `chartGenParams`, so its value there is irrelevant to `frontProd`). Stated on the front-relevant
layers via `prodAux_congr_lt`; here for the full readoff we only need agreement off `topCoordsG` for the
front layers, which this supplies. -/
theorem frontTupleG_congr_front (M : Fin (L + 1) → ℕ) (hL : 0 < L)
    (hrs : r + s = M ((deepLayer hL).castSucc)) {v w : Fin (routeMAmbient M) → ℝ}
    (h : ∀ m, m ∉ topCoordsG M hL hrs → v m = w m) (t : Fin L) (ht : t ≠ deepLayer hL) :
    (frontTupleG M v) t = (frontTupleG M w) t := by
  funext i jf
  exact h _ (coordOfG_frontSlotG_not_mem M hL hrs t ht i jf)

/-- The front PRODUCT `frontProd M (frontTupleG v) = frontProd M (frontTupleG w)` when `v`, `w` agree
off `topCoordsG` — `frontProd = prodAux (L−1)` reads only the front layers `0..L−2`, all `≠ deepLayer`,
which agree by `frontTupleG_congr_front`. -/
theorem frontProd_frontTupleG_congr (M : Fin (L + 1) → ℕ) (hL : 0 < L)
    (hrs : r + s = M ((deepLayer hL).castSucc)) {v w : Fin (routeMAmbient M) → ℝ}
    (h : ∀ m, m ∉ topCoordsG M hL hrs → v m = w m) :
    frontProd M (frontTupleG M v) hL = frontProd M (frontTupleG M w) hL := by
  rw [frontProd, frontProd]
  refine prodAux_congr_lt M _ _ (L - 1) (by omega) (fun t ht => ?_)
  have htne : t ≠ deepLayer hL := by
    intro hteq; rw [hteq] at ht; simp only [deepLayer] at ht; omega
  exact frontTupleG_congr_front M hL hrs h t htne

/-- `SbotuG v = SbotuG w` if `v`, `w` agree off `topCoordsG` (`S_bot` reads bottom slots, `∉ topCoordsG`). -/
theorem SbotuG_congr (M : Fin (L + 1) → ℕ) (hL : 0 < L)
    (hrs : r + s = M ((deepLayer hL).castSucc)) {v w : Fin (routeMAmbient M) → ℝ}
    (h : ∀ m, m ∉ topCoordsG M hL hrs → v m = w m) : SbotuG M hL hrs v = SbotuG M hL hrs w := by
  funext b j
  exact h _ (coordOfG_botSlotG_not_mem M hL hrs b j)

/-- `Lam0uG v = Lam0uG w` if `v`, `w` agree off `topCoordsG` (`Λ₀` is built from `frontProd`'s columns
`P₁`/`P₂`, which are `frontProd`-invariant off `topCoordsG`). -/
theorem Lam0uG_congr (M : Fin (L + 1) → ℕ) (hL : 0 < L)
    (hrs : r + s = M ((deepLayer hL).castSucc)) {v w : Fin (routeMAmbient M) → ℝ}
    (h : ∀ m, m ∉ topCoordsG M hL hrs → v m = w m) : Lam0uG M hL hrs v = Lam0uG M hL hrs w := by
  have hFP := frontProd_frontTupleG_congr M hL hrs h
  have hP1 : P1uG M hL hrs v = P1uG M hL hrs w := by funext i a; simp only [P1uG, hFP]
  have hP2 : P2uG M hL hrs v = P2uG M hL hrs w := by funext i b; simp only [P2uG, hFP]
  rw [Lam0uG, Lam0uG, hP1, hP2]

end DLNFibre.DLN.RLCT
