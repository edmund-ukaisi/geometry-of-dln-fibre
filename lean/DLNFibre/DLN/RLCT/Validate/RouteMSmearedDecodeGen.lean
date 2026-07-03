import DLNFibre.DLN.RLCT.Validate.RouteMSmearedGenAtom
import DLNFibre.DLN.RLCT.Validate.RouteMSmearedChartOpaque
import DLNFibre.DLN.RLCT.Foundations.ParamsReshapeMP

/-!
# `RouteMSmearedDecodeGen` — the general-`L` flat DECODE (generalizing `RouteMSmearedDecodeL2`)

The `Fin (L+1)`-layer generalization of the `Fin 3`-hardcoded L=2 decode (`RouteMSmearedDecodeL2`).
For any depth `0 < L` and any widths `M : Fin (L+1) → ℕ`, with the deepest front-bottleneck split
`r + s = M (deepLayerS hL).castSucc`:

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
`M (deepLayerS hL).castSucc` lands in the FlatIdx deep-slot row type, and `flatEquivOf_symm_coord`
reads it back exactly as the L=2 `packM_shear_entry`.
-/

open MeasureTheory Matrix
open scoped ENNReal BigOperators

namespace DLNFibre.DLN.RLCT

variable {L : ℕ} {M : Fin (L + 1) → ℕ} {r s : ℕ}

/-! ## The deep layer index and the slot bijection -/

/-- The deepest layer index `⟨L−1, _⟩ : Fin L` (the deepest factor `A^{L−1}`). -/
def deepLayerS (hL : 0 < L) : Fin L := ⟨L - 1, Nat.sub_lt hL Nat.one_pos⟩

/-- The width equality `M (deepLayerS hL).castSucc = M (⟨L−1⟩ : Fin (L+1))` (the atom's `e1`). -/
theorem deepLayerS_castSucc_width (M : Fin (L + 1) → ℕ) (hL : 0 < L) :
    M ((deepLayerS hL).castSucc) = M (⟨L - 1, by omega⟩ : Fin (L + 1)) := by
  apply congrArg; apply Fin.ext; simp [deepLayerS, Fin.castSucc, Fin.castAdd, Fin.castLE]

/-- The width equality `M (deepLayerS hL).succ = M (last L)` (the atom's `e2`). -/
theorem deepLayerS_succ_width (M : Fin (L + 1) → ℕ) (hL : 0 < L) :
    M ((deepLayerS hL).succ) = M (Fin.last L) := by
  apply congrArg; apply Fin.ext; simp [deepLayerS, Fin.succ, Fin.last]; omega

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

/-- A deepest-top flat slot `⟨⟨deepLayerS, deepWidthEquiv (inl a)⟩, j⟩` (top `r`-row block). -/
noncomputable def topSlotG (M : Fin (L + 1) → ℕ) (hL : 0 < L)
    (hrs : r + s = M ((deepLayerS hL).castSucc))
    (a : Fin r) (j : Fin (M ((deepLayerS hL).succ))) : FlatIdx M :=
  ⟨⟨deepLayerS hL, deepWidthEquiv hrs (Sum.inl a)⟩, j⟩

/-- A deepest-bottom flat slot `⟨⟨deepLayerS, deepWidthEquiv (inr b)⟩, j⟩` (bottom `s`-row block). -/
noncomputable def botSlotG (M : Fin (L + 1) → ℕ) (hL : 0 < L)
    (hrs : r + s = M ((deepLayerS hL).castSucc))
    (b : Fin s) (j : Fin (M ((deepLayerS hL).succ))) : FlatIdx M :=
  ⟨⟨deepLayerS hL, deepWidthEquiv hrs (Sum.inr b)⟩, j⟩

/-! ## The slots are distinct (the split faithfulness) -/

/-- `deepWidthEquiv` separates the top/bottom blocks: `topSlotG a j ≠ botSlotG b j'`. -/
theorem topSlotG_ne_botSlotG (M : Fin (L + 1) → ℕ) (hL : 0 < L)
    (hrs : r + s = M ((deepLayerS hL).castSucc))
    (a : Fin r) (j : Fin (M ((deepLayerS hL).succ)))
    (b : Fin s) (j' : Fin (M ((deepLayerS hL).succ))) :
    topSlotG M hL hrs a j ≠ botSlotG M hL hrs b j' := by
  intro h
  have hval : (deepWidthEquiv hrs (Sum.inl a) : Fin (M ((deepLayerS hL).castSucc))).val
      = (deepWidthEquiv hrs (Sum.inr b) : Fin (M ((deepLayerS hL).castSucc))).val :=
    congrArg (fun q : FlatIdx M => (q.1.2.val : ℕ)) h
  have hrow : deepWidthEquiv hrs (Sum.inl a) = deepWidthEquiv hrs (Sum.inr b) := Fin.ext hval
  exact Sum.inl_ne_inr ((deepWidthEquiv hrs).injective hrow)

/-- A front slot at a layer `t ≠ deepLayerS` is never a deepest-top slot (different layer). -/
theorem frontSlotG_ne_topSlotG (M : Fin (L + 1) → ℕ) (hL : 0 < L)
    (hrs : r + s = M ((deepLayerS hL).castSucc))
    (t : Fin L) (ht : t ≠ deepLayerS hL) (i : Fin (M t.castSucc)) (jf : Fin (M t.succ))
    (a : Fin r) (j : Fin (M ((deepLayerS hL).succ))) :
    frontSlotG M t i jf ≠ topSlotG M hL hrs a j := by
  intro h
  exact ht (congrArg (·.1.1) h)

/-- A front slot at a layer `t ≠ deepLayerS` is never a deepest-bottom slot. -/
theorem frontSlotG_ne_botSlotG (M : Fin (L + 1) → ℕ) (hL : 0 < L)
    (hrs : r + s = M ((deepLayerS hL).castSucc))
    (t : Fin L) (ht : t ≠ deepLayerS hL) (i : Fin (M t.castSucc)) (jf : Fin (M t.succ))
    (b : Fin s) (j : Fin (M ((deepLayerS hL).succ))) :
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
    (hrs : r + s = M ((deepLayerS hL).castSucc)) : Finset (Fin (routeMAmbient M)) :=
  Finset.image
    (fun p : Fin r × Fin (M ((deepLayerS hL).succ)) => coordOfG M (topSlotG M hL hrs p.1 p.2))
    Finset.univ

/-- The radial pivot coord (the `(0,0)` entry of the deepest-top block) — needs `0 < r`, `0 < M last`. -/
noncomputable def pivotCoordG (M : Fin (L + 1) → ℕ) (hL : 0 < L)
    (hrs : r + s = M ((deepLayerS hL).castSucc)) (hr : 0 < r)
    (hc : 0 < M ((deepLayerS hL).succ)) : Fin (routeMAmbient M) :=
  coordOfG M (topSlotG M hL hrs ⟨0, hr⟩ ⟨0, hc⟩)

/-- The radial pivot value `z = u (pivotCoordG)`. -/
noncomputable def zuG (M : Fin (L + 1) → ℕ) (hL : 0 < L)
    (hrs : r + s = M ((deepLayerS hL).castSucc)) (hr : 0 < r) (hc : 0 < M ((deepLayerS hL).succ))
    (u : Fin (routeMAmbient M) → ℝ) : ℝ :=
  u (pivotCoordG M hL hrs hr hc)

/-- The residual `S_bot b j = u (coordOfG (botSlotG b j))` (the free bottom block). -/
noncomputable def SbotuG (M : Fin (L + 1) → ℕ) (hL : 0 < L)
    (hrs : r + s = M ((deepLayerS hL).castSucc)) (u : Fin (routeMAmbient M) → ℝ) :
    Matrix (Fin s) (Fin (M ((deepLayerS hL).succ))) ℝ :=
  fun b j => u (coordOfG M (botSlotG M hL hrs b j))

/-- The angular UNIT block `H̄_unit a j`: the pivot entry `(⟨0⟩,⟨0⟩)` is fixed `= 1`, every other
deepest-top entry is the free coord `u (coordOfG (topSlotG a j))`. -/
noncomputable def HbarUnitG (M : Fin (L + 1) → ℕ) (hL : 0 < L)
    (hrs : r + s = M ((deepLayerS hL).castSucc)) (hr : 0 < r) (hc : 0 < M ((deepLayerS hL).succ))
    (u : Fin (routeMAmbient M) → ℝ) : Matrix (Fin r) (Fin (M ((deepLayerS hL).succ))) ℝ :=
  fun a j => if coordOfG M (topSlotG M hL hrs a j) = pivotCoordG M hL hrs hr hc then 1
    else u (coordOfG M (topSlotG M hL hrs a j))

/-- **The atom-shaped split hypothesis** `r + s = M (⟨L−1⟩ : Fin (L+1))`, obtained from the
FlatIdx-natural `hrs : r + s = M (deepLayerS hL).castSucc` by the width equality. The atom's
`chartGenParams`/`prod_chartGen_collapse`/`frontProd` all index by `M (⟨L−1⟩ : Fin (L+1))`, so this
is the single conversion point between the FlatIdx-natural split and the atom's split. -/
theorem hrsAtom_of_hrs (hL : 0 < L) (hrs : r + s = M ((deepLayerS hL).castSucc)) :
    r + s = M (⟨L - 1, by omega⟩ : Fin (L + 1)) :=
  hrs.trans (deepLayerS_castSucc_width M hL).symm

/-- The rank-block front columns `P₁ i k = frontProd i (deepWidthEquiv (inl k))` (atom-shaped `hrs`). -/
noncomputable def P1uG (M : Fin (L + 1) → ℕ) (hL : 0 < L)
    (hrs : r + s = M ((deepLayerS hL).castSucc)) (u : Fin (routeMAmbient M) → ℝ) :
    Matrix (Fin (M 0)) (Fin r) ℝ :=
  fun i k => frontProd M (frontTupleG M u) hL i
    (deepWidthEquiv (hrsAtom_of_hrs hL hrs) (Sum.inl k))

/-- The residual front columns `P₂ i k = frontProd i (deepWidthEquiv (inr k))`. -/
noncomputable def P2uG (M : Fin (L + 1) → ℕ) (hL : 0 < L)
    (hrs : r + s = M ((deepLayerS hL).castSucc)) (u : Fin (routeMAmbient M) → ℝ) :
    Matrix (Fin (M 0)) (Fin s) ℝ :=
  fun i k => frontProd M (frontTupleG M u) hL i
    (deepWidthEquiv (hrsAtom_of_hrs hL hrs) (Sum.inr k))

/-- The rational routing `Λ₀ = (P₁ᵀP₁)⁻¹P₁ᵀP₂` (the smeared shear coefficient). -/
noncomputable def Lam0uG (M : Fin (L + 1) → ℕ) (hL : 0 < L)
    (hrs : r + s = M ((deepLayerS hL).castSucc)) (u : Fin (routeMAmbient M) → ℝ) :
    Matrix (Fin r) (Fin s) ℝ :=
  ((P1uG M hL hrs u).transpose * P1uG M hL hrs u)⁻¹ * (P1uG M hL hrs u).transpose * P2uG M hL hrs u

/-! ## `topCoordsG` membership + the radial blow-up `R` -/

/-- `coordOfG (topSlotG a j) ∈ topCoordsG`. -/
theorem coordOfG_topSlotG_mem (M : Fin (L + 1) → ℕ) (hL : 0 < L)
    (hrs : r + s = M ((deepLayerS hL).castSucc)) (a : Fin r) (j : Fin (M ((deepLayerS hL).succ))) :
    coordOfG M (topSlotG M hL hrs a j) ∈ topCoordsG M hL hrs := by
  rw [topCoordsG, Finset.mem_image]
  exact ⟨(a, j), Finset.mem_univ _, rfl⟩

/-- Membership in `topCoordsG` is exactly "is the `coordOfG` of some top slot". -/
theorem mem_topCoordsG_iff (M : Fin (L + 1) → ℕ) (hL : 0 < L)
    (hrs : r + s = M ((deepLayerS hL).castSucc)) (m : Fin (routeMAmbient M)) :
    m ∈ topCoordsG M hL hrs ↔
      ∃ a : Fin r, ∃ j : Fin (M ((deepLayerS hL).succ)), coordOfG M (topSlotG M hL hrs a j) = m := by
  rw [topCoordsG, Finset.mem_image]
  constructor
  · rintro ⟨⟨a, j⟩, _, h⟩; exact ⟨a, j, h⟩
  · rintro ⟨a, j, h⟩; exact ⟨(a, j), Finset.mem_univ _, h⟩

/-- `coordOfG (frontSlotG t i jf) ∉ topCoordsG` when `t ≠ deepLayerS` (a front slot is not a top slot). -/
theorem coordOfG_frontSlotG_not_mem (M : Fin (L + 1) → ℕ) (hL : 0 < L)
    (hrs : r + s = M ((deepLayerS hL).castSucc))
    (t : Fin L) (ht : t ≠ deepLayerS hL) (i : Fin (M t.castSucc)) (jf : Fin (M t.succ)) :
    coordOfG M (frontSlotG M t i jf) ∉ topCoordsG M hL hrs := by
  rw [mem_topCoordsG_iff]
  rintro ⟨a, j, h⟩
  exact frontSlotG_ne_topSlotG M hL hrs t ht i jf a j (coordOfG_injective M h.symm)

/-- `coordOfG (botSlotG b j) ∉ topCoordsG` (a bottom slot is not a top slot). -/
theorem coordOfG_botSlotG_not_mem (M : Fin (L + 1) → ℕ) (hL : 0 < L)
    (hrs : r + s = M ((deepLayerS hL).castSucc)) (b : Fin s) (j : Fin (M ((deepLayerS hL).succ))) :
    coordOfG M (botSlotG M hL hrs b j) ∉ topCoordsG M hL hrs := by
  rw [mem_topCoordsG_iff]
  rintro ⟨a, j', h⟩
  exact topSlotG_ne_botSlotG M hL hrs a j' b j (coordOfG_injective M h)

/-- The radial blow-up `R := pivotBlowupOn (topCoordsG) pivotCoordG`: fixes the pivot, scales the
other deepest-top coords by the pivot, fixes the spectators (front + bottom). -/
noncomputable def RmapG (M : Fin (L + 1) → ℕ) (hL : 0 < L)
    (hrs : r + s = M ((deepLayerS hL).castSucc)) (hr : 0 < r) (hc : 0 < M ((deepLayerS hL).succ)) :
    (Fin (routeMAmbient M) → ℝ) → (Fin (routeMAmbient M) → ℝ) :=
  pivotBlowupOn (topCoordsG M hL hrs) (pivotCoordG M hL hrs hr hc)

/-- The pivot coord is in `topCoordsG`. -/
theorem pivotCoordG_mem (M : Fin (L + 1) → ℕ) (hL : 0 < L)
    (hrs : r + s = M ((deepLayerS hL).castSucc)) (hr : 0 < r) (hc : 0 < M ((deepLayerS hL).succ)) :
    pivotCoordG M hL hrs hr hc ∈ topCoordsG M hL hrs :=
  coordOfG_topSlotG_mem M hL hrs ⟨0, hr⟩ ⟨0, hc⟩

/-- `RmapG u m = u m` off `topCoordsG` (spectators: front + bottom; `pivot ∈ topCoordsG`). -/
theorem RmapG_spectator (M : Fin (L + 1) → ℕ) (hL : 0 < L)
    (hrs : r + s = M ((deepLayerS hL).castSucc)) (hr : 0 < r) (hc : 0 < M ((deepLayerS hL).succ))
    (u : Fin (routeMAmbient M) → ℝ) {m : Fin (routeMAmbient M)} (hm : m ∉ topCoordsG M hL hrs) :
    RmapG M hL hrs hr hc u m = u m := by
  have hmp : m ≠ pivotCoordG M hL hrs hr hc := fun h => hm (h ▸ pivotCoordG_mem M hL hrs hr hc)
  simp only [RmapG, pivotBlowupOn, if_neg hmp, if_neg hm]

/-- `RmapG u (coordOfG (topSlotG a j)) = zuG · HbarUnitG a j`. -/
theorem RmapG_topSlotG (M : Fin (L + 1) → ℕ) (hL : 0 < L)
    (hrs : r + s = M ((deepLayerS hL).castSucc)) (hr : 0 < r) (hc : 0 < M ((deepLayerS hL).succ))
    (u : Fin (routeMAmbient M) → ℝ) (a : Fin r) (j : Fin (M ((deepLayerS hL).succ))) :
    RmapG M hL hrs hr hc u (coordOfG M (topSlotG M hL hrs a j))
      = zuG M hL hrs hr hc u * HbarUnitG M hL hrs hr hc u a j := by
  rw [RmapG, HbarUnitG, zuG, pivotBlowupOn]
  by_cases hpiv : coordOfG M (topSlotG M hL hrs a j) = pivotCoordG M hL hrs hr hc
  · rw [if_pos hpiv, if_pos hpiv, mul_one]
  · have hmem := coordOfG_topSlotG_mem M hL hrs a j
    rw [if_neg hpiv, if_pos hmem, if_neg hpiv]

/-! ## The front tuple / `S_bot` / `Λ₀` read only `topCoordsGᶜ` (shear-spectator coords) -/

/-- `frontTupleG v = frontTupleG w` if `v`, `w` agree off `topCoordsG` (the FRONT layers `t ≠ deepLayerS`
read `frontSlotG` coords, all `∉ topCoordsG`; the deep layer of `frontTupleG` is overridden downstream
by `chartGenParams`, so its value there is irrelevant to `frontProd`). Stated on the front-relevant
layers via `prodAux_congr_lt`; here for the full readoff we only need agreement off `topCoordsG` for the
front layers, which this supplies. -/
theorem frontTupleG_congr_front (M : Fin (L + 1) → ℕ) (hL : 0 < L)
    (hrs : r + s = M ((deepLayerS hL).castSucc)) {v w : Fin (routeMAmbient M) → ℝ}
    (h : ∀ m, m ∉ topCoordsG M hL hrs → v m = w m) (t : Fin L) (ht : t ≠ deepLayerS hL) :
    (frontTupleG M v) t = (frontTupleG M w) t := by
  funext i jf
  exact h _ (coordOfG_frontSlotG_not_mem M hL hrs t ht i jf)

/-- The front PRODUCT `frontProd M (frontTupleG v) = frontProd M (frontTupleG w)` when `v`, `w` agree
off `topCoordsG` — `frontProd = prodAux (L−1)` reads only the front layers `0..L−2`, all `≠ deepLayerS`,
which agree by `frontTupleG_congr_front`. -/
theorem frontProd_frontTupleG_congr (M : Fin (L + 1) → ℕ) (hL : 0 < L)
    (hrs : r + s = M ((deepLayerS hL).castSucc)) {v w : Fin (routeMAmbient M) → ℝ}
    (h : ∀ m, m ∉ topCoordsG M hL hrs → v m = w m) :
    frontProd M (frontTupleG M v) hL = frontProd M (frontTupleG M w) hL := by
  rw [frontProd, frontProd]
  refine prodAux_congr_lt M _ _ (L - 1) (by omega) (fun t ht => ?_)
  have htne : t ≠ deepLayerS hL := by
    intro hteq; rw [hteq] at ht; simp only [deepLayerS] at ht; omega
  exact frontTupleG_congr_front M hL hrs h t htne

/-- `SbotuG v = SbotuG w` if `v`, `w` agree off `topCoordsG` (`S_bot` reads bottom slots, `∉ topCoordsG`). -/
theorem SbotuG_congr (M : Fin (L + 1) → ℕ) (hL : 0 < L)
    (hrs : r + s = M ((deepLayerS hL).castSucc)) {v w : Fin (routeMAmbient M) → ℝ}
    (h : ∀ m, m ∉ topCoordsG M hL hrs → v m = w m) : SbotuG M hL hrs v = SbotuG M hL hrs w := by
  funext b j
  exact h _ (coordOfG_botSlotG_not_mem M hL hrs b j)

/-- `Lam0uG v = Lam0uG w` if `v`, `w` agree off `topCoordsG` (`Λ₀` is built from `frontProd`'s columns
`P₁`/`P₂`, which are `frontProd`-invariant off `topCoordsG`). -/
theorem Lam0uG_congr (M : Fin (L + 1) → ℕ) (hL : 0 < L)
    (hrs : r + s = M ((deepLayerS hL).castSucc)) {v w : Fin (routeMAmbient M) → ℝ}
    (h : ∀ m, m ∉ topCoordsG M hL hrs → v m = w m) : Lam0uG M hL hrs v = Lam0uG M hL hrs w := by
  have hFP := frontProd_frontTupleG_congr M hL hrs h
  have hP1 : P1uG M hL hrs v = P1uG M hL hrs w := by funext i a; simp only [P1uG, hFP]
  have hP2 : P2uG M hL hrs v = P2uG M hL hrs w := by funext i b; simp only [P2uG, hFP]
  rw [Lam0uG, Lam0uG, hP1, hP2]

/-! ## The smeared shear `shiftFullG` (the `−Λ₀·S_bot` correction, by an injective single-term sum) -/

/-- The full-vector correction `−∑_{a,j} [coordOfG(topSlotG a j) = m]·(Λ₀ v'·S_bot v') a j`. At a
deepest-top coord `m = coordOfG(topSlotG a₀ j₀)` it collapses to `−(Λ₀·S_bot) a₀ j₀`; off `topCoordsG`
it is `0`. -/
noncomputable def shiftFullG (M : Fin (L + 1) → ℕ) (hL : 0 < L)
    (hrs : r + s = M ((deepLayerS hL).castSucc)) (v' : Fin (routeMAmbient M) → ℝ)
    (m : Fin (routeMAmbient M)) : ℝ :=
  -∑ a : Fin r, ∑ j : Fin (M ((deepLayerS hL).succ)),
    (if coordOfG M (topSlotG M hL hrs a j) = m
      then (Lam0uG M hL hrs v' * SbotuG M hL hrs v') a j else 0)

/-- **The single-term collapse.** At a deepest-top coord, `shiftFullG` reads off the `(a,j)` correction
(the `coordOfG (topSlotG ·)` injectivity kills every off-diagonal term). -/
theorem shiftFullG_topSlotG (M : Fin (L + 1) → ℕ) (hL : 0 < L)
    (hrs : r + s = M ((deepLayerS hL).castSucc)) (v' : Fin (routeMAmbient M) → ℝ)
    (a₀ : Fin r) (j₀ : Fin (M ((deepLayerS hL).succ))) :
    shiftFullG M hL hrs v' (coordOfG M (topSlotG M hL hrs a₀ j₀))
      = -(Lam0uG M hL hrs v' * SbotuG M hL hrs v') a₀ j₀ := by
  have hcol : ∀ (a : Fin r) (j : Fin (M ((deepLayerS hL).succ))),
      topSlotG M hL hrs a j = topSlotG M hL hrs a₀ j₀ → j = j₀ := fun a j h =>
    Fin.ext (congrArg (fun q : FlatIdx M => (q.2.val : ℕ)) h)
  have hrow : ∀ (a : Fin r) (j : Fin (M ((deepLayerS hL).succ))),
      topSlotG M hL hrs a j = topSlotG M hL hrs a₀ j₀ → a = a₀ := by
    intro a j h
    have hv : (deepWidthEquiv hrs (Sum.inl a) : Fin (M ((deepLayerS hL).castSucc))).val
        = (deepWidthEquiv hrs (Sum.inl a₀) : Fin (M ((deepLayerS hL).castSucc))).val :=
      congrArg (fun q : FlatIdx M => (q.1.2.val : ℕ)) h
    have he : deepWidthEquiv hrs (Sum.inl a) = deepWidthEquiv hrs (Sum.inl a₀) := Fin.ext hv
    exact Sum.inl_injective ((deepWidthEquiv hrs).injective he)
  rw [shiftFullG, neg_inj, Finset.sum_eq_single a₀]
  · rw [Finset.sum_eq_single j₀]
    · rw [if_pos rfl]
    · intro j _ hj
      refine if_neg (fun hcoord => hj ?_)
      exact hcol a₀ j (coordOfG_injective M hcoord)
    · intro hj0; exact absurd (Finset.mem_univ j₀) hj0
  · intro a _ ha
    refine Finset.sum_eq_zero (fun j _ => if_neg (fun hcoord => ha ?_))
    exact hrow a j (coordOfG_injective M hcoord)
  · intro ha0; exact absurd (Finset.mem_univ a₀) ha0

/-! ## The smeared shear `shiftCoreG` + the flat map `ψ`, and the DECODE -/

/-- The shear shift (the `(reg, spec) → core` form `shearMBody` consumes): reconstruct the full vector
from the spec block (zero core), then read `shiftFullG` at the `coreSet.equivFin.symm`-indexed coord. -/
noncomputable def shiftCoreG (M : Fin (L + 1) → ℕ) (hL : 0 < L)
    (hrs : r + s = M ((deepLayerS hL).castSucc))
    (q : (Fin 0 → ℝ) × (Fin (topCoordsG M hL hrs)ᶜ.card → ℝ)) :
    Fin (topCoordsG M hL hrs).card → ℝ :=
  fun jc => shiftFullG M hL hrs
    ((splitOfCoreSet (topCoordsG M hL hrs)).symm
      (q.1, ((0 : Fin (topCoordsG M hL hrs).card → ℝ), q.2)))
    ((topCoordsG M hL hrs).equivFin.symm jc)

/-- The flat smeared map `ψ = paramsEquivFlat ∘ packM ∘ shearMBody`,
`packM := (flatEquivOf (slotEquivG)).symm`. -/
noncomputable def psiMapG (M : Fin (L + 1) → ℕ) (hL : 0 < L)
    (hrs : r + s = M ((deepLayerS hL).castSucc)) :
    (Fin (routeMAmbient M) → ℝ) → (Fin (routeMAmbient M) → ℝ) :=
  fun w => paramsEquivFlat M
    ((flatEquivOf M (slotEquivG M)).symm
      (shearMBody (topCoordsG M hL hrs) (shiftCoreG M hL hrs) w))

/-- **The shear-shift value at a deepest-top coord** (`shiftCoreG` collapse): at the `equivFin` index
of `coordOfG (topSlotG a j)` it is `−(Λ₀·S_bot) a j`. The `equivFin` round-trip + `shiftFullG_topSlotG`
+ the reconstruction's `topCoordsGᶜ`-agreement with `RmapG u` (`= u`). -/
theorem shiftCoreG_at_topSlotG (M : Fin (L + 1) → ℕ) (hL : 0 < L)
    (hrs : r + s = M ((deepLayerS hL).castSucc)) (hr : 0 < r) (hc : 0 < M ((deepLayerS hL).succ))
    (u : Fin (routeMAmbient M) → ℝ) (a : Fin r) (j : Fin (M ((deepLayerS hL).succ)))
    (hmem : coordOfG M (topSlotG M hL hrs a j) ∈ topCoordsG M hL hrs) :
    shiftCoreG M hL hrs
        ((splitOfCoreSet (topCoordsG M hL hrs) (RmapG M hL hrs hr hc u)).1,
          (splitOfCoreSet (topCoordsG M hL hrs) (RmapG M hL hrs hr hc u)).2.2)
        ((topCoordsG M hL hrs).equivFin ⟨coordOfG M (topSlotG M hL hrs a j), hmem⟩)
      = -(Lam0uG M hL hrs u * SbotuG M hL hrs u) a j := by
  rw [shiftCoreG, Equiv.symm_apply_apply]
  set v := (splitOfCoreSet (topCoordsG M hL hrs)).symm
    ((splitOfCoreSet (topCoordsG M hL hrs) (RmapG M hL hrs hr hc u)).1,
      ((0 : Fin (topCoordsG M hL hrs).card → ℝ),
        (splitOfCoreSet (topCoordsG M hL hrs) (RmapG M hL hrs hr hc u)).2.2)) with hv
  have hagree : ∀ m, m ∉ topCoordsG M hL hrs → v m = u m := by
    intro m hm
    rw [hv, splitOfCoreSet_symm_specBlock_eq _ _ _ _ hm, RmapG_spectator M hL hrs hr hc u hm]
  rw [shiftFullG_topSlotG, Lam0uG_congr M hL hrs hagree, SbotuG_congr M hL hrs hagree]

/-- **The packM readback.** `packM (shearMBody … w) layer i j = shearMBody … w (coordOfG ⟨⟨layer,i⟩,j⟩)`
(the `flatEquivOf_symm_coord` extraction at `e := slotEquivG M`). -/
theorem packM_shearG_entry (M : Fin (L + 1) → ℕ) (hL : 0 < L)
    (hrs : r + s = M ((deepLayerS hL).castSucc)) (w : Fin (routeMAmbient M) → ℝ) (q : FlatIdx M) :
    ((flatEquivOf M (slotEquivG M)).symm
        (shearMBody (topCoordsG M hL hrs) (shiftCoreG M hL hrs) w)) q.1.1 q.1.2 q.2
      = shearMBody (topCoordsG M hL hrs) (shiftCoreG M hL hrs) w (coordOfG M q) := by
  rw [flatEquivOf_symm_coord]; rfl

/-- **The deep-layer readback at a top row.** The shear readback at `coordOfG (topSlotG a j)` is the
`(a,j)` entry of the radial-minus-shear block `z·H̄_unit − Λ₀·S_bot`. -/
theorem shearG_topSlotG (M : Fin (L + 1) → ℕ) (hL : 0 < L)
    (hrs : r + s = M ((deepLayerS hL).castSucc)) (hr : 0 < r) (hc : 0 < M ((deepLayerS hL).succ))
    (u : Fin (routeMAmbient M) → ℝ) (a : Fin r) (j : Fin (M ((deepLayerS hL).succ))) :
    shearMBody (topCoordsG M hL hrs) (shiftCoreG M hL hrs) (RmapG M hL hrs hr hc u)
        (coordOfG M (topSlotG M hL hrs a j))
      = (zuG M hL hrs hr hc u • HbarUnitG M hL hrs hr hc u
          - Lam0uG M hL hrs u * SbotuG M hL hrs u) a j := by
  have hmem := coordOfG_topSlotG_mem M hL hrs a j
  rw [shearMBody_apply_of_mem _ _ _ hmem,
    shiftCoreG_at_topSlotG M hL hrs hr hc u a j hmem, RmapG_topSlotG M hL hrs hr hc u a j,
    Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  ring

/-- **The deep-layer readback at a bottom row.** The shear readback at `coordOfG (botSlotG b j)` is the
free residual `S_bot b j` (a bottom slot is `∉ topCoordsG`, so `shearMBody`/`RmapG` leave it untouched). -/
theorem shearG_botSlotG (M : Fin (L + 1) → ℕ) (hL : 0 < L)
    (hrs : r + s = M ((deepLayerS hL).castSucc)) (hr : 0 < r) (hc : 0 < M ((deepLayerS hL).succ))
    (u : Fin (routeMAmbient M) → ℝ) (b : Fin s) (j : Fin (M ((deepLayerS hL).succ))) :
    shearMBody (topCoordsG M hL hrs) (shiftCoreG M hL hrs) (RmapG M hL hrs hr hc u)
        (coordOfG M (botSlotG M hL hrs b j))
      = SbotuG M hL hrs u b j := by
  rw [shearMBody_apply_of_not_mem _ _ _ (coordOfG_botSlotG_not_mem M hL hrs b j),
    RmapG_spectator M hL hrs hr hc u (coordOfG_botSlotG_not_mem M hL hrs b j)]
  rfl

/-- **The deep-row equiv bridge.** `finCongr e1 ∘ deepWidthEquiv hrsAtom = deepWidthEquiv hrs` — both
map `Fin r ⊕ Fin s` to the (propositionally equal) deepest row types via the same `finSumFinEquiv`, so
the underlying vals agree. Lets the atom's `hrsAtom`-split match the FlatIdx-natural `hrs`-split. -/
theorem finCongr_e1_deepWidthEquiv (M : Fin (L + 1) → ℕ) (hL : 0 < L)
    (hrs : r + s = M ((deepLayerS hL).castSucc))
    (e1 : M (⟨L - 1, by omega⟩ : Fin (L + 1)) = M ((⟨L - 1, by omega⟩ : Fin L).castSucc))
    (x : Fin r ⊕ Fin s) :
    ((finCongr e1) (deepWidthEquiv (hrsAtom_of_hrs hL hrs) x) : Fin (M ((deepLayerS hL).castSucc)))
      = deepWidthEquiv hrs x := by
  apply Fin.ext
  simp only [finCongr_apply, Fin.val_cast, deepWidthEquiv, Equiv.trans_apply, Fin.val_cast]

/-- The `symm` form: `(deepWidthEquiv hrsAtom).symm ((finCongr e1).symm i) = (deepWidthEquiv hrs).symm i`. -/
theorem deepWidthEquiv_symm_finCongr_e1 (M : Fin (L + 1) → ℕ) (hL : 0 < L)
    (hrs : r + s = M ((deepLayerS hL).castSucc))
    (e1 : M (⟨L - 1, by omega⟩ : Fin (L + 1)) = M ((⟨L - 1, by omega⟩ : Fin L).castSucc))
    (i : Fin (M ((deepLayerS hL).castSucc))) :
    (deepWidthEquiv (hrsAtom_of_hrs hL hrs)).symm ((finCongr e1).symm i)
      = (deepWidthEquiv hrs).symm i := by
  apply (deepWidthEquiv hrs).injective
  rw [Equiv.apply_symm_apply, ← finCongr_e1_deepWidthEquiv M hL hrs e1, Equiv.apply_symm_apply,
    Equiv.apply_symm_apply]

/-- **Column-cast readback.** Reading a col-cast matrix `h ▸ X` at `k` equals reading `X` at
`finCongr h.symm k` (`subst h; rfl`). -/
theorem cast_col_apply {p w1 w2 : ℕ} (X : Matrix (Fin p) (Fin w1) ℝ) (h : w1 = w2)
    (a : Fin p) (k : Fin w2) : (h ▸ X) a k = X a (finCongr h.symm k) := by
  subst h; rfl

/-! ## The Params-level DECODE `packM (shearMBody (R u)) = chartGenParams …` -/

/-- **The Params-level DECODE.** `packM (shearMBody (R u)) = chartGenParams M (frontTupleG u) hL …`.
The FRONT layers `t ≠ deepLayerS` are the identity readoff (`frontTupleG`, coords `∉ topCoordsG`,
shear-untouched); the deep layer `L−1` is the `deepWidthEquiv` row split (top `r` rows the
radial-minus-shear `z·H̄_unit − Λ₀·S_bot`, bottom `s` rows the free residual `S_bot`). Dispatch by
`layer = deepLayerS?` (NOT `fin_cases` — `layer : Fin L` is opaque). -/
theorem genDecode_params (M : Fin (L + 1) → ℕ) (hL : 0 < L)
    (hrs : r + s = M ((deepLayerS hL).castSucc)) (hr : 0 < r) (hc : 0 < M ((deepLayerS hL).succ))
    (u : Fin (routeMAmbient M) → ℝ)
    (e1 : M (⟨L - 1, by omega⟩ : Fin (L + 1)) = M ((⟨L - 1, by omega⟩ : Fin L).castSucc))
    (e2 : M (Fin.last L) = M ((⟨L - 1, by omega⟩ : Fin L).succ)) :
    (flatEquivOf M (slotEquivG M)).symm
        (shearMBody (topCoordsG M hL hrs) (shiftCoreG M hL hrs) (RmapG M hL hrs hr hc u))
      = chartGenParams M (frontTupleG M u) hL (hrsAtom_of_hrs hL hrs) (zuG M hL hrs hr hc u)
          ((deepLayerS_succ_width M hL) ▸ HbarUnitG M hL hrs hr hc u)
          ((deepLayerS_succ_width M hL) ▸ SbotuG M hL hrs u) (Lam0uG M hL hrs u) e1 e2 := by
  funext layer i j
  rw [packM_shearG_entry M hL hrs (RmapG M hL hrs hr hc u) ⟨⟨layer, i⟩, j⟩]
  by_cases hlayer : layer = deepLayerS hL
  · -- DEEP layer: the row split (top `r` radial-minus-shear, bottom `s` residual)
    subst hlayer
    -- evaluate `chartGenParams … (deepLayerS) i j` = `reindex … chartGenDeep` at `(i,j)`
    have hd : (deepLayerS hL) = (⟨L - 1, by omega⟩ : Fin L) := rfl
    rw [chartGenParams]
    simp only [Function.update, hd, dif_pos]
    rw [Matrix.reindex_apply, Matrix.submatrix_apply, chartGenDeep,
      deepWidthEquiv_symm_finCongr_e1 M hL hrs e1]
    -- split the row `i` via `deepWidthEquiv hrs`
    rcases hsplit : (deepWidthEquiv hrs).symm i with a | b
    · -- TOP row `i = deepWidthEquiv (inl a)`: the slot is `topSlotG a j`
      have hi : i = deepWidthEquiv hrs (Sum.inl a) := by
        rw [← hsplit, Equiv.apply_symm_apply]
      have hslot : (⟨⟨deepLayerS hL, i⟩, j⟩ : FlatIdx M) = topSlotG M hL hrs a j := by
        rw [topSlotG, hi]
      rw [hslot, shearG_topSlotG M hL hrs hr hc u a j, deepBlock, Sum.elim_inl]
      -- reconcile the col cast: `(z•(h▸H) − Λ₀(h▸S)) a ((finCongr e2).symm j) = (z•H − Λ₀S) a j`
      rw [Matrix.sub_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.smul_apply,
        cast_col_apply, Matrix.mul_apply, Matrix.mul_apply]
      congr 2
      funext k
      rw [cast_col_apply]
      rfl
    · -- BOTTOM row `i = deepWidthEquiv (inr b)`: the slot is `botSlotG b j`, the free residual
      have hi : i = deepWidthEquiv hrs (Sum.inr b) := by
        rw [← hsplit, Equiv.apply_symm_apply]
      have hslot : (⟨⟨deepLayerS hL, i⟩, j⟩ : FlatIdx M) = botSlotG M hL hrs b j := by
        rw [botSlotG, hi]
      rw [hslot, shearG_botSlotG M hL hrs hr hc u b j, deepBlock, Sum.elim_inr, cast_col_apply]
      rfl
  · -- FRONT layer: the identity readoff `frontTupleG`, coords `∉ topCoordsG`
    have hlayer' : layer ≠ (⟨L - 1, by omega⟩ : Fin L) := by
      intro h; exact hlayer (by rw [h]; rfl)
    rw [chartGenParams, Function.update_of_ne hlayer']
    show shearMBody (topCoordsG M hL hrs) (shiftCoreG M hL hrs) (RmapG M hL hrs hr hc u)
        (coordOfG M (frontSlotG M layer i j)) = frontTupleG M u layer i j
    rw [shearMBody_apply_of_not_mem _ _ _ (coordOfG_frontSlotG_not_mem M hL hrs layer hlayer i j),
      RmapG_spectator M hL hrs hr hc u (coordOfG_frontSlotG_not_mem M hL hrs layer hlayer i j)]
    rfl

/-! ## The radial blow-up `RmapG` fderiv / injectivity / det + the card -/

/-- `topCoordsG` has card `r · M (deepLayerS).succ` (the `r·c` deepest-top coords). -/
theorem topCoordsG_card (M : Fin (L + 1) → ℕ) (hL : 0 < L)
    (hrs : r + s = M ((deepLayerS hL).castSucc)) :
    (topCoordsG M hL hrs).card = r * M ((deepLayerS hL).succ) := by
  rw [topCoordsG, Finset.card_image_of_injective _ ?_, Finset.card_univ, Fintype.card_prod,
    Fintype.card_fin, Fintype.card_fin]
  · rintro ⟨a, j⟩ ⟨a', j'⟩ h
    have hslot : topSlotG M hL hrs a j = topSlotG M hL hrs a' j' := coordOfG_injective M h
    have hj : j = j' := Fin.ext (congrArg (fun q : FlatIdx M => (q.2.val : ℕ)) hslot)
    have hrow : (deepWidthEquiv hrs (Sum.inl a) : Fin (M ((deepLayerS hL).castSucc)))
        = deepWidthEquiv hrs (Sum.inl a') :=
      Fin.ext (congrArg (fun q : FlatIdx M => (q.1.2.val : ℕ)) hslot)
    have ha : a = a' := Sum.inl_injective ((deepWidthEquiv hrs).injective hrow)
    rw [ha, hj]

/-- The fderiv carrier `DmapG u := pivotBlowupOnDeriv topCoordsG pivotCoordG u`. -/
noncomputable def DmapG (M : Fin (L + 1) → ℕ) (hL : 0 < L)
    (hrs : r + s = M ((deepLayerS hL).castSucc)) (hr : 0 < r) (hc : 0 < M ((deepLayerS hL).succ))
    (u : Fin (routeMAmbient M) → ℝ) :
    (Fin (routeMAmbient M) → ℝ) →L[ℝ] (Fin (routeMAmbient M) → ℝ) :=
  pivotBlowupOnDeriv (topCoordsG M hL hrs) (pivotCoordG M hL hrs hr hc) u

/-- `RmapG` has fderiv `DmapG` on any set (`pivotBlowupOn_hasFDerivWithinAt`). -/
theorem RmapG_hasFDerivWithinAt (M : Fin (L + 1) → ℕ) (hL : 0 < L)
    (hrs : r + s = M ((deepLayerS hL).castSucc)) (hr : 0 < r) (hc : 0 < M ((deepLayerS hL).succ))
    (S : Set (Fin (routeMAmbient M) → ℝ)) (u : Fin (routeMAmbient M) → ℝ) :
    HasFDerivWithinAt (RmapG M hL hrs hr hc) (DmapG M hL hrs hr hc u) S u :=
  pivotBlowupOn_hasFDerivWithinAt _ _ S u

/-- `RmapG` is injective off `{u pivot = 0}` (`pivotBlowupOn_injOn`). -/
theorem RmapG_injOn (M : Fin (L + 1) → ℕ) (hL : 0 < L)
    (hrs : r + s = M ((deepLayerS hL).castSucc)) (hr : 0 < r) (hc : 0 < M ((deepLayerS hL).succ))
    (S : Set (Fin (routeMAmbient M) → ℝ)) :
    Set.InjOn (RmapG M hL hrs hr hc) (S \ {x | x (pivotCoordG M hL hrs hr hc) = 0}) :=
  pivotBlowupOn_injOn _ _ S

/-- `|det (DmapG u)| = |u pivot|^(r·M(deepLayerS).succ − 1)` (`pivotBlowupOnDeriv_det`, card `= r·c`). -/
theorem DmapG_abs_det (M : Fin (L + 1) → ℕ) (hL : 0 < L)
    (hrs : r + s = M ((deepLayerS hL).castSucc)) (hr : 0 < r) (hc : 0 < M ((deepLayerS hL).succ))
    (u : Fin (routeMAmbient M) → ℝ) :
    |(DmapG M hL hrs hr hc u).det|
      = |u (pivotCoordG M hL hrs hr hc)| ^ (r * M ((deepLayerS hL).succ) - 1) := by
  rw [DmapG, pivotBlowupOnDeriv_det _ _ (pivotCoordG_mem M hL hrs hr hc), topCoordsG_card, abs_pow]

/-! ## The general-`L` smeared rate `routeMCore M (ψ (R u)) = (zu u)²·‖P₁·H̄‖²` -/

/-- **The general-`L` opaque-width smeared rate** `routeMCore M (psiMapG (RmapG u)) = (zuG u)²·U`,
`U = ‖P₁·H̄_unit‖²`, off the shear cancellation `P₁·Λ₀ = P₂`. The DECODE (`genDecode_params`) says
`(paramsEquivFlat M).symm (psiMapG (RmapG u)) = chartGenParams …`; the atom's chart-eval collapse
(`prod_chartGen_collapse`, off the cancellation) gives `prod M (chartGenParams …) = z • (P₁·H̄)`; then
`routeMCore_rate_of_prod_collapsed` reads off the rate. -/
theorem routeMCore_psiMapG_RmapG (M : Fin (L + 1) → ℕ) (hL : 0 < L)
    (hrs : r + s = M ((deepLayerS hL).castSucc)) (hr : 0 < r) (hc : 0 < M ((deepLayerS hL).succ))
    (u : Fin (routeMAmbient M) → ℝ)
    (e1 : M (⟨L - 1, by omega⟩ : Fin (L + 1)) = M ((⟨L - 1, by omega⟩ : Fin L).castSucc))
    (e2 : M (Fin.last L) = M ((⟨L - 1, by omega⟩ : Fin L).succ))
    (hcancel : P1uG M hL hrs u * Lam0uG M hL hrs u = P2uG M hL hrs u) :
    routeMCore M (psiMapG M hL hrs (RmapG M hL hrs hr hc u))
      = (zuG M hL hrs hr hc u) ^ 2
        * ∑ i, ∑ j, ((P1uG M hL hrs u
            * ((deepLayerS_succ_width M hL) ▸ HbarUnitG M hL hrs hr hc u)) i j) ^ 2 := by
  -- the decode: `(paramsEquivFlat M).symm (psiMapG (RmapG u)) = chartGenParams …`
  have hdecode : (paramsEquivFlat M).symm (psiMapG M hL hrs (RmapG M hL hrs hr hc u))
      = chartGenParams M (frontTupleG M u) hL (hrsAtom_of_hrs hL hrs) (zuG M hL hrs hr hc u)
          ((deepLayerS_succ_width M hL) ▸ HbarUnitG M hL hrs hr hc u)
          ((deepLayerS_succ_width M hL) ▸ SbotuG M hL hrs u) (Lam0uG M hL hrs u) e1 e2 := by
    rw [psiMapG, MeasurableEquiv.symm_apply_apply]
    exact genDecode_params M hL hrs hr hc u e1 e2
  -- the chart-eval collapse `prod M (chartGenParams …) = z • (P₁·H̄)`
  have hcollapse : prod M ((paramsEquivFlat M).symm (psiMapG M hL hrs (RmapG M hL hrs hr hc u)))
      = (zuG M hL hrs hr hc u)
        • (P1uG M hL hrs u * ((deepLayerS_succ_width M hL) ▸ HbarUnitG M hL hrs hr hc u)) := by
    rw [hdecode]
    exact prod_chartGen_collapse M (frontTupleG M u) hL (hrsAtom_of_hrs hL hrs)
      (zuG M hL hrs hr hc u) _ _ (Lam0uG M hL hrs u) e1 e2
      (P1uG M hL hrs u) (P2uG M hL hrs u) (fun i k => rfl) (fun i k => rfl) hcancel
  rw [routeMCore_rate_of_prod_collapsed M (psiMapG M hL hrs) (RmapG M hL hrs hr hc u)
    (zuG M hL hrs hr hc u) _ hcollapse]

/-- The `z`-free unit `U = ‖P₁·H̄_unit‖²_F` (the polynomial factor of the rate `F = z²·U`). Stated at
the FlatIdx col width `M (deepLayerS).succ` (no cast needed — `H̄_unit` and `P₁` live there natively). -/
noncomputable def UunitG (M : Fin (L + 1) → ℕ) (hL : 0 < L)
    (hrs : r + s = M ((deepLayerS hL).castSucc)) (hr : 0 < r) (hc : 0 < M ((deepLayerS hL).succ))
    (u : Fin (routeMAmbient M) → ℝ) : ℝ :=
  ∑ i, ∑ j, ((P1uG M hL hrs u * HbarUnitG M hL hrs hr hc u) i j) ^ 2

/-- `UunitG ≥ 0` (a sum of squares). -/
theorem UunitG_nonneg (M : Fin (L + 1) → ℕ) (hL : 0 < L)
    (hrs : r + s = M ((deepLayerS hL).castSucc)) (hr : 0 < r) (hc : 0 < M ((deepLayerS hL).succ))
    (u : Fin (routeMAmbient M) → ℝ) : (0 : ℝ) ≤ UunitG M hL hrs hr hc u :=
  frobeniusSq_nonneg _

/-- The cast-cancelled `Frobenius` sum: `∑ (P₁·(h▸H))ᵢⱼ² = ∑ (P₁·H)ᵢⱼ² = UunitG`. The `▸` col-cast on
`H̄` in the rate bridge does not change the sum of squares (`cast_col_apply` + reindex the `j` sum). -/
theorem frobeniusSq_P1_Hbar_cast (M : Fin (L + 1) → ℕ) (hL : 0 < L)
    (hrs : r + s = M ((deepLayerS hL).castSucc)) (hr : 0 < r) (hc : 0 < M ((deepLayerS hL).succ))
    (u : Fin (routeMAmbient M) → ℝ) :
    (∑ i, ∑ j, ((P1uG M hL hrs u
        * ((deepLayerS_succ_width M hL) ▸ HbarUnitG M hL hrs hr hc u)) i j) ^ 2)
      = UunitG M hL hrs hr hc u := by
  rw [UunitG]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  -- match the LHS `j : Fin (M (last L))` sum with the RHS `j : Fin (M (deepLayerS).succ)` sum via the
  -- col-type equiv `finCongr (deepLayerS_succ_width).symm`, matching each summand by `cast_col_apply`
  refine Fintype.sum_equiv (finCongr (deepLayerS_succ_width M hL).symm)
    (fun j => ((P1uG M hL hrs u
      * ((deepLayerS_succ_width M hL) ▸ HbarUnitG M hL hrs hr hc u)) i j) ^ 2)
    (fun j => ((P1uG M hL hrs u * HbarUnitG M hL hrs hr hc u) i j) ^ 2) (fun j => ?_)
  show ((P1uG M hL hrs u
        * ((deepLayerS_succ_width M hL) ▸ HbarUnitG M hL hrs hr hc u)) i j) ^ 2
      = ((P1uG M hL hrs u * HbarUnitG M hL hrs hr hc u) i
          ((finCongr (deepLayerS_succ_width M hL).symm) j)) ^ 2
  congr 2
  rw [Matrix.mul_apply, Matrix.mul_apply]
  exact Finset.sum_congr rfl (fun k _ => by rw [cast_col_apply])

/-! ## `UunitG` is `z`-free (does not read the radial pivot) -/

/-- `HbarUnitG` does not read the pivot coord (the pivot entry is the constant `1`; the others are
non-pivot). -/
theorem HbarUnitG_congr_off_pivot (M : Fin (L + 1) → ℕ) (hL : 0 < L)
    (hrs : r + s = M ((deepLayerS hL).castSucc)) (hr : 0 < r) (hc : 0 < M ((deepLayerS hL).succ))
    {v w : Fin (routeMAmbient M) → ℝ}
    (h : ∀ m, m ≠ pivotCoordG M hL hrs hr hc → v m = w m) :
    HbarUnitG M hL hrs hr hc v = HbarUnitG M hL hrs hr hc w := by
  funext a j
  simp only [HbarUnitG]
  by_cases hpiv : coordOfG M (topSlotG M hL hrs a j) = pivotCoordG M hL hrs hr hc
  · rw [if_pos hpiv, if_pos hpiv]
  · rw [if_neg hpiv, if_neg hpiv, h _ hpiv]

/-- `UunitG` does not read the pivot coord (`z`-free): built from `frontProd` (front, `∉ {pivot}`) and
`HbarUnitG` (pivot entry fixed). -/
theorem UunitG_congr_off_pivot (M : Fin (L + 1) → ℕ) (hL : 0 < L)
    (hrs : r + s = M ((deepLayerS hL).castSucc)) (hr : 0 < r) (hc : 0 < M ((deepLayerS hL).succ))
    {v w : Fin (routeMAmbient M) → ℝ}
    (h : ∀ m, m ≠ pivotCoordG M hL hrs hr hc → v m = w m) :
    UunitG M hL hrs hr hc v = UunitG M hL hrs hr hc w := by
  -- the front layers agree off `{pivot}` (a front slot coord `= pivot = coordOfG (topSlot ⟨0⟩⟨0⟩)`
  -- would force `frontSlot = topSlot`, impossible), so `frontProd` (hence `P₁`) is unchanged
  have hfront : ∀ (t : Fin L), t ≠ deepLayerS hL → (frontTupleG M v) t = (frontTupleG M w) t := by
    intro t ht
    funext i jf
    refine h _ (fun hcoord => ?_)
    exact frontSlotG_ne_topSlotG M hL hrs t ht i jf ⟨0, hr⟩ ⟨0, hc⟩ (coordOfG_injective M hcoord)
  have hFP : frontProd M (frontTupleG M v) hL = frontProd M (frontTupleG M w) hL := by
    rw [frontProd, frontProd]
    exact prodAux_congr_lt M _ _ (L - 1) (by omega) (fun t ht => hfront t (by
      intro hteq; rw [hteq] at ht; simp only [deepLayerS] at ht; omega))
  have hP1 : P1uG M hL hrs v = P1uG M hL hrs w := by funext i a; simp only [P1uG, hFP]
  have hHbar : HbarUnitG M hL hrs hr hc v = HbarUnitG M hL hrs hr hc w :=
    HbarUnitG_congr_off_pivot M hL hrs hr hc h
  rw [UunitG, UunitG, hP1, hHbar]

end DLNFibre.DLN.RLCT
