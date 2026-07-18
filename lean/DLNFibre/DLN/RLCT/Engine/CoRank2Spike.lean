import DLNFibre.DLN.RLCT.Engine.EngineObligations

/-!
# `DLNFibre.DLN.RLCT.Engine.CoRank2Spike` — a corank-2 coordinate-index spike (rung 2C)

A single **corank-2** `LeafData` de-risk: at `M = (3,3,4)` the deepest full-block chart has ONE
shared exceptional divisor (`numDiv = 1`) and a genuine Morse residual of rank `8` (the transverse
on-core rank — `map/battery/g-resrank-minadm.py`), against the flat ambient `flatDim (3,3,4) =
3·3 + 3·4 = 21`. This spike confirms the `Fin (flatDim M)` coordinate-index bookkeeping the
`ChartBridge` per-leaf clause demands (`divCoord`/`resCoord` injective + disjoint) elaborates and
discharges at corank ≥ 2 — where a single divisor is shared over multiple generators and the
residual block is large (`8 ≤ 21`, plenty of room). Nothing load-bearing beyond the coordinate model
(the leaf's other fields are placeholder-valid; this is NOT a `CanonicalResolution` witness).
-/

namespace DLNFibre.DLN.RLCT.Engine

open DLNFibre.DLN.RLCT
open scoped BigOperators

/-- The width vector `(3,3,4)` — the corank-2 instance (a `2×2` residual block shared over `8`
generators; `map/battery/g-coupled-binding-334.py`). -/
abbrev M334 : Fin 3 → ℕ := ![3, 3, 4]

/-- `flatDim (3,3,4) = 21` (`3·3 + 3·4`): the ambient the coordinate indices live in. -/
theorem flatDim_M334 : flatDim M334 = 21 := by
  rw [flatDim_eq]; decide

/-- A **corank-2 leaf**: one shared divisor (`numDiv = 1`) at flat coordinate `0`, and a rank-`8`
Morse residual at flat coordinates `1,…,8` — disjoint index blocks inside `Fin 21`. The pullback /
monomialisation fields are placeholder-valid; only the coordinate model is exercised. -/
noncomputable def corank2Leaf : LeafData M334 where
  numDiv := 1
  divExp := fun _ => 8
  divTilde := fun _ => 0
  cleared := 0
  divProfile := fun _ => ![0, 0]
  numB := 1; bExp := fun _ _ => 0; bChain := fun _ _ _ _ => le_refl _
  chartMap := id
  srcBox := ⇑(paramsEquivFlat M334) ⁻¹' cubeBox (flatDim M334) 1
  resRank := 8
  divCoord := fun _ => ⟨0, by rw [flatDim_M334]; decide⟩
  resCoord := fun i => ⟨i.val + 1, by rw [flatDim_M334]; omega⟩

/-- `divCoord` is injective (a `Fin 1`-indexed family is trivially injective). -/
theorem corank2Leaf_divCoord_injective : Function.Injective corank2Leaf.divCoord := by
  intro a b _
  have hnum : corank2Leaf.numDiv = 1 := rfl
  have ha := a.isLt; have hb := b.isLt
  exact Fin.ext (by omega)

/-- `resCoord` is injective — the `8` Morse coordinates `1,…,8` are distinct. -/
theorem corank2Leaf_resCoord_injective : Function.Injective corank2Leaf.resCoord := by
  intro i j h
  have hv : i.val + 1 = j.val + 1 := congrArg Fin.val h
  exact Fin.ext (by omega)

/-- The divisor and Morse coordinate blocks are disjoint (`{0}` vs `{1,…,8}`) — the `ChartBridge`
per-leaf disjointness clause, at corank 2. -/
theorem corank2Leaf_disjoint_coords :
    Disjoint (Set.range corank2Leaf.divCoord) (Set.range corank2Leaf.resCoord) := by
  rw [Set.disjoint_left]
  rintro x ⟨i, rfl⟩ ⟨j, hj⟩
  have hv : j.val + 1 = 0 := congrArg Fin.val hj
  omega

/-- The residual block fits the ambient: `resRank + numDiv = 9 ≤ flatDim = 21` (the coordinate model
has room at corank 2). -/
theorem corank2Leaf_fits : corank2Leaf.resRank + corank2Leaf.numDiv ≤ flatDim M334 := by
  rw [flatDim_M334]; decide

end DLNFibre.DLN.RLCT.Engine
