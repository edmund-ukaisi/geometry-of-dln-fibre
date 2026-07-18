import DLNFibre.DLN.RLCT.Engine.EngineDefs

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

/-! ## T-rule truth-witness at (3,3,4) — the load-bearing head-preservation case (pnp trace)

`leaf224` exercises the `T`-rule only trivially (case-2 at `layer = 0`: all tail).
The load-bearing case is a case-1(1) merge at `layer = 1`, where the head component is PRESERVED and
the tail written — the exact place a wrong `tail iff n.layer ≤ p.val` boundary would corrupt. These
pins reproduce pnp-atlas verdict-3's page-verified (3,3,4) values and confirm `divExp = Mval(T)`. -/

/-- A (3,3,4) case-1(1) parent at `layer = 1`: one divisor with profile `T = (1,1)`, `divExp = 4 =
Mval(1,1)`, residual cols `M⁽³⁾−J = 4`. -/
def node334 : StepData M334 where
  layer := 1; cleared := 0; resRows := 3; resCols := 4
  numDiv := 1; numB := 1; bExp := fun _ _ => 0; bChain := fun _ _ _ _ => le_refl _
  divExp := fun _ => 4; divProfile := fun _ => ![1, 1]; numGen := 0; support := fun k => k.elim0

/-- The case-1(1) merge substitution: `J₁ = 1`, target divisor `0`. -/
def subst334 : ChartSubst M334 where
  localSub := id; runLen := 1; mergeIdx := 0; jacDivCount := 1; jacPow := fun _ => 0

/-- **T-rule head-preservation** (pnp trace): the merge takes profile `(1,1) → (1,0)` — head
`t⁽¹⁾=1` PRESERVED (`layer = 1`, so `p = 0` is head), tail `t⁽²⁾ := J = 0`. -/
theorem node334_merge_divProfile :
    (stepUpdate node334 StepCase.case11 subst334).divProfile ⟨0, by decide⟩ = ![1, 0] := by decide

/-- **The merge is the binding divisor**: `divExp 4 → 8 = 4 + J₁·resCols = 4 + 1·4`, and
`8 = Mval (3,3,4) (1,0) = minAdm(3,3,4)` — the exponent bookkeeping agrees with the closed form
(the T4 coherence, at the binder). -/
theorem node334_merge_coherent :
    (stepUpdate node334 StepCase.case11 subst334).divExp ⟨0, by decide⟩ = 8 ∧
      (Mval M334 ![1, 0]).toNat = 8 := by decide

/-- **T-rule head-RESET** (pnp trace, case-2 at `layer = 1`): a new full-block pivot resets the head
to widths `t⁽¹⁾ := M⁽²⁾ = 3`, tail `t⁽²⁾ := J = 0` — profile `(3,0)`, and `divExp = resRows·resCols`
`= 12 = Mval (3,3,4) (3,0)`. -/
theorem node334_case2_divProfile :
    (stepUpdate node334 StepCase.case2 subst334).divProfile (Fin.last 1) = ![3, 0] ∧
      (Mval M334 ![3, 0]).toNat = 12 := by decide

end DLNFibre.DLN.RLCT.Engine
