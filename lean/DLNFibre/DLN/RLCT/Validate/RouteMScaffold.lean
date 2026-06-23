import DLNFibre.DLN.RLCT.Validate.RouteMRecursion
import DLNFibre.DLN.RLCT.Validate.RouteMBranch

/-!
# `DLNFibre.DLN.RLCT.Validate.RouteMScaffold` — the #121-independent general-`routeStep` scaffold (fm3 #99)

The co-build scaffold for the general `routeStep` body (#99), built so the realizability obligation that
gates the branch arm is a **named hypothesis** rather than a `sorry`. The dispatch logic, the recursion
carrier, the value fold — everything that does NOT depend on #121 (the achiever-witness realizability tie) —
is unconditional here; the one thing #121-(ii) fills is packaged as the `BranchData`-producer input.

## What is #121-independent (built here, no `sorry`)
- **`BranchData M₀ M`** — the branch arm's payload as DATA: a finite nonempty `cells` of pivot choices, a
  per-cell `split : cells → ChainDimSplit M` (the C1/C5 reduced-width descent), a per-cell `codim`, and the
  per-cell ROOT-anchored `PivotWitness M₀ (codim c)`. This is exactly the tuple `RouteStep.branch` consumes;
  packaging it as a structure names the boundary where #121 lives (the `witness` field — the achiever-witness
  realizability that the chart path reaches the stratum).
- **`routeStepOf`** — leaf-first dispatch consuming a `BranchData`-producer: `if isLeafNode M` then the ⊤
  non-binding terminal `leaf (leafMonoData 0)`, else `branch` from the supplied `BranchData`. No `sorry`,
  fully general `L`. The ONLY input is the `BranchData` hypothesis.
- **`routeAtlasOf`** — the chart-family recursion over `routeStepOf` (mirror of `routeAtlas`, but the
  branch payload comes from a `BranchData` family rather than the unconditional `routeStep`). Termination is
  `chainRel` (`ΣM`-drop) via `ChainDimSplit.redM_chainRel`, exactly as `routeAtlas`.

## The #121 boundary (NOT built here — the named hypothesis)
`routeStepOf` takes `hbranch : ¬ isLeafNode M → BranchData M₀ M`. Producing a `BranchData M₀ M` for an
ARBITRARY non-leaf `M` is the general rank-pattern read: the cell decomposition + per-cell codims are the
combinatorial pivot structure; the `witness` field's honesty (that each codim `= (Mval M₀ T).toNat` for a
`T` GENUINELY reached by a chart path) is the realizability tie #121-(ii) supplies. For finite instances
(`(2,2,2)`/`(3,2,3)`) the witnesses are `decide`-checkable (`Case222RouteStep`, threaded through
`RouteMBranch.routeStepBranch`); the general producer is #99/#121. This scaffold makes that the single
named input, not a `sorry` smuggled into the dispatcher (the trap-(iii) fence — `RouteMBranch` docstring).
-/

open scoped BigOperators
namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-- **The branch arm's payload, as DATA** (root `M₀`, current `M`). A finite nonempty `cells` of pivot
choices, a per-cell `split : cells → ChainDimSplit M` (the reduced-width descent), a per-cell `codim`, and
the per-cell ROOT-anchored `PivotWitness M₀ (codim c)`. Exactly the tuple `RouteStep.branch` consumes —
packaging it names the #121 boundary: the `witness` field is the achiever-witness realizability tie
(#121-(ii)), everything else is the combinatorial cell/codim read. NOT manufactured here. -/
structure BranchData (M₀ M : Fin (L + 1) → ℕ) where
  cells : Type
  cellsFin : Fintype cells
  cellsNe : Nonempty cells
  split : cells → ChainDimSplit M
  codim : cells → ℕ
  witness : (c : cells) → PivotWitness M₀ (codim c)

/-- A `BranchData M₀ M` assembles the `RouteStep.branch` directly (the honest branch term — consumes the
realizability witness, does not manufacture it). -/
def BranchData.toRouteStep {M₀ M : Fin (L + 1) → ℕ} (b : BranchData M₀ M) : RouteStep M₀ M :=
  .branch b.cells b.cellsFin b.cellsNe b.split b.codim b.witness

/-- **The general `routeStep` body, with realizability as a NAMED hypothesis** (#99 co-build scaffold).
The leaf-first dispatch: `if isLeafNode M` then the ⊤ non-binding terminal (`leaf (leafMonoData 0)` — its
node-RLCT is the descent's concern, NOT this value-fold datum), else the `branch` assembled from the
supplied `BranchData M₀ M`. No `sorry`, fully general `L`. The ONLY input is `hbranch` (the
`BranchData`-producer at a non-leaf node) — the #121-(ii) realizability tie + the combinatorial cell/codim
read. This replaces the named `sorry` in `RouteMRecursion.routeStep` with a named hypothesis. -/
noncomputable def routeStepOf (M₀ M : Fin (L + 1) → ℕ)
    (hbranch : ¬ isLeafNode M → BranchData M₀ M) : RouteStep M₀ M :=
  if hleaf : isLeafNode M then
    .leaf (leafMonoData 0)
  else
    (hbranch hleaf).toRouteStep

/-- The leaf arm of `routeStepOf`: at a leaf node it is the ⊤ non-binding terminal, independent of the
`BranchData`-producer. -/
theorem routeStepOf_leaf {M₀ M : Fin (L + 1) → ℕ}
    (hbranch : ¬ isLeafNode M → BranchData M₀ M) (hleaf : isLeafNode M) :
    routeStepOf M₀ M hbranch = .leaf (leafMonoData 0) := by
  unfold routeStepOf; rw [dif_pos hleaf]

/-- The branch arm of `routeStepOf`: at a non-leaf node it is the `BranchData`'s assembled branch
term. -/
theorem routeStepOf_branch {M₀ M : Fin (L + 1) → ℕ}
    (hbranch : ¬ isLeafNode M → BranchData M₀ M) (hleaf : ¬ isLeafNode M) :
    routeStepOf M₀ M hbranch = (hbranch hleaf).toRouteStep := by
  unfold routeStepOf; rw [dif_neg hleaf]

/-! ## The chart-family recursion over `routeStepOf`

`routeAtlasOf` mirrors `RouteMRecursion.routeAtlas` but the branch payload at each non-leaf node comes
from a `BranchData` family (the #121-independent recursion: given the per-node `BranchData`-producer, the
well-founded `chainRel` recursion builds the `NodeChartFamily`). The recursive call on `(split c).red` is
justified by `ChainDimSplit.redM_chainRel` exactly as in `routeAtlas`; the root `M₀` is UNCHANGED on
descent (the witnesses stay root-anchored). -/

/-- **The Route-M chart-family recursion over `routeStepOf`** (the #121-independent recursion). With the
root ambient `M₀` FIXED and a per-node `BranchData`-producer `hbranch`, well-founded recursion on
`chainRel` (`ΣM`-drop) builds the `NodeChartFamily`: a leaf node ↦ a single chart with `leafMonoData 0`; a
branch node ↦ the `Σ` over the `BranchData`'s pivot cells of the recursed child atlas (`rec (split c).red`
justified by `redM_chainRel`), each chart's `MonoData` getting the codim-`c` axis appended
(`MonoData.appendDivisor`). -/
noncomputable def routeAtlasOf (M₀ : Fin (L + 1) → ℕ)
    (hbranch : (M : Fin (L + 1) → ℕ) → ¬ isLeafNode M → BranchData M₀ M) :
    (M : Fin (L + 1) → ℕ) → NodeChartFamily M :=
  WellFounded.fix chainRel_wf fun M rec =>
    match h : routeStepOf M₀ M (hbranch M) with
    | .leaf md => { ι := PUnit, fintype := inferInstance, nonempty := inferInstance, data := fun _ => md }
    | .branch cells cellsFin cellsNe split codim _witness =>
        letI : Fintype cells := cellsFin
        letI : Nonempty cells := cellsNe
        let child : (c : cells) → NodeChartFamily (split c).red :=
          fun c => rec (split c).red (split c).redM_chainRel
        { ι := Σ c : cells, (child c).ι
          fintype := by
            classical
            letI : ∀ c : cells, Fintype ((child c).ι) := fun c => (child c).fintype
            infer_instance
          nonempty := by
            letI : ∀ c : cells, Nonempty ((child c).ι) := fun c => (child c).nonempty
            obtain ⟨c⟩ := cellsNe
            obtain ⟨i⟩ := (child c).nonempty
            exact ⟨⟨c, i⟩⟩
          data := fun x => ((child x.1).data x.2).appendDivisor (codim x.1) }

/-! ## Non-vacuity anchor — `routeStepOf` reproduces the worked `(2,2,2)` branch

The fidelity check that the scaffold's leaf-first dispatch + `BranchData` assembly generalizes the
hand-built `(2,2,2)` template (`Case222RouteStep.case222_routeStep_branch`) exactly. `(2,2,2)` is NOT a
leaf (`not_isLeafNode_M222`), so `routeStepOf` takes the branch arm; fed the `(2,2,2)` `BranchData` (`Bool`
cells, the uniform `schurState M222` split, codims `4`/`3`, the `decide`-checked root-anchored witnesses),
it returns the committed worked-template branch term. Confirms the scaffold is non-vacuous and matches the
anchor. -/

/-- The `(2,2,2)` `BranchData`: `Bool` pivot cells, the uniform `schurState M222` split, codims `4`/`3`,
and the `decide`-checked root-anchored witnesses (`RouteMBranch.witness222`). The honest finite-instance
producer — the witnesses are `decide`-supplied by the caller, not manufactured here. -/
noncomputable def branchData222 : BranchData M222route M222route where
  cells := Bool
  cellsFin := inferInstance
  cellsNe := ⟨true⟩
  split := fun _ => schurState M222route M222_hlo
  codim := fun b => if b then 4 else 3
  witness := witness222

/-- **`routeStepOf` reproduces `case222_routeStep_branch`** through the scaffold's branch arm. At the
non-leaf node `(2,2,2)`, `routeStepOf` fed `branchData222` returns the hand-built worked-template branch
term. The non-vacuity / fidelity check that the scaffold generalizes the `(2,2,2)` anchor exactly. -/
theorem routeStepOf_M222 :
    routeStepOf M222route M222route (fun _ => branchData222) = case222_routeStep_branch := by
  rw [routeStepOf_branch _ not_isLeafNode_M222]
  rfl

end DLNFibre.DLN.RLCT
