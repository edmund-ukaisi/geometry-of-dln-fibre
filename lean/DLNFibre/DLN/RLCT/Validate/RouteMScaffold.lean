import DLNFibre.DLN.RLCT.Validate.RouteMRecursion
import DLNFibre.DLN.RLCT.Validate.RouteMBranch
import DLNFibre.DLN.RLCT.Validate.RouteMBranchRead

/-!
# `DLNFibre.DLN.RLCT.Validate.RouteMScaffold` — the #121-independent general-`routeStep` scaffold (fm3 #99)

The co-build scaffold for the general `routeStep` body (#99), built so the realizability obligation that
gates the branch arm is a **named hypothesis** rather than a `sorry`. The dispatch logic, the recursion
carrier, the value fold — everything that does NOT depend on #121 (the achiever-witness realizability tie) —
is unconditional here; the one thing #121-(ii) fills is packaged as the `RouteMBranchRead`-producer input.

## What is #121-independent (built here, no `sorry`)
- **`RouteMBranchRead M₀ M`** — the branch arm's payload as DATA: a finite nonempty `cells` of pivot choices, a
  per-cell `split : cells → ChainDimSplit M` (the C1/C5 reduced-width descent), a per-cell `codim`, and the
  per-cell ROOT-anchored `PivotWitness M₀ (codim c)`. This is exactly the tuple `RouteStep.branch` consumes;
  packaging it as a structure names the boundary where #121 lives (the `witness` field — the achiever-witness
  realizability that the chart path reaches the stratum).
- **`routeStepOf`** — leaf-first dispatch consuming a `RouteMBranchRead`-producer: `if isLeafNode M` then the ⊤
  non-binding terminal `leaf (leafMonoData 0)`, else `branch` from the supplied `RouteMBranchRead`. No `sorry`,
  fully general `L`. The ONLY input is the `RouteMBranchRead` hypothesis.
- **`routeAtlasOf`** — the chart-family recursion over `routeStepOf` (mirror of `routeAtlas`, but the
  branch payload comes from a `RouteMBranchRead` family rather than the unconditional `routeStep`). Termination is
  `chainRel` (`ΣM`-drop) via `ChainDimSplit.redM_chainRel`, exactly as `routeAtlas`.

## The #121 boundary (NOT built here — the named hypothesis)
`routeStepOf` takes `hbranch : ¬ isLeafNode M → RouteMBranchRead M₀ M`. Producing a `RouteMBranchRead M₀ M` for an
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

/-! The branch arm's payload is `RouteMBranchRead M₀ M` (fm3's locked #125 seam, `RouteMBranchRead.lean`):
`cells [Fintype, Nonempty]`, `split : cells → ChainDimSplit M`, `codim : cells → ℕ`, `witness : (c) →
PivotWitness M₀ (codim c)` — exactly the `RouteStep.branch` tuple. (This scaffold originally carried a
field-identical `BranchData`; DEDUPED onto the canonical `RouteMBranchRead` at #28/#141 — the converged
single seam.) `RouteMBranchRead.toRouteStep` is the branch-term assembler. The `witness` field is the #121
boundary (the achiever-witness realizability tie #121-(ii), now PROVEN — `CascadeAchiever`); everything else
is the combinatorial cell/codim read. -/

/-- **The general `routeStep` body, with realizability as a NAMED hypothesis** (#99 co-build scaffold).
The leaf-first dispatch: `if isLeafNode M` then the ⊤ non-binding terminal (`leaf (leafMonoData 0)` — its
node-RLCT is the descent's concern, NOT this value-fold datum), else the `branch` assembled from the
supplied `RouteMBranchRead M₀ M`. No `sorry`, fully general `L`. The ONLY input is `hbranch` (the
`RouteMBranchRead`-producer at a non-leaf node) — the #121-(ii) realizability tie + the combinatorial cell/codim
read. This replaces the named `sorry` in `RouteMRecursion.routeStep` with a named hypothesis. -/
noncomputable def routeStepOf (M₀ M : Fin (L + 1) → ℕ)
    (hbranch : ¬ isLeafNode M → RouteMBranchRead M₀ M) : RouteStep M₀ M :=
  if hleaf : isLeafNode M then
    .leaf (leafMonoData 0)
  else
    (hbranch hleaf).toRouteStep

/-- The leaf arm of `routeStepOf`: at a leaf node it is the ⊤ non-binding terminal, independent of the
`RouteMBranchRead`-producer. -/
theorem routeStepOf_leaf {M₀ M : Fin (L + 1) → ℕ}
    (hbranch : ¬ isLeafNode M → RouteMBranchRead M₀ M) (hleaf : isLeafNode M) :
    routeStepOf M₀ M hbranch = .leaf (leafMonoData 0) := by
  unfold routeStepOf; rw [dif_pos hleaf]

/-- The branch arm of `routeStepOf`: at a non-leaf node it is the `RouteMBranchRead`'s assembled branch
term. -/
theorem routeStepOf_branch {M₀ M : Fin (L + 1) → ℕ}
    (hbranch : ¬ isLeafNode M → RouteMBranchRead M₀ M) (hleaf : ¬ isLeafNode M) :
    routeStepOf M₀ M hbranch = (hbranch hleaf).toRouteStep := by
  unfold routeStepOf; rw [dif_neg hleaf]

/-! ## The chart-family recursion over `routeStepOf`

`routeAtlasOf` mirrors `RouteMRecursion.routeAtlas` but the branch payload at each non-leaf node comes
from a `RouteMBranchRead` family (the #121-independent recursion: given the per-node `RouteMBranchRead`-producer, the
well-founded `chainRel` recursion builds the `NodeChartFamily`). The recursive call on `(split c).red` is
justified by `ChainDimSplit.redM_chainRel` exactly as in `routeAtlas`; the root `M₀` is UNCHANGED on
descent (the witnesses stay root-anchored). -/

/-- **The Route-M chart-family recursion over `routeStepOf`** (the #121-independent recursion). With the
root ambient `M₀` FIXED and a per-node `RouteMBranchRead`-producer `hbranch`, well-founded recursion on
`chainRel` (`ΣM`-drop) builds the `NodeChartFamily`: a leaf node ↦ a single chart with `leafMonoData 0`; a
branch node ↦ the `Σ` over the `RouteMBranchRead`'s pivot cells of the recursed child atlas (`rec (split c).red`
justified by `redM_chainRel`), each chart's `MonoData` getting the codim-`c` axis appended
(`MonoData.appendDivisor`). -/
noncomputable def routeAtlasOf (M₀ : Fin (L + 1) → ℕ)
    (hbranch : (M : Fin (L + 1) → ℕ) → ¬ isLeafNode M → RouteMBranchRead M₀ M) :
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

The fidelity check that the scaffold's leaf-first dispatch + `RouteMBranchRead` assembly generalizes the
hand-built `(2,2,2)` template (`Case222RouteStep.case222_routeStep_branch`) exactly. `(2,2,2)` is NOT a
leaf (`not_isLeafNode_M222`), so `routeStepOf` takes the branch arm; fed the `(2,2,2)` `RouteMBranchRead` (`Bool`
cells, the uniform `schurState M222` split, codims `4`/`3`, the `decide`-checked root-anchored witnesses),
it returns the committed worked-template branch term. Confirms the scaffold is non-vacuous and matches the
anchor. -/

/-- The `(2,2,2)` `RouteMBranchRead`: `Bool` pivot cells, the uniform `schurState M222` split, codims `4`/`3`,
and the `decide`-checked root-anchored witnesses (`RouteMBranch.witness222`). The honest finite-instance
producer — the witnesses are `decide`-supplied by the caller, not manufactured here. -/
noncomputable def branchData222 : RouteMBranchRead M222route M222route where
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

/-! ## The achiever-witness extractor — the binding cell's `PivotWitness` (decision-independent primitive)

The `minAdm`-achiever yields a root-anchored `PivotWitness M (minAdm M)`: the admissible exponent `T*`
minimising `Mval` over `Adm M` (`Finset.exists_mem_eq_inf'`) certifies the binding codim `minAdm`. This is
the witness EVERY non-leaf read needs for its binding cell (the leaf that achieves `½·minAdm` in the value
fold), whatever the cell decomposition — a single achiever cell (the value-correct waypoint) or the binding
cell of the genuine multi-cell cover. It is NOT a cell decomposition itself; it is the per-cell witness
primitive the decomposition consumes. Non-vacuous: `T*` is exhibited via `exists_mem_eq_inf'`. -/

/-- **The `minAdm`-achiever's root-anchored `PivotWitness`.** The admissible `T*` minimising `Mval` over
`Adm M` certifies the binding codim `minAdm M = ((Adm M).inf' Mval).toNat`: `T* ∈ Adm M` (`hAdm`) and
`minAdm = (Mval M T*).toNat` (`hCodim`, since `Mval M T* = inf'` and `.toNat` is a function). The binding
cell's witness, decomposition-agnostic. -/
noncomputable def achieverPivotWitness (M : Fin (L + 1) → ℕ) :
    PivotWitness M (((Adm M).inf' (Adm_nonempty M) (Mval M)).toNat) :=
  let h := Finset.exists_mem_eq_inf' (Adm_nonempty M) (Mval M)
  { T := h.choose
    hAdm := h.choose_spec.1
    hCodim := congrArg Int.toNat h.choose_spec.2 }

/-! ## The read body, Shape C — the binding cell split off as green data + the complement as the named gap

The general non-leaf read (#99) produces a `RouteMBranchRead M₀ M` from two pieces (decorrelated-Codex Shape C,
`fm3-coord-bridge/codex/readbody-skeleton-answer.md`): a **binding cell** carrying the achiever's
root-anchored `PivotWitness M₀ (minAdm M₀)` (GREEN — the value fold's `C=∃` leaf is constructed, not
gapped) + a **complement cover** of the remaining pivot cells (the named gap, the genuine rank-pattern
read). The producer `branchDataOfReadParts` assembles them via `PUnit ⊕ cells` so the binding cell is
ALWAYS present (the non-vacuity guard: the achiever leaf cannot be dropped). The per-cell analytic descent
(`IsSchurStraightenSqueeze`/`hnode`) is carried SEPARATELY at the cover-lintegral level (#104, crux2's
`redCore_eq`) — NOT a field here, per the §4 feasibility cert §3 ("`redCore_eq` carries the analytic
descent separately"); the read is the COMBINATORIAL cell/codim/witness emission, the geometric fidelity is
fm3's R1-result. -/

/-- **The binding cell** (root `M₀`, current `M`): the achiever's root-anchored data. Carries a
`ChainDimSplit M` (the `T*`-profile split — the achiever's rank-drop, NOT the front-collapsing uniform
`schurState`, §4 cert §4), the binding `codim`, the root-anchored `PivotWitness M₀ codim`, and the binding
proof `codim = minAdm M₀`. The `C=∃` leaf the value fold lands on. -/
structure R1BindingCell (M₀ M : Fin (L + 1) → ℕ) where
  split : ChainDimSplit M
  codim : ℕ
  witness : PivotWitness M₀ codim
  hbind : codim = ((Adm M₀).inf' (Adm_nonempty M₀) (Mval M₀)).toNat

/-- **The complement cover** (the named gap): the remaining pivot cells of the general rank-pattern read.
A finite (possibly EMPTY) family with per-cell `split`/`codim`/per-cell root-anchored `PivotWitness M₀`.
This is the combinatorial cell decomposition the #99 grind produces for arbitrary non-leaf `M`. Empty
`cells` is allowed (NO `Nonempty` field — the binding cell alone, via `branchDataOfReadParts`'s `Sum.inl`,
is already a valid degenerate-but-value-correct cover); the genuine cover has the non-binding pivot cells
here. (The producer's `Nonempty` comes from the binding `Sum.inl`, never from `d`, so the field would be a
spurious obligation on the #99 grind — reviewer catch, dropped.) -/
structure R1ComplementData (M₀ M : Fin (L + 1) → ℕ) where
  cells : Type
  cellsFin : Fintype cells
  split : cells → ChainDimSplit M
  codim : cells → ℕ
  witness : (c : cells) → PivotWitness M₀ (codim c)

/-- **The read body producer** (GREEN): assemble `RouteMBranchRead M₀ M` from a binding cell + a complement
cover. The cell type is `PUnit ⊕ d.cells` — the binding cell (`Sum.inl`) is ALWAYS present (the non-vacuity
guard), the complement cells (`Sum.inr`) are the named-gap cover. `split`/`codim`/`witness` are the
`Sum.elim` of the two sources. The single named gap is producing the `R1ComplementData` (and the binding
cell's `T*`-profile split); the binding `witness` is GREEN (`achieverPivotWitness M₀`, see
`r1BindingCellRoot`). -/
def branchDataOfReadParts {M₀ M : Fin (L + 1) → ℕ}
    (b : R1BindingCell M₀ M) (d : R1ComplementData M₀ M) : RouteMBranchRead M₀ M where
  cells := PUnit ⊕ d.cells
  cellsFin := by letI := d.cellsFin; infer_instance
  cellsNe := ⟨Sum.inl PUnit.unit⟩
  split := Sum.elim (fun _ => b.split) d.split
  codim := Sum.elim (fun _ => b.codim) d.codim
  witness := fun c => match c with
    | Sum.inl _ => b.witness
    | Sum.inr c' => d.witness c'

/-- **The binding cell at the ROOT** (`M = M₀`): GREEN, non-vacuous. The achiever's root-anchored
`PivotWitness M₀ (minAdm M₀)` is `achieverPivotWitness M₀` (the `inf'`-achiever `T*`); the binding proof is
`rfl`. The `split` field is supplied (the `T*`-profile `ChainDimSplit M₀` — the achiever's rank-drop split,
the one piece of the binding cell still gated on the §4 chart, here taken as input). Witnesses that the
binding cell's combinatorial data is constructible: the achiever leaf exists and binds at `minAdm`. -/
noncomputable def r1BindingCellRoot (M₀ : Fin (L + 1) → ℕ) (split : ChainDimSplit M₀) :
    R1BindingCell M₀ M₀ where
  split := split
  codim := ((Adm M₀).inf' (Adm_nonempty M₀) (Mval M₀)).toNat
  witness := achieverPivotWitness M₀
  hbind := rfl

/-- **Non-vacuity guard**: the assembled `RouteMBranchRead` always has the binding cell — its `cells` is
inhabited by `Sum.inl PUnit.unit`, and the binding cell's `codim` is `b.codim` (`= minAdm M₀` for a
`r1BindingCellRoot`). So the read is NOT the empty/degenerate cover — the `C=∃` achiever leaf is present by
construction. -/
theorem branchDataOfReadParts_binding_present {M₀ M : Fin (L + 1) → ℕ}
    (b : R1BindingCell M₀ M) (d : R1ComplementData M₀ M) :
    (branchDataOfReadParts b d).codim (Sum.inl PUnit.unit) = b.codim := rfl

/-! ## Why there is NO concrete achiever-only producer here (controller ruling 2026-06-23)

A single-`PUnit`-cell read (binding achiever cell + empty complement) type-checks and is "value-correct"
(the `⨅` lands on `½·minAdm`), but it is NOT a valid #99 read and is deliberately NOT built: it is
**degenerate-as-cover** (it asserts ONE cell where the genuine resolution is multi-cell) AND
**redundant-as-value** (the achiever-binds-at-`minAdm` fact is ALREADY `routeM_value_eq`'s `i₀`/`hbind₀`
input — a single-cell read adds nothing the value fold did not already have). It is the trap-(iii)
smuggle in value-correct disguise. The genuine read (the multi-cell rank-pattern decomposition) is gated
on the general-M `hnode` producer (G-a, #135 — pp-rstar #133: absent + formaliser-weeks); it is built
there, NOT stubbed here. The Shape-C skeleton above (`R1BindingCell`/`R1ComplementData`/
`branchDataOfReadParts`/`r1BindingCellRoot`) is the honest INTERFACE the genuine read populates. -/

end DLNFibre.DLN.RLCT
