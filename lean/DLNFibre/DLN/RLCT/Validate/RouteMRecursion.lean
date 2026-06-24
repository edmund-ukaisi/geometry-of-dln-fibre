import DLNFibre.DLN.RLCT.Validate.GeneralR1Recursion
import DLNFibre.DLN.RLCT.Validate.RouteMState
import DLNFibre.DLN.RLCT.Validate.RouteMLeaf
import DLNFibre.DLN.RLCT.Validate.SchurState
import Mathlib.Data.Fintype.Sigma

/-!
# `DLNFibre.DLN.RLCT.Validate.RouteMRecursion` — the Route-M recursion REBASED onto `ChainDimSplit`

The recursion DRIVER for the general-M resolution, rebased onto crux2's banked `ChainDimSplit`
(controller seam decision g156: crux2 = the per-step additive straighten/descent over `ChainDimSplit`;
fm3 = the blow-up cover / `⨅`-min over pivot branches, layered on top). This file replaces the parallel
`RouteState`/`routeMeasure`/`routeRel_wf` machinery (which duplicated `ChainDimSplit`'s state-transition —
Codex-flagged sync liability) with the `ChainDimSplit`-based termination.

## What is shared vs owned (the seam, g155–g157)
- **crux2 owns** `ChainDimSplit` (the one-step width split `drop + red = M`, `L` fixed, `ΣM`-decreasing),
  its transport lemmas (`rlctAtOn_reduced_transport`, `schur_recursion_step_sound`/`_squeeze`), and the
  per-step `hGne`. `ChainDimSplit` is only ever CONSUMED in `GeneralR1Recursion`, never constructed there.
- **fm3 owns** (here + `RouteMState`): the iterated recursion over `ChainDimSplit` (terminating on `ΣM`),
  the per-node pivot BRANCHING (the `⨅`-min over pivot cells — `ChainDimSplit` is single-path), and the
  `MonoData` accumulation (`appendDivisor`/`foldDivisors`, `RouteMState.lean`, driver-agnostic, banked).

## Termination (the only piece banked here so far)
The recursion descends `M ↦ S.red` via a `ChainDimSplit M`. Termination is the `ΣM`-drop: `hdrops`
(`0 < Σ drop`) + `hsum` (`drop + red = M`) give `Σ red < Σ M`. This is the reusable, construction-agnostic
foundation — `redM_widthSum_lt` below names it (it was inlined in crux2's `schur_straighten_of_data`).
-/

open MeasureTheory
open scoped BigOperators
namespace DLNFibre.DLN.RLCT

/-- The total width `Σ M` — the recursion's termination measure (rebased: replaces `RouteState.widthSum`,
now keyed to `ChainDimSplit`'s `ΣM`-drop rather than a parallel `RouteState`). -/
def chainWidthSum {L : ℕ} (M : Fin (L + 1) → ℕ) : ℕ := ∑ s, M s

/-- **The `ChainDimSplit` termination measure drops.** A reduction `S : ChainDimSplit M` strictly
decreases the total width: `Σ S.red < Σ M`. From `hsum` (`drop + red = M`) and `hdrops` (`0 < Σ drop`).
The well-founded measure for the iterated Route-M recursion (was inlined in `schur_straighten_of_data`;
named here as the reusable, split-construction-agnostic foundation). -/
theorem ChainDimSplit.redM_widthSum_lt {L : ℕ} {M : Fin (L + 1) → ℕ} (S : ChainDimSplit M) :
    chainWidthSum S.red < chainWidthSum M := by
  unfold chainWidthSum
  have hle : ∑ s, S.red s ≤ ∑ s, M s :=
    Finset.sum_le_sum fun s _ => by have := S.hsum s; omega
  have hne : ∑ s, S.red s ≠ ∑ s, M s := by
    intro hEq
    have hdrop0 : ∑ s, S.drop s = 0 := by
      have hadd : ∑ s, S.drop s + ∑ s, S.red s = ∑ s, M s := by
        rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun s _ => S.hsum s
      omega
    exact absurd hdrop0 (by have := S.hdrops; omega)
  omega

/-! ## The well-founded recursion carrier (rebased: replaces `RouteState`/`routeRel_wf`)

The iterated Route-M recursion descends over the width vector `M : Fin (L+1) → ℕ` (`L` fixed — the
`ChainDimSplit` reduction is width-only), terminating on `chainWidthSum`. `chainRel` is the strict
`ΣM`-decrease; `chainRel_wf` (its well-foundedness) is the carrier for the `WellFounded.fix` that builds
the chart family — the split-construction-agnostic recursion skeleton. Any `ChainDimSplit M`-driven step
descends along `chainRel` by `redM_widthSum_lt`, so the recursion is well-founded whoever constructs the
per-node split. -/

/-- The recursion's well-founded relation on width vectors (fixed `L`): strict `ΣM`-decrease. -/
def chainRel {L : ℕ} (N M : Fin (L + 1) → ℕ) : Prop := chainWidthSum N < chainWidthSum M

/-- `chainRel` is well-founded (pullback of `<` on `ℕ` along `chainWidthSum`). The carrier for the
iterated Route-M `WellFounded.fix`, replacing the parallel `routeRel_wf`. -/
theorem chainRel_wf {L : ℕ} : WellFounded (@chainRel L) :=
  InvImage.wf chainWidthSum wellFounded_lt

/-- A `ChainDimSplit M` descends along `chainRel` (its reduced widths are `chainRel`-below `M`). The
bridge from crux2's one-step split to the recursion's descent proof — the `WellFounded.fix` recursive
call on `S.red` is justified by this, independent of how `S` is constructed. -/
theorem ChainDimSplit.redM_chainRel {L : ℕ} {M : Fin (L + 1) → ℕ} (S : ChainDimSplit M) :
    chainRel S.red M :=
  S.redM_widthSum_lt

/-! ## The per-cell reduced-chain transport (the LIGHT det-1 reindex — crux2 #73, the recursion-closing link)

The per-cell transport field on a `branch` cell (g178, the light interface — NOT the heavy
`IsSchurStraightenSqueeze`, which is L2's deepest-gauge node). After the cell's blow-up presents the node
core as `G²` (my G2 `node_loss_pivot_factor`, threaded at the cover-fact), `ReducedTransport` bundles
crux2's banked `rlctAtOn_reduced_transport` datum (det-1 measure-preserving reindex) closing the descent:
`rlctAtOn (G²) 0 = rlctAtOn (dlnLoss S.red 0) 0` at the child's deepest point. `Y` is the post-blow-up
reduced ambient (a field — the blow-up reindexes coords, so `Y ≠ Params S.red` literally; `redEmbed` is the
reindex). `redZero` is pinned to `0 : Params S.red` (the child's deepest point — `hzero : redEmbed 0 = 0`),
so the descent composes with the recursion on `S.red`. Data-carrying (`Type`, so the dispatcher constructs
it from the chart). -/
structure ReducedTransport {L : ℕ} {M : Fin (L + 1) → ℕ} (S : ChainDimSplit M)
    (Y : Type) [MeasureSpace Y] [TopologicalSpace Y] [Zero Y] where
  /-- The cell's post-blow-up core root `G` (`G² =` the reduced loss). -/
  G : Y → ℝ
  /-- The det-1 measure-preserving reindex to the reduced chain `Params S.red`. -/
  redEmbed : Y ≃ₜ Params S.red
  /-- The reindex is measure-preserving (det 1). -/
  hmp : MeasurePreserving redEmbed volume volume
  /-- The reindex is a measurable embedding. -/
  hemb : MeasurableEmbedding redEmbed
  /-- The reindex sends the cell's deepest point to the child's deepest point `fun _ => 0 : Params S.red`
  (`Params` has no canonical `Zero`; the reduced deepest point is the layerwise-zero tuple). -/
  hzero : redEmbed 0 = (fun _ => 0 : Params S.red)
  /-- `G² =` the reduced-chain loss on the embedded coords (so the recursion descends on `S.red`). -/
  hredCore : ∀ y, G y ^ 2 = dlnLoss S.red 0 (redEmbed y)

/-- **The reduced-chain transport closes the descent.** From a `ReducedTransport S Y`, the cell's
post-blow-up core RLCT equals the child's reduced-chain RLCT at its deepest point `fun _ => 0`:
`rlctAtOn (G²) 0 = rlctAtOn (dlnLoss S.red 0) (fun _ => 0)`. Consumes crux2's banked
`rlctAtOn_reduced_transport` (det-1 MP); the bundled datum + the anchored `hzero` give the
recursion-closing form (the child's deepest point = the layerwise-zero tuple). -/
theorem ReducedTransport.descent {L : ℕ} {M : Fin (L + 1) → ℕ} {S : ChainDimSplit M}
    {Y : Type} [MeasureSpace Y] [TopologicalSpace Y] [Zero Y] (rt : ReducedTransport S Y) :
    rlctAtOn (fun y => rt.G y ^ 2) (0 : Y)
      = rlctAtOn (dlnLoss S.red 0) (fun _ => 0 : Params S.red) :=
  rlctAtOn_reduced_transport S rt.G rt.redEmbed rt.hmp rt.hemb _ rt.hzero rt.hredCore

/-! ## The chart family + the per-node dispatcher (the producer's job — crux2 #66: fm3 constructs)

`NodeChartFamily M` is the output the bridge consumes: the index set `ι` (Fintype, as a field) + the
per-leaf monomial datum `(d, k, h)` (an `i ↦ MonoData`). The recursion builds it over `chainRel_wf`.

The per-node `RouteStep` is the DISPATCHER's output (crux2 #66: fm3 owns construction; `ChainDimSplit`
stays the minimal width-only carrier; the pivot-cell coord-center lives in the paired
`IsSchurStraightenSqueeze` datum, not here). At a node it is EITHER:
- a `leaf` (terminal — `L = 1` / the bottomed-out chain): one chart, `MonoData` the accumulated path; OR
- a `branch`: a `Finset` of pivot choices, each a `ChainDimSplit M` whose `red` is `chainRel`-below `M`
  (`redM_chainRel`), recursed; the per-cell `(d,k,h)` accumulates via `MonoData.appendDivisor` (the
  codim-`card` pivot axis). `ι` is the `Σ` over pivot cells of the recursed children's `ι` (the BRANCHING
  = the `⨅`-min over paths). -/

/-- **The Route-M chart family at a node**: the index set `ι` (Fintype + Nonempty, as fields) + the
per-leaf `(d,k,h)` datum. The output the cover/value bridge consumes. `Nonempty ι` is carried as a field
(the chart family always has ≥1 leaf) — `routeM_rlctAtOn_eq_iInf` needs `[Nonempty ι]` for the achiever-side
`iInf_le` (crux2's bridge-wiring catch). -/
structure NodeChartFamily {L : ℕ} (_M : Fin (L + 1) → ℕ) where
  ι : Type
  fintype : Fintype ι
  nonempty : Nonempty ι
  data : ι → MonoData

/-- A per-node dispatch result, **root-anchored to `M₀`** (the original ambient) while the node's split
lives over the current `M`. Either a terminal leaf (its `MonoData`) or a finite branching into pivot
cells. Each branch cell carries a `ChainDimSplit M` (so its `red = schurState M` descends —
`redM_chainRel`), the `codim` of its pivot stratum (the `appendDivisor` weight, the geometric **cardinality**
read directly off the blow-up center), and the **root-anchored `PivotWitness M₀`** certifying
`codim = (Mval M₀ T).toNat` for an admissible `T ∈ Adm M₀` (pp2 g207/g214 — anchoring at `M₀` not the
reduced chain, since `minAdm(schurState M) < minAdm(M₀)` would otherwise undershoot; the geometric codim is
reindex-invariant, so it equals `Mval M₀ T` at every depth). The per-cell TRANSPORT (descent-soundness) is
crux2's `IsSchurStraightenSqueeze.redCore_eq` (`G² = dlnLoss S.red 0 ∘ redEmbed`, gated on `S.red =
schurState M`), threaded at the cover-fact lintegral level — NOT a field here. The dispatcher (pp2 g183/g194
recipe) produces this; STUBBED to pin the shape. -/
inductive RouteStep {L : ℕ} (M₀ M : Fin (L + 1) → ℕ) : Type 1
  | leaf (md : MonoData)
  | branch (cells : Type) (cellsFin : Fintype cells) (cellsNe : Nonempty cells)
      (split : cells → ChainDimSplit M) (codim : cells → ℕ)
      (witness : (c : cells) → PivotWitness M₀ (codim c))

/-- The dispatcher: classify a node — root `M₀`, current `M` — into a root-anchored `RouteStep M₀ M`
(leaf or branching), reading the rank pattern.

**OPEN — a single, precisely-fenced obligation (NOT a vacuously-fillable stub).** Three syntactically-green
bodies are all *wrong*: (i) `leaf` everywhere makes the atlas trivial (`leafMonoData` has threshold `⊤ ≠
½·minAdm` in non-degenerate cases — `RouteMState.leafMonoData_threshold`); (ii) a `branch` with `codim =
card pivotCoords` hits the `(4,3,2)` trap (`card ≠ Mval` there — pp2 cert §7); (iii) — the SUBTLE one (Codex
g208, decorrelated) — a `branch` with `Unit` cells, `split := schurState M`, and `codim := minAdm` (or `T :=
0`/the `inf'`-minimiser, whose `PivotWitness.hAdm`/`hCodim` DO discharge via `zero_mem_Adm` + concrete
`Mval`) type-checks and forces the abstract fold value, but **smuggles** the missing realizability theorem
into the dispatcher: `PivotWitness M₀ c` proves only `T ∈ Adm M₀ ∧ c = Mval M₀ T`, NOT that the rank stratum
is *reached by this chart path* (that "reached" proof is `IsResolutionAtlas.stratum_surjective`, which
`resolution_value_of_atlas` consumes in the achiever `≤` leg — the dispatcher cannot manufacture it). All
three are **worse than this `sorry`**, so it is left named. The certified body needs three Core-level pieces
NOT yet in the library (pp2 g183 dispatcher cert §2/§4 + Codex g206/g208, decorrelated):
1. **a `residualCore` / rank-defect classifier** over `M` deciding `leaf` (`IsUnit residualCore`, cert §1.1 —
   NOT "no C1 applies") vs `branch` (the rank-pattern read);
2. **the realizability witness** for each branch cell: `codim = (Mval M₀ T).toNat` for an admissible
   `T ∈ Adm M₀` that is GENUINELY reached by a legal chart path. Cert §4: "only the minimiser need be
   reached, but THAT COVERAGE IS A THEOREM" — it rides `Core.OrbitKostant`/`baseChange_normalForm`
   realizability, not a freebie. This is what builds `witness : PivotWitness M₀ (codim c)` honestly;
3. **the general lintegral recursion descent** tying the per-cell pullback residual to `dlnLoss (split c).red
   0` (`split.red = schurState M`, in the cover lintegral via crux2's `redCore_eq`).

The branch SPLIT is already constructible (`schurState M` @442a2e0, given the per-node `hMid`); the carrier,
termination, and value-fold are banked.

**STRUCTURE FILLED (fm3 #103, controller ruling 2026-06-23): leaf-first dispatch, realizability in the
COVER.** The dispatch is now leaf-first: `if minAdm M = 0` (the geometric leaf, `isLeafNode`, =
`∃ s, M_s = 0`, `RouteMClassify.isLeafNode_iff_width_zero`) `then .leaf (leafMonoData 0)` — the ⊤
non-binding terminal (its node-RLCT `⊤`/`#70` is the DESCENT's concern, NOT the value-fold datum;
decl-forced + decorrelated-Codex-confirmed, fm3 g236/ee81ce8); `else` the `branch`. The leaf arm + dispatch
are CONCRETE; the **single remaining gap** (fm3-authorized named `sorry`, NOT faked) is the GENERAL branch
cell-construction — emitting, for arbitrary non-leaf `M`, the genuine per-cell admissible-`Mval` codims +
the achiever `T*` (the rank-pattern read). Realizability (that the chart path reaches the stratum) is NOT
manufactured here — it lives in the `IsRouteMCover` COVER (#104, `cover_le`/`cover_ge_div` catch a
fabricated `(d,k,h)`), so the `branch`'s admissible-`PivotWitness M₀` is honest-by-construction with the
cover as the honesty-gate. The concrete anchors `(2,2,2)`/`(3,2,3)` are `Case222RouteStep`/decidable; the
general achiever-leaf-existence rides the cascade realizability (`Core.CascadeRealizable`, #116) at #104.

**BINDING-COUPLED FIDELITY (the `diag(b)` reconciliation, `verify-r1-diagb-334.md`/`-4422.md`).** The
committed per-cell `codim : ℕ` is the geometric `Mval M₀ T` (the `PivotWitness M₀` field), read from the
CLOSED Aoyagi form ROOT-anchored — it is NOT a per-row divisor multiplicity. So the obstruction the
resolution certificate identifies (a per-row-multiplicity recursion mishandles a coupled corank-≥2 residual
block, computing the WRONG core RLCT) does NOT bind this datum: the sharing identity is never re-derived
per-row; it is encoded once, globally, in `Mval`. Decidable anchors LOCK this. `(3,3,4)` is the BINDING
coupled witness — its unique minimiser is a corank-`(2,2)` partial drop, a per-row recursion gives `3`, the
true value is `4`; `Case334RouteStep.case334_routeStep_value` folds the committed datum to `4` (`= ½·8`,
reading `Mval M₀ (1,0) = 8` directly). `(4,4,2,2)` is the NON-binding contrast — its corank-2 branch carries
`Mval = 7` but the CLEAN binder `t=(4,2,0)` sets the value at `2`; `case4422_routeStep_value` folds to `2`
(the `min` correctly takes the clean binder, NOT `7/2`). The no-undershoot `codim ≥ minAdm` is automatic from
`minAdm = inf_{T∈Adm M₀} Mval M₀ T` (`PivotWitness.minAdm_le`), so even a wrong dispatcher CANNOT undershoot
the binding value — only over-emit non-binding cells (caught by the cover `≤`-leg). -/
noncomputable def routeStep {L : ℕ} (M₀ M : Fin (L + 1) → ℕ) : RouteStep M₀ M :=
  if _hleaf : isLeafNode M then
    -- LEAF (`isLeafNode M`, the degenerate boundary `∃ s, M_s = 0`, `isLeafNode_iff_width_zero`). The ⊤
    -- non-binding terminal (`leafMonoData 0`); its node-RLCT (`#70`/`nReg/2`) is the descent's concern,
    -- NOT this value-fold datum.
    .leaf (leafMonoData 0)
  else
    -- BRANCH: the general rank-pattern read. WALLED at the CARRIER level (verified 2026-06-24: three
    -- independent checks + decorrelated Codex xhigh; agent-a4fc thread report). The honest construction
    -- is FORCED to be the geometrically faithful blow-up recursion, which is LAYER-COLLAPSING — and the
    -- fixed-arity carrier cannot express it:
    --   minAdm(M₀,M₁,M₂,…) = min_{t ≤ min(M₀,M₁)} [ (M₀−t)(M₁−t) + minAdm(t, M₂, …, M_L) ]  (base a·b).
    -- Branch on the leading pivot rank-drop `t`, emit ONE divisor of codim = the block exponent
    -- `(M₀−t)(M₁−t)`, then recurse on the LAYER-COLLAPSED chain `(t,M₂,…,M_L)` on `Fin L` (one fewer
    -- layer). Why no width-only fill is honest (the trap-iii SMUGGLE, Codex-confirmed):
    --   • `PivotWitness M₀` demands per-cell `codim = (Mval M₀ T).toNat` (root-anchored admissible `T`);
    --     a node's `appendDivisor` emits ONE codim = the block term, which is `< minAdm` for `t ≥ 1`
    --     (e.g. (2,2,2), t=1: block=1 < minAdm=3). No admissible `T*` with `T*₁=t` has
    --     `Mval = (M₀−t)(M₁−t)` for `t ≥ 1` (checked 6/6 + (4,3,2)) — block exponent ≠ `Mval M₀ T*`.
    --   • `ChainDimSplit M` forces `red ≤ M` at fixed arity `L`; the genuine reduced chain `(t,M₂,…)` is
    --     on `Fin L`. Exhaustive (2,2,2): no width-only `red ≤ M` (Σ red < 6) reproduces the per-`t`
    --     reduced minAdm for all `t` (t=2 needs minAdm(red)=4, width-only tops at 2; t=0 needs −1).
    --     Paddings `(t,t,M₂,…)` undershoot (min over t of {4,2,3}=2 ≠ 3 on (2,2,2)).
    --   • `split` is geometrically load-bearing: `RouteMNodeDescent`/`RouteMO1Bridge` require
    --     `(split c).red = schurState M` (a SINGLE-width peel); a `split` independent of the witness is
    --     the smuggle (one chart claimed to span all strata, unproven).
    -- MINIMAL UNBLOCK (controller decision — re-architecture, NOT a leaf fill): replace `ChainDimSplit M`
    -- with a layer-collapsing carrier (`LayerSplit M : Σ L' < L, {red : Fin (L'+1) → ℕ // collapse}`),
    -- refactor `routeAtlas` to recurse on `(L', red)`, and generalise the descent certificate to
    -- `dlnLoss red` for the collapsed chain. Then the block recursion above encodes directly; the leaf
    -- arm + dispatch are CONCRETE and unaffected.
    sorry

/-- **The Route-M chart-family recursion (the G1 deliverable, rebased onto `ChainDimSplit`).** With the
root ambient `M₀` FIXED, well-founded recursion on `chainRel` (`ΣM`-decrease) over the current node `M`
builds the `NodeChartFamily`: a `leaf` step ↦ a single chart with its `MonoData`; a `branch` step ↦ the
`Σ` over pivot cells of the recursed child atlas (`rec (split c).red` justified by `redM_chainRel`, root
`M₀` UNCHANGED on descent), each chart's `MonoData` getting the codim-`c` pivot axis appended
(`MonoData.appendDivisor`). The root-anchored witness (`PivotWitness M₀`) rides the dispatch result for the
value fold; the atlas itself reads only `split`/`codim`/`md`. -/
noncomputable def routeAtlas (M₀ : Fin (L + 1) → ℕ) :
    (M : Fin (L + 1) → ℕ) → NodeChartFamily M :=
  WellFounded.fix chainRel_wf fun M rec =>
    match routeStep M₀ M with
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

/-- The chart-family index set `ι M` = the atlas's leaves (root = current node at the top of the
recursion). -/
def routeMIota {L : ℕ} (M : Fin (L + 1) → ℕ) : Type := (routeAtlas M M).ι

/-- `ι M` is a `Fintype` (carried as the atlas field — finite branching × `ΣM`-bounded depth). -/
noncomputable instance {L : ℕ} (M : Fin (L + 1) → ℕ) : Fintype (routeMIota M) :=
  (routeAtlas M M).fintype

/-- `ι M` is `Nonempty` (carried as the atlas field — the chart family always has ≥1 leaf). The
`[Nonempty ι]` `routeM_rlctAtOn_eq_iInf` needs for the achiever-side `iInf_le` (crux2's bridge catch). -/
instance {L : ℕ} (M : Fin (L + 1) → ℕ) : Nonempty (routeMIota M) :=
  (routeAtlas M M).nonempty

/-- Per-leaf chart dimension. -/
noncomputable def routeD {L : ℕ} (M : Fin (L + 1) → ℕ) (i : routeMIota M) : ℕ :=
  ((routeAtlas M M).data i).d
/-- Per-leaf loss-base exponents `k`. -/
noncomputable def routeK {L : ℕ} (M : Fin (L + 1) → ℕ) (i : routeMIota M) : Fin (routeD M i) → ℕ :=
  ((routeAtlas M M).data i).k
/-- Per-leaf Jacobian exponents `h`. -/
noncomputable def routeH {L : ℕ} (M : Fin (L + 1) → ℕ) (i : routeMIota M) : Fin (routeD M i) → ℕ :=
  ((routeAtlas M M).data i).h

end DLNFibre.DLN.RLCT
