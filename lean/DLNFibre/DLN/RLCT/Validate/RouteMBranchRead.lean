import DLNFibre.DLN.RLCT.Validate.RouteMRecursion
import DLNFibre.DLN.RLCT.Validate.RouteMValue
import DLNFibre.DLN.RLCT.Validate.RouteMLeaf

/-!
# `RouteMBranchRead` — the #99 co-build seam contract (fm3 #99-lead)

The general `routeStep` body (#99) is built as a co-build across two worktrees: rs-grind owns the
**non-leaf rank-pattern READ** (the BODY — which cells, which per-cell admissible-`Mval` codims, the
per-cell `PivotWitness M₀`), fm3 owns the **recursion assembly + value-fold** (the CONSUMER — recursing via
`chainRel`, folding `⨅ over routeMIota → ½·minAdm` via the banked `routeM_value_eq`).

This file is the **LOCKED SIGNATURE** both sides build against BEFORE parallel-filling — the seam-drift
mitigation that has worked all expedition (the `ChainDimSplit` / `IsSchurStraightenSqueeze` / `RouteMAtlas`
interfaces). It pins (i) the producer's emission shape as a structure `RouteMBranchRead`, and (ii) the
achiever-witness realizability as a NAMED OBLIGATION stated EXACTLY as `#121-(ii)`'s conclusion (NOT a weaker
`∃ i₀`), so the discharge plugs in re-derivation-free when the tie-formaliser lands.

No proof content here — only the frozen contract (a structure + `example`-blocks pinning the types).
-/

open DLNFibre.DLN.RLCT
open scoped BigOperators ENNReal

namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-- **The non-leaf branch READ contract (the #99 seam).** For a non-leaf node `M` (root `M₀`), rs-grind's
read produces exactly the data of a `RouteStep.branch`: a finite nonempty `cells`, a per-cell width-split
`split` (each a `ChainDimSplit M`, so `redM_chainRel` lets the recursion descend), the per-cell pivot
`codim`, and the **root-anchored** `PivotWitness M₀` certifying `codim c = (Mval M₀ T).toNat` for an
admissible `T ∈ Adm M₀`. fm3's assembly consumes a `RouteMBranchRead` and emits the `RouteStep.branch`
term; rs-grind's read produces the `RouteMBranchRead`. The fields ARE `RouteStep.branch`'s fields — frozen. -/
structure RouteMBranchRead (M₀ M : Fin (L + 1) → ℕ) where
  cells : Type
  cellsFin : Fintype cells
  cellsNe : Nonempty cells
  split : cells → ChainDimSplit M
  codim : cells → ℕ
  witness : (c : cells) → PivotWitness M₀ (codim c)

/-- The READ assembles into a `RouteStep.branch` term — the assembly's one-liner (fm3 consumer side). The
LOCKED bridge: a `RouteMBranchRead` IS a `RouteStep.branch`, field-for-field. -/
def RouteMBranchRead.toRouteStep {M₀ M : Fin (L + 1) → ℕ} (r : RouteMBranchRead M₀ M) :
    RouteStep M₀ M :=
  .branch r.cells r.cellsFin r.cellsNe r.split r.codim r.witness

/-! ## `example`-blocks pinning the seam types (durable contracts; both sides build against these)

These are not used downstream — they are the frozen signature both worktrees compile against. If either
side's emission/consumption drifts from these types, its build breaks here first (the seam-drift catch). -/

/-- PRODUCER contract (rs-grind): the non-leaf read has the shape `(M₀ M : _) → ¬ isLeafNode M →
RouteMBranchRead M₀ M`. (The `¬ isLeafNode M` is the dispatch precondition; `schurState_hlo_of_not_isLeafNode`
supplies the `schurState` `hlo` for the splits.) -/
example : Prop :=
  ∀ (M₀ M : Fin (L + 1) → ℕ), ¬ isLeafNode M → RouteMBranchRead M₀ M → True

/-- CONSUMER contract (fm3): the assembly folds `⨅ over routeMIota M → ½·minAdm` via the banked
`routeM_value_eq`, whose hypotheses (`hdata` the `appendDivisor` accumulation, `hwit` per-leaf
`PivotWitness M`, `i₀`/`hbind₀` the achiever leaf) the read + recursion supply. Pinned: the value-fold's
exact signature is `routeM_value_eq`. -/
example (M : Fin (L + 1) → ℕ) (codimsOf : routeMIota M → List ℕ)
    (hdata : ∀ i, (routeAtlas M M).data i = MonoData.foldDivisors (codimsOf i))
    (hm₀ : 1 ≤ ((Adm M).inf' (Adm_nonempty M) (Mval M)).toNat)
    (hwit : ∀ i, ∀ c ∈ codimsOf i, PivotWitness M c)
    (i₀ : routeMIota M) (hbind₀ : ((Adm M).inf' (Adm_nonempty M) (Mval M)).toNat ∈ codimsOf i₀) :
    (⨅ i : routeMIota M, monomialThreshold (routeD M i) (routeK M i) (routeH M i))
      = ((((Adm M).inf' (Adm_nonempty M) (Mval M)).toNat : ℝ≥0∞)) / 2 :=
  routeM_value_eq M codimsOf hdata hm₀ hwit i₀ hbind₀

/-! ## The achiever-witness NAMED HYP = EXACTLY `#121-(ii)`'s conclusion (controller directive b, 2026-06-23)

The general branch's achiever-leaf-existence (that `hbind₀`'s achiever leaf `i₀` is GENUINELY reached, not
vacuously satisfiable) is the ONE named gap, and it must be stated as EXACTLY `#121-(ii)`'s conclusion — the
GENUINE realizability equality — NOT a weaker `∃ i₀, minAdm ∈ codimsOf i₀` (which could hold without the
cascade realizing the achiever's orbit stratum). `#121-(ii)` (pp-rstar's statement, on the `#121` branch;
plugged in at the `#28` merge) is:

    rankFn_cascadeTuple_eq_achieverRankPattern :
      (hT : T ∈ Adm M) → rankFn M (cascadeTuple M T) = achieverRankPattern M T

where `achieverRankPattern M T` is the INDEPENDENT (Adm-side, NOT cascade) target — the column-constant
completion `(i<j ↦ T_{j-1}; i=j ↦ M_i; else 0)` — and the equality establishes
**`achieverRankPattern` = the achiever's ORBIT-stratum pattern** via the `Q3` monotonicity collapse
(`admPred ⟹ ρ` weakly-decreasing `⟹` window-min over `(i,j]` = the right endpoint `ρ_j`), i.e. the
**column-constant-completion = orbit-stratum** content (fm3 `#121-(i)` review caveat b). The gate the
`#121-(ii)` tie-formaliser is held to (fm3): (a) the equality is to the INDEPENDENT `achieverRankPattern`
(not a `⟨_, rfl⟩` membership), (b) `achieverRankPattern = orbit-stratum` is PROVEN via `Q3` (not assumed),
(c) it holds on the property-breaker `M` (`L ≥ 3`, interior nonzero `T (j-1) > 0`, a strict drop before the
final zero, an increasing-width step) — not only the trivial-`T*=(1,0)` anchors.

NOT STATED as a typed parameter HERE (it references `achieverRankPattern`, the `#121`-branch decl, absent on
`fm3/routem`). The CONSUMER (fm3's general-branch assembly) takes it as a hypothesis named to this
conclusion; the discharge plugs in re-derivation-free when `#121` merges. Pinned here so rs-grind's read +
fm3's assembly + the `#121-(ii)` discharge all reference the SAME object — no weaker placeholder. -/

end DLNFibre.DLN.RLCT
