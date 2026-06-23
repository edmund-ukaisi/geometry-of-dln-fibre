import DLNFibre.DLN.RLCT.Validate.RouteMRecursion
import DLNFibre.DLN.RLCT.Validate.GeneralR1Recursion

/-!
# `RouteMNodeDescent` — the #135 G-a LOCKED SEAM (fm3 #135-lead, descent side)

The general-M RLCT recursion (#135) splits G-a (the per-node hnode producer — which datum each non-leaf
node emits) and G-b (the cover lintegral CoV recursing the datum). This file is the **LOCKED producer/
consumer interface** both sides build against BEFORE parallel-filling — the seam-drift mitigation that worked
for #99/#125 (`RouteMBranchRead`). It is the DESCENT-side analog of `RouteMBranchRead` (the value-side seam).

**Naming caveat (controller #136 verdict, 2026-06-23).** `descentStep` is an RLCT identity only —
`rlctAtOn flatCore (0,0) = nReg/2 + rlctAtOn (dlnLoss S.red 0) 0`; it makes NO codim claim. When G-b's
cover assigns a per-node codim, that codim is the **RESOLUTION / combinatorial `Mval`** (the monomial
threshold the blow-up presents), NOT the geometric Ext-codim of the cascade's orbit stratum (the two
agree only on width-monotone `M`, and the cascade's column-constant `achieverRankPattern` differs at
interior cells from the `Mval=multSum` pattern `r=ρ_j+(M_i−ρ_i)` — pp-rstar #136). The binding headline
`½·minAdm` uses only the combinatorial `Mval` and is unaffected; the general-M geometric reading is a
scoped, deferred extension (width-monotone), not what this descent proves.

The per-node datum (pp-rstar #134: ONE shape covers C1 hard-pivot AND C5 partial-drop, differing only in
FIELD VALUES) bundles:
- `IsSchurStraightenSqueeze` — the squeeze giving `rlctAtOn flatCore (0,0) = nReg/2 + rlctAtOn (G²) 0`
  (`schur_straighten_squeeze_of_data`);
- `ReducedTransport S Y` — the det-1 MP reindex closing `rlctAtOn (G²) 0 = rlctAtOn (dlnLoss S.red 0) 0`
  (`ReducedTransport.descent`).
Composed: `rlctAtOn flatCore (0,0) = nReg/2 + rlctAtOn (dlnLoss S.red 0) 0` — the per-node DESCENT STEP that
G-b's cover lintegral recurses on the smaller chain `S.red` (`measure_drops`).

`Y` + its instances are STRUCTURE PARAMETERS (the `ReducedTransport`/`IsSchurStraightenSqueeze` idiom),
NOT fields — the per-node-varying `Y` is bundled by the producer's existential `RouteMNodeDescentExists`
(`∃ nReg Y _ _ _, RouteMNodeDescent …`). This sidesteps the heavy-dependent-instance-field elaboration crux2
hit with Y-as-field (controller: the Y-parameter route is the cleaner one). No proof content beyond the
bundle + the composed descent step (consuming the two banked lemmas).
-/

open DLNFibre.DLN.RLCT MeasureTheory
open scoped BigOperators ENNReal

namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-- **The per-node descent datum (the #135 G-a seam).** For a non-leaf node `M` with width-split
`S : ChainDimSplit M`, regular-block count `nReg`, and reduced-coords `Y` (a PARAMETER + the heavy
`schur_straighten_squeeze_of_data` instance bundle: `PseudoMetricSpace` / `ProperSpace` / Borel + finite-on-
compacts `volume` — the squeeze's `rlctAtOn` measure hygiene; the `MeasureSpace` / `TopologicalSpace` / `Zero`
the lighter `ReducedTransport` needs are derived from it). The datum bundles the post-blow-up core `flatCore`,
the squeeze constants `c₁ c₂`, the `IsSchurStraightenSqueeze` proof, and a `ReducedTransport S Y` (the det-1
MP descent). ONE shape (pp-rstar #134) for both C1 (hard-pivot: defect in the `b·E` perturbation) and C5
(partial-drop: defect in an `nReg`-regular generator after the shear) — the difference is the FIELD VALUES.

The reduced core `G` and the reduced-coord embed `redEmbed` are SOURCED from `transport` (`transport.G`,
`transport.redEmbed`), not standalone fields: the squeeze's `G` IS the transport's `G`, so the two descent
legs compose by construction (no coherence side-condition). `redEmbed` is fed to the squeeze as the
underlying function of the transport's homeomorphism (`↑transport.redEmbed`). -/
structure RouteMNodeDescent (M : Fin (L + 1) → ℕ) (S : ChainDimSplit M) (nReg : ℕ)
    (Y : Type) [PseudoMetricSpace Y] [MeasureSpace Y] [ProperSpace Y]
    [IsFiniteMeasureOnCompacts (volume : Measure Y)] [BorelSpace Y] [OpensMeasurableSpace Y] [Zero Y] where
  /-- The post-blow-up per-node core at the deepest point. -/
  flatCore : (Fin nReg → ℝ) × Y → ℝ
  /-- The det-1 MP descent transport (closes `rlctAtOn (G²) 0 = rlctAtOn (dlnLoss S.red 0) 0`); its `G` is
  also the squeeze's reduced core, and its `↑redEmbed` the squeeze's reduced-coord embed. -/
  transport : ReducedTransport S Y
  /-- The squeeze constants (genuine units). -/
  c₁ : ℝ
  c₂ : ℝ
  /-- The #134 ONE-datum squeeze: `rlctAtOn flatCore (0,0) = nReg/2 + rlctAtOn (G²) 0`, with `G` and
  `redEmbed` sourced from `transport`. -/
  isSqueeze : IsSchurStraightenSqueeze M S flatCore transport.G (fun y => transport.redEmbed y) c₁ c₂

/-- **The per-node DESCENT STEP (the consumer, fm3).** From a `RouteMNodeDescent`, the per-node RLCT at the
deepest point splits AND descends to the reduced chain:
`rlctAtOn flatCore (0,0) = nReg/2 + rlctAtOn (dlnLoss S.red 0) (fun _ => 0)`. Composes the banked
`schur_straighten_squeeze_of_data` (the `nReg/2 + rlctAtOn (G²) 0` split, with `G = transport.G`) with
`ReducedTransport.descent` (`rlctAtOn (G²) 0 = rlctAtOn (dlnLoss S.red 0) 0`). The two legs share the SAME
`G` (sourced from `transport`), so they compose with no coherence gap. G-b's cover lintegral recurses on
`S.red`. -/
theorem RouteMNodeDescent.descentStep {M : Fin (L + 1) → ℕ} {S : ChainDimSplit M} {nReg : ℕ}
    {Y : Type} [PseudoMetricSpace Y] [MeasureSpace Y] [ProperSpace Y]
    [IsFiniteMeasureOnCompacts (volume : Measure Y)] [BorelSpace Y] [OpensMeasurableSpace Y] [Zero Y]
    (nd : RouteMNodeDescent M S nReg Y) :
    rlctAtOn nd.flatCore (0, 0)
      = (nReg : ℝ≥0∞) / 2 + rlctAtOn (dlnLoss S.red 0) (fun _ => 0 : Params S.red) := by
  rw [schur_straighten_squeeze_of_data M S nd.flatCore nd.transport.G
        (fun y => nd.transport.redEmbed y) nd.c₁ nd.c₂ nd.isSqueeze,
    nd.transport.descent]

/-- **The per-node datum, `Y`-existential (the PRODUCER's emission shape).** The per-node-varying reduced
coords `Y` are bundled here: the G-a producer emits, for each non-leaf node, some `nReg`/`Y`/datum. This is
what rs-grind's per-node read + fm3's per-node construction jointly supply. -/
def RouteMNodeDescentExists (M : Fin (L + 1) → ℕ) (S : ChainDimSplit M) : Prop :=
  ∃ (nReg : ℕ) (Y : Type) (_ : PseudoMetricSpace Y) (_ : MeasureSpace Y) (_ : ProperSpace Y)
    (_ : IsFiniteMeasureOnCompacts (volume : Measure Y)) (_ : BorelSpace Y)
    (_ : OpensMeasurableSpace Y) (_ : Zero Y),
    Nonempty (RouteMNodeDescent M S nReg Y)

/-! ## `example`-blocks pinning the seam (durable contracts; both worktrees build against these)

If either side's emission/consumption drifts from these, its build breaks here first (the seam-drift catch). -/

/-- PRODUCER contract (rs-grind + fm3 co-build): the G-a hnode producer emits, for each non-leaf node,
a `RouteMNodeDescentExists M S` (some nReg/Y/datum). rs-grind supplies the per-node defect-class +
cell-enumeration + the binding `T*`-profile split; fm3 builds the `flatCore`/`G`/squeeze from
`schur_node_loss_presentation` + the L2 `DeepestGaugeBlocks` template (C1 = `schur_node_squeeze_unif`,
C5 = the shear `δ'` fold). -/
example : Prop :=
  ∀ (M : Fin (L + 1) → ℕ) (S : ChainDimSplit M), ¬ isLeafNode M → RouteMNodeDescentExists M S → True

/-- CONSUMER contract (fm3, G-b): the cover lintegral CoV consumes the per-node `descentStep`
(`rlctAtOn flatCore (0,0) = nReg/2 + rlctAtOn (dlnLoss S.red 0) 0`) and recurses on `S.red` (the
`measure_drops` well-foundedness in `isSqueeze`). Pinned: the descent step's exact form. -/
example {M : Fin (L + 1) → ℕ} {S : ChainDimSplit M} {nReg : ℕ}
    {Y : Type} [PseudoMetricSpace Y] [MeasureSpace Y] [ProperSpace Y]
    [IsFiniteMeasureOnCompacts (volume : Measure Y)] [BorelSpace Y] [OpensMeasurableSpace Y] [Zero Y]
    (nd : RouteMNodeDescent M S nReg Y) :
    rlctAtOn nd.flatCore (0, 0)
      = (nReg : ℝ≥0∞) / 2 + rlctAtOn (dlnLoss S.red 0) (fun _ => 0 : Params S.red) :=
  nd.descentStep

end DLNFibre.DLN.RLCT
