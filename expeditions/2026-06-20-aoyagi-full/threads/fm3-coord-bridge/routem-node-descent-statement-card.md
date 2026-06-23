# Statement card — `RouteMNodeDescent` (the #135 G-a LOCKED descent seam)

- **Status:** `sorry-free`, seam LOCKED (awaiting fidelity review). Branch `origin/fm3/routem-ga`
  @2480960. File `lean/DLNFibre/DLN/RLCT/Validate/RouteMNodeDescent.lean`. Build GREEN (2679 jobs,
  0 sorry); `descentStep` axiom clean-three (`propext`, `Classical.choice`, `Quot.sound` — NO `sorryAx`,
  transitively clean: composes two banked lemmas).
- **Role:** the descent-side analog of `RouteMBranchRead` (the #99/#125 value seam). It is the LOCKED
  producer/consumer interface both the G-a hnode producer (rs-grind: cell-enum + defect-class + T*-profile)
  and the G-b cover lintegral (fm3: flatCore/transport/squeeze fill) build against BEFORE parallel-filling
  — the seam-drift mitigation that worked for #99/#125.

## The structure (the per-node descent datum)

```text
structure RouteMNodeDescent (M : Fin (L+1) → ℕ) (S : ChainDimSplit M) (nReg : ℕ)
    (Y : Type) [PseudoMetricSpace Y] [MeasureSpace Y] [ProperSpace Y]
    [IsFiniteMeasureOnCompacts (volume : Measure Y)] [BorelSpace Y] [OpensMeasurableSpace Y] [Zero Y] where
  flatCore  : (Fin nReg → ℝ) × Y → ℝ
  transport : ReducedTransport S Y
  c₁ c₂     : ℝ
  isSqueeze : IsSchurStraightenSqueeze M S flatCore transport.G (fun y => transport.redEmbed y) c₁ c₂
```

## The descent step (the consumer, PROVEN)

```text
RouteMNodeDescent.descentStep (nd : RouteMNodeDescent M S nReg Y) :
    rlctAtOn nd.flatCore (0, 0)
      = (nReg : ℝ≥0∞) / 2 + rlctAtOn (dlnLoss S.red 0) (fun _ => 0 : Params S.red)
  := by rw [schur_straighten_squeeze_of_data M S nd.flatCore nd.transport.G
              (fun y => nd.transport.redEmbed y) nd.c₁ nd.c₂ nd.isSqueeze,
            nd.transport.descent]
```

## The producer's emission shape (the `Y`-existential)

```text
RouteMNodeDescentExists (M) (S : ChainDimSplit M) : Prop :=
  ∃ nReg Y (_ : PseudoMetricSpace Y) (_ : MeasureSpace Y) (_ : ProperSpace Y)
    (_ : IsFiniteMeasureOnCompacts (volume : Measure Y)) (_ : BorelSpace Y)
    (_ : OpensMeasurableSpace Y) (_ : Zero Y),
    Nonempty (RouteMNodeDescent M S nReg Y)
```

## English gloss

For a non-leaf node `M` with width-split `S : ChainDimSplit M`, the per-node RLCT at the deepest point
`(0,0)` SPLITS as `nReg/2 + rlctAtOn (dlnLoss S.red 0) 0` — the `nReg` regular smooth blocks plus the
strictly-smaller reduced-chain core, which the G-b cover lintegral recurses on (`measure_drops` in the
squeeze datum). The datum bundles the post-blow-up core `flatCore`, the squeeze proof
(`IsSchurStraightenSqueeze`, the `nReg/2 + rlctAtOn (G²) 0` split), and the det-1 MP descent transport
(`ReducedTransport S Y`, closing `rlctAtOn (G²) 0 = rlctAtOn (dlnLoss S.red 0) 0`). The two legs compose
to the descent step.

## Two load-bearing design pins (the build-fixes)

1. **`G` + `redEmbed` are SOURCED FROM `transport`** (`transport.G`, `↑transport.redEmbed`), NOT standalone
   fields. The squeeze's reduced core IS the transport's `G`, so `descentStep`'s two rewrites compose with
   ZERO coherence side-condition. Standalone `G`/`redEmbed` fields left the second `rw`
   (`transport.descent`, stated for `fun y => transport.G y ^ 2`) with a function mismatch against the
   squeeze's output (`fun y => G y ^ 2`) — unsolved goal.
2. **`Y` carries the HEAVY `schur_straighten_squeeze_of_data` instance bundle**
   (`PseudoMetricSpace`/`MeasureSpace`/`ProperSpace`/`IsFiniteMeasureOnCompacts volume`/`BorelSpace`/
   `OpensMeasurableSpace`/`Zero`), not the lighter `MeasureSpace`/`TopologicalSpace`/`Zero`. The lighter
   `ReducedTransport` requirements derive from it (`PseudoMetricSpace → TopologicalSpace`); the heavier set
   is what the squeeze's `rlctAtOn` measure hygiene needs. The light bundle failed instance synthesis at
   `schur_straighten_squeeze_of_data`.

## ONE datum covers C1 AND C5 (pp-rstar #134)

The same structure serves both non-leaf defect classes — C1 (hard-pivot: defect in the `b·E` perturbation)
and C5 (partial-drop: defect in an `nReg`-regular generator after the shear `δ' = δ + (G·q·e)/‖e‖²`). The
difference is the FIELD VALUES the producer supplies (`flatCore`, the squeeze constants, the transport),
NOT the structure. `nReg` VARIES per node (= the regular-block count = #non-binding layers).

## The seam contracts (two `example`-blocks, durable)

- **PRODUCER** (rs-grind + fm3 co-build): `∀ M S, ¬ isLeafNode M → RouteMNodeDescentExists M S → True` —
  the G-a producer emits some `nReg`/`Y`/datum per non-leaf node.
- **CONSUMER** (fm3, G-b): the `descentStep` form, consumed verbatim by the cover lintegral CoV.

If either side's emission/consumption drifts from these, its build breaks HERE first (the seam-drift catch).

## Honest scope / what is NOT here

- This is the LOCKED INTERFACE + the composed `descentStep` only. It carries NO producer content: the
  `IsSchurStraightenSqueeze.squeeze` field (the `c₁·Φ ≤ flatCore ≤ c₂·Φ` estimate from
  `flatCore − Φ ∈ ideal(regular gens)`) and the `ReducedTransport` instances are what the parallel-fill
  builds — from `schur_node_loss_presentation` + the L2 `DeepestGaugeBlocks` template (C1 =
  `schur_node_squeeze_unif`, C5 = the shear `δ'` fold).
- It consumes the two banked lemmas `schur_straighten_squeeze_of_data` (#129/#130/#131, the squeeze→split
  engine) and `ReducedTransport.descent` (crux2 #73/#119, the det-1 MP reindex). Both are themselves
  sorry-free + axiom clean-three on `fm3/routem`; `descentStep` inherits that cleanliness.
- The G-b cover lintegral (the recursion ON `S.red` using `descentStep` + `measure_drops`) is NOT here —
  that is the consumer fill that builds against this seam.

## Parallel-fill split (the gate this card opens)

- **rs-grind (producer read):** per non-leaf node — (a) defect-class tag (C1/C5), (b) cell-enumeration
  (the `cells : Type` of `RouteStep.branch`; confirm cell↔node map), (c) binding-`T*`-profile split
  (feeds `nReg`).
- **fm3 (fill):** `flatCore`/`transport`/`squeeze` per cell from the L2 template.
- **crux2:** on-call for `#72`/`#71`-peel in the cover `cover_le`.
