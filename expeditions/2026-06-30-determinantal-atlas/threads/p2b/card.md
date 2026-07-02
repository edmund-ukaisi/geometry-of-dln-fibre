# P2.b statement cards — overlap transition maps of the constructive pivot-chart atlas

Home: `lean/DLNFibre/Core/RingTheory/Determinantal/AtlasTransition.lean` (bare `Algebra` namespace,
L7 Mathlib-mirror, sibling of P2.a's `Algebra.StandardFibreChart`). Built from the P1.a overlap API
(`Localization.awayOverlap`/`awayOverlapTransition`/`awayCongr'`,
`Core/RingTheory/Localization/Overlap.lean`) + the P2.a atlas datum (`Algebra.StandardFibreChart`,
`Core/RingTheory/Determinantal/Atlas.lean`). The DLN target-side transition
(`Core/FibreTargetOverlap.lean`) is re-homed to the instance. Design (Option C: chartElt + bare-`k`
trivialization) decorrelated-Codex-vetted (`codex/design-{prompt,answer}.md`, xhigh).

**SCOPE: transition OBJECTS + basic identities only.** The cocycle round-trip / triple associativity
is the **P2.c CRUX** — set up reachable here, not proved.

---

## The chart-element pairing (Flag 2)

> **Claim.** A chart of a constructive pivot-chart atlas pairs its principal-open base element with a
> bare `k`-algebra trivialization of the localized chart total ring as a fixed standard fibre model.
>
> - **Lean:** `Algebra.AtlasChart k Base M` (structure) — fields `chartElt : Base`,
>   `trivK : Localization.Away chartElt ≃ₐ[k] M`. Companion `Algebra.AtlasFibreChart k Base M BaseLoc
>   Fibre extends AtlasChart`, carrying `fibreModel : StandardFibreChart k (Away chartElt) BaseLoc
>   Fibre` (the over-base content for the capstone, NOT consumed by the transition).
> - **Gloss.** P2.a's `StandardFibreChart` deliberately dropped the base element; the transitions live
>   on overlaps `D(f) ∩ D(g)`, so the base element must travel with the chart. `AtlasChart` is the
>   minimal pairing the transitions need; `AtlasFibreChart` records the over-base fibre model.
> - **Proved.** The structures + their API. Single universe `Type u` throughout (matching the sibling
>   `StandardFibreChart` / `LocalTrivializationDatum`); the multi-universe form floated metavars in the
>   DLN instance (the over-base tensor model's universe), pinned by the single-universe convention.
> - **Two-base discipline.** `Base` is the GLOBAL base (where `chartElt` + the overlap localizations
>   live); `BaseLoc` is the per-chart base DIRECTION of the fibre model. A `chartElt` is `: Base`.
> - **Status.** sorry-free; axiom-clean.

## The overlap transition map (the headline)

> **Claim.** Two charts `C, D` of the atlas, with base elements `f, g : Base`, have a canonical
> `k`-algebra transition between the two trivialized presentations of their overlap `D(f) ∩ D(g)` on
> the standard fibre model `M`: conjugate the base-side overlap transition (P1.a's
> `awayOverlapTransition`, `k`-restricted) through the two base→target localization transports.
>
> - **Lean:** `Algebra.AtlasChart.overlapTransition C D : targetChartLoc C D ≃ₐ[k] targetChartLoc D C`
>   (`lean/DLNFibre/Core/RingTheory/Determinantal/AtlasTransition.lean`).
> - **Supporting defs.** `overlapElt C D := algebraMap Base (Away C.chartElt) D.chartElt` (the
>   chart-`D` element localized into the chart-`C` total ring; its `Away` is `awayOverlap C.chartElt
>   D.chartElt`); `@[reducible] targetChartLoc C D := Localization.Away (C.trivK (overlapElt C D))`
>   (`M` localized at the image — the double-localized object); `overlapTriv C D := Localization.
>   awayCongr' C.trivK (overlapElt C D) _ rfl : awayOverlap C.chartElt D.chartElt ≃ₐ[k] targetChartLoc
>   C D` (the base→target transport); `chartOverlapTransitionK C D := (awayOverlapTransition C.chartElt
>   D.chartElt).restrictScalars k` (the `k`-restricted base transition).
> - **Gloss.** `overlapTransition C D = (overlapTriv C D).symm ≪≫ (chartOverlapTransitionK C D ≪≫
>   overlapTriv D C)`. The parenthesization is fixed as a `trans` sandwich so the P2.c round-trip is
>   reachable by the `AlgEquiv` groupoid laws.
> - **Proved.** The transition object, over arbitrary `k`-algebras `Base`, `M` and any chart elements.
>   `chartOverlapTransitionK_apply` (agrees with the underlying base transition as a function) and
>   `chartOverlapTransitionK_trans_symm` (the base-side round-trip `(C,D)∘(D,C) = refl`, the
>   `k`-restriction of P1.a's `awayOverlapTransition_trans_symm`).
> - **Cited.** none.
> - **Deferred (P2.c CRUX).** The TARGET-side round-trip `overlapTransition C D ≪≫ overlapTransition D
>   C = refl` and triple associativity — NOT proved here. The base-side round-trip
>   `chartOverlapTransitionK_trans_symm` is the evidence; the structural route (rearrange the `trans`
>   sandwich via `AlgEquiv.trans_assoc`/`trans_refl`/`refl_trans` from P2.b′, off the heavy
>   `targetChartLoc`) is unblocked but the proof is the next rung.
> - **Status.** sorry-free; `#print axioms = [propext, Classical.choice, Quot.sound]`.

## The localization transport `awayCongr'` (re-homed brick)

> **Claim.** For an `R`-algebra iso `e : A ≃ₐ[R] B` carrying `a` to `b`, the canonical
> `Localization.Away a ≃ₐ[R] Localization.Away b`.
>
> - **Lean:** `Localization.awayCongr'` (+ `awayCongr'_symm`)
>   (`lean/DLNFibre/Core/RingTheory/Localization/Overlap.lean`, bare `Localization` ns).
> - **Re-home.** Lifted verbatim from the DLN `FibreTargetOverlap.awayCongr'` to the abstract
>   `Localization` overlap home (it is a general localization combinator; the DLN-specific `awayCongr`
>   `A ≃ₐ A` variant in `FibreChartConjugation` stays). The transition conjugates a base overlap
>   through a chart trivialization with it.
> - **Status.** sorry-free; axiom-clean.

---

## The DLN bundle as the instance (re-home of `FibreTargetOverlap`, kept-DLN)

> `pivotAtlasChart d r hp hq I : Algebra.AtlasChart k (sweepSigmaRing k d r) (SchurLoc ⊗_k
> sweepFibreRing)` — base element `pivotElt I = chartDsigAt I.s I.t`, `trivK =
> perPivotLocalTrivializationDatum.trivialization`. **The DLN reduced-fibre bundle is now an instance
> of the abstract atlas transition layer.**
>
> - The DLN base-side transition `chartOverlapTransitionK` and round-trip
>   `chartOverlapTransitionK_trans_symm` (`Core/FibreTargetOverlap.lean`) are **literally**
>   `Algebra.AtlasChart.chartOverlapTransitionK (pivotAtlasChart I) (pivotAtlasChart J)` &c. (the
>   abstract `restrictScalars` def pins the scalar-tower internally — the DLN `set_option
>   maxHeartbeats 800000` on these is gone).
> - The DLN target-side data (`overlapElt`/`targetChartLoc`/`overlapTriv`/
>   `targetProductOverlapTransition`) keep the original one-`Localization.Away`-layer shape (now
>   calling `Localization.awayCongr'`), definitionally the abstract data at `pivotAtlasChart`. Routing
>   `targetChartLoc` through the abstract `AtlasChart` structure projection makes `Semiring`-synthesis
>   whnf-reduce the heavy per-pivot trivialization and TIME OUT (the same kernel-cost trap as P2.c);
>   the one-layer shape keeps the doubly-localized instances firing. Documented in-file.
> - **`minorChartTransition`** (`FibreBundleTransition.lean`) — left as-is: it is already a thin wrapper
>   of P1.a's base-side `awayOverlapTransition` (no trivialization / no target side; the
>   ambient-affine-space cover transition). Not re-routed through the atlas (no `trivK` to consume).

## Flag 3 (instance-diamond) — DODGED

No `includeLeft.toAlgebra` vs `TensorProduct.leftAlgebra` diamond / stuck `SMulCommClass` arose: the
transition consumes only the **bare `k`-algebra `trivK`**, never the over-base `StandardFibreChart.triv`
(`≃ₐ[BaseLoc]`), so no over-base/refl iso is constructed in the transition path. The over-base content
is carried by `AtlasFibreChart` (for the capstone) but not touched by `overlapTransition`. No explicit
`AlgEquiv.ofRingEquiv`-over-`letI` was needed.

---

## Gates

- Full aggregator green (`scripts/lb DLNFibre`, **3832 jobs**); `scripts/sorries` = 0.
- `#print axioms` = `[propext, Classical.choice, Quot.sound]` on `Algebra.AtlasChart.overlapTransition`,
  `Algebra.AtlasChart.chartOverlapTransitionK`, `..._trans_symm`, `Algebra.AtlasChart.overlapTriv`,
  `Localization.awayCongr'`, and the DLN instances `targetProductOverlapTransition`,
  `chartOverlapTransitionK_trans_symm`, `pivotAtlasChart`.
- L7 bare namespaces (`Algebra` / `Localization`); L2 consumer sweep clean (only `FibreTargetOverlap`
  depended on the moved `awayCongr'`/the target transition, re-homed in lockstep); L4 all my lines
  ≤ 100; sibling-clash `rg` — `AtlasChart`/`AtlasFibreChart`/`overlapTransition` unique to the new file.
- **Set up for P2.c:** `chartOverlapTransitionK_trans_symm` named at the base level; `overlapTransition`
  parenthesized as a `trans` sandwich; the `AlgEquiv` groupoid laws (P2.b′) are imported-reachable.
