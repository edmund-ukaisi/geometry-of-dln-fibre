# Review — divCoord-reachability sub-arc (fidelity + honesty)

*Reviewer (controller-spawned, `review/reach`), function = FIDELITY + honesty. Target: the
divCoord-reachability sub-arc merged in `70331a786` (t07 step2+3) on top of step-1 (`89325331e`):
`Engine/DivBirthReach.lean` (DivBirthInv + the reachability→injectivity chain) and the
`leafOfState.divCoord` real-ification in `Engine/EngineConstruction.lean`. Worktree branched off a
stale `origin/expedition/aoyagi-engine`; fast-forwarded to `944521526` (tick-232 tip) so the audit
sees the actually-merged content. Report-only per `review.md`; propose-never-act.*

**Verdict: SURVIVED.** All six items PASS. Independent build (Mathlib cache + targeted rebuild)
green; `#print axioms` clean-three on all seven public theorems of the chain
(`flatIdx_corner_inj` needs only `[propext]`). One decorrelated Codex leg (items 2/4) concurs:
sound, no gap or circularity. Two precision co-locations recorded (neither a break): the
region_glue call site consumes from the ChartBridge *atlas* (virtual leaves), not
`ResolutionTree.leaves` directly — the identity is a coverage forecast, honestly caveated; and two
of the three clauses (resCoord-inj, disjoint) are vacuous via `resRank=0` (honestly marked), so their
*real* content is untested until resRank>0 leaves (if ever) arrive.

---

## Item 1 — Consumer fidelity: PASS

`leaves_chart_clauses_conRoot` (DivBirthReach:325-329) concludes, for
`l ∈ ResolutionTree.leaves (buildTree M (conOracle M) conRoot)`:

    Function.Injective l.divCoord ∧ Function.Injective l.resCoord ∧
      Disjoint (Set.range l.divCoord) (Set.range l.resCoord)

The consumer `leaf_chart_image_lintegral_lt_top` (RegionGluePerLeaf:123-124) consumes exactly:

    (hdcInj : Function.Injective l.divCoord) (hrcInj : Function.Injective l.resCoord)
    (hdisj : Disjoint (Set.range l.divCoord) (Set.range l.resCoord))

Verbatim type/form match at the `LeafData M` level. The tree identity is consistent: the ChartBridge
is built for `buildTree M (conOracle M) conRoot` (EngineObligations:52), the same object the producer
quantifies over.

**Precision co-location (not a break).** The *actual* region_glue call site is
`region_glue_of_chartBridge` (RegionGlueAssembly:120-123): it destructures the `ChartBridge` **atlas**
(`List (LeafData M)` — "virtual leaves", EngineDefs:96-109) and reads hdcInj/hrcInj/hdisj from the
per-piece props, NOT from `leaves_chart_clauses_conRoot`. So the producer's role is to *discharge* the
atlas clauses once `chartBridge_buildTree` (still a named sorry, EngineObligations:51-53) is filled.
That discharge works only if each atlas piece's `divCoord`/`resCoord` equal its ledger leaf's — which
is exactly the tick-232 addendum's "atlas pieces share the ledger leaf's coordinate data" forecast,
a coverage-lane implication NOT yet in Lean. This is honestly stated in the journal and does not
inflate any Lean name. Item passes; the object-identity bridge is a documented forecast, not a
delivered fact.

## Item 2 — dite-fallback honesty: PASS (a,b,c)

**(2a) Real branch = genuine diagonal birth corner.** `birthFlatCoord` (EngineConstruction:1755-1772)
on its real branch returns `Fintype.equivFin (FlatIdx M) ⟨⟨⟨a,hL⟩,⟨b,hi⟩⟩,⟨b,hj⟩⟩` with
`(a,b) = divBirthCoord k` — the flat slot `(layer=a, row=b, col=b)`, i.e. the diagonal corner
`(a,b,b)`. `stepAppendAdvance` stores `(s.layer, s.cleared)` (the OLD cleared, pre-increment;
EngineConstruction:189-193), so the corner is `(birth-layer, cleared-at-birth, cleared-at-birth)` =
cert §3's `(S,J,J)`. The docstring's "equal to `CenterIndices.flatCoordOf` on the real branch (defeq)"
is accurate (`flatCoordOf M s i j = equivFin ⟨⟨s,i⟩,j⟩`, CenterIndices:30-32).

**(2b) Fallback provably never fires on the cone.** Traced the birth maintenance
(`DivBirthInv_stepAppendAdvance`, DivBirthReach:91-129) myself: the append guard
`hlt : cleared < widthMinUpto M (layer+1)` (supplied only in the non-rollover conOracle branch,
DivBirthReach:151) yields corner validity via `widthMinUpto_le`:

- row: `(i:ℕ)=layer ≤ layer+1 ⟹ cleared < widthMinUpto M (layer+1) ≤ M i`;
- col: `(i:ℕ)=layer+1 ≤ layer+1 ⟹ cleared < widthMinUpto M (layer+1) ≤ M i`.

`birthFlatCoord_of_valid` (DivBirthReach:211-222) turns `CornerValid` into `dif_pos` on all three
guards — the real branch. Since `DivBirthInv` carries validity for **every** `k`, every divisor on the
cone takes the real branch. Off-cone the total function may collide at `⟨0,h⟩`, but no theorem consumes
that: injectivity is stated *under* `DivBirthInv`.

**(2c) Nothing downstream consumes the fallback as real.** `leaves_chart_clauses(_conRoot)` and
`leafOfState_divCoord_injective` are all hypothesised on `DivBirthInv M s`, threaded from
`DivBirthInv_conRoot` (vacuous) through `DivBirthInv_conOracle_stepChildren`. The injectivity theorem
quantifies the **cone** (reachable-from-conRoot states), not all `ConState`. No other theorem reads
`leafOfState.divCoord` (o5_realization/isFullMono/srcBox read divExp/divProfile/srcBox only). The
`flatDim=0` branch has an empty divisor index type (vacuous injectivity), never invoking the fallback.

## Item 3 — Vacuity honesty: PASS

`leafOfState_resCoord_injective` (DivBirthReach:275-281) and `leafOfState_disjoint` (283-293) are
vacuous via `leafOfState_resRank_zero`. Both docstrings say so **plainly** ("vacuously, the residual
side is empty" / "vacuously, the residual range is empty") — no vacuous-as-content dressing. The
consumer is sound at `resRank=0`: `leaf_chart_image_lintegral_lt_top` routes through
`flat_leaf_model_lt_top`'s `nr=0` branch (RegionGluePerLeaf:82-105), where the residual factor
collapses to `1` and `hrcInj`/`hdisj` are consumed only via `prod_two_family_eq` with an empty `rc` —
holds trivially. The proof does **not** need a nonempty resCoord range.

**Context (out of this sub-arc, recorded for the co-location).** Two of the three "fed hyps" are
therefore vacuous: only `divCoord`-injectivity is genuine content here; resCoord-inj and disjoint hold
*because* `leafOfState.resRank = 0`. If geometrically-real leaves ever carry Morse residual
coordinates (`resRank > 0`), the disjointness of the birth-corner divCoord range from the residual
range becomes a *real* obligation this sub-arc does not establish. This is a pre-existing `leafOfState`
model choice, not a regression; flagging only so the vacuity is not later mistaken for tested content.

## Item 4 — Injectivity chain: PASS

`flatIdx_corner_inj` (DivBirthReach:227-239): equal FlatIdx sigmas at `(a,b,b)`/`(a',b',b')` give
`a=a'` (inner-sigma layer `Fin.val`) and `b=b'` (col HEq via `Fin.heq_ext_iff`, types agree once
`a=a'` since the col width depends only on `succ layer`). Discarding the row HEq is safe — the col
alone recovers `b`. `birthFlatCoord_injective` (244-253): validity ⟹ both real branches; equal coords
⟹ (equivFin injective) equal sigmas ⟹ (flatIdx_corner_inj) equal corner pairs ⟹ (`divBirthCoord`
injective, the DivBirthInv clause) `k=k'`.

The `.get` composition preserves injectivity because `t0Indices` is NoDup:
`leafOfState_divCoord_injective` (263-271) builds
`Function.Injective (t0Indices s).get` from `((List.nodup_finRange s.numDiv).filter _).injective_get`
(`finRange` NoDup, `.filter` preserves it, NoDup ⟹ injective_get), then composes with
`birthFlatCoord_injective`. Both legs verified. The load-bearing NoDup fact IS established.

## Item 5 — Freshness soundness: PASS (strengthening, named)

The Lean freshness clause — "every stored corner at the current layer has column `< cleared`"
(DivBirthInv, DivBirthReach:57) — is the **inductive strengthening** of cert §4's argument (within a
layer, cleared strictly increases between births; across layers, distinct layer index). It is
self-maintaining: at a birth the appended `(layer, cleared)` satisfies `cleared < cleared+1` and old
same-layer corners stay `< cleared+1` (DivBirthReach:119-127); at rollover it is vacuous (all stored
layers `≤ old < new`, DivBirthReach:83-86); case11 carries it verbatim. Freshness feeds
`hnotmem` (the new corner is not in the old range), which drives `Fin.snoc_injective_of_injective` —
so it is exactly what preserves `divBirthCoord` injectivity across births. This is a
different-but-sufficient (indeed the natural inductive) form of the cert's distinctness argument, and
it closes the induction. (Named as a strengthening per the audit ask.)

## Item 6 — Wording scrub: PASS (no removals needed)

`grep -rniE` of the banned-wording list over the sub-arc's Lean docstrings (DivBirthReach.lean, the
`birthFlatCoord`/`leafOfState` region of EngineConstruction.lean): **zero hits**. Journal ticks
229/232 use "honestly" only as an object-level descriptor ("holes named honestly", "resRank=0,
honestly marked") — kept per `review.md` (object-level, not authorial self-reassurance). Nothing to
remove; nothing object-level lost.

---

## Verification performed

- Fast-forwarded review branch to `944521526`; confirmed step2+3 (`70331a786`) content present.
- `lake exe cache get` + `lake build DivBirthReach RegionGluePerLeaf` → **BUILD_EXIT=0**
  (the only `sorry` warnings are in the unrelated legacy `Skeleton.lean`).
- `#print axioms`: `leaves_chart_clauses_conRoot`, `leafOfState_divCoord_injective`,
  `birthFlatCoord_injective`, `DivBirthInv_conOracle_stepChildren`, `leafOfState_resCoord_injective`,
  `leafOfState_disjoint` → `[propext, Classical.choice, Quot.sound]`; `flatIdx_corner_inj` →
  `[propext]`. All clean, no `sorryAx`.
- Decorrelated Codex (xhigh, my verdicts withheld):
  `codex/reach-inj-{prompt,answer}.md` — verdict "sound under DivBirthInv; no gap or circularity",
  confirming validity arithmetic, fallback-unreachability, `flatIdx_corner_inj`, freshness induction,
  and one-way (non-circular) dependency.

## Escalations to operator

None. No fidelity mismatch, no soundness break. The two precision co-locations (item 1 atlas-vs-leaves
forecast; item 3 resRank=0 vacuity) are honestly documented in the sub-arc and journal; recorded here
so the forecasts are not later read as delivered facts.
