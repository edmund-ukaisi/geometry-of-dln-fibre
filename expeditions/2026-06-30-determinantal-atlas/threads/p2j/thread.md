# P2.j — route the DLN transition defs through the abstract atlas

**Thread:** p2j-reroute (lean-formaliser). Branch `expedition/det-atlas-p2`.
**File touched:** `lean/DLNFibre/Core/FibreTargetOverlap.lean` (only).

## Goal (as briefed)
Redefine the concrete DLN transition objects (`overlapElt`, `targetChartLoc`, `overlapTriv`,
`targetProductOverlapTransition`) to LITERALLY delegate to `Algebra.AtlasChart.…` at
`pivotAtlasChart`, giving the module a single source of truth, AND remove the
`set_option maxHeartbeats 800000 in` on `targetProductOverlapTransition_trans_symm` (the brief's
premise: after delegation the theorem becomes a one-step unfold, bump-free).

## What LANDED
- All four DLN defs now delegate to the abstract atlas (single source of truth):
  - `overlapElt I J        := Algebra.AtlasChart.overlapElt (pivotAtlasChart I) (pivotAtlasChart J)`
  - `targetChartLoc I J     := Algebra.AtlasChart.targetChartLoc (pivotAtlasChart I) (…J)`
  - `overlapTriv I J        := Algebra.AtlasChart.overlapTriv (pivotAtlasChart I) (…J)`
  - `targetProductOverlapTransition I J := Algebra.AtlasChart.overlapTransition (…I) (…J)`
  (`chartOverlapTransitionK` already delegated — left as-is.)
- **`(k := k)` on `pivotAtlasChart` in each body is load-bearing.** The DLN section is `{k : Type}`
  implicit; `pivotAtlasChart`'s `k` appears only in its return type, so a bare
  `pivotAtlasChart d r hp hq I` leaves `k` a metavar → `Infinite ?m` stuck → the def's `k` param
  gets auto-mangled. Naming `k` explicitly pins it. (Needed especially on `targetChartLoc`, whose
  `: Type` return ascription pins nothing.)
- Consumer sweep: the ONLY consumer of the DLN `targetChartLoc`/`overlapTriv`/
  `targetProductOverlapTransition` is this file itself. The P2.f/g triple layer + witnesses +
  `Core/FibreZariskiLocalTriviality` (`pivotAtlasFibreChart`,
  `reducedFibre_isZariskiLocallyTrivialAffineProduct`) all build on the ABSTRACT `AtlasChart.…`, not
  the DLN objects — confirmed by `rg`. So the reroute is contained; no downstream proof broke.
- Docs updated to say the defs are DEFINED AS the abstract (removed "re-spelled" / "unfolded to a
  single Localization.Away layer" framing).

## What did NOT land — the bump is NOT eliminable (obstruction to the brief's premise)
`targetProductOverlapTransition_trans_symm` still needs a raised `maxHeartbeats` (reduced 800000 →
**400000**, but not removable). Precise obstruction:

- The timeout is a `(deterministic) timeout at isDefEq` during **elaboration of the theorem's
  STATEMENT**, before any tactic runs — specifically synthesizing the `Semiring`/`Algebra k`
  instances of the `AlgEquiv.refl (R := k)` / `.trans` at the reducible DLN `targetChartLoc` alias.
  Resolving those instances `whnf`-reduces `Localization.Away (C.trivK (overlapElt C D))` where
  `C.trivK = perPivotLocalTrivializationDatum.trivialization` — the heavy per-pivot trivialization
  applied to the overlap element.
- This cost is a **property of the concrete `targetChartLoc` TYPE**, present in BOTH the old
  re-spelled form and the new delegated form — the delegation changes the def BODIES, not the
  theorem's type. So no reformulation of the def or the proof term removes it. Confirmed empirically:
  plain `exact`, `simp only [targetProductOverlapTransition]; exact`, `show`-into-abstract-type, and
  `AlgEquiv.ext`-pointwise ALL still time out at default 200000 — because the statement type is what
  is expensive, not the proof.
- WHY the abstract `overlapTransition_trans_symm` needs no bump but the DLN instance does: in the
  abstract, `C D : AtlasChart …` are VARIABLES, so `C.trivK` is an opaque projection and
  `targetChartLoc C D` never `whnf`-reduces into anything heavy. At the concrete `pivotAtlasChart I`,
  `.trivK` IS the heavy trivialization, so instance synthesis over the reducible alias unfolds it.
- The reroute DID roughly halve the cost (800000 → 400000): evidence the delegation helps the
  transition-object comparison, just not the intrinsic statement-type synthesis.

## Gates
- `scripts/lb DLNFibre` full aggregator: GREEN, **3834 jobs**.
- `scripts/sorries`: 0 sorry / 0 #exit / 0 native_decide / 0 axiom.
- `#print axioms` (all `[propext, Classical.choice, Quot.sound]`, no regression):
  - `targetProductOverlapTransition_trans_symm` ✓ (still axiom-clean; bump adds no axioms)
  - `reducedFibre_isZariskiLocallyTrivialAffineProduct` ✓
  - `DLNFibre.DLN.rlct_lossDLN_eq_half_cCodim_add_shift_via_aoyagi` ✓
  - `DLNFibre.DLN.rlct_lossDLN_d222_one_eq_two_via_aoyagi` ✓
- Gate 4 (`rg maxHeartbeats FibreTargetOverlap.lean` → empty): **NOT met** — one bump remains at
  400000 (obstruction above). Formatted with the repo's reason-comment idiom (linter clean).

## Scope addition — stale-doc sweep (3 files, from PR #21 review)
Comment/docstring-only sweep of live prose still implying the LOCAL target-side cocycle / round-trip
(R1) is unbuilt. Narrowed every now-false claim to: the LOCAL target-side pairwise round-trip (P2.c)
+ canonical triple cocycle (P2.f) + restricted-2-fold naturality/cocycle (P2.g) are PROVED (per
chart / per overlap); only the GLOBAL gluing of the per-chart data into one fibration morphism /
`Flat π` over all of `rankROpen` stays roadmapped (R1). Kept the GLOBAL caveat (genuinely still
unbuilt) everywhere; did not over-narrow.
- `lean/DLNFibre.lean` — 3 aggregator comments (the `reducedFibre_pivotLocalProductAtlasOnRankOpen`
  residual note; the `FibreLocallyTrivial` "UNCOCYCLED"; the `FibreProjectionCompat` "target-side
  cocycle still residual"). Comments only, no import reorder. The already-accurate P2.c/f/g cluster
  and the genuine "R1/global gluing" notes were left as-is.
- `lean/DLNFibre/Core/FibreBundleHeadline.lean` — module OPEN-ITEM block + 3 docstrings. Dropped
  "uncocycled".
- `lean/DLNFibre/Core/FibreOverBaseTriv.lean` — module intro + main-results flatness bullet + Scope
  (ii) + `TopLeftFlat` section header + both `_flat` theorem docstrings (shortened the two long
  bold-headline first lines, moved the R1 caveat into the prose body).

**FLAGGED (not edited — for lead adjudication):** `DLNFibre.lean` lines ~357–361 / ~373–378 /
~396–400 are thread-scoped HISTORICAL annotations ("Scope-3 … thread NN #NNN … PARTIAL: still NOT
`locallyTrivial` — the cocycle transport ON the per-pivot trivializations remains (#133)"). These
describe what those INDIVIDUAL earlier modules delivered at their thread's time — accurate as
per-module provenance, but a reader could read "cocycle transport … remains" as implying the
now-landed (P2.c/f/g) transport is still open. Left untouched; flagged in the report.

Build: full aggregator GREEN, 3834 jobs; `scripts/sorries` = 0; comment-only ⟹ axioms unchanged.

## Codex consult (xhigh, decorrelated)
See `codex-consult.md`. Confirmed the diagnosis: the timeout is aligning the reducible-typed
`AlgEquiv.refl` through the localization; Codex's proposed `show`/`change`-to-abstract-type idiom did
NOT work empirically because the cost is in statement-type instance synthesis, which those idioms
still trigger. Codex's Q1 (delegation preserves downstream defeqs) and Q3 (ascription is fine) held.
