# P2.h — strengthen the product-atlas API + fix stale docs (PR #21 re-review)

Rung: operator PR #21 re-review, three fidelity/doc items. Branch `expedition/det-atlas-p2`.

## Item 3 (substantive) — RESOLVED via STRENGTHEN-A

The gap: `Algebra.AtlasFibreChart` carried TWO independent trivializations — the bare-`k`
`AtlasChart.trivK` (which all transitions/cocycles are built from) and the over-base
`fibreModel.triv` (the product) — with `M` a free unconstrained parameter and nothing tying them. So
the proven pairwise-inverse + triple cocycle were coherence of a generic bare-`k` `M`-presentation,
NOT of the over-`BaseLoc` PRODUCT trivialization, which the predicate name
`IsZariskiLocallyTrivialAffineProduct` reads as.

**Resolution (STRENGTHEN-A — the product triv is the single source of truth).**
`Algebra.AtlasFibreChart k Base BaseLoc Fibre` (in `AtlasTransition.lean`) no longer `extends
AtlasChart` and no longer takes an `M` parameter. It stores only:
- `chartElt : Base`
- `fibreModel : StandardFibreChart k (Localization.Away chartElt) BaseLoc Fibre`

and DERIVES the bare-`k` chart via a `def`:

    noncomputable def toAtlasChart (C) : AtlasChart k Base (BaseLoc ⊗[k] Fibre) where
      chartElt := C.chartElt
      trivK := letI := C.fibreModel.structMap.toRingHom.toAlgebra
               C.fibreModel.triv.restrictScalars k

So `trivK` IS the over-base product trivialization, scalars forgotten — the product tie is
DEFINITIONAL (`trivK_eq_product : ... = fibreModel.triv.restrictScalars k := rfl`), not a stored
field that could drift, and there is no redundant stored trivialization.

`restrictScalars k` typechecks: `structMap : BaseLoc →ₐ[k] Away chartElt` gives
`IsScalarTower k BaseLoc (Away chartElt)` via `IsScalarTower.of_algHom` (reintroduced by the `letI`),
plus the standard tower on `BaseLoc ⊗_k Fibre`.

**Product-coherence corollary.** `Algebra.AtlasFibreChart.overlapTransition_isProduct C D` — the
pairwise round-trip of the target-side overlap transitions is `refl`, and (by the definitional tie)
this is coherence of the over-`BaseLoc` PRODUCT presentations, since the transitions conjugate
through `trivK = fibreModel.triv.restrictScalars k`. Restated `AtlasChart.overlapTransition_trans_symm`
on the derived charts, re-surfaced to record the product interpretation the tie licenses.

**Downstream.** The predicate `Algebra.IsZariskiLocallyTrivialAffineProduct` (in
`LocalTriviality.lean`) drops its `M` parameter (now `k Base BaseLoc Fibre U`); all derived cocycle
theorems adjust (they read `(chart i).toAtlasChart.…` / `(chart i).chartElt` / `(chart
i).fibreModel.structMap`, all still valid — `toAtlasChart` is a def, `chartElt`/`fibreModel` direct
fields). The DLN instance `pivotAtlasFibreChart` (in `FibreZariskiLocalTriviality.lean`) stores
`chartElt := pivotElt I` + `fibreModel := standardFibreChartOfPivot I`; the derived `trivK` is
`chartDsigAt_schurLocTensorEquiv.restrictScalars k`, which is `chartDsigAt_tensorEquiv` (the old
`pivotAtlasChart.trivK`) with scalars forgotten — `chartDsigAt_schurLocTensorEquiv =
AlgEquiv.ofRingEquiv chartDsigAt_tensorEquiv.toRingEquiv`, so the tie is genuinely `rfl` (verified in
a guard-first STRENGTHEN-B build before converting to A).

## Codex verdict (decorrelated, xhigh)

Prompt + answer: `codex-item3-prompt.md` / `codex-item3-answer.md`.

**VERDICT: STRENGTHEN-A** — "implemented by dropping `extends` and deriving `toAtlasChart`, because
it makes the product trivialization the only stored trivialization." Confirmed:
- (Q1) Specializing only `AtlasFibreChart` + tying `trivK` to `fibreModel.triv.restrictScalars k` is
  the right strengthening; the product triv should be the source of truth.
- (Q2) True (A) is NOT achievable with `extends` (inherited `trivK` stays stored parent data; a
  default is only a constructor default, not an invariant). Achievable by ABANDONING `extends` and
  making `toAtlasChart` a def — exactly what was done.
- (Q3) The product-coherence corollary follows in the precise bare-`k` sense (`restrictScalars_apply`
  is `rfl`): the transitions ARE the product-coordinate changes as `k`-algebra maps. What is NOT
  automatically gotten: `BaseLoc`-linearity of the transitions, identity-on-base — those need
  separate statements if wanted. (`overlapTransition_isProduct` claims exactly the licensed reading.)
- (Q4) Little lost: `AtlasChart` + all general transition theorems stay reusable over arbitrary `M`;
  only `AtlasFibreChart` specializes.
- (Q5) No soundness trap; the `IsScalarTower k BaseLoc Total` under the `structMap`-`letI` is the one
  synthesis point, supplied by `IsScalarTower.of_algHom`.

## Items 1–2 (stale/contradictory live docs) — FIXED

- `AtlasTransition.lean` — paragraph above `tripleElt` (naturality tie "NOT built here / roadmap R1"
  → now built, P2.g); `AtlasFibreChart` chart-pairing prose + "What is built" bullets (extends →
  derived-def + product tie; added `overlapTransition_isProduct` bullet).
- `FibreTargetOverlap.lean` — "Scope (honest)" + "Roadmap residual" (round-trip cocycle "infra-blocked
  / deferred / precisely-scoped residual" → LANDED P2.c abstractly, inherited on the DLN instance;
  triple P2.f + naturality P2.g likewise; only GLOBAL gluing R1 remains); two witness docstrings.
- `DLNFibre.lean` (aggregator, comments only, no reorder) — `AtlasTransition` import comment
  ("Transition OBJECTS only" → LANDED P2.c/f/g + product coherence); `FibreTargetOverlap` import
  comment ("round-trip infra-blocked by missing AlgEquiv laws" → PROVED); predicate signature `k
  Base M BaseLoc Fibre U` → `k Base BaseLoc Fibre U`; DLN-instance chart description.
- `FibreZariskiLocalTriviality.lean` — module header instance type + chart description; "What this is
  NOT" ("triple-overlap coherence roadmapped" → landed; only GLOBAL gluing R1); `pivotAtlasFibreChart`
  docstring.
- `LocalTriviality.lean` — module + structure docstrings (`M` removed; the "two genuine data" bullet
  now the derived-trivK product tie; the "atlas glues compatibly" overstatement qualified to LOCAL
  coherence only, GLOBAL gluing NOT derived).

Uniform message: **proved** = cover · per-chart over-base product · pairwise inverse · canonical
triple cocycle · restricted-2-fold naturality/cocycle · product-trivialization coherence;
**roadmapped (R1)** = GLOBAL gluing / global `π` / `Flat π` only.
