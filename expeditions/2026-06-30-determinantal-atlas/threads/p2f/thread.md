# Thread P2.f — target-side triple cocycle (CRUX, operator-requested via PR #21)

Branch `expedition/det-atlas-p2`. Builder/committer: `p2f-triple` (lean-formaliser).

## Target

Build the **target-side triple cocycle** `g_jk ∘ g_ij = g_ik` on common triple overlaps for the
constructive pivot-chart atlas, mirroring the base-side `Localization.awayTriple_cocycle`. Surface
it as a derived lemma on the `IsZariskiLocallyTrivialAffineProduct` predicate. Operator's full
coherence package: cover · per-chart product · 2-fold inverse · **triple cocycle**.

## What landed (sorry-free, axiom-clean [propext, Classical.choice, Quot.sound])

In `lean/DLNFibre/Core/RingTheory/Determinantal/AtlasTransition.lean`, namespace
`Algebra.AtlasChart`:

- `tripleElt C D E : Away C.chartElt` — pivot-`C` chart total ring localized at the PRODUCT
  `D.chartElt * E.chartElt` of the two non-pivot elements (`@[reducible]`). **Symmetric in D, E.**
- `isLocalization_tripleElt C D E {x} (hx : x = C·D·E) : IsLocalization (powers x) (Away (tripleElt
  C D E))` — every pivot presentation localizes `Base` at the SAME `powers (C·D·E)` (Away.mul' +
  of_associated). The common-submonoid brick the cocycle consumes.
- `targetTripleLoc C D E := Away (C.trivK (tripleElt C D E))` (`@[reducible]`) — chart-`C` target
  presentation, symmetric in D, E.
- `tripleTriv C D E : Away (tripleElt C D E) ≃ₐ[k] targetTripleLoc C D E` — `awayCongr'` of
  `C.trivK` (analogue of `overlapTriv`, one denominator up).
- `chartTripleTransitionK C D E : Away (tripleElt C D E) ≃ₐ[k] Away (tripleElt D E C)` — the
  k-restricted canonical localization iso (`IsLocalization.algEquiv` at `powers (C·D·E)`) between
  the pivot-`C` and pivot-`D` presentations of the SAME triple {C,D,E}.
- `tripleTransition C D E : targetTripleLoc C D E ≃ₐ[k] targetTripleLoc D E C` — conjugate
  `chartTripleTransitionK` through the two `tripleTriv` transports. **Built IDENTICALLY to the
  2-fold `overlapTransition`.**
- `chartTripleTransitionK_cocycle` — base-side cyclic composite = `refl`, by `Base`-subsingleton
  (`algHom_subsingleton`, localization initiality).
- **`tripleTransition_cocycle C D E : ((τ CDE).trans (τ DEC)).trans (τ ECD) = AlgEquiv.refl (R :=
  k)`** — the triple cocycle, by groupoid-law conjugation collapse (no localization elements
  entered).

In `lean/DLNFibre/Core/RingTheory/Determinantal/LocalTriviality.lean`, namespace
`Algebra.IsZariskiLocallyTrivialAffineProduct`:

- `tripleTransition_cocycle (A) (i j l)` — derived lemma delegating to the abstract theorem at the
  three charts. Predicate docstrings updated: atlas advertises cover · per-chart product · 2-fold
  inverse · triple cocycle.

## The DESIGN PIVOT (the crux decision)

The operator's described triple object was the **asymmetric nested form** (`Away (overlapTriv C D
(E-elt))` — localize the 2-fold overlap at E). With a CYCLIC orientation
`targetTripleLoc C D E → targetTripleLoc D E C` this cocycle is **provable** (and I proved it first),
BUT — Codex-confirmed (decorrelated, `codex/naturality-answer.md`) — the **naturality (iv)** tying it
to the restricted 2-fold `overlapTransition` **does NOT type**: restricting `overlapTransition C D`
to the triple lands in `targetTripleLoc D C E`, the cyclic cocycle wants `targetTripleLoc D E C`.

I **redesigned to a SYMMETRIC triple presentation** (localize the pivot chart at the PRODUCT of the
two non-pivot elements). This makes the standard **pivot-swap-on-a-fixed-triple** cocycle well-typed
(matching composition targets) and is the genuine standard-atlas reading of `g_ij` on a triple
overlap. The cocycle is proved on the canonical triple transitions.

## What is NOT done (precisely): naturality (iv), roadmap R1

The tie `tripleTransition C D E = (further-localization of overlapTransition C D)` is **NOT** proved.
Reason (in-docstring): the symmetric triple localizes the pivot chart at the PRODUCT `D·E`, the
2-fold `targetChartLoc C D` at `D` alone — so the tie needs the `Away.mul'` refinement iso
`Away (d*e) ≃ (Away d) away e` plus a transition-compatibility lemma. The shipped cocycle is
explicitly the cocycle of the **canonical** triple transitions (built identically to
`overlapTransition`), NOT the cocycle of the restricted 2-fold transition. Docstrings carry the
caveat; the surfaced predicate lemma is named/glossed accordingly.

Per Codex decision (a) and operator instruction ("if naturality is unprovable as stated, STOP and
report the precise obstruction; do NOT fabricate a weaker cocycle"): the canonical-triple cocycle is
the honest deliverable; naturality is a bounded, named follow-on rung.

## Proof engines

- Base cocycle: `Base`-subsingleton (`IsLocalization.algHom_subsingleton` at `powers (C·D·E)`) —
  the cyclic composite is a `Base`-algebra endo of the localization, hence `id`. The k-restriction
  preserves it (pointwise, via `restrictScalars_apply = rfl`).
- Target cocycle: groupoid-law conjugation collapse (`AlgEquiv.trans_assoc` / `self_trans_symm` /
  `refl_trans` / `symm_trans_self`), mirroring `overlapTransition_trans_symm`.
- The cross-cyclic submonoid-label mismatch (`chartTripleTransitionK X Y Z` uses `powers (X·Y·Z)`)
  is handled by supplying `isLocalization_tripleElt` instances at the matching per-edge submonoid.

## Gates

- Full aggregator `scripts/lb DLNFibre` GREEN — **3834 jobs**.
- `scripts/sorries` = 0 (0 sorry / 0 #exit / 0 native_decide / 0 axiom).
- `#print axioms` ⊆ `[propext, Classical.choice, Quot.sound]` on `tripleTransition_cocycle`,
  `chartTripleTransitionK_cocycle`, `isLocalization_tripleElt`, and the predicate-level lemma.
- Additive to existing files (`AtlasTransition.lean`, `LocalTriviality.lean`); no new file, no
  aggregator import change (transitively imported already).

## Codex consults (decorrelated)

- `codex/cocycle-{prompt,answer}.md` — initial design (cyclic): conjugation sound, subsingleton-on-M
  unsound, orientation `((τ).trans).trans = refl` correct.
- `codex/naturality-{prompt,answer}.md` — (iv) wall on cyclic design (target mismatch), decision (a)
  ship cocycle + report obstruction.
- `codex/symmetric-final-{prompt,answer}.md` — FINAL faithfulness check on the symmetric design.
  **Verdict: cocycle shape + symmetric object FAITHFUL, scoping HONEST; bottom line "fix
  stale/overbroad doc wording first, no statement redesign."** Applied: tightened the predicate
  docstrings (no unqualified "full cocycle package"; the surfaced lemma + bridge-view explicitly say
  "canonical triple transitions, naturality tie = R1, NOT yet the 2-fold-transition cocycle").
