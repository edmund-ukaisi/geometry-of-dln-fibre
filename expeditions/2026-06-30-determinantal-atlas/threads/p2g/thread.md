# P2.g — naturality: tie the triple cocycle to the RESTRICTED 2-fold transition

Rung P2.g of the determinantal-atlas expedition. Closes the R1 naturality gap flagged in P2.f:
the triple cocycle `tripleTransition_cocycle` (P2.f) is of the CANONICAL triple transitions, not
yet tied to the further-localization of the 2-fold `overlapTransition`. This rung proves the tie.

## Codex consult (gpt-5.5, xhigh) — verdict SOUND

Prompt/answer: `codex-prompt.md` / `codex-answer.md`. Key guidance adopted:

1. **Subsingleton over `Base`, never `k`.** Build `Base`-algebra versions of every transition, prove
   the naturality by `IsLocalization.algHom_subsingleton` at the source's `powers` submonoid over
   `Base`, then `.restrictScalars k` at the end. (P2.f already flagged target-`M` subsingleton is
   UNSOUND.) No domain/reducedness/nonzero hypotheses needed — uniqueness comes from the source
   localization alone.
2. **Cleanest core (Q2):** define the base restricted-2-fold transition as the canonical `Base`
   localization iso `Away(tripleElt C D E) ≃ₐ[Base] Away(tripleElt D C E)`, and prove
   `chartOverlapTransitionTripleBase C D E ≪≫ tripleReorderBase D C E = chartTripleTransitionBase C D E`
   by Base-subsingleton. Conjugate through `tripleTriv` → target naturality is a pure groupoid rewrite.
3. **Reorder (Q3):** `Localization.awayCongr'` of `AlgEquiv.refl (R := Base) (A₁ := Away D.chartElt)`,
   carrying `tripleElt D C E ↦ tripleElt D E C` by `mul_comm`. Conjugate through `tripleTriv` for the
   target-side reorder.
4. **Q4 trap:** `C.trivK (tripleElt C D E) = C.trivK (overlapElt C D) * C.trivK (E-elt)` by ring-hom
   multiplicativity (scratch-confirmed). Define the target restriction map **by conjugation** through
   the trivializations (not via an inferred `targetChartLoc C D → targetTripleLoc C D E` scalar tower —
   Probe D showed that tower is NOT automatic), so it agrees with the base restriction by construction.
5. **Main obstruction to avoid:** do NOT silently treat the nested-further-localization type as the
   product triple type. Bridge by the canonical `algEquiv`, or define the restricted transition on the
   triple directly as the canonical common-localization iso and characterize-as-further-localization
   afterward.

## Guard-first probes (ScratchP2g, deleted before commit)

- Probe A/B (reorder iso via `awayCongr'` of refl): ELABORATES (needs `noncomputable` + `coe_refl`).
- Probe C (`C.trivK(tripleElt) = C.trivK(overlap) * C.trivK(E-elt)`): PROVED by `← map_mul`.
- Probe D (`IsScalarTower M (targetChartLoc C D) (targetTripleLoc C D E)`): FAILS to synth — the
  further-loc tower is not automatic ⟹ build restriction by conjugation, per Codex Q4.
- Base restriction `awayOverlap C D →ₐ[Base] Away(tripleElt C D E)` via `IsLocalization.liftAlgHom`
  (structure map `Algebra.ofId Base`, `powers(C·D)` units since `C·D·E` is a unit and `C·D ∣ C·D·E`):
  ELABORATES.

## Plan (line-count estimate ~180-220 LoC net in AtlasTransition + ~25 in LocalTriviality)

Base layer (all over `Base`, then `.restrictScalars k` where needed for the target conjugation):
1. `baseRestrTriple C D E : awayOverlap C.chartElt D.chartElt →ₐ[Base] Away (tripleElt C D E)` — the
   base further-localization (liftAlgHom). [~12 LoC]
2. `restrictTriple C D E : targetChartLoc C D →ₐ[k] targetTripleLoc C D E` — genuine further-loc of
   `overlapTransition`'s domain, defined by conjugation `(overlapTriv C D).symm ; baseRestr ; tripleTriv`.
   [~6 LoC]
3. `tripleReorder C D E : targetTripleLoc D C E ≃ₐ[k] targetTripleLoc D E C` — the codomain reorder
   (awayCongr' of refl over M). [~5 LoC]
4. `restrict_overlapTransition_eq_tripleTransition C D E` — naturality (iv): the restricted 2-fold
   (restrictTriple ; overlapTransition-induced ; reorder) = tripleTransition C D E. Proof: base
   subsingleton + trivK conjugation. [~40-60 LoC]
5. `overlapTransition_restricted_triple_cocycle` — the cocycle of the restricted 2-fold, by rewriting
   `tripleTransition_cocycle` along (iv). [~15 LoC]
6. Surface on `IsZariskiLocallyTrivialAffineProduct` + update docstrings (remove R1 caveat). [~25 LoC]

## Outcome (DELIVERED, commit ef658b4d, PR #21)

All deliverables landed sorry-free, axiom-clean, full aggregator GREEN (3834 jobs).

- baseRestrTriple / restrictTriple — the genuine restriction map (Away.mul' further-loc via liftAlgHom).
- restrict_overlapTransition_eq_tripleTransition — NATURALITY (iv). Route: base-subsingleton over Base
  (chartOverlapTripleBase_trans_reorder) + trivK conjugation. Reorder needed (C·E vs E·C), handled by
  awayCongr' of AlgEquiv.refl (base) + targetTripleReorder (conjugated). SOUND per Codex.
- baseRestr_square / restrictTriple_comp_overlapTransition — the genuine commuting square tying
  restrictedOverlapTripleTransition to the ACTUAL overlapTransition (fidelity: "restriction of the
  ACTUAL 2-fold" is literal, not just the canonical iso).
- overlapTransition_restricted_triple_cocycle — cocycle of the restricted 2-fold.
- Predicate surface + docstrings updated (R1 now = GLOBAL gluing only).

Net +313 LoC. Reviewer requested for fidelity.
