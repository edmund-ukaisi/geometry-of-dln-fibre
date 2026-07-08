# Statement card — P2.g naturality (restricted 2-fold transition = triple transition)

**Status:** sorry-free (awaiting reviewer fidelity check).
**Commit:** `ef658b4d` on `expedition/det-atlas-p2` (PR #21).
**Files:** `lean/DLNFibre/Core/RingTheory/Determinantal/AtlasTransition.lean` (namespace
`Algebra.AtlasChart`), `LocalTriviality.lean` (namespace
`Algebra.IsZariskiLocallyTrivialAffineProduct`).
**Axioms:** all `[propext, Classical.choice, Quot.sound]`.

## Claim (informal)

For a constructive pivot-chart atlas of a Zariski-locally-trivial affine product, the canonical
triple-overlap transition `tripleTransition C D E` equals (up to the non-pivot reorder) the
further-localization of the honest 2-fold transition `overlapTransition C D` to the triple overlap
`D(C.chartElt) ∩ D(D.chartElt) ∩ D(E.chartElt)`. Consequently the atlas's OWN 2-fold transitions,
restricted to the triple, satisfy the cocycle `g_jk ∘ g_ij = g_ik`.

## Lean signatures (AtlasChart-level)

- Naturality (iv):
  ```
  theorem restrict_overlapTransition_eq_tripleTransition (C D E : AtlasChart k Base M) :
      (restrictedOverlapTripleTransition C D E).trans (targetTripleReorder C D E)
        = tripleTransition C D E
  ```
  Gloss: the restricted 2-fold transition (`restrictedOverlapTripleTransition`, defined by
  conjugating the base canonical iso `chartOverlapTripleBase` through `tripleTriv`), followed by the
  non-pivot reorder `D·C·E → D·E·C`, equals the canonical triple transition.

- Commuting square (literal tie to the ACTUAL `overlapTransition`):
  ```
  theorem restrictTriple_comp_overlapTransition (C D E : AtlasChart k Base M) :
      (restrictTriple D C E).comp (overlapTransition C D).toAlgHom
        = (restrictedOverlapTripleTransition C D E).toAlgHom.comp (restrictTriple C D E)
  ```
  Gloss: `restrictTriple` (the further-localization map `targetChartLoc → targetTripleLoc`)
  intertwines the honest 2-fold `overlapTransition C D` with `restrictedOverlapTripleTransition` —
  so the latter genuinely IS the restriction of the former.

- Restricted 2-fold cocycle:
  ```
  theorem overlapTransition_restricted_triple_cocycle (C D E : AtlasChart k Base M) :
      ((((restrictedOverlapTripleTransition C D E).trans (targetTripleReorder C D E)).trans
            ((restrictedOverlapTripleTransition D E C).trans (targetTripleReorder D E C))).trans
          ((restrictedOverlapTripleTransition E C D).trans (targetTripleReorder E C D)))
        = AlgEquiv.refl (R := k)
  ```

Predicate-level (`IsZariskiLocallyTrivialAffineProduct`): `restrictedOverlapTransition_eq`,
`restrictTriple_comp_overlapTransition`, `overlapTransition_restricted_triple_cocycle` (each the
above at `(chart i/j/l).toAtlasChart`).

## Hypotheses

`k Base M` commutative `k`-algebras, `Type u`. NO domain / reducedness / nonzero / Noetherian
hypotheses — uniqueness comes from the source localization alone.

## Proof route

Base-side subsingleton over `Base` (`IsLocalization.algHom_subsingleton` at `powers (C·D·E)` /
`powers (C·D)`), then trivialization conjugation through `tripleTriv` (pure `AlgEquiv`-groupoid
rewrite). The `Away.mul'` refinement is `baseRestrTriple` (base further-localization via
`IsLocalization.liftAlgHom`). Codex (gpt-5.5, xhigh) verdict SOUND; explicitly flagged that a
target-`M` subsingleton would be UNSOUND, so the argument is over `Base`.

## Fidelity notes for reviewer

- Does `restrict_overlapTransition_eq_tripleTransition` + `restrictTriple_comp_overlapTransition`
  faithfully say "the restricted 2-fold transition is the further-localization of the ACTUAL
  `overlapTransition`"? (The naturality alone uses `restrictedOverlapTripleTransition`, defined via
  the canonical iso; the commuting square is what makes the tie to `overlapTransition` literal.)
- Is the non-pivot reorder honest (`C·E` vs `E·C` = `mul_comm`, via `awayCongr'` of `refl`)?
- Non-vacuity: the equated objects are genuine non-identity pivot-swap isos.
