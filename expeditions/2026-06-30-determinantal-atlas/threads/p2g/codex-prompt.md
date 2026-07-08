# P2.g naturality: tie triple cocycle to the RESTRICTED 2-fold overlap transition

Lean 4 + Mathlib v4.29. Determinantal-atlas expedition. I need a decorrelated design review on
the STATEMENT and the SOUND PROOF ROUTE for a naturality theorem before I spend build cycles.

## Setup (already built, sorry-free)

Over a base ring `k`, `Base`, model `M`, all `Type u` commutative `k`-algebras:

- `AtlasChart k Base M` : `{ chartElt : Base, trivK : Localization.Away chartElt ≃ₐ[k] M }`.
- `overlapElt C D := algebraMap Base (Localization.Away C.chartElt) D.chartElt`.
- `targetChartLoc C D := Localization.Away (C.trivK (overlapElt C D))`  (localize M at trivK-image of D).
- `overlapTriv C D : Localization.awayOverlap C.chartElt D.chartElt ≃ₐ[k] targetChartLoc C D`
  (= `Localization.awayCongr' C.trivK (overlapElt C D) ...`; `awayOverlap f g = Away (algebraMap Base (Away f) g)`).
- `chartOverlapTransitionK C D : awayOverlap C.chartElt D.chartElt ≃ₐ[k] awayOverlap D.chartElt C.chartElt`
  (= k-restriction of `Localization.awayOverlapTransition` = `IsLocalization.algEquiv` at `powers (C·D)`).
- `overlapTransition C D : targetChartLoc C D ≃ₐ[k] targetChartLoc D C`
  := `(overlapTriv C D).symm ≪≫ (chartOverlapTransitionK C D ≪≫ overlapTriv D C)`.

Triple layer (one denominator up, SYMMETRIC in the two non-pivot charts — localize at the PRODUCT):
- `tripleElt C D E := algebraMap Base (Localization.Away C.chartElt) (D.chartElt * E.chartElt)`.
- `targetTripleLoc C D E := Localization.Away (C.trivK (tripleElt C D E))`.
- `tripleTriv C D E : Localization.Away (tripleElt C D E) ≃ₐ[k] targetTripleLoc C D E` (awayCongr' of C.trivK).
- `isLocalization_tripleElt C D E (hx : x = C·D·E) : IsLocalization (powers x) (Away (tripleElt C D E))`
  (via `IsLocalization.Away.mul'` + `IsLocalization.Away.of_associated`).
- `chartTripleTransitionK C D E : Away (tripleElt C D E) ≃ₐ[k] Away (tripleElt D E C)`
  := k-restriction of `IsLocalization.algEquiv (powers (C·D·E)) (Away (tripleElt C D E)) (Away (tripleElt D E C))`.
- `tripleTransition C D E : targetTripleLoc C D E ≃ₐ[k] targetTripleLoc D E C`
  := `(tripleTriv C D E).symm ≪≫ (chartTripleTransitionK C D E ≪≫ tripleTriv D E C)`.
- `tripleTransition_cocycle` (DONE): the cyclic composite of tripleTransition = refl (proved via
  base-side `chartTripleTransitionK_cocycle` by `IsLocalization.algHom_subsingleton` over Base, then trivK conjugation).

## What P2.g must deliver

The triple cocycle above is of the CANONICAL triple transitions `tripleTransition`, NOT yet proved to
equal the RESTRICTION (further-localization at E) of the 2-fold `overlapTransition C D` to the triple
overlap. The operator (PR #21) wants: (a) naturality tying the restricted 2-fold to the triple transition,
(b) the cocycle `g_jk ∘ g_ij = g_ik` for the ACTUAL 2-fold `overlapTransition` restricted to the triple.

## The reorder wrinkle

`overlapTransition C D` lands in `targetChartLoc D C = Away(D.trivK(C))`. Its further-localization at E lands
in `Away(D.trivK(C·E))` = `targetTripleLoc D C E`. But `tripleTransition C D E` lands in
`targetTripleLoc D E C = Away(D.trivK(E·C))`. So `C·E` vs `E·C` — SAME localization up to `mul_comm`
(Associated), not defeq. Reorder iso needed on the codomain.

## Proposed SOUND route (want your red-team)

1. Restriction map (via `Away.mul'`): `targetChartLoc C D →ₐ[k] targetTripleLoc C D E` — the further
   localization of `Away(C.trivK D)` at the trivK-image of E, since `C.trivK(D·E) = C.trivK D * C.trivK E`.
2. Base-side naturality FIRST: the further-localization of `chartOverlapTransitionK C D` equals the base
   triple transition (both `Base`-algebra maps between `Away(tripleElt C D E)` and `Away(tripleElt D C E)`,
   two localizations of Base at the SAME `powers(C·D·E)` submonoid — hence EQUAL by
   `IsLocalization.algHom_subsingleton` OVER Base). This is the sound core.
   [P2.f flagged that using target-`M` subsingleton (`Localization.Away (C.trivK ...)` as an M-algebra endo)
    is UNSOUND — the endo need not be over M's structure map. So the subsingleton MUST be over `Base`.]
3. Transport through the trivK transports (`overlapTriv`/`tripleTriv`) to get target-side naturality by
   conjugation — exactly mirroring how `tripleTransition_cocycle` transported the sound base cocycle.
4. Handle the `C·E` vs `E·C` reorder by the canonical localization iso between the two triple presentations
   (`IsLocalization.algEquiv` / `awayCongr'` of identity, both Away at Associated images).

## Questions

Q1. Is the base-side subsingleton argument SOUND and does it need any hypothesis I've missed? Both
    `Away(tripleElt C D E)` and `Away(tripleElt D C E)` are localizations of `Base` at `powers(C·D·E)`
    (up to Associated). Any two Base-algebra maps between them agree — correct?
Q2. Is there a CLEANER statement of "the restricted 2-fold = the triple transition" that sidesteps
    building an explicit restriction ring-hom? E.g. state it purely at the base level (both base maps
    equal by subsingleton) and note the target-side follows by the same trivK-conjugation the cocycle used —
    then the RESTRICTED-2-fold cocycle is literally `tripleTransition_cocycle` rewritten along naturality.
Q3. The reorder: is `awayCongr' (AlgEquiv.refl) (tripleElt D C E) (tripleElt D E C) (by rw[mul_comm])`
    the cleanest reorder iso `Away(tripleElt D C E) ≃ Away(tripleElt D E C)`, or is `IsLocalization.algEquiv`
    at the common `powers(D·C·E)=powers(D·E·C)` submonoid cleaner? (Note tripleElt is over `Away C.chartElt`
    on domain side but over `Away D.chartElt` on codomain — the reorder is codomain-only, pivot D.)
Q4. Any trap: does the restriction map (further-localization) commute with trivK the way I claim, given
    trivK is a `k`-algebra iso `Away C.chartElt ≃ₐ[k] M` and I need `C.trivK(D·E) = C.trivK D * C.trivK E`
    (ring-hom multiplicativity) to identify `targetTripleLoc C D E` as `Away(C.trivK D * C.trivK E)`?

Give SOUND/UNSOUND on the route, the cleanest statement shape, and any obstruction you foresee.
