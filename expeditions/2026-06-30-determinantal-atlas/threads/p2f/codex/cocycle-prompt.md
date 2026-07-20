<task>
I am formalising in Lean 4 + Mathlib (v4.29) the COHERENCE PACKAGE of a constructive
pivot-chart atlas of a Zariski-locally-trivial affine product (algebraic geometry,
localization of commutative rings). I need an independent review of a STATEMENT + PROOF
STRATEGY for the **target-side TRIPLE cocycle** `g_jk ∘ g_ij = g_ik` on common triple
overlaps, before I spend compute proving it.

## What is already DONE (base side, proven sorry-free)

Over a commutative ring `R`, for `f g h : R`, the principal opens `D(f), D(g), D(h)` of
`Spec R`. Iterated `Away` localizations:
- `awayOverlap f g := Localization.Away (algebraMap R (Localization.Away f) g)` — the double
  overlap `O(D(f) ∩ D(g))`; by `IsLocalization.Away.mul'` this is the localization of `R` at
  `f*g`.
- `awayTriple f g h := Localization.Away (algebraMap R (awayOverlap f g) h)` — the triple
  overlap; localization of `R` at `(f*g)*h`.
- `isLocalization_awayTriple {a b c x} (hx : x = a*b*c) : IsLocalization (powers x) (awayTriple a b c)`
  — ALL cyclic presentations localize at the SAME submonoid `powers (f*g*h)` (via
  `IsLocalization.Away.of_associated` realigning the product).
- `awayTriple_cocycle f g h`: the cyclic composite of the three canonical localization
  transitions `IsLocalization.algEquiv (powers (f*g*h)) (awayTriple f g h) (awayTriple g h f)`
  etc. composes around the cycle to `AlgEquiv.refl`. PROVED by localization initiality:
  the cyclic composite is an `R`-algebra ENDO of the localization `awayTriple f g h`, and
  `IsLocalization.algHom_subsingleton (powers (f*g*h))` says the only such endo is `id`.

The 2-fold base transition `awayOverlapTransition f g : awayOverlap f g ≃ₐ[R] awayOverlap g f`
and its round-trip `awayOverlapTransition_trans_symm` are also done by the same subsingleton move.

## The TARGET side (the atlas API, over a base field `k`)

A chart `C : AtlasChart k Base M` bundles `chartElt : Base` (cutting `D(chartElt)`) and a bare
`k`-algebra trivialization `trivK : Localization.Away chartElt ≃ₐ[k] M` of the localized chart
total ring as a fixed model `M`. The 2-fold target objects (all DONE):
- `overlapElt C D : Away C.chartElt := algebraMap Base (Away C.chartElt) D.chartElt`
  (so `awayOverlap C.chartElt D.chartElt = Localization.Away (overlapElt C D)`).
- `targetChartLoc C D := Localization.Away (C.trivK (overlapElt C D))` — the chart-`C` TARGET
  presentation of the 2-fold overlap (the model `M` localized at the trivK-image).
- `overlapTriv C D : awayOverlap C.chartElt D.chartElt ≃ₐ[k] targetChartLoc C D`
  `:= Localization.awayCongr' C.trivK (overlapElt C D) (C.trivK (overlapElt C D)) rfl`
  where `awayCongr' (e : A ≃ₐ[R] B) (a : A) (b : B) (hb : e a = b) : Away a ≃ₐ[R] Away b` is
  the localization transport of an AlgEquiv carrying `a ↦ b`.
- `chartOverlapTransitionK C D : awayOverlap cElt dElt ≃ₐ[k] awayOverlap dElt cElt`
  = `(awayOverlapTransition …).restrictScalars k`.
- `overlapTransition C D : targetChartLoc C D ≃ₐ[k] targetChartLoc D C`
  := `(overlapTriv C D).symm.trans ((chartOverlapTransitionK C D).trans (overlapTriv D C))`
  — the base transition CONJUGATED through the two trivK-transports.
- `overlapTransition_trans_symm C D : (overlapTransition C D).trans (overlapTransition D C) = refl`
  DONE, by groupoid-law rewriting (no element entry).

## My PROPOSED triple design (mirroring the 2-fold, reusing awayCongr')

(i) `tripleElt C D E : awayOverlap C.chartElt D.chartElt := algebraMap Base (awayOverlap cElt dElt) eElt`
    so the base-side triple is `awayTriple cElt dElt eElt = Localization.Away (tripleElt C D E)`.
(i') `targetTripleLoc C D E := Localization.Away (overlapTriv C D (tripleElt C D E))` — the
    chart-`C` TARGET presentation of the triple overlap (model side, localized at the
    overlapTriv-image of the triple element).
(ii) `tripleTriv C D E : awayTriple cElt dElt eElt ≃ₐ[k] targetTripleLoc C D E`
    := `awayCongr' (overlapTriv C D) (tripleElt C D E) (overlapTriv C D (tripleElt C D E)) rfl`
    — the EXACT analogue of `overlapTriv` one level up (transport the base triple through
    `overlapTriv C D` instead of through `trivK`).
(iv) The triple transition + the cocycle: conjugate the base-side `awayTriple_cocycle` through
    the three `tripleTriv` transports. The cyclic composite of the conjugated transitions on
    `targetTripleLoc` = `refl`, BECAUSE conjugation by isos preserves "cyclic composite = id"
    (refl conjugates to refl), OR equivalently because `targetTripleLoc C D E` is itself a
    `Localization.Away` of `M`, so `IsLocalization.algHom_subsingleton` gives its only relevant
    endo is `id`.

But there is a SUBTLETY I want reviewed: on the base side all three presentations
`awayTriple fgh / ghf / hfg` are localizations of `R` at ONE submonoid `powers (f*g*h)`, so
`IsLocalization.algEquiv` directly gives canonical transitions between cyclic reorderings. On
the TARGET side, `targetTripleLoc C D E`, `targetTripleLoc D E C`, `targetTripleLoc E C D` are
localizations of `M` — but at DIFFERENT elements (`overlapTriv C D (tripleElt C D E)` vs
`overlapTriv D E (tripleElt D E C)` etc.), and even via DIFFERENT 2-fold transports
(`overlapTriv C D` vs `overlapTriv D E`). They need NOT be `IsLocalization` of `M` at a common
submonoid in any obvious way. So the clean "single submonoid ⟹ algEquiv ⟹ subsingleton" base-side
move does NOT transparently transfer; the honest route looks like CONJUGATION of the base cocycle.

For the conjugation route, the load-bearing naturality lemma is:
(iii)+(iv) `restrict_overlapTransition_to_triple_eq_tripleTransition`: the atlas's actual 2-fold
    transition `overlapTransition C D`, RESTRICTED/further-localized to the triple presentation
    (localize `targetChartLoc C D` further at the E-element image to land in `targetTripleLoc C D E`,
    then the induced map to `targetTripleLoc D C E`), EQUALS the directly-built canonical triple
    transition. With that, the atlas transitions ON THE TRIPLE are the conjugates of the base
    triple transitions, and the base cocycle transfers.

## My questions

1. Is the cocycle STATEMENT faithful? The operator wants the FULL standard coherence
   `g_jk ∘ g_ij = g_ik` on the common triple overlap — equivalently cyclic composite = id with the
   correct orientation matching the base `awayTriple_cocycle` (which is
   `(fgh→ghf) ≫ (ghf→hfg) ≫ (hfg→fgh) = refl`). Does my proposed triple object + transports
   capture exactly that, or does conjugation silently weaken it (e.g. to a statement that only holds
   "through a common target" rather than genuinely on the triple overlap)?

2. Which proof ENGINE is sound and cleanest: (a) pure CONJUGATION of `awayTriple_cocycle` through the
   three `tripleTriv`s (needs the cyclic-composite-preserved-under-conjugation algebra + the
   naturality lemma (iii)), or (b) a direct SUBSINGLETON argument on `targetTripleLoc C D E` as a
   `Localization.Away M` (does `algHom_subsingleton` even APPLY here, given the three cyclic targets
   are localizations at DIFFERENT elements — i.e. is the cyclic composite even an ENDO of a single
   localization, the precondition subsingleton needs)?

3. Does the naturality lemma (iv) `restrict_overlapTransition_to_triple_eq_tripleTransition` HOLD as
   stated, and is it actually NEEDED for the cocycle, or is it a separate (stronger) claim about the
   2-fold transition restricting correctly? If the cocycle can be stated purely in terms of the
   directly-built triple transitions (bypassing the 2-fold `overlapTransition`), is that a FAITHFUL
   rendering of "the atlas's transitions satisfy the cocycle", or a weaker self-consistent statement
   that doesn't connect to the actual atlas transition maps?

4. Any trap in the orientation / parenthesization that would make the Lean `AlgEquiv.trans`
   composite fail to be defeq to what the base cocycle conjugates to?
</task>

<output_contract>
  Four numbered sections answering Q1-Q4 in order. For each: a clear verdict
  (faithful / not / sound / unsound) then the 2-4 sentence justification. Then a final
  section "RECOMMENDATION" — the single cleanest sound route (conjugation vs subsingleton),
  whether naturality (iii)/(iv) is load-bearing or droppable, and the exact cocycle statement
  shape you would commit to. Be concrete about Lean/Mathlib mechanics where it matters.
</output_contract>

<grounding_rules>
  Distinguish what FOLLOWS from the localization universal property (provable) from what is
  an INFERENCE about Lean defeq/instance behavior you cannot verify without the build. Flag any
  step where you are guessing about Mathlib v4.29 API. If a route is unsound, say so plainly
  rather than salvaging it.
</grounding_rules>
