# C2 overlap-restricted cocycle: cleanest genuinely-provable statement

Context: Lean 4 + Mathlib v4.29. A per-pivot local-product atlas `PivotLocalProductAtlas` over the
rank-r open of `Spec(sweepSigmaRing k d r)`. Each pivot `I : PivotDatum` has:
- `pivotElt I = chartDsigAt d r I.s I.t : sweepSigmaRing` (its localizing base-ring element).
- a trivialization `triv I : Localization.Away (chartDsigAt I.s I.t) ≃ₐ[k] SchurLoc ⊗[k] sweepFibreRing`
  (a FIXED common target ring, independent of I).
- `chartLocalizedAlgEquivAt I : Localization.Away (chartDsigAt I.s I.t) ≃ₐ[k] Localization.Away chartGfib`
  (also a fixed common target).

There is a base-side overlap transition cocycle (over R := sweepSigmaRing), banked from a thread-19
"localization initiality" engine:
- `awayOverlap f g := Localization.Away (algebraMap R (Localization.Away f) g)` — both `awayOverlap f g`
  and `awayOverlap g f` are `IsLocalization.Away (f*g) R` (same submonoid `powers (f*g)`).
- `chartOverlapTransition I J : awayOverlap (pivotElt I) (pivotElt J) ≃ₐ[R] awayOverlap (pivotElt J)(pivotElt I)`
  = `IsLocalization.algEquiv (powers (pivotElt I * pivotElt J)) _ _`.
- laws `_commutes` (fixes base image), `_symm`, `_trans_symm`, triple cocycle — all by
  `IsLocalization.algHom_subsingleton`.

CURRENT FIELD `transitionFactors` (the OVER-CLAIM we are correcting):
```
(triv I).trivialization.trans (triv J).trivialization.symm
  = (chartLocalizedAlgEquivAt I).trans (chartLocalizedAlgEquivAt J).symm
```
This compares the two trivializations DIRECTLY through the common target (a cancellation), NOT after
restricting both charts to the double overlap D(pivotElt I · pivotElt J). It is weaker than a genuine
overlap-local trivialization cocycle.

GOAL: state (and prove, axiom-clean) the atlas's transition compatibility ON the double overlap, using
`chartOverlapTransition`. I.e. the single-localized trivializations, RESTRICTED to the overlap, are
related by the overlap transition.

The subtlety: `triv I`'s target `SchurLoc ⊗ sweepFibreRing` is a FIXED ring, it does not itself
"restrict to the overlap". The genuine overlap object is the base-ring overlap `awayOverlap (pivotElt I)(pivotElt J)`.
The structure map from the single chart to the overlap is
`algebraMap (Localization.Away (pivotElt I)) (awayOverlap (pivotElt I)(pivotElt J))`.

QUESTIONS:
1. What is the cleanest genuinely-PROVABLE overlap-restricted compatibility statement here? Candidates:
   (a) The transition `chartOverlapTransition I J` intertwines the two single-chart→overlap structure
       maps composed with the base: `chartOverlapTransition I J (algebraMap R (awayOverlap I J) x) =
       algebraMap R (awayOverlap J I) x` (this is just `_commutes`, already banked — too weak?).
   (b) Define the restriction of each trivialization to the overlap by composing the overlap→single-chart
       localization with `chartLocalizedAlgEquivAt`, and show the two restrictions agree after applying
       `chartOverlapTransition` (a square commuting on the overlap ring). Is this provable by
       `IsLocalization.algHom_subsingleton` over R (both sides R-algebra maps out of a localization of R)?
   (c) Something else.
2. Is the cancellation-through-common-target `transitionFactors` actually IMPLIED BY / EQUIVALENT TO the
   overlap-restricted one, or genuinely weaker? Be precise about what each captures.
3. If a full overlap-cocycle FIELD is too heavy for one tide, what is the minimal honest LEMMA to add
   alongside `transitionFactors` + the precise corrected docstring wording for `transitionFactors`?

Answer with the exact Lean statement(s) you'd write and the one-line proof strategy for each. Be a
red-team: if (b) is not actually provable by initiality (because `chartLocalizedAlgEquivAt` is a
k-algebra map, not an R=sweepSigmaRing-algebra map, so the subsingleton-over-R trick fails on the
chart-equiv side), SAY SO and give the honest fallback.
