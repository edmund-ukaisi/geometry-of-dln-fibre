# Thread 25 — atlas API fix (C1 bridge + C2 overlap-local restriction) — statement card

**Status: sorry-free, reviewer PASS (one wording nit actioned).** Modules
`lean/DLNFibre/Core/FibreBundleLocallyTrivialFull.lean` (the `PivotLocalProductAtlas`) +
`lean/DLNFibre/Core/FibreBundleTransition.lean` (abstract helpers). Whole library green (3805 jobs);
0 sorry/axiom/native_decide (`scripts/sorries`); all new/changed headlines axiom-clean
`[propext, Classical.choice, Quot.sound]` (gated via `#print axioms`, forced elaboration). NO new
import lines (everything from existing imports). One decorrelated xhigh Codex design consult (C2
formulation) + the reviewer's own decorrelated Codex honesty red-team.

The OPERATOR (PR #11 review) flagged two genuine API/fidelity gaps in the bundle atlas. Both closed
honestly. The point of this tide: the atlas's coherence was over-claimed (`transitionFactors` was a
common-target cancellation masquerading as an overlap cocycle); this corrects the claim AND adds the
genuine overlap-local content + the missing cover↔datum bridge.

---

## C1 — the bridge from a covering raw chart to its pivot datum (CLOSED)

> **Gap.** `schemeCover` is indexed by raw selector pairs `(s, t)`; `triv` / `overlapTransition` are
> indexed by `PivotDatum` (which carries the permutations σ, τ + the proofs they carry the first `r`
> rows/columns to `s, t`). There was NO exported bridge — a downstream consumer could not take a
> covering chart and obtain its `triv`.

> **Closed.** An injective selector extends to a permutation carrying the first `r` indices to it;
> a covering chart `(s, t)` (injective selectors — a repeated row/column kills the minor det, putting
> the chart in `V({chartDsigAt})`, not `rankROpen`) yields a `PivotDatum` at the same localizing
> element.
>
> - **Lean (`FibreBundleLocallyTrivialFull.lean`):**
>   - `extendToPerm {r n} (hp : r ≤ n) (s : Fin r → Fin n) (hs : Injective s) : Equiv.Perm (Fin n)`
>     — via `Equiv.extendSubtype` of `(ofInjective (Fin.castLE hp)).symm ≪≫ ofInjective s`.
>   - `extendToPerm_apply : extendToPerm hp s hs (Fin.castLE hp i) = s i`.
>   - `pivotDatumOfSelectors d r hp hq s t hs ht : PivotDatum d r hp hq` — `.s = s`, `.t = t`,
>     `σ = extendToPerm hp s hs`, `τ = extendToPerm hq t ht`, fields by `extendToPerm_apply`.
>   - `pivotElt_pivotDatumOfSelectors` (`@[simp]`): `pivotElt (pivotDatumOfSelectors …) =
>     chartDsigAt d r s t` — a genuine `rfl`; the cover chart's localizing element.
>   - **atlas FIELD** `pivotOfCover : ∀ s t, Injective s → Injective t →
>     {I : PivotDatum d r hp hq // pivotElt … I = chartDsigAt d r s t}`, wired in
>     `pivotLocalProductAtlas` to `⟨pivotDatumOfSelectors …, pivotElt_pivotDatumOfSelectors …⟩`.
> - **Reviewer:** PASS, genuine + non-vacuous (`.s = s`/`.t = t` by `rfl`; `pivotElt_…` genuine).
> - **Status.** sorry-free, axiom-clean. Witness `example` fires at an abstract field.

## C2 — the overlap-LOCAL transition restriction + the corrected over-claim (CLOSED, honest scope)

> **Gap.** `transitionFactors` compared the two single-localized trivializations DIRECTLY through the
> common target `SchurLoc ⊗ sweepFibreRing` (a cancellation), NOT after restricting both charts to
> the double overlap `D(g_I · g_J)` — weaker than a genuine overlap-local trivialization cocycle.

> **Closed (the genuinely-provable part) + claim corrected.** The base-side overlap restriction is
> stated and proved; the FULL trivialization-overlap cocycle square is honestly disclaimed (Codex
> red-team, accepted: `chartLocalizedAlgEquivAt` is only a `k`-algebra (gauge) map, not an
> `R = sweepSigmaRing`-algebra map, so the localization-subsingleton argument fails on the chart-equiv
> side — a genuine target-side localization comparison `targetOverlapTransition` is needed, which is
> new + heavy, NOT a finishing touch).
>
> - **Lean (abstract, `FibreBundleTransition.lean`):**
>   - `isUnit_ofId_powers_awayOverlap (f g : R) (y : powers f) :
>     IsUnit ((Algebra.ofId R (awayOverlap g f)) y)` — `f` a unit in the swapped overlap.
>   - `chartToSwappedOverlap (f g : R) : Localization.Away f →ₐ[R] awayOverlap g f` — the canonical
>     `R`-algebra map (via `IsLocalization.liftAlgHom`); a genuine non-trivial map.
>   - `awayOverlapTransition_restrict_left : (awayOverlapTransition f g).toAlgHom.comp
>     (IsScalarTower.toAlgHom R (Away f) (awayOverlap f g)) = chartToSwappedOverlap f g` — the
>     transition, restricted along the chart-`f`→overlap localization map, is the canonical
>     chart-`f`→swapped-overlap map. Proof `IsLocalization.algHom_subsingleton (powers f)`
>     (`rfl` does NOT close it — reviewer-verified non-vacuous).
> - **Lean (pivots + atlas, `FibreBundleLocallyTrivialFull.lean`):**
>   - `chartOverlapTransition_restrict` — the pivot instance at `f = pivotElt I`, `g = pivotElt J`.
>   - **atlas FIELD** `transitionCommutes` — base normalization on the overlap
>     (`chartOverlapTransition_commutes`).
>   - **atlas FIELD** `overlapRestrict` — the genuine overlap-local restriction
>     (`chartOverlapTransition_restrict`).
>   - **`transitionFactors` KEPT, docstring CORRECTED** — now states it is common-target cancellation
>     (a `k`-algebra equality between the single chart rings), explicitly NOT an overlap cocycle, and
>     points to `overlapRestrict` / `transitionCommutes` for the overlap data.
> - **Reviewer:** PASS, `chartToSwappedOverlap` non-trivial, `restrict_left` non-vacuous (rfl-fails),
>   corrected docstring honest, deferral a real obstruction (Codex CORRECT-OBSTRUCTION).
> - **Status.** sorry-free, axiom-clean.

---

## Honest scope (what the atlas coherence now genuinely is)

- **EARNED (new):** (C1) every covering chart connects to its `PivotDatum`-indexed trivialization;
  (C2) the base-side overlap transition genuinely restricts to each single localized chart *on the
  double overlap* (`overlapRestrict`) — the genuine overlap-local cocycle content — plus the base
  normalization (`transitionCommutes`).
- **CORRECTED (was over-claimed):** `transitionFactors` is now honestly labelled a common-target
  cancellation (single-chart `k`-algebra fact), NOT an overlap cocycle.
- **STILL NOT done (disclaimed in-file):** the FULL overlap-restricted *trivialization* cocycle
  square needs `targetOverlapTransition` (a target-side localization comparison) — genuinely new,
  because the trivializations are `k`-algebra (gauge) maps, not `R`-algebra maps. This is the precise
  residual, alongside the previously-banked prime residue-field-rank bridge for `locallyTrivial`.

## Net effect

The atlas `PivotLocalProductAtlas` / `reducedFibre_pivotLocalProductAtlasOnRankOpen` now: cover +
**C1 bridge** `pivotOfCover` + per-pivot trivializations + overlap cocycle (`overlapTransition`,
`transitionRoundTrip`, `transitionCommutes`) + **C2 overlap-local restriction** `overlapRestrict` +
common-target cancellation `transitionFactors` (correctly labelled). A cover chart connects to its
trivialization, and the transition coherence is now stated at the genuine (overlap-local, base-side)
level it actually holds — no faked coherence.
