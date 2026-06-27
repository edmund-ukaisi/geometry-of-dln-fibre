# Thread 27 — scheme-level cover→PivotDatum bridge (PR #11 review round 2) — statement card

**Status: sorry-free + reviewed (fidelity PASS).** Module
`lean/DLNFibre/Core/FibreBundleLocallyTrivialFull.lean` (the only file changed). Whole library green (3806 jobs); 0 sorry/axiom/native_decide (`scripts/sorries`); all
new/changed headlines axiom-clean `[propext, Classical.choice, Quot.sound]` (gated via `#print
axioms`, forced elaboration). NO new import lines (everything from the existing import set:
`Matrix.det_zero_of_row_eq/_column_eq`, `PrimeSpectrum.mem_basicOpen`, `Function.not_injective_iff`).

The OWNER (PR #11 review round 2) flagged a genuine usability gap: the round-1 C1 bridge `pivotOfCover`
TAKES `Injective s`, `Injective t` as hypotheses, so a *scheme-level* consumer starting from
`p ∈ basicOpen (chartDsigAt s t)` could not obtain a `PivotDatum` without separately proving
injectivity. This closes the missing "non-injective ⟹ empty chart" half, so injectivity is now
derived from chart membership rather than assumed.

---

## The non-injective ⟹ empty chart half (CLOSED)

> **Gap.** `pivotOfCover` / `pivotDatumOfSelectors` need `Injective s`, `Injective t`. A scheme-cover
> consumer with only `p ∈ basicOpen (chartDsigAt s t)` had no way to discharge them.

> **Closed.** A non-injective selector makes the deep minor a determinant with a repeated row/column,
> so `chartDsigAt s t = 0`; a prime in `basicOpen (chartDsigAt s t)` would have to omit `0`,
> impossible — so chart membership forces both selectors injective, and the banked
> `pivotDatumOfSelectors` fires.
>
> - **Lean (`FibreBundleLocallyTrivialFull.lean`):**
>   - `ΔPdeepAt_eq_zero_of_not_injective_left  (d : Fin (N+1) → ℕ) (r) (s t) (hs : ¬ Injective s) :
>     ΔPdeepAt d r s t = 0` — `submatrix s t` has two equal rows, `Matrix.det_zero_of_row_eq`.
>   - `ΔPdeepAt_eq_zero_of_not_injective_right (… ht : ¬ Injective t) : ΔPdeepAt d r s t = 0` —
>     two equal columns, `Matrix.det_zero_of_column_eq`.
>   - `chartDsigAt_eq_zero_of_not_injective (d : Fin (N+2) → ℕ) (r) (s t)
>     (h : ¬ Injective s ∨ ¬ Injective t) : chartDsigAt d r s t = 0` — the deep minor vanishes
>     (above) and `chartDsigAt` is its quotient class (`map_zero`).
>   - `injective_of_mem_basicOpen_chartDsigAt (d r s t) {p}
>     (hp : p ∈ basicOpen (chartDsigAt d r s t)) : Injective s ∧ Injective t` — contrapositive:
>     non-injective ⟹ `chartDsigAt = 0 ∈ p.asIdeal`, contradicting `mem_basicOpen`.
> - **Gloss.** A pivot chart `basicOpen (chartDsigAt s t)` is empty unless both selectors are
>   injective; equivalently, any prime in the chart has injective selectors.
> - **Status.** sorry-free, axiom-clean. Genuine (`det_zero_of_row_eq` non-vacuous, not `rfl`).

## The scheme-level bridge (CLOSED — NO external injectivity hypothesis)

> **Closed.** From `p ∈ basicOpen (chartDsigAt s t)` directly to the chart's `PivotDatum`, at the same
> localizing element, with no injectivity hypothesis to discharge.
>
> - **Lean (`FibreBundleLocallyTrivialFull.lean`):**
>   - `pivotDatumOfMemBasicOpen (d r hp hq s t) {p}
>     (hmem : p ∈ basicOpen (chartDsigAt d r s t)) :
>     {I : PivotDatum d r hp hq // pivotElt d r hp hq I = chartDsigAt d r s t}` — standalone bridge
>     lemma (`injective_of_mem_basicOpen_chartDsigAt` then the banked `pivotDatumOfSelectors` +
>     `pivotElt_pivotDatumOfSelectors`).
>   - **atlas FIELD** `pivotOfBasicOpen : ∀ s t {p}, p ∈ basicOpen (chartDsigAt d r s t) →
>     {I : PivotDatum d r hp hq // pivotElt … I = chartDsigAt d r s t}` — new field on
>     `PivotLocalProductAtlas`, wired in `pivotLocalProductAtlas` to `pivotDatumOfMemBasicOpen`.
>   - Witness `example`: fires `A.pivotOfBasicOpen s t hmem` at an abstract field, no injectivity hyp,
>     and confirms the localizing element is `chartDsigAt d r s t`.
> - **Gloss.** A scheme-cover consumer with a prime in a pivot chart obtains that chart's
>   `PivotDatum`-indexed trivialization `triv (pivotOfBasicOpen …)` for free.
> - **Status.** sorry-free, axiom-clean.

---

## Honest scope

- **EARNED (new):** the scheme-side half of the C1 bridge — chart membership ⟹ injective selectors
  ⟹ `PivotDatum` at the chart's element, with NO external injectivity hypothesis. A scheme-cover
  consumer is now usable. The point-set `cover` field (which already returns injective selectors via
  `exists_invertible_minor_of_rank`) is unchanged; `pivotOfCover` (taking injectivity) is kept for it.
- **Docstrings updated:** module header C1-bridge bullet + `PivotLocalProductAtlas` header now state
  the scheme-side bridge is usable (`pivotOfBasicOpen` / `pivotDatumOfMemBasicOpen`).
- **NOT touched (residuals from thread 25/26, unchanged):** the full overlap-restricted
  *trivialization* cocycle (`targetOverlapTransition`); the prime residue-field-rank bridge for a bare
  `locallyTrivial`. This thread is strictly the injectivity-from-membership half.

## Net effect

`PivotLocalProductAtlas` / `reducedFibre_pivotLocalProductAtlasOnRankOpen` now expose
`pivotOfBasicOpen` alongside `pivotOfCover`: a prime in a pivot chart `basicOpen (chartDsigAt s t)`
yields that chart's `PivotDatum` (hence `triv`) with no injectivity to prove — the scheme-cover API the
owner asked for.
