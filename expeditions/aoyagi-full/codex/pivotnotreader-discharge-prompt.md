# Design review: discharging PivotNotReader cleanly (Lean 4 + Mathlib, DLNFibre harness)

## Context
A (2,2,2) interior-determinant headline `interiorDet_headline_222` is COMPLETE + axiom-clean except it rests on one open hypothesis:

    PivotNotReader : structPivot M222 hN_M222 ∉ readerSet

where:
- `structPivot M hN : Fin (routeMAmbient M) := ⟨0, hN⟩`  — a GLOBALLY-SHARED def (RouteMFlatStructV.lean), the LITERAL flat-slot 0. It is the radial coordinate of the achiever chart `phiFlatLiveR1` (its rate is `(x structPivot)^2 · U`), and is consumed pervasively downstream: the RLCT measure-transfer contract `RouteMInteriorContract` integrates over `{x | x (structPivot) = 0}` (the radial axis), and many rate/diff lemmas read `x (structPivot)`.
- `readerSet : Finset (Fin (routeMAmbient M222))` = `{readerSlotK, readerSlotX, readerSlotN, readerSlotW0, readerSlotW1}`, the 5 reader slots, each defined as `(chartIdxEquiv M222 …).symm ⟨tag⟩` where `chartIdxEquiv` is a NONCOMPUTATIONAL bijection (built via `Fintype.equivFin`). It does NOT kernel-reduce: `decide` gets stuck.
- `PivotNotReader` is used to build a `Fin 8 ≃ Fin 8` reindex equiv (`slotEquiv`/`colEquivT`) from the 8 slots `[a,b,n,w0,w1,p,lf0,lf1]` being PAIRWISE DISTINCT. The pivot `p = structPivot` must be ≠ each of the 5 readers. That equiv computes `|det DB| = |aRead|²` (the engine). `PivotNotReader` is the ONLY thing that ties slot-0 to "not a reader".

## Verified facts (I checked the actual code)
1. NO proof does `rfl`/`decide` on `structPivot = ⟨0,_⟩` to extract the literal 0. It's used purely as an abstract `Fin N` element everywhere. So changing its VALUE is type-safe (no literal-0 dependence).
2. The headline wiring `interiorDet_headline_of_BData` / `radialComp_abs_det` uses ONLY `hp_mem : structPivot ∈ active` + `hcard : active.card = minAdm` — NOT slot-0-ness, NOT PivotNotReader.
3. The leaf slots `lf0, lf1` are ALREADY chosen from `univ \ forbiddenSlots` where `forbiddenSlots = insert structPivot {5 readers}` (card ≤ 6, complement ≥ 2), so `lf_i ∉ readerSet` and `lf_i ≠ structPivot` hold BY MEMBERSHIP — no opaque comparison. This is the existing discharge PATTERN.
4. A pen-and-paper verdict says `PivotNotReader` for `structPivot = ⟨0,_⟩` is FRAGILE/possibly FALSE (slot-0 has no constructed relation to the chartIdxEquiv readers; "prove it semantically" = route (i) is a dead end). Verdict = route (ii): "re-point the pivot to a chosen non-reader slot."

## The tension I want adjudicated
`structPivot` is GLOBALLY shared (RouteMFlatStructV, consumed by the chart `phiFlatLiveR1`, the rate lemmas, AND the RLCT measure-transfer `RouteMInteriorContract` which integrates over `{x (structPivot) = 0}`). "Re-point structPivot to a non-reader slot" is NOT obviously local — it touches the whole downstream cone, and worse, the general `structPivot M hN` has NO `readerSet M` to choose its complement from (readerSet is M222-specific). So "choose pivot from `univ \ readerSet`" doesn't directly generalize ∀M the way `structPivot := ⟨0,_⟩` does.

## QUESTION
What is the CLEANEST discharge of `PivotNotReader`, given the above? Rank these and flag traps:

(A) Change `structPivot M hN := ⟨0,hN⟩` globally to a `Classical.choice` of `univ \ (reader-image)` — but reader-image needs `chartIdxEquiv M` ∀M, and structPivot is in a low-level shared file that may not import the chart machinery. Is this a layering violation / import cycle risk?

(B) Keep `structPivot := ⟨0,_⟩` global, but make the (2,2,2) BData use a DIFFERENT pivot `pRad := Classical.choice (univ \ readerSet)` LOCAL to RouteMBData222, and prove the headline for THAT pivot — then bridge `phiFlatLiveR1 … (radial read at structPivot)` to the pРad-radial chart. Does this require re-deriving the rate `routeMCore_phiFlatLiveR1` for a non-structPivot radial? (The rate is `(x structPivot)^2·U` — hard-wired.)

(C) Prove `PivotNotReader` is TRUE after all via a CARDINALITY/counting argument: `readerSet.card + minAdm M ≤ flatDim M` is TIGHT at M222 (5 + 3 = 8). Does tightness HELP prove `structPivot ∉ readerSet`? (I suspect NOT — a counting bound says the complement is nonempty, but doesn't pin slot-0 into it. Confirm this is a dead end, or show the counting argument that DOES force `⟨0,_⟩ ∉ readerSet`.)

(D) Some other route — e.g. make `phiFlatLiveR1` PARAMETRIC in the radial slot `p₀` (currently hard-wired to `structPivot`), so the chart, rate, and headline all take `p₀` as an argument, and instantiate `p₀ := a chosen non-reader slot`. Most faithful but most invasive — is it the right ∀M move?

Give me: the ranked recommendation, the import-layering check for (A), whether (C) is truly a dead end, and which route GENERALIZES to ∀M cleanly. Be concrete about Lean mechanics.
