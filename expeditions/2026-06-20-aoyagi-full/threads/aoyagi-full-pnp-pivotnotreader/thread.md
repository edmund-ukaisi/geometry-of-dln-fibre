# pen-and-paper thread — `PivotNotReader` (M222 interior-det headline)

DIRECTION: obstruction/adjudication (truth-value + cleanest-discharge). SCOPE: L=2, M222. READ-ONLY.

## The question
`interiorDet_headline_222` (origin/genm-detfderiv, `RouteMBData222.lean:1270`) is complete + axiom-clean
EXCEPT it takes `hpiv : PivotNotReader` where
`PivotNotReader := structPivot M222 hN_M222 ∉ readerSet` (`RouteMBData222.lean:820`).

## DATA (exact defs, read on origin/genm-detfderiv)
- `structPivot M hN := (⟨0, hN⟩ : Fin (routeMAmbient M))` (`RouteMFlatStructV.lean:89`) — LITERAL flat slot 0.
- `routeMAmbient M := flatDim M` (`RouteMExtraction.lean:37`). For M222: `= 8` (`routeMAmbient_M222`, decide).
- `routeMCore M := dlnLoss M 0 ∘ (paramsEquivFlat M).symm` (`RouteMExtraction.lean:41`). The flat space
  `Fin (flatDim M)→ℝ` is the codomain of the measure-preserving `paramsEquivFlat`. `phiGen`/`routeMCore`/
  `structPivot` are defined ENTIRELY on this space; NONE mention `chartIdxEquiv`. (Verified: grep shows
  `chartIdxEquiv` absent from RouteMExtraction/RouteMState/RouteMFlatStructV except structPivot's own file.)
- `chartIdxEquiv M t … := (finCongr h).trans (Fintype.equivFin (ChartIdx M t)).symm`
  (`RouteMChartIdxEquiv.lean:80`). `ChartIdx := Σ k:Fin L, Fin(schurDim k) ⊕ Fin(liftDim k)`. Standard
  derived Sigma/Sum/Fin `Fintype`. `Fintype.equivFin` is noncomputable here, does NOT kernel-reduce.
- `readerSlotK/X/N/W0/W1 := chartIdxEquiv.symm ⟨tag⟩` (RouteMBData222:441-467); `readerSet := {the 5}`.
- M222 ChartIdx tile (hand-computed, M222=(2,2,2), tach222=[2,1,0]⟹t0=2,t1=1,t2=0; Wext0=Wext1=Wext2=2):
  schurDim0 = t0·Wext1 = 4, schurDim1 = t1·Wext2 = 2, liftDim0 = (Wext1−t1)·Wext2 = 2, liftDim1 = 0.
  ⟹ ChartIdx ≅ (Fin4⊕Fin2) ⊞ (Fin2⊕Fin0), card 8 = flatDim. The 8 role tags ↔ all 8 flat slots.
- minAdm M222 = 3 (`minAdm_M222`).

## The geometry (INTERPRETATION, grounded in the data)
There are TWO unrelated bijections out of `Fin 8`:
  (1) the SEMANTIC `paramsEquivFlat`/`FlatIdx` one — defines what slot 0 IS (the radial scalar `u`);
  (2) `chartIdxEquiv` — an INDEPENDENT `Fintype.equivFin` enumeration, no constructed relation to slot 0.
`structPivot = ⟨0,_⟩` is a slot in (1). The reader slots are `chartIdxEquiv.symm` images in (2). Whether
`⟨0,_⟩` coincides with a reader slot is therefore decided SOLELY by where the arbitrary `Fintype.equivFin`
enumeration sends the 5 reader tags — decoupled from slot-0's semantics. Synthesis UPDATE-? (line 2595)
records this independently: structPivot=coord-0 has "no slot/role link".

## TRUTH-VALUE: FRAGILE / ENUMERATION-DEPENDENT (NOT a forced mathematical fact)
`PivotNotReader` is true for whatever value the CURRENT Mathlib `Fintype.equivFin` instance happens to
give, but it is NOT forced by the construction: a differently-derived but equally-valid `Fintype (ChartIdx)`
instance could send a reader tag to flat-slot 0, making it FALSE. It is an artifact of the opaque
enumeration, not a chart invariant. (Codex xhigh, decorrelated: same verdict — FRAGILE; prior Codex
`decoder-answer.md:39` + `genM-chart-arch-answer.md:80` reached the same independently earlier.)

## ROUTE (i) — prove semantically: DEAD END (NO)
Tag injectivity proves `chartIdxEquiv.symm tag_i ≠ chartIdxEquiv.symm tag_j` (both sides tagged). Here one
side is bare `⟨0,_⟩`. Rewriting `⟨0,_⟩ = chartIdxEquiv.symm (chartIdxEquiv ⟨0,_⟩)` leaves the OPAQUE tag
`chartIdxEquiv ⟨0,_⟩` (needs `Fintype.equivFin` reduction, which is blocked). No role-structure contradiction
is reachable. (Codex agrees: NO.)

## ROUTE (ii) — restructure (choose pivot from complement): FEASIBLE + the recommendation
Redefine the pivot to be CHOSEN from `univ \ readerSet` (exactly the existing `lf0,lf1`
choose-from-complement pattern, `exists_leaf_pair`/`lf0_ne_pivot`), instead of hardcoded `⟨0,_⟩`. Then
`PivotNotReader` holds BY MEMBERSHIP — no opaque comparison, mirroring `lf0_mem ⟹ lf0 ∉ readerSet`.

Why it preserves the headline (verified against the actual chain, NOT assumed):
- The rate `routeMCore_phiFlatLiveR1 = (x p)²·U` (`RouteMFlatLive.lean`) feeds the radius as the SCALAR
  `x (structPivot M hN)` into `phiGen`; `routeMCore_phiGen` is scalar-parametric. Any fixed slot works.
- The det chain `radialComp_abs_det` (`RouteMRadialComp.lean:43`) needs ONLY `structPivot ∈ active` +
  `active.card = minAdm`. It NEVER uses slot-0-ness; `radial_abs_det_minAdm` gives `|u_p|^{minAdm−1}` from
  the cardinality alone. `BData`/`interiorDet_headline_of_BData`/`pivotBlowupOn active (structPivot)` all
  reference `structPivot` as an ABSTRACT `Fin (routeMAmbient M)` element (RouteMBInterface:48-83).
- `pivotBlowupOn {N} (active) (p:Fin N) x` takes ANY `Fin N` pivot (S1G5Charts:384). The witness leg
  reads `wInt … (structPivot)` as a scalar (WitnessInterior:537) — agnostic.
So the ONLY consumer of slot-0-ness is `PivotNotReader` itself; redefining the pivot dissolves it.
Cardinality precondition: pivot+2 leaves distinct from readers needs `readerSet.card + 3 ≤ flatDim M222`,
i.e. `5 + 3 ≤ 8` — TIGHT but holds (already proven shape: `forbiddenSlots.card ≤ 6 < 8 = free ≥ 2`; with a
chosen pivot the bookkeeping is `readerSet.card ≤ 5`, choose pivot+2 leaves = 3 from the ≥3 complement).

Depth of change: LOCAL/API. `structPivot` is a 1-line def; make it (or a new `pRad M hN` chosen from the
complement) the pivot everywhere it currently appears. Because every downstream lemma already treats it
abstractly, the change is a re-pointing, not a re-proof. (Codex: FEASIBLE, "API/local wiring change".)

## ∀M
Route (ii) is ROBUST ∀M (independent of `Fintype.equivFin`); route (i) is not reachable ∀M.
Invariant route (ii) needs: `readerSet.card + minAdm M ≤ flatDim M` (pivot+active live/leaf slots all
distinct from readers). For M222: 5 + 3 = 8 ≤ 8. ∀M this is a SEPARATE budget/cardinality theorem — NOT a
consequence of `chartIdxEquiv`. It is the natural sibling of the already-banked `budget_identity`
(Σ r_k c_k + Text·Wext = minAdm) + `chartDim_eq_flatDim` accounting (role slots = flatDim − radial), so it
should be provable on those, but it must be PROVEN, not assumed.

## KILL-CONDITION
Route (ii) dies iff `readerSet.card + minAdm M ≤ flatDim M` FAILS for the exact general reader set (then no
complement room for a non-reader pivot + minAdm active slots). For M222 it is exactly tight (8 = 8) — verify
the general inequality is `≤` not `<` (a strict-`<` reading would already fail at M222). Sharpest single
check: confirm `readerSet.card` (the role-tag count actually read) `= flatDim M − minAdm M` would be FALSE
(would leave zero pivot room) — it must be `≤ flatDim − minAdm`, i.e. readers are a STRICT subset leaving
≥ minAdm free. At M222 readers = 5, flatDim−minAdm = 5 — so readers occupy EXACTLY the non-active tags and
the minAdm=3 active slots (pivot + 2 leaves) are exactly the complement. Tight, holds, but zero slack: the
general bound must be proven, not eyeballed.
