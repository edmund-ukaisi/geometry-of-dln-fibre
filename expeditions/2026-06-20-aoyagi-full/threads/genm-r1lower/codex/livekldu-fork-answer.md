# Codex consult — LIVE+kLDU architectural fork (answer + my adjudication)

**Date:** 2026-06-30. **Model:** gpt-5-codex xhigh (decorrelated).

## Codex verdict (condensed)

- **Q1 (fresh bundle `p := leafPivot`)**: VIABLE. `NodeAchieverChart.p` feeds the assembly only
  through `leafH`, the pivot-exclusion set, and `leaf_integrand`. Rebuild those on `leafPivot` and the
  assembled theorem doesn't care `structPivot` differs. *Caveat*: audit `leaf_integrand_of_rate` and
  the box/measurability helpers to confirm they take the pivot ABSTRACTLY, not hardcoded `⟨0⟩`.
- **Q2 (det chain-rule)**: SOUND **only if** the headline is applied to the PRE-kLDU chart so that
  `|det DB|` is the residual-block det, NOT already counting the K-block — else multiplying by
  `|det D(kLDU)|` DOUBLE-COUNTS the pivot factors (squares them).
- **Q3 (injOn factorization)**: SOUND if kLDU's good set = the exact forbidden-axes the assembly
  deletes, and BchartLeaf injectivity tolerates the K-entries becoming triangular combinations
  (holds iff the LDU recovery is bijective on nonzero pivots).

## My adjudication (source-verified) — the double-count is AVOIDED by the right factorization

Codex's Q2 warning is the live risk. The resolution: **do NOT chain-rule through kLDU twice.** Push
kLDU INTO the boundary factor. Concretely, `radialComp_abs_det_at` is generic in `B`. Set
`B' := BchartLeaf ha ∘ kLDU` and prove the single map identity
`phiFlatLiveAt M ha hL leafPivot (kLDU x) = B' (pivotBlowupOn activeM leafPivot x)`. Then the headline
fires ONCE: `|det D(phiFlatLiveAt ∘ kLDU) u| = |u leafPivot|^{minAdm−1} · |det DB'|`, and `|det DB'|`
is computed as a single monomial. The radial pivot is separated exactly once; no squaring.

The map identity reduces to a **commute fact**: `pivotBlowupOn activeM leafPivot (kLDU x) =
kLDU (pivotBlowupOn activeM leafPivot x)`. SOURCE-VERIFIED this holds:
- `activeM = activeEImg ∪ activeLeafImg` (E-block ∪ leaf slots) — `RouteMLeafSlot.activeM`. NO K-slots.
- `kLDU` touches ONLY frame-K-branch slots, identity elsewhere — `RouteMKLens.kLDU` + the `read*_kLDU`
  pass-through lemmas.
- `pivotBlowupOn activeM leafPivot` scales only `activeM` slots + the pivot.
- ⟹ kLDU and the blow-up act on DISJOINT coordinate sets ⟹ they commute.

Then `phiFlatLiveAt(kLDU x) = BchartLeaf(pivotBlowupOn (kLDU x)) = BchartLeaf(kLDU(pivotBlowupOn x))
= (BchartLeaf ∘ kLDU)(pivotBlowupOn x)`, applying the BUILT `hmap_leaf` at the point `kLDU x`.

## Q1 caveat checked

`structPivot M hN := ⟨0, hN⟩` (literal slot 0); `leafPivot = leafSlot…0 0` (a leaf slot). They are
GENUINELY DIFFERENT. The dead-leaf contract `RouteMInteriorLDUContract` is wedded to `structPivot`
(rate `routeMCore_phiFlatLDU` reads `x ⟨0⟩`). So re-pointing `interiorLDUphi` in place is the WRONG
move — it would mismatch the rate's pivot. The clean path is a FRESH contract on the LIVE chart with
`p := leafPivot`, reusing the BUILT LIVE infra (`hmap_leaf`, `interiorDet_leaf_headline`,
`phiFlatLiveAt_rate`, the kLDU monomialization, the `ldu_cov_of_differentiable_injOn` engine). The
dead-leaf `RouteMInteriorLDUContract` is then RETIRED (it was the non-injective decoder genm-hinj
walled).

`leaf_integrand_of_rate` (`RouteMGenLeafIntegrand`) is generic in `p` (it takes `p : Fin N` and the
rate as an argument) — confirmed abstract, no `⟨0⟩` hardcode.

## DECISION

Build a fresh `NodeAchieverChart M` bundle on `phiFlatLiveAt ∘ kLDU`, pivot `leafPivot`, via the
B' = BchartLeaf ∘ kLDU factorization (radial separated once → no double-count). injOn factors through
the composition (kLDU LDU-recovery, single block — much cheaper than the monolithic opaque-width
27-coord recovery). The dead-leaf `RouteMInteriorLDUContract` is retired.
