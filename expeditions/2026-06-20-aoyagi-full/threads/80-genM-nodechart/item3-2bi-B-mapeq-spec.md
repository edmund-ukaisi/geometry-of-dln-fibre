# 2b-i-B — the item-3 map equality `composeFold fs = phiFlatLiveR1 ∘ kLDU` (SPEC, cast-avoiding, for the gate)

Branch genm-interior @c10bccd4. 2b-i-A (card-bridge) + 2b-i-C/D (interior det, map-eq as hypothesis) are
GREEN, cast-light, banked. This specs the LAST + HEAVIEST piece: the map equality (the item-3 bottleneck,
the cast weight the whole expedition deferred), with the cast-avoiding formulation FIRST per the gate.

## THE TARGET
`∃ fs : List (ChartFactor N), composeFold fs = phiFlatLiveR1 M (tach M) ha hN p hp1 hp2 (kLDU-reparam)`,
the factored presentation of the interior chart, so `interiorDet_of_factored` (banked) delivers the
monomial det. `phiFlatLiveR1 ∘ kLDU = phiGen (x p₀) (genBlkFlatLiveR1 … (kLDU x) x)` = `paramsEquivFlat ∘
chartParamsGen (x p₀) (genBlkFlatLiveR1 (kLDU x))`. The factor list (foldr ∘, head applied LAST):
  fs = [ linearFactor Q (= paramsEquivFlat ∘ pack reshape, det 1),
         radialFactor active p₀ (det |u_p|^{minAdm−1}),
         <per boundary s descending>: lduChartFactor E'_s (LDU monomial), schurChartFactor E_s (|det K|^{r+c}),
         chainChartFactor … (det 1) ].

## PRECEDENTS (the two worked map equalities)
- (4,4,2,2) `phi4422_eq_composeFold` (RouteM4422Bridge): pure-radial, fs = [linearFactor Q, radialFactor].
  A 5-line `funext u; rw [composeFold_cons*, …]; change …; rw [hQ, …, ← chartParams4422_eq_pack_pb]`. CLEAN
  because NO Schur/LDU factors (trivial K-cores) ⟹ no per-boundary split-CLE.
- (3,3,3,3) is NOT a composeFold (it's Q ∘ Frame ∘ Kparam, det via det_comp on the fused Frame). So the
  composeFold-map-eq route has NO t≥2 worked precedent — (4,4,2,2) is pure-radial, (3,3,3,3) is fused.

## THE CAST WEIGHT (where the (3,3,3,3) pattern fails over opaque widths — flagged from item-3 spec)
Each schurChartFactor/lduChartFactor takes an ABSTRACT CLE `E_s : (Fin N → ℝ) ≃L[ℝ] Block_s × R` splitting
the ambient into boundary-s's block space (SchurInc t r c / LDUParam t) and the rest. At (3,3,3,3) these
slots are DEFINITIONAL (Fin-27 literals). At opaque Wext/Text the split-CLE must be built from
`chartIdxEquiv`'s role-slots (frameSplitEquiv/liftSlotEquiv), and `chartIdxEquiv` is Classical
(Fintype.equivFin, NOT rfl). The map equality `composeFold fs = chartParamsGen∘kLDU` holds only
PROPOSITIONALLY after heterogeneous Fin.cast rewrites through the opaque equiv — the genuine multi-tide fight.

## THE CAST-AVOIDING FORMULATIONS (candidates — the gate question)
Mirroring (a)'s Function.update / splitM's piCongrLeft (avoid the global Fin-N bijection):
(F1) **Per-boundary readback via apply_symm_apply (the witness's readK_wInt pattern, PROVEN to work).**
  Build each E_s NOT as a fresh CLE but as the composition `chartIdxEquiv` ∘ (role-slot injection), and prove
  `composeFold fs = chart` by `funext` + the SAME `Equiv.apply_symm_apply` cancellation that closed
  readK/X/N/E/W_kLDU + genBlkFlatLiveR1_wInt_Rmat. The map-eq reduces to per-coordinate role-reads, each
  cancelling the chartIdxEquiv round-trip — NO Fin-N bijection-level cast, NO literal indices. RISK: the
  composeFold's foldr prefix-evaluation (head applied last) means factor s's E_s reads the PREFIX output
  (composeFold tail), so the readback must thread through the prefix — the per-factor "reads only own-block,
  prefix-untouched" lemma (flagged in the 2b grading spec). This is the genuine design.
(F2) **DEFINE the chart AS composeFold fs (skip the map equality for the det).** RouteMPhiFlatDet's
  composeFold_abs_det_leafH gives the det of composeFold fs DIRECTLY (no map equality). Then transfer only
  the RATE by a separate map equality (rate is decoder-agnostic, local — robust). But the cov field's chart
  must be the SAME phi as the rate's (NodeAchieverChart ties one phi). So F2 needs phiFlatLiveR1 = composeFold
  fs at the RATE level — same map equality, but only where the rate engine consumes it (lighter than the det
  extensionality). Codex's item-3 recommendation. RISK: the rate map-eq still needs the per-boundary readback.
(F3) **The fused-Frame route (generalize (3,3,3,3) directly): det via det_comp + layer-filtration
  block-triangular det, NO composeFold.** Avoids the split-CLEs entirely but needs the opaque-width
  block-triangular det (the 2b grading spec's layer filtration) — a DIFFERENT cast fight (BlockTriangular.det
  over opaque toSquareBlock, the off-block-vanishing). RISK: heavier per the earlier grading-spec analysis.

## RECOMMENDATION FOR THE GATE
RANK: F1 (per-boundary apply_symm_apply readback) > F2 (define-as-fold + rate-only map-eq) > F3 (fused). F1
reuses the PROVEN cast-clean pattern (readK_wInt / genBlkFlatLiveR1_wInt_Rmat — the apply_symm_apply
cancellation that has worked every time this expedition); the genuine new design is the prefix-threading
(factor s reads the composeFold-prefix output). F2 is the fallback if the prefix-threading is intractable
(define the chart as the fold, transfer the rate separately). F3 is last (a different, heavier cast fight).
This is a GENUINE multi-tide build (the deferred item-3 bottleneck); recommend opening F1 as its own tide
with a sub-spec of the prefix-threading lemma FIRST. Confirm the route (F1) before the cold build.

## STATE OF THE INTERIOR LEG (for context)
COMPLETE + sorry-free: rate (phiFlatLDU/phiFlatLive/phiFlatLiveR1), witness (2e), budget_identity,
decoder (genBlkFlatLiveR1 + all decoder-equalities), card-bridge (2b-i-A), interior-det assembly (2b-i-C/D).
REMAINING (the det realization): 2b-i-B (this map equality) + the `minAdm ≤ routeMAmbient` sub-lemma
(2b-i-A's hypothesis) + the n-fold null-slice cov (2b-i-D's injOn/add-back, generalizing phi3333_cov) +
the contract assembly (NodeAchieverChart instance + interiorContractLDU). 2b-i-B is the long pole.
