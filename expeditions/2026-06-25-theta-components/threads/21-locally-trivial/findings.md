# Thread 21 — bundle bridge B3-4 (top-left e_β↔ambient) (formaliser, #118) — certificate

**Formaliser tide, scoped PARTIAL.** New file `lean/DLNFibre/Core/FibreBundleLocallyTrivial.lean`, wired
by the controller; whole library green (3789 jobs); headlines axiom-clean `[propext, Classical.choice,
Quot.sound]` (controller-gated); reviewer PASS (fidelity + honesty gate). **Does NOT earn `locallyTrivial`.**

## HEADLINE — the genuine TOP-LEFT bridge (not the full atlas)
The thread-19 ambient principal-open presentation `D(detMinorPoly)` (top-left pivot) is genuinely
identified with the deep-chart presentation that `e_β` inverts. A real `LocalTrivializationDatum` is
instantiated at the top-left chart. The bundle is NOT `locallyTrivial`: the per-pivot trivialization
`e_{s,t}` (non-top-left) + the cocycle transport onto it remain (#123).

## Landed (axiom-clean)
- `detMinorPoly_topLeft_rename` — THE SEAM: `renameEquiv repStratumEquiv (detPivotPoly q p r) =
  detMinorPoly (topLeftRows) (topLeftCols)`, identifying the ambient single-matrix coordinate ring
  `MvPolynomial (Fin p × Fin q) k` with the chart-side stratum ring `MvPolynomial (RepCoord (dStratum
  q p)) k`. Unconditional, `k : Type`.
- `topLeftBaseToChartAway (d r) : Away (detPivotPoly (d0)(d_last) r) →ₐ[k] Away (ΔPdeep d r)` — the
  bridge AlgHom (= banked `baseLocMap`).
- `topLeftBaseToChartAway_algebraMap_detPivot` — the bridge carries `algebraMap (detPivotPoly)` to
  `algebraMap (ΔPdeep)`: it identifies the two INVERTED denominators (ΔPdeep's quotient class =
  `chartDsig` = what `e_β` inverts). Load-bearing, NOT a `refl`.
- `LocalTrivializationDatum k Base Total BaseLoc Fibre` (structure: `chartElt : Base`, `trivialization :
  Total ≃ₐ[k] BaseLoc ⊗[k] Fibre`) + `topLeftLocalTrivializationDatum [Infinite k] (d r)` — the
  bundle-chart datum, top-left chart GENUINELY instantiated (`chartElt = chartDsig`, `trivialization =
  reducedFibre_chartDsig_tensorEquiv_reducedVariety` = the real e_β+tensor composite). Non-vacuous data.

## THE REMAINING COST to `locallyTrivial` (#123, Codex xhigh decorrelated, ranked)
The cheap "transport `e_β` along a coordinate permutation" route to the per-pivot chart is
PLAUSIBLE-BUT-NOT-AUTOMATIC: it requires first proving the **conjugation skeleton** — that permuting
end-factor rows/cols conjugates the WHOLE deep-chart construction (`vanishingIdeal Σ^r`, `ΔPdeep`, every
Schur generator) to its `(s,t)` analogue, not merely the determinant. Otherwise it is a
~250-LoC-per-pivot re-derivation. That is the next tide for an actual `locallyTrivial`.

## Net bundle state (controller synthesis) — STILL NOT locallyTrivial
single-chart triviality (#11) + per-minor cover + family (#18) + ambient transition cocycle (#19) + the
top-left `e_β`↔ambient bridge & a genuine top-left `LocalTrivializationDatum` (#21). The bundle direction
remains a tower; the one rung to the EARNED `locallyTrivial` is the per-pivot conjugation skeleton (#123).

## Synthesis-coherence note (reviewer flag, ACTIONED)
The tasks #117/#118 carried "→ earned LocallyTrivial" in their titles; the code earns NO such name.
Titles scrubbed. Any synthesis must cite #21 ONLY as a top-left single-chart `LocalTrivializationDatum`
+ the honest bridge — NEVER as local triviality / an earned `locallyTrivial`.

## Artifacts (committed @ cfe91c3e etc.)
`threads/21-locally-trivial/statement-card.md` + codex consults (scope + reviewer fidelity). Lean:
`Core/FibreBundleLocallyTrivial.lean`. Untouched the parallel `smooth-c2a` files. Universe: `k : Type 0`
(common ground with thread-18/19; ℂ is Type 0, harmless).
