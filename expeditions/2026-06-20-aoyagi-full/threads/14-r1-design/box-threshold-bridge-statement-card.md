# BoxThresholdBridge — statement card (#11, the R1 box→point RLCT collapse)

**Task #11.** The side-fact the adjudication cert (addendum-2/3) named as load-bearing: *the all-zero
deepest point is the global-minimum local RLCT of `dlnLoss M 0` over any bounded region*, which
collapses a5f5ceb1's cover GE-leg recursive **box-integrability** (`hKint`) to the **point** threshold.

**Status: `sorry-free`, axiom-clean (`propext`/`Classical.choice`/`Quot.sound`).** Built on base
`@174cc3f6` (has `DeepestMinRlct` + `S1Fubini`). File:
`lean/DLNFibre/DLN/RLCT/Validate/BoxThresholdBridge.lean`. Controller ports it onto
`fm3/routem-ga-transport` at integration so a5f5ceb1's producer imports it.

## What it delivers

The consumer (`chart_pullback_lt_top` family, `S1NodeCoverGE.lean`) threads, per chart, the child core
box-integrability `hKint : IntegrableOn (fun z => |K z|^(-c')) Vz`. This bridge produces exactly that
`hKint` from the **relative** point threshold `c' < rlctAtOn K 0` — value-agnostic.

## Lean signatures

```
-- the abstract finite-subcover collapse (ordering form)
theorem box_integrable_of_lt_rlctAtOn_deepest {M} [PseudoMetricSpace M] [MeasureSpace M]
    [ProperSpace M] [IsFiniteMeasureOnCompacts volume] [OpensMeasurableSpace M]
    [PseudoMetrizableSpace M]
    (F : M → ℝ) (hFmeas : Measurable F) (deepest : M)
    (hmin : ∀ p, rlctAtOn F deepest ≤ rlctAtOn F p)
    (Vz : Set M) (hVz : IsCompact Vz) (c' : NNReal)
    (hc' : (c' : ℝ≥0∞) < rlctAtOn F deepest) :
    IntegrableOn (fun w => |F w| ^ (-(c' : ℝ))) Vz volume

-- the cite-free BoxThresholdBridge (ordering discharged by homogeneity)
theorem box_integrable_of_lt_rlctAtOn_zero_of_homogeneous {N} (F : (Fin N → ℝ) → ℝ) (D : ℕ)
    (hFmeas : Measurable F) (hhomog : ∀ c w, F (c • w) = c ^ D * F w)
    (Vz : Set (Fin N → ℝ)) (hVz : IsCompact Vz) (c' : NNReal)
    (hc' : (c' : ℝ≥0∞) < rlctAtOn F (0 : Fin N → ℝ)) :
    IntegrableOn (fun w => |F w| ^ (-(c' : ℝ))) Vz volume

-- the homogeneity that discharges the ordering for the true loss
theorem dlnLoss_zero_smul (H) (A) (c) : dlnLoss H 0 (fun s => c • A s) = c ^ (2 * L) * dlnLoss H 0 A
```

## English gloss

For a homogeneous `F` (e.g. the flattened true loss `dlnLoss M 0`, degree `2L`), if `c'` is below the
origin's local RLCT `rlctAtOn F 0`, then `|F|^{−c'}` is integrable over any compact box `Vz`. The
origin (all-zero deepest point) is the global-minimum local RLCT, so it governs the box-integrability
threshold — every point of the box is no more singular than the origin.

## Proved / Reused / Cited (the honest split)

- **PROVED here** (cite-free, the genuinely-new finite-subcover layer): `lt_sSup` extraction from the
  `rlctAtOn = sSup` definition + the admissible-down-set `admissible_downset` (S1Fubini) give an
  integrable open neighbourhood at each `p ∈ Vz`; `LocallyIntegrableOn.integrableOn_isCompact`
  (Mathlib) pastes them over the compact `Vz`.
- **REUSED** (proven, `DeepestMinRlct`): `deepest_le_of_homogeneous_core` — value-free ordering
  `rlctAtOn F 0 ≤ rlctAtOn F v` for homogeneous `F`. The cone-vertex reading: the all-zero parameter
  point is in every zero-product stratum's closure, so its local RLCT is the minimum.
- **NOT here / CITED elsewhere**: the *value* `rlctAtOn deepest = ½·minAdm` is the cover's S2-only job
  (the spine + atom, #12). This bridge never mentions `Mval`/`minAdm`/`rlct = ½·mval` — non-circular,
  headline stays "proven modulo only S2".

## Fidelity notes (verified)

- The cone-vertex reading is NOT the naive "all-zero EXPONENT `T = 0` realizes `minAdm`": that is FALSE
  (`Mval(M, 0) = M⁰·M¹ ≠ minAdm` in 7/9 width-census cases, e.g. `(2,2,2)`: `4 ≠ 3`). The all-zero
  PARAMETER point is the cone vertex whose RLCT is the *minimum over all strata*, established by
  homogeneity + lsc — not by a single-stratum `Mval`. (Confirmed against the cert addendum-2 §0.)
- (2,2,2) GATE: `box_integrable_of_lt_rlctAtOn_zero_of_homogeneous` instantiates at the homogeneous full
  loss (`myF222 = ‖A·B‖²`, degree 4, `rlctAtOn · 0 = 3/2`): `c' < 3/2 ⟹ IntegrableOn |myF222|^{−c'} Vz`.

## Open / consumer interface

- The bridge's `hmin` is discharged by homogeneity for any node whose core is the true loss
  `dlnLoss M 0` (homogeneous). For a node core that is `monomial · unit` POST-Schur-reduction (not
  homogeneous), `deepest_le_of_homogeneous_core` does not apply; that node's `hmin` (or its direct
  box-integrability) is the spine/atom's to supply — the generic `box_integrable_of_lt_rlctAtOn_deepest`
  consumes whatever ordering is provided. Pinned with the controller as the consumer-interface seam.

Pinned commit (base): `@174cc3f6`.
