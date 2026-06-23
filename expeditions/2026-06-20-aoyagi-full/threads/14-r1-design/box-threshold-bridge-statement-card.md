# BoxThresholdBridge — statement card (#11, the R1 box→point RLCT collapse)

**Task #11.** The side-fact the adjudication cert (addendum-2/3) named as load-bearing: *the all-zero
deepest point is the global-minimum local RLCT of `dlnLoss M 0` over any bounded region*, which
collapses a5f5ceb1's cover GE-leg recursive **box-integrability** (`hKint`) to the **point** threshold.

**Status: `reviewed` — `sorry-free`, axiom-clean (`propext`/`Classical.choice`/`Quot.sound`),
fidelity-reviewed (faithful / cite-honest / non-vacuous, findings actioned below).** Built on base
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

-- the cite-free BoxThresholdBridge, compact form (ordering discharged by homogeneity)
theorem box_integrable_of_lt_rlctAtOn_zero_of_homogeneous {N} (F : (Fin N → ℝ) → ℝ) (D : ℕ)
    (hFmeas : Measurable F) (hhomog : ∀ c w, F (c • w) = c ^ D * F w)
    (Vz : Set (Fin N → ℝ)) (hVz : IsCompact Vz) (c' : NNReal)
    (hc' : (c' : ℝ≥0∞) < rlctAtOn F (0 : Fin N → ℝ)) :
    IntegrableOn (fun w => |F w| ^ (-(c' : ℝ))) Vz volume

-- the BoxThresholdBridge predicate's EXACT shape (bounded measurable box) — drop-in for the consumer
theorem box_integrable_of_lt_rlctAtOn_zero_of_homogeneous_of_bounded {N} (F : (Fin N → ℝ) → ℝ) (D : ℕ)
    (hFmeas : Measurable F) (hhomog : ∀ c w, F (c • w) = c ^ D * F w)
    (Vz : Set (Fin N → ℝ)) (_hVzm : MeasurableSet Vz) (hVzbdd : Bornology.IsBounded Vz)
    (c' : NNReal) (hc' : (c' : ℝ≥0∞) < rlctAtOn F (0 : Fin N → ℝ)) :
    IntegrableOn (fun w => |F w| ^ (-(c' : ℝ))) Vz volume   -- via closure Vz (proper ⟹ compact) + mono_set

-- the homogeneity that discharges the ordering for the true loss
theorem dlnLoss_zero_smul (H) (A) (c) : dlnLoss H 0 (fun s => c • A s) = c ^ (2 * L) * dlnLoss H 0 A

-- THE TURNKEY DELIVERABLE: BoxThresholdBridge for the RAW loss dlnLoss M 0 (flattened), end-to-end
noncomputable def flatRawLoss (H : Fin (L+1) → ℕ) : (Fin (flatDim H) → ℝ) → ℝ :=
  fun w => dlnLoss H 0 ((paramsEquivFlat H).symm w)
theorem flatRawLoss_measurable  (H) : Measurable (flatRawLoss H)
theorem flatRawLoss_homogeneous (H) (c) (w) : flatRawLoss H (c • w) = c ^ (2*L) * flatRawLoss H w
theorem boxThresholdBridge_flatRawLoss (H : Fin (L+1) → ℕ)
    (Vz : Set (Fin (flatDim H) → ℝ)) (hVzm : MeasurableSet Vz) (hVzbdd : Bornology.IsBounded Vz)
    (c' : NNReal) (hc' : (c' : ℝ≥0∞) < rlctAtOn (flatRawLoss H) 0) :
    IntegrableOn (fun w => |flatRawLoss H w| ^ (-(c' : ℝ))) Vz volume
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

## Consumer-interface match (fidelity review, addressed)

A reviewer audited fidelity + cite-honesty against the consumer predicate
`BoxThresholdBridge K := ∀ c' < rlctAtOn K 0, ∀ Vz, MeasurableSet Vz → IsBounded Vz →
IntegrableOn |K|^{−c'} Vz` (`S1NodeCoverBridge.lean`, `fm3/routem-ga-transport`). Verdict:
**faithful, clean-three, non-vacuous, no hidden hole.** Findings actioned:

- **Hypothesis shape** (`IsCompact` vs the consumer's `IsBounded + MeasurableSet`): closed — added
  `box_integrable_of_lt_rlctAtOn_zero_of_homogeneous_of_bounded`, the bounded-measurable form (via
  `closure Vz` compact on the proper space `Fin N → ℝ`). This is the verbatim drop-in for the
  predicate. Both forms ship; the consumer picks per its `Vz`.
- **`dlnLoss M 0` flattening seam**: the docstring no longer asserts the lemma "instantiates at
  `dlnLoss M 0`" as realised. `dlnLoss_zero_smul` is the homogeneity on `Params` (smul `fun s => c•A s`);
  the homogeneous lemma takes flat Pi-smul `F (c • w)`. The `Params H ≃ (Fin N → ℝ)` smul-compatibility
  carrying one to the other is NOT in this module — the consumer (who owns the flattening, e.g.
  `rlctAtOn_dlnLoss222_transport`) composes them. Docstring now says "a homogeneous `F` of the relevant
  shape **is** the flattened true loss", not "this lemma instantiates at it".
- **Scope**: the bridge requires `ProperSpace` (+ loc-finite vol); the consumer predicate is generic
  over `Z`. The bridge serves the proper-space instantiations (`Fin N → ℝ` and its recursion children),
  which is the actual use. Noted, not a hole.

## Consumer seam — RESOLVED (controller ruling, no open work here)

The recursion-node consumption is a5f5ceb1's GE-leg call, and the monomial·unit ordering is **not** open
work on this lemma in either branch:

- **Homogeneous node** (the cover consumes `BoxThresholdBridge` at the true loss / a re-pointed child
  `dlnLoss(child)`, which is itself a raw homogeneous loss): served directly by
  `boxThresholdBridge_flatRawLoss` / `box_integrable_of_lt_rlctAtOn_zero_of_homogeneous(_of_bounded)`
  — `hmin` from homogeneity.
- **Monomial·unit core** (the cover needs the post-Schur reduced core's box-integrability): established
  by the cover's **monomial machinery** (`integrableOn_monomial_mul_unit_iff` + `monomialThreshold`,
  the S2 route, à la the `(2,2,2)` `Case222Resolution`) — **NOT** an `hmin` ordering this bridge must
  force. `deepest_le_of_homogeneous_core` being "too weak" for monomial·unit is moot: that path is
  S2-monomial, not the homogeneity bridge.

So there is **no open `hmin` residual** on this lemma. `#11 = the generic bridge +
`gate`/`flatRawLoss` homogeneous forms`, complete. The per-node mechanism (homogeneous true-loss vs
monomial·unit→S2) is a5f5ceb1's GE-leg instantiation, routed by the controller.

## (2,2,2) gate — PASSED

`boxThresholdBridge_flatRawLoss` instantiates at `H222 = ![2,2,2]` (`flatDim = 8`, matching `myF222`'s
`Fin 8 → ℝ`; degree `2L = 4`; deepest = origin): for `c' < rlctAtOn (flatRawLoss H222) 0` and bounded
measurable `Vz`, `|flatRawLoss H222|^{−c'}` is integrable on `Vz`. Validates the generic bridge on the
concrete homogeneous `(2,2,2)` instance.

Pinned commit (base): `@174cc3f6`.
