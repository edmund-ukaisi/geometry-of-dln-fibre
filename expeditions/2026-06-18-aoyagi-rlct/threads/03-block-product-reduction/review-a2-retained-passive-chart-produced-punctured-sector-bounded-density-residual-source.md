# Review: A2 retained-passive chart-produced punctured-sector bounded-density residual source

## Route Verdict

PASS.  Xhigh route review by `McClintock the 4th` found no blocking issue.

## Route Checks

- The generic measure helper route is sound.  From
  `hf : forall a.e. x with respect to mu.restrict s, f x <= c` and
  `hs : MeasurableSet s`, the proof uses `restrict_withDensity hs`,
  `withDensity_mono hf`, `withDensity_const`, and loosens
  `c • mu.restrict s <= c • mu` to obtain
  `(mu.withDensity f).restrict s <= c • mu`.

- The Aoyagi wrapper is non-overclaiming.  It defines
  `sourceMeasure = passiveSource.withDensity sourceDensity`, returns the
  punctured sector `V`, and assumes only the local bound
  `forall a.e. z with respect to passiveSource.restrict V, density z <= c`
  with `c < infinity` before feeding the derived domination into the banked
  local-domination socket.

- The helper should not require `c < infinity`; finiteness belongs only to
  the residual-source wrapper because the finite-integral transfer uses it.

## Nonclaims

No proof that an external/original source prior admits this density or local
bound; no determinant-chart Haar transport, raw/source Haar theorem, passive
Jacobian formula, source-image equality, source-rank coverage, normal
crossings, pole order, or RLCT extraction.

## Implementation Review

PASS.  Xhigh post-implementation review by `Kierkegaard the 4th` found no
blocking issue.

Checks:

- The Lean statement matches the card: `sourceMeasure =
  passiveSource.withDensity density`, the theorem returns `V`, and the local
  bounded-density hypothesis is on `passiveSource.restrict V`.
- The support conclusion `mu.restrict localSource = mu` is unconditional.
- The residual positivity and integrability conclusions are under
  `forall {c : ENNReal}, c < infinity -> ...`.
- No source-prior, Haar, Jacobian, coverage, normal-crossing, pole-order, or
  RLCT overclaim was found.
- No hidden quiver reliance was found by a recursive dependency crawl from
  the handoff target.

Focused Lean checks by the reviewer passed for:

```text
DLNFibre/DLN/Aoyagi/LocalMeasureHandoff.lean
DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveSelectedEntrySourceMeasureHandoff.lean
```

## Final Gates

Controller verification after the interruption passed:

```text
scripts/lb DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveSelectedEntrySourceMeasureHandoff
scripts/lb DLNFibre
scripts/sorries
git diff --check
rg -n "(sorry|axiom|native_decide|#exit)" touched Lean files
```

Direct axiom probes for
`DLNFibre.DLN.Aoyagi.restrict_withDensity_le_smul_of_ae_le` and
`DLNFibre.DLN.Aoyagi.PaperEndpointFixedBaseRegularCoordinateSourceData.exists_open_residualSourceHypotheses_of_case2EndpointTransport_withPassive_puncturedSector_inverseReadout_of_withDensity_ae_le_const_passiveProductMeasure_finiteMass`
reported only `[propext, Classical.choice, Quot.sound]`.
