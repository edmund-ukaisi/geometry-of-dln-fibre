# Review: A2 retained-passive chart-produced punctured-sector local-domination residual source

## Verdict

PASS.  Xhigh post-implementation review by `Einstein the 3rd` found no
blocking issue.

## Checks

- The Lean theorem
  `exists_open_residualSourceHypotheses_of_case2EndpointTransport_withPassive_puncturedSector_inverseReadout_of_restrict_le_smul_passiveProductMeasure_finiteMass`
  is present in
  `lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveSelectedEntrySourceMeasureHandoff.lean`.
  It keeps `sourceMeasure` arbitrary, defines
  `passiveSource = passiveMeasure.prod weightedBox`, returns an open sector
  `V`, and places the local domination assumption
  `sourceMeasure.restrict V <= c • passiveSource` after `V` is chosen.

- The statement separates support from domination: `mu.restrict localSource =
  mu` is proved unconditionally from the socket, while residual positivity and
  `residualNegPowerIntegrableOn` are conditional on `c < infinity` and the
  local domination field.

- The proof uses the intended two-step domination route.  First,
  `Measure.map Prod.snd passiveSource =
  passiveMeasure Set.univ • weightedBox`, and finite passive mass transfers
  the raw selected-entry facts to the passive product marginal.  Second,
  `map_le_smul_map_of_le_smul measurable_snd` maps the local source-domain
  domination to residual-coordinate marginal domination, and the finite scalar
  `c` transfers the same positivity/integrability facts to the arbitrary
  source marginal.

- Required hypotheses are explicit: finite passive mass, finite scalar `c`,
  nonnegative exponent, positive signed-box radii, the selected-entry critical
  inequality, and the retained-passive continuity/base determinant/pivot
  hypotheses.

- The theorem does not overclaim.  Its docstring excludes source-prior
  transport, determinant-chart Haar transport, passive Jacobian formula,
  source-image coverage, normal crossings, pole order, and RLCT extraction.
  The statement assumes domination; it does not prove domination for an
  external/original source prior.

- No hidden quiver-paper reliance was found.  The target file imports only the
  retained-passive Aoyagi source-measure handoff path and local measure
  utilities.

## Verification

The reviewer ran:

```text
LEAN_NUM_THREADS=1 ~/.elan/bin/lake env lean DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveSelectedEntrySourceMeasureHandoff.lean
```

and it exited successfully.  The controller separately retains the standard
expedition gate for banking: focused `scripts/lb`, full `DLNFibre` build,
`scripts/sorries`, `git diff --check`, touched-file forbidden-marker scan, and
direct axiom probe.

Controller banking gate also passed:

```text
scripts/lb DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveSelectedEntrySourceMeasureHandoff
scripts/lb DLNFibre
scripts/sorries
git diff --check
rg -n "sorry|axiom|native_decide|#exit" lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveSelectedEntrySourceMeasureHandoff.lean
#print axioms ...of_restrict_le_smul_passiveProductMeasure_finiteMass
```

The direct axiom probe reported only:

```text
[propext, Classical.choice, Quot.sound]
```
