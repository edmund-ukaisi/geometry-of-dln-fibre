# Review - A2 source-stratum two-sided loss-density iff

Date: 2026-06-29.

Reviewers: xhigh read-only scouts `Bohr the 2nd` and `Dirac the 2nd`.

## Verdict

PASS as a source-stratum specialization of the local-source supplied-bound
integrability equivalence.

## Checks

Bohr confirmed that the theorem is exactly a specialization of the local-source
iff: the proof defines `sourceStratum`, invokes the local theorem with
`source := sourceStratum`, and rewrites back.  Bohr also checked that
measurability, residual positivity, residual boundedness by `R^2`, constant
positivity, `0<t`, and all four source-stratum loss/density comparison bounds
remain explicit hypotheses.

Dirac confirmed the namespace and API shape.  The conclusion is over

```text
(mu.restrict (U inter sourceStratum)).prod nu
```

and the residual side is

```text
residualNegPowerIntegrableOn Cedge (U inter sourceStratum) mu t.
```

Dirac also found the proof robust and narrow: it delegates to the local-source
theorem and adds no new analytic content.

## Nonclaim Boundary

Both reviewers confirmed that the theorem and docs do not claim any proof of
comparison bounds, residual hypotheses, p.13 chart construction or coverage,
density/Jacobian/product-measure transport, normal crossings, pole order, or
RLCT.

## Verification

The controller ran:

```text
cd lean
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.RegularSuspensionLocalMeasure
```

It passed.  Bohr additionally reported a read-only Lean check of the touched
file passing.  `scripts/sorries`, `git diff --check`, the touched-file
forbidden-marker scan, and the direct axiom probe passed; the theorem depends
only on `[propext, Classical.choice, Quot.sound]`.
