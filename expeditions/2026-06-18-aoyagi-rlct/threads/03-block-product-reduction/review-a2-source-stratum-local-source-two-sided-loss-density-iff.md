# Review - A2 source-stratum/local-source two-sided loss-density iff

Date: 2026-06-29.

Reviewers: xhigh read-only scouts `Herschel the 2nd` and `Franklin the 2nd`.

## Verdict

PASS as a boundary-explicit local-coverage wrapper.

## Checks

Herschel checked theorem fidelity.  The theorem assumes residual hypotheses on
`localSource`, keeps the local coverage hypothesis explicit as

```text
Ulocal inter sourceStratum subset Ulocal inter localSource,
```

applies the local-source two-sided iff to

```text
source := Ulocal inter sourceStratum,
```

and returns the final witness as `U := Uchart inter Ulocal`, yielding the iff
over `U inter sourceStratum`.

Franklin checked API and proof robustness.  The filter rewrite from
`sourceStratum` to `Ulocal inter sourceStratum` uses
`nhdsWithin_inter_of_mem` in the right direction.  Residual measurability,
positivity, and `<= R^2` restrict from `localSource` through the supplied
coverage inclusion using `AEMeasurable.mono_set` and
`ae_mono (Measure.restrict_mono ...)`.  The final set rewrite uses standard
intersection associativity/commutativity.

Franklin noted that the coverage hypothesis could be stated as
`Ulocal inter sourceStratum subset localSource`, but the current
`Ulocal inter sourceStratum subset Ulocal inter localSource` form matches the
documented local-coverage boundary and is clear.

## Nonclaim Boundary

Both reviewers confirmed that the theorem does not prove comparison bounds,
residual hypotheses, the local coverage inclusion, p.13 chart construction or
coverage, density/Jacobian/product-measure transport, normal crossings, pole
order, or RLCT.

## Verification

The controller ran:

```text
cd lean
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.RegularSuspensionLocalMeasure
```

It passed.  `scripts/sorries`, `git diff --check`, the touched-file
forbidden-marker scan, and the direct axiom probe passed; the theorem depends
only on `[propext, Classical.choice, Quot.sound]`.
