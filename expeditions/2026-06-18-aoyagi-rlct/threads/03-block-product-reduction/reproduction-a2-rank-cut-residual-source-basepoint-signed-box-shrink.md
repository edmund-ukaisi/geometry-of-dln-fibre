# A2 rank-cut residual-source basepoint signed-box shrink

## Object-level calculation

The strict source-cylinder rank-cut residual-source theorem still asks for the
terminal support socket

```text
rankCutSource subset sourceChart '' (W cap sourceCylinder),
sourceCylinder = {z | z.1.yNext in signedBoxSet Rres}.
```

If the basepoint already satisfies

```text
z0.1.yNext in signedBoxSet Rres,
```

then the source cylinder is an open neighborhood of `z0`.  Indeed, the signed
box is open and `z -> z.1.yNext` is continuous.  Running the strict
source-cylinder theorem inside

```text
G cap sourceCylinder
```

returns

```text
V subset W subset G cap sourceCylinder.
```

The rank-cut image equality gives

```text
rankCutSource subset sourceChart '' V.
```

Thus for `E in rankCutSource`, write `E = sourceChart z` with `z in V`.
Since `V subset W` and `W subset sourceCylinder`, the same witness satisfies
`z in W cap sourceCylinder`, giving the required source-cylinder support.

## Lean artifact

The new declaration is:

```text
exists_open_residualSourceHypotheses_originalEdgeFamilyPrior_rankCutP13Readback_case2PassiveThetaWithFollowingFactor_of_z0_yNext_mem_signedBox_of_sourceDensity_continuousAt_lt_top_strict_sourceDensity_lower_strict_priorDensity_upper_of_continuousAt_priorDensity_of_subset_detSector
```

in:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaOriginalPriorResidualRankCutBridge.lean
```

## Boundary

This removes only the terminal source-cylinder support hypothesis in the local
basepoint-in-box case.  For a fixed `Rres`, it still requires
`z0.1.yNext in signedBoxSet Rres`; positivity of the radii alone is not
enough.  It does not prove source-density positivity, prior-density strict
upper bounds, determinant/raw Haar transport, source-prior transport,
source-rank or atlas coverage, normal crossings, pole order, or RLCT
extraction.
