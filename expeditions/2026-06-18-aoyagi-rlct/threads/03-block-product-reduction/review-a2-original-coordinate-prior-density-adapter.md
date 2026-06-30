# Review - A2 Original Coordinate Prior And Density Adapter

Date: 2026-06-30.

## Verdict

PASS. Xhigh reviewer `Laplace the 2nd` found no blocking formal, mathematical,
or source-fidelity issue in the current diff.

## Mathematical Scope

The generic helper

```text
restrict_withDensity_le_smul_of_restrict_le_smul_of_ae_le
```

assumes an unweighted local domination and an a.e. density upper bound, then
proves exactly

```text
(mu.withDensity f).restrict s <= (C * c) • nu.
```

It does not assert chart transport or source-image comparison.  The
`OriginalPrior` module only names product Lebesgue measure on the flattened
coordinate space `RepCoord d -> Real`, its prior-weighted variant, and local
domination by restricted coordinate volume under a density bound.

## Source Fidelity

The docs correctly keep the Aoyagi source boundary: pp. 5 and 8 support a
smooth compactly supported prior and local boundedness after a valid
coordinate transport; pp. 10-13 support the p.13 coordinate algebra.  The
transport from flattened original coordinates through the Aoyagi source chart
to the retained-passive chart-produced measure remains open.

## Fixes Applied

The reviewer requested replacing ambiguous measure-scalar notation such as
`c * nu` with `c • nu` in the new cards.  This was applied.

The reviewer also noted that the helpers record domination but do not require
finite scalar bounds.  The Lean docstrings and cards now state that finiteness
is a downstream hypothesis when an integrability transfer needs it.

## Verification

```text
env LEAN_NUM_THREADS=3 lake env lean DLNFibre/DLN/Aoyagi/LocalMeasureHandoff.lean
env LEAN_NUM_THREADS=3 lake build DLNFibre.DLN.Aoyagi.LocalMeasureHandoff
env LEAN_NUM_THREADS=3 lake env lean DLNFibre/DLN/Aoyagi/OriginalPrior.lean
env LEAN_NUM_THREADS=3 lake build DLNFibre.DLN.Aoyagi.OriginalPrior
env LEAN_NUM_THREADS=3 lake env lean DLNFibre.lean
env LEAN_NUM_THREADS=3 lake build DLNFibre
./scripts/sorries
git diff --check
```

The new theorem axiom footprint is `[propext, Classical.choice, Quot.sound]`.

## Nonclaims

No theorem transports the flattened coordinate volume through an Aoyagi source
chart.  No source-image equality, source-rank coverage, Haar/Jacobian
transport, normal crossings, pole order, or RLCT extraction is proved.
