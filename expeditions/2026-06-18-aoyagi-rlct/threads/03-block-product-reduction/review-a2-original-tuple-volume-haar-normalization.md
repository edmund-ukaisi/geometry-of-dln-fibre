# Review - A2 Original Tuple Volume Haar Normalization

Date: 2026-06-30.

Reviewer: xhigh `Kant the 2nd`.

Verdict: PASS after repair.

## Initial Finding

The first version proved the Haar-normalization facts correctly, but exported
duplicate global `Matrix ... ℝ` topology/Borel instances that overlapped with
the existing generic instances in `ChartTopology.lean`.

Required change:

- remove the duplicate global matrix topology/Borel instances;
- reuse the existing `ChartTopology` instances;
- keep any remaining local-compactness bridge proof-local if needed for Haar
  uniqueness.

## Repair

`OriginalPriorHaar.lean` now imports `ChartTopology` and exports no duplicate
matrix topology/Borel instances. The only additional local-compactness bridge
is a proof-local `haveI` inside
`originalTupleVolume_eq_addHaarScalarFactor_smul`.

The reproduction and statement card were updated to match this implementation.

## Checks

Reviewer read-only checks:

```text
lake env lean DLNFibre/DLN/Aoyagi/OriginalPriorHaar.lean
lake env lean DLNFibre.lean
```

Controller verification after repair:

```text
env LEAN_NUM_THREADS=3 lake env lean DLNFibre/DLN/Aoyagi/OriginalPriorHaar.lean
env LEAN_NUM_THREADS=3 lake build DLNFibre.DLN.Aoyagi.OriginalPriorHaar
env LEAN_NUM_THREADS=3 lake env lean DLNFibre.lean
env LEAN_NUM_THREADS=3 lake build DLNFibre
./scripts/sorries
git diff --check
env LEAN_NUM_THREADS=3 lake env lean /tmp/aoyagi_original_prior_haar_axioms.lean
```

The axiom probe reports only:

```text
[propext, Classical.choice, Quot.sound]
```

## Nonclaims Checked

No chart-transport overclaim was found. The theorem proves Haar normalization
and scalar comparison for original tuple volume only. It does not prove
retained-passive or selected-entry chart-produced source-image measure
equality, chart-piece equality, readback domination, Aoyagi chart
Haar/Jacobian transport, source-rank coverage, normal crossings, pole order, or
RLCT extraction.
