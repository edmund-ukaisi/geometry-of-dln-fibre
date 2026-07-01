# Review - A2 p.13 Formal-product Density Identity

Date: 2026-07-01.

Status: PASS after Lean implementation and verification.

## Check

The intended proof is exactly scalar bookkeeping:

```text
formal = c • original
0 < c
original = c^{-1} • formal
formal.withDensity (fun _ => c^{-1}) = c^{-1} • formal
```

Restricting the constant-density identity to the chart piece matches the
already-proved inverse-scalar corollary. The a.e. bound is reflexivity.

## Verification

Passed:

```text
lake env lean DLNFibre/DLN/Aoyagi/OriginalEdgeFamilyP13SourceMeasureBridge.lean
lake build DLNFibre.DLN.Aoyagi.OriginalEdgeFamilyP13SourceMeasureBridge
lake env lean DLNFibre.lean
lake build DLNFibre
./scripts/sorries
git diff --check
lake env lean /tmp/aoyagi_formal_product_density_axioms.lean
```

The direct axiom probe reports only:

```text
[propext, Classical.choice, Quot.sound]
```

## Nonclaims

This is not passive-theta source-image equality, source-prior transport,
source coverage, scalar normalization, normal crossings, pole order, or RLCT
extraction.
