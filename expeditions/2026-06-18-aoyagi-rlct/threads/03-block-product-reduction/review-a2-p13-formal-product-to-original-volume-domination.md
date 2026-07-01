# Review - A2 p.13 Formal-product to Original-volume Domination

Date: 2026-07-01.

Status: PASS after Lean implementation and verification.

## Check

The proof uses only scalar bookkeeping:

```text
original = c^{-1} • formal
formal <= D • sourceRef
original <= (c^{-1} * D) • sourceRef
```

For the bounded-density variant, the only additional step is
`restrict_withDensity_le_smul_of_ae_le` applied to the supplied formal-product
source-reference density identity.

## Verification

Passed:

```text
lake env lean DLNFibre/DLN/Aoyagi/OriginalEdgeFamilyP13SourceMeasureBridge.lean
lake build DLNFibre.DLN.Aoyagi.OriginalEdgeFamilyP13SourceMeasureBridge
lake env lean DLNFibre.lean
lake build DLNFibre
./scripts/sorries
git diff --check
lake env lean /tmp/aoyagi_formal_to_original_domination_axioms.lean
```

The direct axiom probes for both public theorems report only:

```text
[propext, Classical.choice, Quot.sound]
```

## Nonclaims

This is not formal-product/source-reference transport, passive-theta
source-image equality, source-prior transport, source coverage, scalar
normalization, normal crossings, pole order, or RLCT extraction.
