# Statement Card - A5 Lemma 5 Counted Datum Injection

## Lean Names

- `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedNonbaseFamily.countDatumOfBranchCoord_injOn`
- `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedNonbaseFamily.countDatumClassifierOfBranchCoord_of_branchCoord_eq`
- `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedBinaryNonbaseFamily.countDatumOfBranchCoord`
- `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedBinaryNonbaseFamily.countDatumClassifierOfBranchCoord`
- `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedBinaryFamily.countDatumOfBranchCoord`
- `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedBinaryFamily.countDatumClassifierOfBranchCoord`

## Claim

For a supplied nonbase branch family, a correct supplied branch-coordinate map
already makes the counted-datum map injective on the full branch set.

The counted datum is:

```text
none    |-> none
some b  |-> some (branchCoord b, F.value b).
```

If two nonbase branches have equal counted datum, their supplied coordinates
are equal and their supplied values are equal.  The coordinate equality puts
them in the same coordinate branch set, and the supplied per-coordinate
injectivity of `F.value` proves the branches are equal.

## Inputs

- A supplied nonbase family `F : AoyagiLemma5SuppliedNonbaseFamily`.
- A map `branchCoord : beta -> Nat`.
- A supplied correctness proof:

```text
b in F.branches j  =>  branchCoord b = j.
```

The binary-family wrappers use only the underlying nonbase-family fields.

## Proves

```text
Set.InjOn (F.countDatumOfBranchCoord branchCoord) F.fullBranches
```

and therefore builds the existing `AoyagiLemma5CountDatumClassifier` without
requiring a separate tagged-classifier injectivity hypothesis.

For `AoyagiLemma5SuppliedBinaryNonbaseFamily` and
`AoyagiLemma5SuppliedBinaryFamily`, Lean exposes the same counted datum and
classifier through the binary namespaces.

## Does Not Prove

- Construction of the supplied branch family from Aoyagi's printed equations.
- Source proof of coordinate-wise value coverage.
- Source proof of `value` injectivity or branch-coordinate correctness.
- Back-to-label coverage, terminal-label exactness, pole order, normal
  crossings, or RLCT extraction.

## Source

This is source-independent finite supplied-data bookkeeping below Aoyagi Lemma
5.  It does not use a new citation boundary.
