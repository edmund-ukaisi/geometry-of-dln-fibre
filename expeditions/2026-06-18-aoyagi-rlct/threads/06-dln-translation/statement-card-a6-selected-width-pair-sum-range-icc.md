# Statement card - A6 selected-width pair sum range/Icc form

## Declaration

```text
DLNFibre.DLN.Aoyagi.aoyagiSelectedWidthPairSum_eq_range_Icc_selectedWidthNat
```

## File

```text
lean/DLNFibre/DLN/Aoyagi/FinalFormula.lean
```

## Statement

For any selected-width family `m : Fin (ell + 1) -> Int`, Aoyagi Theorem 2's
finite pair sum in `Fin`/indicator form equals the Nat-indexed strict
upper-triangle sum:

```text
aoyagiSelectedWidthPairSum ell m =
  sum i in range (ell+1), sum j in Icc (i+1) ell,
    aoyagiSelectedWidthNat ell m i *
    aoyagiSelectedWidthNat ell m j.
```

## Role

This is source-facing finite formula bookkeeping.  It prepares the
Theorem 2 formula layer for later comparison with range/Icc summation APIs
without importing `Core` or choosing a Definition 3 branch.

## Boundary

The theorem does not prove selected cutpoint existence, branch independence,
the corrected `paperEll` cutoff, normal crossings, pole order, RLCT, or any
Core/quiver codimension statement.

## Verification

Focused build passed:

```text
cd lean
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.FinalFormula
```

