# Statement card - A6 Definition 3 exact ceiling data

## Declarations

```text
DLNFibre.DLN.Aoyagi.AoyagiDefinition3CeilData.ofSelectedSumCeil
DLNFibre.DLN.Aoyagi.AoyagiDefinition3CeilData.ofSelectedSumCeil_ceilWidth
DLNFibre.DLN.Aoyagi.AoyagiDefinition3CeilData.ofSelectedSumCeil_aParam
```

## Files

```text
lean/DLNFibre/DLN/Aoyagi/FinalFormula.lean
lean/DLNFibre/DLN/Aoyagi/Definition3Bridge.lean
```

## Statement

For any integer selected-width family `m : Fin (ell + 1) -> Int` and
`0 < ell`, `ofSelectedSumCeil` constructs `AoyagiDefinition3CeilData ell m`
with

```text
ceilWidth = (sum_j m_j + ell - 1) / ell
aParam    = ((sum_j m_j - 1) % ell + 1).toNat.
```

The older existential theorem

```text
AoyagiDefinition3CeilData.nonempty_of_ell_pos
```

now delegates to this exact constructor.

## Role

This removes a small existential looseness in the Theorem 2 formula layer:
the ceiling integer and positive residue are now pinned to Aoyagi's displayed
ceiling convention rather than merely being shown to exist.

## Boundary

This is formula arithmetic only.  It does not construct selected cutpoints,
prove Definition 3 source data, repair the printed inactive inequality, prove
normal crossings, compute pole order, prove RLCT extraction, or use Core/quiver
codimension facts.

## Verification

Focused builds passed:

```text
cd lean
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.FinalFormula
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.Definition3Bridge
```

