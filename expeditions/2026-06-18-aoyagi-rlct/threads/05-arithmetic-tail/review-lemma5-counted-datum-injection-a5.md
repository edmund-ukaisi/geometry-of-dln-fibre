# Review - Lemma 5 counted datum injection

Reviewer: Gibbs, xhigh-effort subagent.
Date: 2026-06-21.

## Verdict

No mathematical or Lean correctness blockers.

The only review finding was a documentation hygiene issue: the ledgers already
referenced this review artifact before it existed.  This file resolves that
gap.

## Checks

- `AoyagiLemma5SuppliedNonbaseFamily.countDatumOfBranchCoord_injOn` is
  mathematically correct.
- The dependent-pair step is safe because `AoyagiLemma5CountDatum` is
  `Option (Sigma fun _ : Nat => Int)`, whose second component type is constant.
  Thus `congrArg Sigma.fst` gives equality of the branch-coordinate tags and
  `congrArg Sigma.snd` gives equality of the integer values.
- The proof uses `branchCoord_eq`, membership in `F.fullBranches`, and
  per-coordinate `F.value_injective`.
- The proof does not use `branches_pairwiseDisjoint`, `value_image`,
  `baseValue_mem`, binary deltas, terminal `H`, base `H`, normal crossings, or
  RLCT extraction.
- The binary nonbase and binary full-family wrappers are convenience wrappers
  over the underlying nonbase-family proof and do not add source content.

## Follow-Up Delta

The reviewer noted that `countDatumClassifierOfBranchCoord_of_branchCoord`
would be clearer as a name ending in `branchCoord_eq`, because the decisive
extra hypothesis is the coordinate-correctness proof.  The final slice uses:

```text
AoyagiLemma5SuppliedNonbaseFamily.countDatumClassifierOfBranchCoord_of_branchCoord_eq
```

## Boundary

This slice does not construct Aoyagi's printed branch family, prove source
value-injectivity, prove source branch-coordinate correctness, prove
back-to-label coverage, identify pole order, prove normal crossings, or extract
RLCT data.

## Verification

The reviewer ran:

```text
lake env lean DLNFibre/DLN/Aoyagi/Lemma5SuppliedFamily.lean
git diff --check be824d3
```

and found no forbidden placeholders in the reviewed slice.  The controller
also ran the module build, full `DLNFibre` build, placeholder scanner, and
`git diff --check`.
