# Reproduction - Lemma 5 Full Supplied Family Branchwise Admissibility

Status: supplied-data boundary; ready for a narrow Lean wrapper.

This note packages the base and nonbase admissibility fields of the supplied
full family into one branchwise statement over the tagged branch type.

## Supplied Encoding

The full branch set is

```text
FullBranches = {none} union union_j {some b : b in B_j}.
```

Define the branch `H`-chain by cases:

```text
fullH(none) = baseH,
fullH(some b) = H(b).
```

Membership of a nonbase tagged branch is equivalent to membership in some
coordinate branch set:

```text
some b in FullBranches
  iff exists j in {1,...,ell-1}, b in B_j.
```

The reverse direction is the already-proved insertion into the full branch
set.  The forward direction uses that `some b` is not `none`, so it must lie in
the union of `some`-images; injectivity of the constructor gives a witness
`b in B_j`.

## Branchwise Lemma 4 Count

Assume the source arithmetic hypotheses used by the existing Lemma 4 bridge:

```text
a <= ell,
sum_i M(S_i) = ell*(M-1)+a.
```

Let `x in FullBranches`.

- If `x = none`, then `fullH x = baseH`, and the supplied base Lemma 4 fields
  give the two-value count by the existing Lemma 4 bridge.
- If `x = some b`, the membership equivalence gives a coordinate `j` and
  `b in B_j`.  The inherited admissible nonbase fields give the same
  two-value count by the existing nonbase branch theorem.

Thus every supplied full branch satisfies Lemma 4's finite two-value count.

## Lean Targets

```text
AoyagiLemma5SuppliedNonbaseFamily.some_mem_fullBranches_iff
AoyagiLemma5SuppliedAdmissibleFamily.fullH
AoyagiLemma5SuppliedAdmissibleFamily.fullBranch_twoValueCount
```

## Kill Conditions

- Do not infer membership or admissibility from Aoyagi's printed equations.
- Do not claim this proves source-label legality or chart construction.
- Do not use this as a pole-order, normal-crossing, or RLCT theorem.

## Nonclaims

- No displayed vector is constructed.
- No source-backed full family is constructed.
- No Case 1(2) chart sequence is reconstructed.
- No terminal `tilde t=0`, pole-order interpretation, normal-crossing
  resolution, or RLCT extraction is proved.
