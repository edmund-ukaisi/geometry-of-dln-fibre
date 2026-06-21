# Reproduction - Lemma 5 Full Supplied Family Base Branch

Status: supplied-data boundary; ready for a narrow Lean wrapper.

This note strengthens the supplied chart-family count boundary by making the
leading `1` in

```text
1 + sum_j (|I_j|-1) = a(ell-a)+1
```

an explicit supplied base branch.  It still does not construct Aoyagi's printed
branch family.

## Source Boundary

Aoyagi Lemma 5, PDF pp. 25-27, counts the interior same-coordinate intervals
and adds one base contribution.  After the printed-equation obstruction
checkpoint, the existence and admissibility of that full family must remain
supplied.

## Supplied Encoding

Let `B_j` be the already-supplied nonbase branch set at coordinate `j`.  Encode
the full finite family by

```text
FullBranches = {none} union union_j {some b : b in B_j}.
```

The constructor `none` is the supplied base branch.  The constructor `some`
embeds nonbase branches into a type disjoint from the base branch.

The previous supplied boundary gives:

```text
1 + |union_j B_j| = a(ell-a)+1,
```

where the union count uses supplied cross-coordinate disjointness of the
`B_j`.

Because `none` is not in the image of `some`, and `some` is injective,

```text
|FullBranches|
  = 1 + |union_j {some b : b in B_j}|
  = 1 + |union_j B_j|
  = a(ell-a)+1.
```

The admissible full-family extension supplies a base `H`-chain with the same
Lemma 4 witness fields as the nonbase branches:

```text
H_0 = M(S_1),
Htilde <= H <= Htilde',
H_{r-1} - H_r + M(S_{r+1}) is M-1 or M for every r.
```

Then the existing Lemma 4 bridge proves the base branch's two-value count.  The
nonbase branch count remains the inherited theorem from the previous supplied
boundary.

## Lean Targets

```text
AoyagiLemma5SuppliedNonbaseFamily.fullBranches
AoyagiLemma5SuppliedNonbaseFamily.fullBranches_card
AoyagiLemma5SuppliedAdmissibleFamily
AoyagiLemma5SuppliedAdmissibleFamily.base_twoValueCount
```

## Kill Conditions

- Do not treat the base branch as constructed from Aoyagi's printed formulas.
- Do not use `none` as more than a finite bookkeeping tag.
- Do not claim source-backed Lemma 5 order count; the branch family and base
  admissibility are supplied.
- Do not prove or cite normal crossings or RLCT extraction here.

## Nonclaims

- No displayed vector is constructed.
- No source-label legality is proved.
- No Case 1(2) chart sequence is reconstructed.
- No terminal `tilde t=0`, pole-order interpretation, normal-crossing
  resolution, or RLCT extraction is proved.
