# Reproduction - counted-datum injection for supplied branches

Date: 2026-06-21.

Scope: supplied-data injection for the label-free counted-datum classifier in
Aoyagi Lemma 5.  This does not construct Aoyagi's displayed source branches,
prove coordinate-wise value coverage from equations `(3)`, `(4)`, `(5)`,
prove source label legality, prove pole order, normal crossings, or extract
RLCT data.

## Setup

Let `F` be a supplied nonbase family.  Thus, for every interior coordinate
`j=1,...,ell-1`, `F.branches j` is a finite set of branches, `F.value` maps
branches to integer same-coordinate values, and the structure supplies:

- injectivity of `F.value` on each `F.branches j`;
- disjointness of `F.branches i` and `F.branches j` for `i != j`;
- interval image coverage and base-value membership.

For the classifier injection only the first bullet is relevant.  Disjointness
is needed elsewhere for branch counting, but the tagged coordinate itself
separates different coordinate branch sets.  Suppose also a supplied coordinate
map

```text
branchCoord : beta -> Nat
```

satisfies

```text
b in F.branches j  =>  branchCoord b = j.
```

Define the counted datum on full branches by

```text
none    |-> none
some b  |-> some (branchCoord b, F.value b).
```

## Injection Check

Take two full branches with equal counted datum.

If one is `none` and the other is `some b`, equality is impossible because
`none != some (...)`.  The same holds in the opposite order.  If both are
`none`, they are equal.

It remains to consider `some b` and `some c`.  Membership in `F.fullBranches`
gives interior coordinates `j,k` with

```text
b in F.branches j,
c in F.branches k.
```

The supplied coordinate equation gives

```text
branchCoord b = j,
branchCoord c = k.
```

Equality of counted data gives equality of the tagged pairs

```text
(branchCoord b, F.value b) = (branchCoord c, F.value c).
```

Therefore `branchCoord b = branchCoord c`, so `j=k`.  The same tagged-pair
equality also gives

```text
F.value b = F.value c.
```

Now both `b` and `c` lie in the same finite branch set `F.branches j`, and
`F.value` is injective there.  Hence `b=c`, so `some b = some c`.

## Binary-Family Bridge

A supplied binary nonbase family extends the same nonbase family.  The
counted-datum classifier does not use terminal `H`, binary deltas, or the base
`H` chain.  It can therefore reuse the supplied-family injection proof
directly, with the same branch-coordinate hypothesis.  A full binary family
inherits the same wrapper as API bookkeeping, not new source content.

## Formalisation Boundary

The Lean slice should add:

```text
AoyagiLemma5SuppliedNonbaseFamily.countDatumOfBranchCoord_injOn
AoyagiLemma5SuppliedNonbaseFamily.countDatumClassifierOfBranchCoord_of_branchCoord_eq
AoyagiLemma5SuppliedBinaryNonbaseFamily.countDatumOfBranchCoord
AoyagiLemma5SuppliedBinaryNonbaseFamily.countDatumClassifierOfBranchCoord
AoyagiLemma5SuppliedBinaryFamily.countDatumOfBranchCoord
AoyagiLemma5SuppliedBinaryFamily.countDatumClassifierOfBranchCoord
```

The important negative statement is that this does not prove the supplied
branch family fields from Aoyagi's PDF.  In particular, the source obstruction
to Case 1(2) nonduplication is shifted into supplied `value_injective` and
branch-coordinate correctness; it is not solved from the printed paragraph.
