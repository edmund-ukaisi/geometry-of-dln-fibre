# Reproduction - Definition 3 `L=2`, `ell=1` Repeated Formula Branch

Date: 2026-07-02.

Status: controller reproduction; Lean target selected.

## Source Anchor

Aoyagi Definition 3 on PDF pp. 8-9 supplies the finite selected-width
inequalities.  The existing Lean branch package reproduces the finite Theorem
2 formula arithmetic for the `L=2` repeated-positive `ell=1` branch.  This
slice is only a fixed-`ell=1` dispatch theorem.

## Claim

Given

```text
S : AoyagiDefinition3SourceData 2 1 H r C
```

and Nat witnesses

```text
M^(1)=w1,   M^(2)=w2,   M^(3)=w3,
```

the finite Theorem 2 branch package is the repeated-positive package:

```text
L2RepeatedPositiveTheorem2FormulaBranch H r w1 w2 w3.
```

This does not say that no triangle package can also exist for the same width
profile; it only records the branch forced by the supplied `ell=1` datum.

## Calculation

The extracted classifier

```text
exists_ell_one_sourceData_iff_repeatedPositive_of_L_eq_two
```

turns `S` into

```text
0 < M^(1),   0 < M^(2),   0 < M^(3),
```

and one repeated-value equality among the three source-range reduced widths.
Using the Nat-width identities, these become

```text
0 < w1,   0 < w2,   0 < w3,
```

and one of

```text
w1 = w2,   w1 = w3,   w2 = w3.
```

Now call the existing repeated-positive finite formula constructor:

```text
exists_ell_one_theorem2Formula_of_L_eq_two_positive_repeated.
```

The Nat-width wrapper first obtains `w1,w2,w3` from the supplied `ell=1`
source datum via the existing `L=2` source-data Nat-width extraction and then
applies the fixed-`ell=1` branch theorem.

## Lean Shape

Add in `lean/DLNFibre/DLN/Aoyagi/Definition3Bridge.lean`:

```text
AoyagiDefinition3SourceData.exists_L_eq_two_ell_one_theorem2Formula_repeatedBranch_of_sourceData
AoyagiDefinition3SourceData.exists_L_eq_two_ell_one_theorem2Formula_repeatedBranch_of_sourceData_natWidths
```

## Nonclaims

No repeated-branch exclusivity for arbitrary `L=2` source data, no claim that
triangle branches cannot overlap, no branch-independent lambda/order payload,
no Eq5 payload, no chart production, no normal crossings, no pole order, and
no RLCT extraction.
