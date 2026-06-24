# Reproduction - A6 Definition 3 `L=2` repeated-positive formula package

Date: 2026-06-24.

Status: pen-and-paper reproduction before Lean implementation.

## Question

For `L=2`, the already-formalised Definition 3 classification says source-data
existence is equivalent to either:

- the repeated-positive branch: the three source-range reduced widths are
  positive and at least two are equal; or
- the all-source triangle branch.

The triangle branch already has an explicit finite Theorem 2 formula package.
The remaining repeated-positive formula package should remove the supplied
selected pair from the earlier safe `ell=1` theorem, but without pretending that
there is a canonical selected pair independent of the repeated equality.

## Source Anchor

Aoyagi PDF pp. 8-9 defines the selected cutpoints and Theorem 2 formula.  For
`L=2`, there are three source-range reduced widths:

```text
w1 = M^(1),   w2 = M^(2),   w3 = M^(3).
```

In the repeated-positive branch, all three are positive and at least one of
`w1=w2`, `w1=w3`, `w2=w3` holds.  Definition 3 with `ell=1` selects two
cutpoints, so the selected value set must cover all three width values.

## Branch Choices

The selected pair can be chosen by the repeated equality:

```text
if w1 = w2, select cutpoints (1,3), so (u,v)=(w1,w3);
if w1 = w3, select cutpoints (1,2), so (u,v)=(w1,w2);
if w2 = w3, select cutpoints (1,2), so (u,v)=(w1,w2).
```

In each branch, every one of `w1,w2,w3` lies in the selected value set
`{u,v}`.  The selected values are positive because the source widths are
positive.  Therefore the existing constructor

```text
of_ell_eq_one_selectedValueSet_covers
```

builds `AoyagiDefinition3SourceData 2 1 H r C`.

## Automatic `ell=1` Ceiling Datum

Before the repeated-positive branch theorem, isolate the finite `ell=1`
ceiling arithmetic.  For selected widths `u,v`, the selected sum is

```text
T = u+v.
```

Definition 3 asks for `ceilWidth` and `aParam` such that

```text
T = ell*(ceilWidth-1) + aParam,
0 < aParam <= ell.
```

When `ell=1`, choose

```text
ceilWidth = u+v,
aParam    = 1.
```

Then

```text
1*((u+v)-1) + 1 = u+v.
```

Thus the previously supplied decomposition `u+v=ceilPred+1` is unnecessary
finite arithmetic in the `ell=1` selected-pair package.

## Repeated-Branch Ceiling Datum

The repeated branch can now choose `ceilWidth` directly from the selected pair.
No separate quotient/remainder input is needed:

```text
if w1 = w2, selected (u,v)=(w1,w3), so ceilWidth = w1+w3;
if w1 = w3, selected (u,v)=(w1,w2), so ceilWidth = w1+w2;
if w2 = w3, selected (u,v)=(w1,w2), so ceilWidth = w1+w2.
```

In all cases `aParam=1` and the order formula is

```text
1 * (1 - 1) + 1 = 1.
```

## Pair Sum and Lambda

For `ell=1`, there is exactly one selected pair, hence

```text
aoyagiSelectedWidthPairSum 1 m = u*v.
```

In the Theorem 2 lambda formula, the selected-average square coefficient is
zero because `ell*(ell-1)/4 = 0`, and the residue term is zero because
`a=ell=1`.  Thus the finite formula simplifies to

```text
aoyagiTheorem2Lambda_fromCeilData 2 1 H r m data
  = aoyagiTheorem2RegularTerm 2 H r + u*v/2.
```

## Lean Target

The intended theorem should consume:

- identifications `M^(s)=ws` for `s=1,2,3`;
- positivity of `w1,w2,w3`;
- a disjunction of repeated-equality branches;
- source-range rank-width, needed to rewrite selected widths as Nat
  differences.

It should produce selected cutpoints `C`, selected values `u,v`, selected
widths `m`, and ceiling data `data`, together with the source data, explicit
ceiling fields `data.ceilWidth = u+v`, order formula, selected-width
provenance, pair sum, and lambda formula.

## Guardrails

This slice must not:

- assert a unique or canonical selected pair for repeated-positive profiles;
- add source-rank wrappers or final sockets;
- construct Eq5 payloads, chart certificates, normal crossings, pole order, or
  RLCT.
