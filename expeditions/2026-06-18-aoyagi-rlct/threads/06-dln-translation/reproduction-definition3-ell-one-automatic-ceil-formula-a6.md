# Reproduction - A6 Definition 3 `ell=1` automatic ceiling formula

Date: 2026-06-24.

Status: pen-and-paper reproduction before Lean implementation.

## Question

The earlier safe `ell=1` selected-pair formula package required a supplied
equation

```text
u + v = ceilPred + 1.
```

For `ell=1`, this is unnecessary finite arithmetic.  Definition 3's
ceiling/residue datum can be constructed directly from the selected pair.

## Source Anchor

Aoyagi PDF pp. 8-9 define Definition 3's selected widths and the Theorem 2
formula.  For `ell=1`, there are two selected widths:

```text
m0 = u,
m1 = v.
```

The selected sum is `T = u+v`.

## Ceiling Datum

Definition 3's datum has fields satisfying

```text
T = ell*(ceilWidth - 1) + a,
0 < a <= ell.
```

When `ell=1`, set

```text
ceilWidth = u+v,
a = 1.
```

Then

```text
1*((u+v)-1) + 1 = u+v = T.
```

The positivity and upper bound for `a` are immediate:

```text
0 < 1 <= 1.
```

## Order and Lambda

The order formula is

```text
a*(ell-a)+1 = 1*(1-1)+1 = 1.
```

For `ell=1`, the selected pair sum has one term:

```text
aoyagiSelectedWidthPairSum 1 m = u*v.
```

The Theorem 2 lambda formula simplifies because

```text
a*(ell-a)/(4*ell) = 0,
ell*(ell-1)/4 = 0.
```

Therefore

```text
aoyagiTheorem2Lambda_fromCeilData 2 1 H r m data
  = aoyagiTheorem2RegularTerm 2 H r + u*v/2.
```

## Lean Target

The theorem should have the same source hypotheses as the selected-pair
remainder package except for the deleted `ceilPred` and remainder equation.  It
should conclude:

```text
data.ceilWidth = u+v,
data.aParam = 1,
data.theorem2OrderFormula = 1,
pairSum = u*v,
lambda = regularTerm + u*v/2.
```

## Guardrails

This is finite Definition 3 arithmetic only.  It does not choose selected
cutpoints from a repeated branch, construct Eq5 payloads or charts, prove
normal crossings, identify pole order, or extract RLCT.
