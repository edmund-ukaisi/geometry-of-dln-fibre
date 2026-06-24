# Statement card - A6 Definition 3 equal-width explicit ceiling data

Date: 2026-06-24.

## Claim

In Aoyagi's equal-width example, suppose the common reduced width `w` has a
positive-remainder decomposition

```text
w = L*q + a,    0 < a <= L.
```

Then the Definition 3 ceiling datum for the constant selected-width family has

```text
ceilWidth = w + q + 1,
aParam = a.
```

Combining this with the equal-width consecutive cutpoint constructor gives a
source-facing package with explicit `ceilWidth` and `aParam`.

## Source Status

Aoyagi Definition 3 and the equal-width example on PDF pp. 8-9 state that for
`ell = L`,

```text
M - 1 < ((L + 1) M^(1)) / L <= M,
a = (L + 1) M^(1) - (M - 1)L.
```

The Lean names avoid the paper's overloaded `M`: `ceilWidth` is Aoyagi's
integer `M`, and `aParam` is Aoyagi's `a`.

## Pen-and-paper Reproduction

Reproduction:
`reproduction-definition3-equal-width-explicit-ceil-data-a6.md`.

Review:
`review-definition3-equal-width-explicit-ceil-data-a6.md`.

Verdict: pass.  The reviewer checked the PDF source anchor, the arithmetic
including the divisible case, and the nonclaims.

## Lean Status

File: `lean/DLNFibre/DLN/Aoyagi/Definition3Bridge.lean`.

```text
AoyagiDefinition3CeilData.equalWidthOfDecomposition
AoyagiDefinition3SourceData.exists_consecutive_explicitCeilData_of_constant_reducedWidth_decomposition
```

The first definition constructs the explicit ceiling datum for the constant
family `fun _ => w`.  The second theorem returns consecutive cutpoints,
equal-width source data, selected reduced widths, the explicit ceiling datum,
Nat-width rewrites, nonnegativity, strict selected inequalities, selected-width
upper bounds, and the pointwise equal-width identity.

## Nonclaims

No arbitrary Definition 3 selected-cutpoint existence, no uniqueness theorem
for `ceilWidth` or `aParam`, no automatic construction of the
positive-remainder decomposition for every `L,w`, no Eq5 payload, no finite
exponent formula, no chart production, no normal crossings, no pole order, and
no RLCT extraction.
