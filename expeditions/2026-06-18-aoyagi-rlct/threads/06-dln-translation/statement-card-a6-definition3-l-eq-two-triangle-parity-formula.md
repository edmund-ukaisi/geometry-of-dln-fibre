# Statement card - A6 Definition 3 `L=2` triangle parity formula package

Date: 2026-06-24.

## Lean declarations

File:
`lean/DLNFibre/DLN/Aoyagi/Definition3Bridge.lean`

New theorems:

```text
AoyagiDefinition3SourceData.exists_consecutive_three_widths_theorem2Formula_of_triangle_odd_rankWidth
AoyagiDefinition3SourceData.exists_consecutive_three_widths_theorem2Formula_of_triangle_even_rankWidth
```

Follow-up no-`hr` wrappers:

```text
AoyagiDefinition3SourceData.exists_consecutive_three_widths_theorem2Formula_of_triangle_odd
AoyagiDefinition3SourceData.exists_consecutive_three_widths_theorem2Formula_of_triangle_even
```

See
`statement-card-a6-definition3-l-eq-two-branch-formula-rankwidth-removal.md`.

## Statement

For the all-source `L=2`, `ell=2` triangle branch, the previous formula theorem
required a supplied positive-remainder decomposition

```text
w1+w2+w3 = 2*ceilPred+a,   0<a<=2.
```

The new theorems derive that decomposition from parity of
`T = w1+w2+w3`.

Odd branch:

```text
T % 2 = 1
ceilPred = T/2
ceilWidth = T/2 + 1
aParam = 1
order = 2
```

Even branch:

```text
T % 2 = 0
ceilPred = T/2 - 1
ceilWidth = T/2
aParam = 2
order = 1
```

Both theorems retain the all-source cutpoint construction, Definition 3 source
data, selected-width Nat/nonnegativity/strictness provenance, selected pair
sum

```text
w1*w2 + w1*w3 + w2*w3
```

and the corresponding finite Theorem 2 lambda formula.

The later no-`hr` wrappers derive the usual source-range rank-width hypothesis
from the same concrete triangle inequalities via the all-source strict
rank-width theorem, then delegate to the `_rankWidth` parity theorems recorded
here.

## Source reproduction

`threads/06-dln-translation/reproduction-definition3-l-eq-two-triangle-parity-formula-a6.md`

## Verification

Focused elaboration passed:

```text
cd lean
LEAN_NUM_THREADS=1 ~/.elan/bin/lake env lean DLNFibre/DLN/Aoyagi/Definition3Bridge.lean
```

## Nonclaims

This is finite Definition 3/Theorem 2 arithmetic only.  It does not classify
`L>2`, choose between repeated-positive and triangle branches, add source-rank
wrappers or final sockets, construct Eq5 payloads or charts, prove normal
crossings, identify pole order, or extract RLCT.
