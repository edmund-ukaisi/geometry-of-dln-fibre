# Pen-and-paper reproduction - Lemma 5 equation (4) p=2 boundary membership example

Status: checked finite guardrail example.

This note records a concrete constant-width example showing that the
source-selected obstruction

```text
boundary-coordinate membership => 2 <= p
```

is only a necessary condition.  It is not a uniform nonmembership theorem once
`p>=2`.

## Source

Aoyagi PDF p. 27, equation `(4)`, supplies the strict boundary value

```text
B = T(S_(p+ell-a+2)-1) = Htilde'_(p+ell-a) - p + 1.
```

The already-formalised boundary-coordinate window says that, for

```text
r = p+(ell-a)+1,
W_r = M(S_(r+1)),
```

membership in the boundary-coordinate interval is equivalent to

```text
M-p+1 <= W_r <= M-p+1+min(ell-a,a-p-1).
```

## Example

Take

```text
ell = 5,
a = 4,
p = 2,
M = 5,
W_i = 4 for all i = 0,...,5.
```

Then there are six selected widths, so

```text
sum_i W_i = 6*4 = 24,
ell*(M-1)+a = 5*4+4 = 24.
```

For every selected index,

```text
ell*W_i = 5*4 = 20 < 24 = sum_j W_j,
```

so the Definition 3-shaped selected-width hypotheses hold.  The strict
boundary guard also holds:

```text
p+1<a  means  3<4.
```

The boundary coordinate is

```text
r = p+(ell-a)+1 = 2+1+1 = 4.
```

At that coordinate,

```text
W_r = 4,
M-p+1 = 5-2+1 = 4,
min(ell-a,a-p-1) = min(1,1) = 1.
```

Thus the width window is

```text
4 <= W_r <= 5,
```

which holds because `W_r=4`.  Therefore, for any supplied equation `(4)`
piecewise certificate with these constants, the boundary value lies in the
boundary-coordinate interval.

## Guard Check

This example does not satisfy the earlier own-coordinate guard

```text
p <= ell-a,
```

since `2<=1` is false.  That is intentional: the previous same-coordinate
classifier at coordinate `p+(ell-a)` needs that guard, but the
boundary-coordinate membership theorem at coordinate `p+(ell-a)+1` does not.

## Lean Target

```text
aoyagiLemma5Eq4_boundaryValue_mem_boundaryInterval_p2_constantWidth_example
aoyagiLemma5Eq4_boundaryValue_mem_boundaryInterval_p2_constantWidth_sourceSelected_example
```

## Nonclaims

- This does not construct equation `(4)`'s supplied piecewise certificate.
- This does not construct the displayed source vector.
- This does not prove terminal `tilde t=0`.
- This does not prove introduced-label status, a Case 1(2) chart sequence,
  vector admissibility, Lemma 5 order count, normal crossings, or RLCT
  extraction.
