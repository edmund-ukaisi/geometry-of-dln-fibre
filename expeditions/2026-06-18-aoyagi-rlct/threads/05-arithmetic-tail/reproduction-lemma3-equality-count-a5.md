# Pen-and-paper reproduction - Lemma 3 equality count

Status: checked sub-slice.  This counts only the integer values of the Lemma 3
parameter `b` in the source interval that attain the isolated cleared numerator
lower bound.  It does not count admissible exponent chains, Lemma 5 chart
coordinates, pole-order variables, normal crossings, or RLCT data.

## Setup

Use the equality classification already reproduced:

```text
A(b) = a ell (ell-a)
  iff (b=a and a <= ell-1) or (b=a-1 and 1 <= a)
```

for `b` in the source interval

```text
0 <= b <= ell-1
```

under `1 <= ell`.

Assume additionally

```text
0 <= a <= ell.
```

## Count

The feasible equality candidates are the intersection of the source interval
with the two algebraic candidates:

```text
b = a      feasible iff a <= ell-1;
b = a - 1  feasible iff 1 <= a.
```

The cases are:

```text
a = 0:
  b=a=0 is feasible;
  b=a-1=-1 is not feasible.
  Count: 1.

0 < a < ell:
  1 <= a and a <= ell-1;
  both b=a-1 and b=a are feasible;
  they are distinct.
  Count: 2.

a = ell:
  b=a=ell is not feasible;
  b=a-1=ell-1 is feasible.
  Count: 1.
```

The small case `ell=1` is consistent: there is no strict interior integer
`a`, and the endpoints `a=0` and `a=ell=1` each leave the single source value
`b=0`.

Equivalently, for the finite equality set

```text
M(ell,a) = { b in Z : 0 <= b <= ell-1 and A(b)=a ell (ell-a) },
```

the endpoint-corrected cardinality is

```text
|M(ell,a)| = 1 + indicator(0 < a < ell).
```

## Lean Boundary

This supports only:

- defining the finite source-interval equality set;
- proving it is `{0}` at `a=0`;
- proving it is `{ell-1}` at `a=ell`;
- proving it is `{a-1,a}` when `0<a<ell`;
- deriving the cardinality formula `1 + if 0<a<ell then 1 else 0`.

It does not prove that the counted values are terminal variables with
`\tilde t_{s,k}=0`, that they arise from feasible exponent chains, or that
they give the Lemma 5 order `a(ell-a)+1`.
