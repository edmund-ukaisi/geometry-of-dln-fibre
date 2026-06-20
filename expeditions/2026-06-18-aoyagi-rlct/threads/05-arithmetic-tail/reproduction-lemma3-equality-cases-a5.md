# Pen-and-paper reproduction - Lemma 3 equality cases

Status: checked sub-slice.  This continues the isolated integer numerator
calculation for Aoyagi's Lemma 3 on PDF p. 24.  It classifies equality in the
cleared lower-bound arithmetic only.  It does not reproduce the terminal
candidate set, the `\tilde t_{s,k}=0` restriction, feasibility of exponent
chains, Lemma 4, Lemma 5, pole order, normal crossings, or RLCT extraction.

## Source Target

From the endpoint arithmetic reproduction, the cleared integer numerator is

```text
A(b) = a ell (ell-a) + ell^2 (b-a)(b-a+1).
```

The lower bound is `a ell (ell-a)`.  The equality question is therefore:

```text
A(b) = a ell (ell-a)
```

under the nondegenerate source hypothesis `ell != 0`.

## Equality Algebra

Subtract the lower-bound term:

```text
A(b) = a ell (ell-a)
  iff ell^2 (b-a)(b-a+1) = 0.
```

If `ell != 0`, then `ell^2 != 0`.  Since the integers have no zero divisors,

```text
ell^2 (b-a)(b-a+1) = 0
  iff (b-a)(b-a+1) = 0
  iff b-a = 0 or b-a+1 = 0
  iff b = a or b = a-1.
```

Conversely, both candidates make the consecutive product vanish:

```text
b = a     gives (b-a)(b-a+1) = 0 * 1 = 0;
b = a-1   gives (b-a)(b-a+1) = (-1) * 0 = 0.
```

Thus the exact equality cases over the integers are

```text
A(b) = a ell (ell-a)  iff  b = a or b = a-1,
```

provided `ell != 0`.

The hypothesis is necessary.  If `ell=0`, the defect
`ell^2 (b-a)(b-a+1)` vanishes for every integer `b`, so equality would not
force either adjacent candidate.

## Source Interval Truncation

Aoyagi's integer parameter lies in the source interval

```text
0 <= b <= ell-1,
```

with `1 <= ell`.  Intersecting the algebraic equality candidates with this
interval gives:

```text
b = a     is feasible only if a <= ell-1;
b = a-1   is feasible only if 1 <= a.
```

Equivalently, under `0 <= b <= ell-1`,

```text
A(b) = a ell (ell-a)
  iff (b=a and a <= ell-1) or (b=a-1 and 1 <= a).
```

Endpoint forms:

```text
a = 0:     only b = 0 remains;
a = ell:   only b = ell-1 remains.
```

The endpoint exclusions are interval exclusions only.  They do not supply
exponent-chain feasibility or the terminal `\tilde t_{s,k}=0` condition.

## Lean Boundary

This supports only the following Lean layer:

- prove the exact equality cases for the cleared integer numerator;
- prove the source-interval equality statement recording endpoint truncation;
- name the endpoint equality cases for `a=0` and `a=ell`.

It does not prove Aoyagi's full Lemma 3 candidate set, minimising exponent
chains, Lemma 4, Lemma 5, pole-order counting, normal crossings, or RLCT
extraction.
