# Pen-and-paper reproduction - Lemma 3 endpoint arithmetic

Status: checked sub-slice.  This reproduces only the integer algebra in
Aoyagi's Lemma 3 on PDF p. 24.  It does not reproduce the terminal candidate
set, the `\tilde t_{s,k}=0` restriction, feasibility of exponent chains,
Lemma 4, Lemma 5, pole order, normal crossings, or RLCT extraction.

## Source Target

Aoyagi writes

```text
A(b)/ell^2
  = b((ell-a)/ell)^2
    + (ell-1-b)(-a/ell)^2
    + (b(ell-a)/ell - (ell-1-b)a/ell)^2.
```

Clearing the denominator gives the integer numerator

```text
A(b) = b(ell-a)^2
       + (ell-1-b)a^2
       + (b(ell-a) - (ell-1-b)a)^2.
```

The source differentiates in the real variable `b` and concludes that the
integer minimisers are `a-1` and `a`.  This needs endpoint repair: Definition 3
allows `a=ell`, and the conventional algebraic endpoint `a=0` is also useful
when stating the cleaned theorem.

## Algebra

First simplify the linear term:

```text
b(ell-a) - (ell-1-b)a
  = b ell - ba - ell a + a + ba
  = ell(b-a) + a.
```

Therefore

```text
A(b)
  = b(ell-a)^2 + (ell-1-b)a^2 + (ell(b-a)+a)^2.
```

Expanding and collecting gives

```text
A(b) = a ell (ell-a) + ell^2 (b-a)(b-a+1).
```

The second summand is nonnegative over the integers because, for every integer
`y`, the consecutive product `y(y+1)` is nonnegative:

- if `y >= 0`, then both factors are nonnegative;
- if `y < 0`, then `y <= -1`, so `y+1 <= 0`, and the product of two
  nonpositive integers is nonnegative.

With `y=b-a`, this proves the lower bound

```text
a ell (ell-a) <= A(b)
```

for every integer `b`.

## Endpoint-Corrected Minimisers

Assume

```text
1 <= ell,     0 <= a <= ell,     0 <= b <= ell-1.
```

The minimum value is

```text
a ell (ell-a).
```

The feasible witnesses are:

```text
a = 0:          b = 0;
1 <= a < ell:   b = a-1 and b = a;
a = ell:        b = ell-1.
```

The witness policy used in Lean is:

```text
if a = 0, use b = 0;
otherwise, use b = a-1.
```

When `a=ell`, this gives `b=ell-1`, the only feasible endpoint minimiser.

## Lean Boundary

This supports only the following Lean layer:

- define the integer numerator `aoyagiLemma3A`;
- prove the completed-square identity;
- prove the universal lower bound;
- prove the constrained least-value statement over integer `b` with
  `0 <= b <= ell-1`;
- record the endpoint cases `a=0` and `a=ell`.

It does not prove that the minimizing `b` values arise from Aoyagi exponent
chains or terminal variables.  Those remain separate A5 obligations.
