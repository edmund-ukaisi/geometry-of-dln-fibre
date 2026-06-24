# Reproduction - A6 Definition 3 `L=2` triangle parity formula package

Date: 2026-06-24.

Status: pen-and-paper reproduction before Lean implementation.

## Question

The all-source triangle formula package for `L=2`, `ell=2` currently requires a
supplied positive-remainder decomposition

```text
w1 + w2 + w3 = 2*ceilPred + a,   0 < a <= 2.
```

For `ell=2`, this decomposition is elementary parity arithmetic.  The goal is
to replace the supplied decomposition by explicit odd/even branch hypotheses on
the total selected width.

## Source Anchor

Aoyagi PDF pp. 8-9 define Definition 3 and Theorem 2.  For the all-source
`L=2` triangle branch, all three source layers are selected:

```text
m0 = w1,
m1 = w2,
m2 = w3,
T  = w1+w2+w3.
```

The triangle inequalities

```text
2*w_i < T   for i=1,2,3
```

give the all-source selected Definition 3 data.

## Odd Total

If

```text
T % 2 = 1,
```

then

```text
T = 2*(T/2) + 1.
```

Thus Definition 3 may use

```text
ceilPred = T/2,
ceilWidth = T/2 + 1,
aParam = 1.
```

The order formula is

```text
1*(2-1)+1 = 2.
```

The lambda formula is the existing Theorem 2 finite formula with
`ceilPred=T/2` and `a=1`.

## Even Total

If

```text
T % 2 = 0,
```

then `T > 0` in the triangle branch, hence `0 < T/2`, and

```text
T = 2*(T/2 - 1) + 2.
```

Thus Definition 3 may use

```text
ceilPred = T/2 - 1,
ceilWidth = T/2,
aParam = 2.
```

The order formula is

```text
2*(2-2)+1 = 1.
```

The lambda formula is the existing Theorem 2 finite formula with
`ceilPred=T/2-1` and `a=2`.

## Lean Target

Add two theorem variants in `Definition3Bridge.lean`:

```text
exists_consecutive_three_widths_theorem2Formula_of_triangle_odd_rankWidth
exists_consecutive_three_widths_theorem2Formula_of_triangle_even_rankWidth
```

Both should reuse the already-reviewed all-source triangle formula theorem,
but derive the positive-remainder equation from parity.  They should retain the
same selected-width provenance, pair-sum formula, and finite lambda formula.

## Guardrails

This is finite Definition 3/Theorem 2 arithmetic only.  It does not classify
`L>2`, choose between repeated-positive and triangle branches, add source-rank
wrappers or final sockets, construct Eq5 payloads or charts, prove normal
crossings, identify pole order, or extract RLCT.
