# Reproduction - binary prefix-delta bounds for the Htilde interval

Date: 2026-06-21.

Scope: elementary finite arithmetic inside the Aoyagi-only expedition.  This
does not prove the source vector-to-chain correspondence, binary deltas from
Aoyagi's exponent vectors, the Lemma 5 upper-bound classifier, chart coverage,
pole order, normal crossings, or RLCT extraction.

## Statement

Let `ell` be the number of increments, and let

```text
D_0, D_1, ..., D_ell
```

be an integer sequence with

```text
D_0 = 0,              D_ell = a,
Delta_i = D_{i+1}-D_i in {0,1}       for 0 <= i < ell.
```

Assume also `a <= ell`, as in Aoyagi's selected-width decomposition.  Then for
every `0 <= j <= ell`,

```text
min(a, j-(ell-a)) <= D_j <= min(j,a),
```

where subtraction in the displayed lower bound is natural-number truncated
subtraction.  These are exactly the high-count prefixes of the displayed upper
and lower Htilde chains:

```text
aoyagiHtildeUpperHighCount ell a j = min(a, j-(ell-a)),
aoyagiHtildeLowerHighCount a j     = min(j,a).
```

## Reproduction

Telescoping gives

```text
D_j = sum_{i=0}^{j-1} Delta_i.
```

Since each `Delta_i` is either `0` or `1`, each summand is nonnegative and at
most `1`.  Hence

```text
0 <= D_j <= j.
```

The same telescoping at the endpoint gives

```text
a = D_ell = sum_{i=0}^{ell-1} Delta_i.
```

The prefix is a sub-sum of this nonnegative total, so

```text
D_j <= a.
```

Together these prove

```text
D_j <= min(j,a).
```

For the lower bound, split the total into prefix and tail:

```text
a = D_j + sum_{i=j}^{ell-1} Delta_i.
```

The tail has `ell-j` terms and each is at most `1`, so

```text
a - D_j <= ell-j.
```

Equivalently, over the integers,

```text
a - (ell-j) <= D_j.                         (1)
```

Now compare this with the natural truncated expression
`j-(ell-a)`.

If `j < ell-a`, then `j-(ell-a)=0`, so

```text
min(a, j-(ell-a)) = 0 <= D_j
```

by nonnegativity.

If `ell-a <= j`, then `j-(ell-a)` is the ordinary difference.  Since
`j <= ell` and `a <= ell`,

```text
j-(ell-a) = j+a-ell = a-(ell-j),
```

and this value is at most `a`.  Therefore

```text
min(a, j-(ell-a)) = j-(ell-a) = a-(ell-j) <= D_j
```

by (1).

Thus the desired two-sided bound follows for every `j`.

## Formalisation boundary

In Lean this should be named as a conditional finite arithmetic theorem.  The
source-facing hypotheses should remain explicit:

- the source convention `H_0=m_0`, giving `D_0=0`;
- terminal `H_ell=0` plus the selected-width sum, giving `D_ell=a`;
- the supplied binary-delta hypothesis.

The theorem may then feed the existing
`aoyagiHtildeChainBounds_of_incrementPrefix_bounds` and
`aoyagiHtilde_interval_mem_of_incrementPrefix_bounds` wrappers.  It should not
be described as proving Aoyagi Lemma 5's source classifier.
