# Review - Definition 3 equal-width explicit ceiling data

Date: 2026-06-24.

Reviewer: xhigh independent explorer `Dalton the 2nd`.

## Verdict

PASS, no required corrections.

## Checked Source Fidelity

The reviewer checked Aoyagi PDF pp. 8-9.  Definition 3 gives the integer `M`
by

```text
M - 1 < sum/ell <= M,
```

and the equal-width example specializes this to `ell = L`,

```text
M - 1 < ((L + 1) M^(1)) / L <= M,
```

with

```text
a = (L + 1) M^(1) - (M - 1) L.
```

This matches the reproduction's source anchors.

## Checked Arithmetic

The positive-remainder convention is correct.  If

```text
w = L q + a,    1 <= a <= L,
```

then `L > 0` and

```text
((L + 1) w) / L = w + q + a/L
```

with `0 < a/L <= 1`.  Hence Aoyagi's integer is

```text
ceilWidth = w + q + 1.
```

The residue is

```text
aParam = (L + 1) w - (ceilWidth - 1) L
       = w - L q
       = a.
```

The divisible case is handled by taking `a = L` and the quotient one less.

## Scope Check

The target is narrow: a finite arithmetic constructor plus equal-width source
packaging.  It does not claim arbitrary Definition 3 existence, uniqueness of
`ceilWidth` or `aParam`, Eq5/Lemma 5 payloads, pole order, or RLCT extraction.
