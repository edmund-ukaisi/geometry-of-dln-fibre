# Reproduction - Lemma 5 Eq5 own-block counted/introduced payload

Date: 2026-06-22.

Scope: a one-branch adapter for a supplied equation `(5)` own-block branch.
This does not construct Aoyagi's displayed branch family, prove source
coverage, prove nonbase status, construct a classifier, prove injection or
back-to-label coverage, prove the Lemma 5 order count, prove normal crossings,
or extract RLCT data.

## Source

Aoyagi PDF p. 27, equation `(5)`, gives a strict-offset branch whose own
selected block has value

```text
T(S) = Htilde'_p - alpha
```

and source label

```text
k = Htilde'_p + 1 - alpha.
```

Thus on the own block

```text
T(S) = k - 1.
```

The previous source-label slice already formalised that, under the supplied
equation `(5)` piecewise certificate, source-range bound, selected-width bound
at `S`, and label formula, this label belongs to

```text
introducedLabelFinset L n S k.
```

The previous interval slice also gives

```text
T(S) in aoyagiHtildeIntervalValueSetNat ell a M m p.
```

## Reproduction

Assume `S` lies in the own selected block:

```text
C.block p S.
```

For counted data, we need `p` to be an interior selected coordinate.  The block
hypothesis gives `p < ell`; adding the explicit positive-coordinate hypothesis
`1 <= p` gives

```text
p in Finset.Icc 1 (ell - 1).
```

If the branch value is not the supplied base value,

```text
T(S) != baseValue p,
```

then interval membership and the counted-datum adapter give

```text
some (p, T(S)) in aoyagiLemma5CountDatumSet ell a M m baseValue.
```

Independently, the own-block source-label wrapper gives

```text
T(S) = k - 1
Sigma.mk S k in introducedLabelFinset L n S k.
```

Combining these facts gives a single payload theorem for the supplied branch.

## Lean Target

```text
aoyagiLemma5Eq5_ownBlock_countDatumSet_mem_introducedLabelFinset_of_lastPoint_widthBound
```

## Nonclaims

- No construction of the Eq5 piecewise vector.
- No proof that the branch is nonbase; nonbase is an explicit hypothesis.
- No proof that alphas cover the strict Eq5 domain.
- No endpoint realisation or terminal exactness.
- No classifier, injection, back-to-label map, no-extra theorem, or order count.
- No pole order, normal crossings, or RLCT extraction.
