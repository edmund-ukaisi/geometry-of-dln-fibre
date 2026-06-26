# Reproduction - Lemma 5 first-nonbase cardinal bound

Status: finite cardinal-bound adapter; source-faithful only as conditional
bookkeeping under supplied terminal binary chain data and supplied injectivity.

## Source Position

Aoyagi Lemma 5 on PDF p. 25 states the count

```text
theta = a*(ell-a)+1.
```

For the upper-bound direction, the proof says that, once
`t_{s,k}^{(S_{j+1}-1)} = H_j`, Lemma 4 bounds the number of vectors
corresponding to `lambda` by the interval-value count over the interior
coordinates. It then displays the cardinalities of the intervals

```text
Htilde_j <= H <= Htilde'_j
```

and uses the Case 1(2) increment of `J` to get the upper bound
`theta <= a*(ell-a)+1`.

The Lean development has already reproduced the finite codomain count as

```text
|{base} union {(j,H) : 1 <= j <= ell-1,
                       H in I_j,
                       H != baseValue j}|
  = a*(ell-a)+1.
```

The source does not itself provide a canonical classifier from all source
branches to this codomain, prove that the classifier is injective, or prove a
back-to-label/no-extra theorem.

## Pen-and-Paper Check

Let `candidates` be a finite set of supplied terminal objects. For each
candidate `x`, suppose a terminal chain

```text
H_x : Fin (ell+1) -> Int
```

is supplied and satisfies the terminal binary-prefix-delta hypotheses used by
Lemma 4:

```text
H_x(0) = m_0,
H_x(ell) = 0,
sum_i m_i = ell*(M-1)+a,
Delta_r(H_x) is 0 or 1 for every r.
```

Fix supplied base values `baseValue j` lying in the interval codomain `I_j`.
Define the deterministic selector

```text
c(x) =
  none,                    if H_x(j) = baseValue j for every interior j;
  some (j0, H_x(j0)),      for the least interior j0 with H_x(j0) != baseValue j0.
```

The previous terminal first-nonbase selector theorem proves

```text
c(x) in countedDatumSet
```

for every candidate `x`.

If, in addition, the selector `c` is injective on the candidate set, then

```text
|candidates| = |c[candidates]|
             <= |countedDatumSet|
             = a*(ell-a)+1.
```

This is exactly the finite image-cardinality argument needed once the
source-moving classifier and injectivity parts have been supplied.

## Lean Theorem

The formal theorem is

```text
aoyagiLemma5FirstInteriorNonbaseCountDatumOrBase_candidates_card_le
```

in `lean/DLNFibre/DLN/Aoyagi/Lemma5SuppliedFamily.lean`.

It constructs an `AoyagiLemma5CountDatumClassifier` whose `classify` field is
the deterministic first-nonbase-or-base selector. The `mapsTo` field is
proved from

```text
aoyagiLemma5FirstInteriorNonbaseCountDatumOrBase_mem_of_terminalH_binaryIncrementPrefixDelta
```

and the supplied `injOn` field is passed unchanged. It then applies

```text
AoyagiLemma5CountDatumClassifier.candidates_card_le.
```

## Boundary

This theorem does not construct Aoyagi's source vectors, does not prove that
the first-nonbase selector is Aoyagi's classifier, and does not prove the
injectivity hypothesis. It only says that if supplied terminal chains map
injectively through this finite selector, then the candidate count is bounded
by the displayed Lemma 5 count.

## Nonclaims

- No source vector or Eq3/Eq4/Eq5 branch family is constructed.
- No canonical source classifier is proved from the PDF.
- No injectivity, back-to-label map, or no-extra terminal-minimum theorem is
  proved.
- No finite minimum-to-`lambda` equality, pole order, normal crossings, or
  RLCT extraction is proved.
