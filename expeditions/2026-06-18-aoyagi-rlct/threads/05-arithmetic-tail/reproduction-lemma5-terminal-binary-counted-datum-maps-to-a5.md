# Reproduction - Lemma 5 terminal binary counted-datum maps-to

Status: elementary finite bridge; formalisation-ready.

This slice isolates only the `mapsTo` part of the counted-datum classifier for
one nonbase branch.  It does not construct a source branch family, prove
coverage, prove injection, or produce a back-to-label map.

## Setup

Fix an interior coordinate

```text
j in {1,...,ell-1}.
```

Let `H : Fin (ell+1) -> Int` be a chain satisfying:

```text
H_0 = m_0,
H_ell = 0,
sum_i m_i = ell*(M-1)+a,
Delta_r(H) in {0,1} for every r < ell,
a <= ell.
```

The previously reproduced binary prefix-delta theorem gives, for every
coordinate `q`,

```text
H_q in [Htilde_q, Htilde'_q].
```

Equivalently,

```text
H_q in aoyagiHtildeIntervalValueSet ell a M m q.
```

At the chosen interior coordinate `j`, this is the same as membership in the
Nat-indexed wrapper:

```text
H_j in aoyagiHtildeIntervalValueSetNat ell a M m j,
```

because `j <= ell-1`, hence `j < ell+1`.

## Counted datum

The counted datum set contains nonbase data of the form

```text
some (j, value)
```

exactly when

```text
j in {1,...,ell-1}
value in (aoyagiHtildeIntervalValueSetNat ell a M m j).erase (baseValue j).
```

Thus, if the branch value at coordinate `j` is not the supplied base value,

```text
H_j != baseValue j,
```

then

```text
some (j, H_j) in aoyagiLemma5CountDatumSet ell a M m baseValue.
```

This proves the maps-to/codomain-membership part for one terminal binary chain.

## Nonclaims

- No source vector-to-chain correspondence is proved.
- No source branch family is constructed.
- No coordinate-wise coverage or value-image theorem is proved.
- No Case 1(2) uniqueness, classifier injection, or back-to-label theorem is
  proved.
- No terminal-label exactness, pole order, normal crossings, or RLCT extraction
  is proved.
