# Reproduction - Lemma 5 Counted Datum Classifier Boundary

Status: supplied classifier boundary; formalisation-ready as finite
bookkeeping.

The counted datum set gives a finite codomain of size `a*(ell-a)+1`.
A source-backed upper bound for Aoyagi Lemma 5 would additionally require an
injective classifier from the source candidates being counted into this
codomain.

The PDF does not provide such a classifier explicitly.  The boundary is
therefore packaged as supplied finite data.

## Supplied Classifier

For a finite source-candidate set `candidates`, a counted-datum classifier
consists of:

```text
classify : alpha -> AoyagiLemma5CountDatum
mapsTo:
  x in candidates -> classify x in countedDatumSet
injOn:
  classify is injective on candidates
```

The `mapsTo` field is the interval-membership/back-to-codomain part.  The
`injOn` field is the nonduplication part that Aoyagi's Case 1(2) sentence does
not yet supply as a formal theorem.

## Count

The proof is finite set theory:

1. injectivity identifies `candidates.card` with the cardinality of its image;
2. `mapsTo` puts that image inside the counted datum set;
3. the counted datum set has cardinality `a*(ell-a)+1`.

Thus

```text
candidates.card <= a*(ell-a)+1.
```

## Nonclaims

- No source candidate set is constructed.
- No source vector `T_{s,k}` is classified.
- No interval classifier, Case 1(2) uniqueness, or back-to-label theorem is
  proved from the PDF.
- No terminal-label exactness, pole order, normal crossings, or RLCT extraction
  is proved.
