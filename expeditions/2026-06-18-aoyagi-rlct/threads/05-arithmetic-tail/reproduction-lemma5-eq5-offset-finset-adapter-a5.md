# Reproduction - Lemma 5 Eq5 offset finset adapter

Status: checked API adapter over supplied Eq5 data.

This note packages one supplied equation `(5)` branch value simultaneously as
a strict Eq5 offset value, an interval value, a label-value equality, and a
finite introduced-label-domain member.

## Source

Aoyagi Lemma 5 equation `(5)`, PDF p. 27, fixes

```text
alpha = Htilde'_j0 + 1 - k,
Htilde_j0 + 1 <= k < Htilde'_j0 + 1,
j0 > alpha.
```

At the own block, the displayed branch value is:

```text
Htilde'_p - alpha.
```

The existing Lean supplied-piecewise certificate records this for one fixed
`alpha`; it does not construct all alpha branches simultaneously.

## Reproduction

For a supplied Eq5 piecewise certificate:

1. The own-coordinate branch record gives

   ```text
   T(S) = Htilde'_p - alpha.
   ```

2. The certificate guards include:

   ```text
   1 <= alpha,
   alpha < p,
   alpha <= Htilde'_p - Htilde_p.
   ```

   Therefore `alpha` lies in the index set of `Eq5OffsetValueSet`, and:

   ```text
   T(S) in Eq5OffsetValueSet_p.
   ```

3. The existing interval/introduced-label wrapper already proves:

   ```text
   T(S) in HtildeIntervalValueSet_p,
   T(S)=k-1,
   Sigma.mk S k in introducedLabelFinset L n S k.
   ```

Combining these conclusions gives the adapter theorem.

## Lean Target

```text
aoyagiLemma5Eq5_ownBlock_offsetValue_mem_introducedLabelFinset_of_lastPoint_widthBound
```

## Nonclaims

- No construction of the displayed Eq5 vector.
- No simultaneous family over all `alpha`.
- No derivation of the actual-width lower bound from Definition 3.
- No terminal `tilde t=0`, vector admissibility, chart sequence, Lemma 5 order
  count, normal crossings, or RLCT extraction.
