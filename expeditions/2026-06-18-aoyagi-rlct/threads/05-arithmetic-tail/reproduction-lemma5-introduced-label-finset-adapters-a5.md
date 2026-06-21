# Reproduction - Lemma 5 introduced-label finite-domain adapters

Status: checked API adapter, no new source calculation.

This note records a finite-domain wrapper layer for the existing Lemma 5
introduced-label adapters.  It does not reproduce a new calculation from
Aoyagi's PDF; it packages already-proved source-label facts into the finite
domain used by later products and sums.

## Input Facts

The existing wrappers prove post-advance introduced labels:

```text
T(S)=k-1 and introducedLabel L n S k S k.
```

For Eq3 and Eq4, the own coordinate is the selected left endpoint
`S=C.point ... - 1`.  For Eq5, `S` is any member of the own selected block.

The general finite-domain API is:

```text
p in introducedLabelFinset L n S J
  iff introducedLabel L n S J p.1 p.2.
```

## Adapter Step

Specialising `p` to `Sigma.mk S k` and the state to `(S,k)`, the existing
introduced-label conclusion gives:

```text
Sigma.mk S k in introducedLabelFinset L n S k.
```

The value equality `T(S)=k-1` and, for Eq5, the same-coordinate interval
membership are carried unchanged from the existing wrapper.

## Lean Targets

```text
aoyagiLemma5Eq4_piecewise_ownCoordinate_mem_introducedLabelFinset_of_lastPoint
aoyagiLemma5Eq3_piecewise_ownCoordinate_mem_introducedLabelFinset_of_lastPoint
aoyagiLemma5Eq5_ownBlock_intervalValue_mem_introducedLabelFinset_of_lastPoint_widthBound
```

## Nonclaims

- No new actual-width compatibility theorem.
- No `LabelExponentCertificate`; terminal-exponent and least-value fields are
  not supplied by these wrappers.
- No displayed-vector construction.
- No terminal `tilde t=0`, vector admissibility, chart sequence, Lemma 5 order
  count, normal crossings, or RLCT extraction.
