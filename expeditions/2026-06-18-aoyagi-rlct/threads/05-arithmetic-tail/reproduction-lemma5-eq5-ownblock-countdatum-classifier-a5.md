# Reproduction - Lemma 5 Eq5 own-block counted-datum classifier

Status: reproduced; Lean checked; supplied finite classifier adapter.

## Source Boundary

The previous Eq5 own-block slices prove a one-branch payload:

```text
some (p,T S) in aoyagiLemma5CountDatumSet
T S = k - 1
(S,k) in introducedLabelFinset L n S k.
```

This slice packages a finite supplied family of such one-branch witnesses as
an `AoyagiLemma5CountDatumClassifier`.  The classifier map and its injectivity
are not derived from Aoyagi's printed Lemma 5 paragraph.  The injectivity
field remains explicit supplied data.

## Calculation

Let `labels` be a finite set of source labels.  A label is written
`label = Sigma.mk S k`; the supplied functions give:

```text
p = pOf label
alpha = alphaOf label
T_label = T label.
```

Define the counted-datum map by

```text
classify(label) = some (pOf label, T label label.1).
```

For `label in labels`, the hypotheses supply:

- an Eq5 piecewise source vector for `(pOf label, alphaOf label)`;
- own-block membership `C.block (pOf label) label.1`;
- the last-point source range;
- the Eq5 label formula for `label.2`;
- the nonbase inequality `T label label.1 != baseValue (pOf label)`;
- either a raw selected-width bound or one of the source-shaped hypotheses
  deriving it.

The Eq5 alpha data gives `1 <= pOf label` from
`1 <= alphaOf label < pOf label`.  The existing own-block payload then proves
the counted-datum membership:

```text
classify(label) in aoyagiLemma5CountDatumSet ell a M m baseValue.
```

This is exactly the `mapsTo` field of `AoyagiLemma5CountDatumClassifier`.
The `injOn` field is the supplied hypothesis

```text
Set.InjOn classify labels.
```

The source-shaped wrappers only replace the raw selected-width bound by one
of:

- block-local actual-width dominance;
- selected left-endpoint identities plus block-local minimum;
- off-selected non-strict dominance;
- off-selected strict dominance.

## Lean Targets

```text
aoyagiLemma5Eq5_ownBlock_countDatumClassifier_of_labelPayloads_lastPoint_widthBound
aoyagiLemma5Eq5_ownBlock_countDatumClassifier_of_labelPayloads_lastPoint_blockWidth
aoyagiLemma5Eq5_ownBlock_countDatumClassifier_of_labelPayloads_lastPoint_leftEndpointMin
aoyagiLemma5Eq5_ownBlock_countDatumClassifier_of_labelPayloads_lastPoint_offSelected
aoyagiLemma5Eq5_ownBlock_countDatumClassifier_of_labelPayloads_lastPoint_offSelected_lt
```

## Kill Conditions

- Do not derive classifier injectivity; it is supplied.
- Do not infer the nonbase inequality.
- Do not replace the local introduced-label payload by a fixed terminal
  introduced-label domain.
- Do not treat the finite label set as source-constructed or exhaustive.

## Nonclaims

No Eq5 branch construction, no nonbase-status proof, no branch-label
injectivity proof, no back-to-label map, no no-extra terminal-minimum
coverage, no Lemma 5 order count, no pole order, no normal crossings, and no
RLCT extraction is proved here.
