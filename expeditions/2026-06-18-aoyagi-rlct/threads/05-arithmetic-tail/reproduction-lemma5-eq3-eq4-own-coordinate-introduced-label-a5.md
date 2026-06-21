# Pen-and-paper reproduction - Lemma 5 equations (3)/(4) own-coordinate introduced labels

Status: checked wrapper over existing actual-label adapters.

This note records a source-label API consequence of the existing equation
`(3)` and `(4)` own-coordinate actual-label adapters.  It does not construct
the displayed vectors.

## Source

Aoyagi Lemma 5 lists special displayed vectors for equations `(3)` and `(4)`.
The already-proved adapter layer records that, for supplied piecewise
certificates and the required guards, the own coordinate has value

```text
T S = k-1
```

and `k` is a legal actual source label at `S`.

For equation `(4)`:

```text
S = C.point p - 1,
k = Htilde_p + 1.
```

For equation `(3)`:

```text
S = C.point 1 - 1,
k = Htilde'_1 + 1.
```

## Introduced Label Step

The blow-up bookkeeping uses the finite predicate

```text
introducedLabel L n S J s k
```

meaning that `(s,k)` is an actual source label and has already been introduced
by state `(S,J)`.

If `actualWidthLabel L n S k` is known, then at the post-advance state
`(S,k)` the same label is introduced:

```text
introducedLabel L n S k S k.
```

This is exactly `introducedLabel_of_eq_stage_le` with equality of source layer
and `k <= k`.

## Hypotheses Preserved

The wrappers deliberately preserve the existing hypotheses:

- supplied equation `(3)` or `(4)` piecewise certificate;
- Definition 3 selected-width sum and strict selected-width inequalities;
- last-cutpoint range `C.point ell <= L+1`;
- actual-width compatibility at the own source layer;
- for equation `(3)`, the explicit slack `W_1+2<=M`;
- for equation `(4)`, the repaired guards including `1<=p` and `p<=ell-a`.

## Lean Targets

```text
aoyagiLemma5Eq4_piecewise_ownCoordinate_introducedLabel_of_lastPoint
aoyagiLemma5Eq3_piecewise_ownCoordinate_introducedLabel_of_lastPoint
```

## Nonclaims

- No construction of equation `(3)` or `(4)` displayed source vectors.
- No derivation of actual-width compatibility from Definition 3 alone.
- No removal of the equation `(3)` slack.
- No terminal `tilde t=0`, vector admissibility, chart sequence, Lemma 5
  order count, normal crossings, or RLCT extraction.
