# Reproduction - Lemma 5 Eq3/Eq4 Interval Finset Adapters

Status: checked endpoint/API wrapper.

This note packages the already-supplied equation `(3)` and `(4)` own-coordinate
values with same-coordinate interval membership and finite-domain
introduced-label membership.  It does not construct the displayed source
vectors.

## Source

Aoyagi Lemma 5, PDF pp. 26-27:

- Equation `(3)` supplies the upper endpoint value at coordinate `1`.
- Equation `(4)` supplies the lower endpoint value at coordinate `p`.
- The same-coordinate interval is
  `{H : Htilde_j <= H <= Htilde'_j}`.

The Lean development has already isolated the required source-side guards:

- Eq3 keeps the explicit one-unit slack needed for its source-label bound.
- Eq4 keeps the repaired index/source-selected guards used by the existing
  own-coordinate theorem.

## Reproduction

For Eq4, the supplied piecewise theorem gives:

```text
T(C.point p - 1) = Htilde_p.
```

The lower endpoint belongs to its same-coordinate interval:

```text
Htilde_p in HtildeIntervalValueSet_p.
```

The existing finite-domain introduced-label adapter gives:

```text
T(C.point p - 1) = k - 1,
Sigma.mk (C.point p - 1) k in introducedLabelFinset L n (C.point p - 1) k.
```

Combining these three facts gives:

```text
T(C.point p - 1) in HtildeIntervalValueSet_p,
T(C.point p - 1) = k - 1,
Sigma.mk (C.point p - 1) k in introducedLabelFinset L n (C.point p - 1) k.
```

For Eq3, the supplied piecewise theorem gives:

```text
T(C.point 1 - 1) = Htilde'_1.
```

The upper endpoint belongs to its same-coordinate interval:

```text
Htilde'_1 in HtildeIntervalValueSet_1.
```

The existing Eq3 finite-domain introduced-label adapter, with the explicit
slack retained, gives the label predecessor and introduced-label finset facts.
Combining them gives the analogous conjunction for Eq3.

## Lean Targets

```text
aoyagiLemma5Eq4_piecewise_ownCoordinate_intervalValue_mem_introducedLabelFinset_of_lastPoint
aoyagiLemma5Eq3_piecewise_ownCoordinate_intervalValue_mem_introducedLabelFinset_of_lastPoint
```

## Kill Conditions

- Do not remove Eq3's explicit slack hypothesis.
- Do not weaken Eq4's repaired source-selected/index hypotheses.
- Do not claim Eq3/Eq4 displayed-vector construction.
- Do not claim terminal `tilde t=0`, vector admissibility, chart coverage,
  Lemma 5 order count, normal crossings, or RLCT extraction.
