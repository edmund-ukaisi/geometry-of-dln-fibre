# Reproduction - Lemma 5 Eq3/Eq4 local interval cardinality

Status: reproduced; Lean checked; finite count bookkeeping.

## Source Boundary

Aoyagi's Lemma 5 uses the displayed equations `(3)`, `(4)`, and `(5)` to
account for the same-coordinate interval values.  Earlier source probes found
that the printed equations do not by themselves give a source-backed
all-branch classifier or order-count theorem.  This slice stays below that
boundary: it assumes local Eq3-shaped and Eq4 piecewise certificates and
counts the finite set already shown to fill one rising interval.

## Calculation

For a fixed coordinate `p`, the existing local equality is

```text
insert (T3(C.point p - 1))
  (insert (T4(C.point p - 1)) Eq5OffsetValueSet)
  = HtildeIntervalValueSetNat p.
```

It uses:

- an Eq3-shaped local certificate for the upper component value;
- an Eq4 local certificate for the lower endpoint value;
- `1 <= p`;
- the rising-side guard `p <= ell-a`;
- the Eq4 index guard, which gives `p <= a`.

Taking cardinalities and using the existing interval-cardinality theorem gives

```text
card(insert upper (insert lower Eq5OffsetValueSet))
  = intervalSize(ell,a,p).
```

In the rising region, `intervalSize(ell,a,p)=p+1`, while the strict Eq5 offset
set has cardinality `p-1`.  Therefore the same set has cardinality

```text
Eq5OffsetValueSet.card + 2.
```

The two inserted values are counted through the interval equality; the theorem
does not separately prove that the inserted labels are legal source labels.

## Lean Targets

```text
aoyagiLemma5_Eq3Upper_Eq4_local_insertComponents_card_eq_intervalSize
aoyagiLemma5_Eq3Upper_Eq4_local_insertComponents_card_eq_offsetCard_add_two
```

## Kill Conditions

- Do not drop the local Eq3/Eq4 piecewise hypotheses.
- Do not read the cardinality equality as source construction of the printed
  branch family.
- Do not use these wrappers as a classifier, no-extra terminal-minimum
  coverage, or Lemma 5 order-count theorem.

## Nonclaims

No displayed-vector construction, no source-label legality, no all-coordinate
coverage, no branch injectivity, no back-to-label map, no pole order, no
normal crossings, and no RLCT extraction is proved here.
