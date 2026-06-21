# Reproduction - Lemma 5 Eq3-Shaped Component Supplied Label Bounds

Status: checked source-label/API wrapper.

This note records the p-general source-label adapter for a supplied
Eq3-shaped component value.  The label bounds are explicit hypotheses; this
does not derive Eq3 label legality from Definition 3.

## Source

Aoyagi Lemma 5, PDF pp. 26-27, displays an Eq3-shaped upper branch whose
component value on selected block `p` is `Htilde'_p`.  The Lean record
`AoyagiLemma5Eq3PiecewiseSourceVector` stores that branch value as supplied
piecewise data.

The source-label claim for the component with label

```text
k = Htilde'_p + 1
```

requires the actual source-layer label bounds

```text
1 <= k <= n(C.point p).
```

In this adapter these bounds are not derived from the paper's selected-width
hypotheses.  They are supplied through:

```text
n(C.point p) = aoyagiSelectedWidthNat ell m p
1 <= Htilde'_p + 1 <= aoyagiSelectedWidthNat ell m p.
```

## Reproduction

Assume `1 <= p` and `p <= ell-a`.  The supplied Eq3-shaped component theorem
gives:

```text
T(C.point p - 1) = Htilde'_p.
```

If `(k : Int) = Htilde'_p + 1`, then:

```text
T(C.point p - 1) = k - 1.
```

The selected cutpoint range hypothesis `C.point ell <= L+1` and the block
membership of `C.point p - 1` give:

```text
1 <= C.point p - 1 <= L.
```

The supplied width compatibility and label-bounds hypotheses give:

```text
1 <= k <= n((C.point p - 1)+1).
```

Together these prove:

```text
actualWidthLabel L n (C.point p - 1) k.
```

The introduced-label and finite-domain wrappers then follow from the generic
same-stage introduction lemma and `mem_introducedLabelFinset`.  The interval
membership wrapper adds only that `Htilde'_p` is the upper endpoint of the same
coordinate interval.

## Lean Targets

```text
aoyagiLemma5Eq3_component_actualWidthLabel_of_lastPoint_labelBounds
aoyagiLemma5Eq3_component_introducedLabel_of_lastPoint_labelBounds
aoyagiLemma5Eq3_component_mem_introducedLabelFinset_of_lastPoint_labelBounds
aoyagiLemma5Eq3_component_intervalValue_mem_introducedLabelFinset_of_lastPoint_labelBounds
```

## Kill Conditions

- Keep label bounds and actual-width compatibility supplied.
- Do not derive p-general Eq3 label legality from Definition 3.
- Do not construct Eq3 displayed vectors.
- Do not prove terminality, all-interval coverage, all-branch coverage, Lemma 5
  order count, normal crossings, or RLCT extraction.
