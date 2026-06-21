# Statement Card - A5 Lemma 5 Eq3 Upper Away From Boundary

## Lean Names

- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq3_piecewise_component_upperEndpoint_of_ne_boundary`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5_suppliedEq3UpperComponent_Eq5_offsets_eq_intervalValueSetNat_of_nonrising_ne_boundary`

## Claim

Away from Eq3's special boundary and the terminal endpoint, a supplied Eq3
piecewise certificate gives the same-coordinate upper endpoint as a component
value:

```text
T3(C.point p - 1) = Htilde'_p.
```

Under the additional non-rising hypothesis, this component value and the Eq5
strict offsets fill the same-coordinate interval.

## Inputs

- A supplied `AoyagiLemma5Eq3PiecewiseSourceVector`.
- `1 <= p`, `p < ell`, and `p != ell-a+1`.
- For the coverage theorem, `not (p <= a and p <= ell-a)`.

## Proves

The component-value theorem proves:

```text
T3(C.point p - 1) = aoyagiHtildeUpperNat ell a M m p.
```

The coverage theorem proves:

```text
insert (T3(C.point p - 1))
  (aoyagiLemma5Eq5OffsetValueSet ell a p M m)
= aoyagiHtildeIntervalValueSetNat ell a M m p.
```

## Does Not Prove

- Eq3 source-label legality, introduced-label status, or own-source-label
  status for this component.
- Coverage at `p=ell-a+1`.
- Coverage at `p=ell`.
- Construction of Eq3 or Eq5 displayed vectors.
- All-coordinate endpoint realisation, injection, back-to-label coverage,
  Lemma 5 order count, pole order, normal crossings, or RLCT extraction.

## Source

Aoyagi Lemma 5 equation `(3)`, PDF pp. 26-27, represented in Lean by the
supplied `AoyagiLemma5Eq3PiecewiseSourceVector.upper` and `.tail` clauses,
combined with the existing Eq5 non-rising finite-set coverage theorem.
