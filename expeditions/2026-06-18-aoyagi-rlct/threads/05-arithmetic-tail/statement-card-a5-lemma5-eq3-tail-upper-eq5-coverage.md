# Statement Card - A5 Lemma 5 Eq3 Tail Upper Eq5 Coverage

## Lean Names

- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq3_piecewise_tail_upperEndpoint_of_boundary_lt`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5_suppliedEq3TailUpper_Eq5_offsets_eq_intervalValueSetNat_of_boundary_lt`

## Claim

For an ordinary selected block strictly after Eq3's special boundary and before
the terminal endpoint,

```text
ell-a+1 < p < ell,
```

a supplied Eq3 piecewise certificate gives the upper same-coordinate endpoint
at that selected-block left endpoint:

```text
T3(C.point p - 1) = Htilde'_p.
```

Since this coordinate is outside the rising region, that upper endpoint and
the strict Eq5 offsets fill the same-coordinate interval.

## Inputs

- A supplied `AoyagiLemma5Eq3PiecewiseSourceVector`.
- Tail-region guards `ell-a+1 < p` and `p < ell`.

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

- Eq3 source-label legality or introduced-label status.
- That this component is the vector's own source label.
- Construction of Eq3 or Eq5 displayed vectors.
- Coverage at the special boundary `p=ell-a+1`.
- Coverage at the terminal endpoint `p=ell`.
- All-coordinate branch-family coverage, Lemma 5 order count, pole order,
  normal crossings, or RLCT extraction.

## Source

Aoyagi Lemma 5 equation `(3)`, PDF p. 27, represented in Lean by the supplied
`AoyagiLemma5Eq3PiecewiseSourceVector.tail` clause, combined with the existing
Eq5 non-rising finite-set coverage theorem.
