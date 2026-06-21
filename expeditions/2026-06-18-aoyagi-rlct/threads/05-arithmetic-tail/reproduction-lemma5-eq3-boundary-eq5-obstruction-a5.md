# Reproduction - Lemma 5 Eq3 boundary Eq5 obstruction

Date: 2026-06-21.

Scope: one-coordinate obstruction at Eq3's special boundary
`p = ell-a+1`.  This records why the special Eq3 boundary value cannot be used
as the supplied upper endpoint in the Eq5 endpoint-coverage wrapper.  It is
finite interval/set bookkeeping only.

This does not construct Aoyagi's displayed vectors, prove source-label
legality, terminal `tilde t=0`, chart coverage, all-coordinate branch-family
coverage, pole order, normal crossings, or RLCT extraction.

## Source Inventory

Aoyagi Lemma 5, PDF pp. 26-27, displays the Eq3 branch with a special boundary
line.  In the supplied Lean certificate this line is

```text
T(C.point (ell-a+1) - 1) = Htilde'_(ell-a+1) + 1.
```

The same-coordinate interval at coordinate `ell-a+1` has upper endpoint
`Htilde'_(ell-a+1)`.  Therefore the boundary value is not an upper endpoint;
it is one unit above the upper endpoint.

The Eq5 strict offsets at a coordinate `p` are values of the form

```text
Htilde'_p - alpha,    1 <= alpha.
```

Existing Lean arithmetic already proves that these offset values are contained
in the same-coordinate interval.

## Pen-And-Paper Derivation

Put

```text
j = ell-a+1,
U = Htilde'_j,
B = T(C.point j - 1).
```

The Eq3 boundary clause gives

```text
B = U + 1.
```

Hence

```text
U < B.
```

Every value in the same-coordinate interval at `j` is at most `U`, so

```text
B notin IntervalValueSet_j.
```

Since Eq5 strict offsets are a subset of the same-coordinate interval,

```text
B notin Eq5Offsets_j.
```

Finally, suppose that inserting the Eq3 boundary value into the Eq5 offset set
filled the interval:

```text
insert B Eq5Offsets_j = IntervalValueSet_j.
```

But `B` is a member of the left-hand inserted set, so the equality would imply

```text
B in IntervalValueSet_j,
```

contradicting the boundary interval obstruction above.  Therefore

```text
insert B Eq5Offsets_j != IntervalValueSet_j.
```

The same statement can be restated with an external coordinate variable `p`
under the hypothesis `p = ell-a+1`.

## Lean Targets

```text
aoyagiLemma5Eq3_boundaryValue_ne_upperEndpoint
aoyagiLemma5Eq3_boundaryValue_not_mem_Eq5_offsets
aoyagiLemma5Eq3_boundaryValue_insert_Eq5_offsets_ne_intervalValueSetNat
aoyagiLemma5Eq3_boundaryValue_insert_Eq5_offsets_ne_intervalValueSetNat_of_eq_boundary
```

## Kill Conditions

- Keep the Eq3 piecewise certificate supplied.
- Keep this as an obstruction at `p=ell-a+1`, not as endpoint coverage.
- Do not infer that Eq3 supplies the upper endpoint at the special boundary.
- Do not infer that Eq5 offsets cover the boundary value.
- Do not infer source-label legality, own-source-label status, all-coordinate
  endpoint realisation, injection, back-to-label coverage, Lemma 5 order count,
  normal crossings, or RLCT extraction.
