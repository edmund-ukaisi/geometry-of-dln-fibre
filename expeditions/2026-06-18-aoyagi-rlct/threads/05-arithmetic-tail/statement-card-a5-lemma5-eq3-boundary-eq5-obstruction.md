# Statement Card - A5 Lemma 5 Eq3 Boundary Eq5 Obstruction

## Lean Names

- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq3_boundaryValue_ne_upperEndpoint`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq3_boundaryValue_not_mem_Eq5_offsets`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq3_boundaryValue_insert_Eq5_offsets_ne_intervalValueSetNat`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq3_boundaryValue_insert_Eq5_offsets_ne_intervalValueSetNat_of_eq_boundary`

## Claim

At Eq3's special boundary `p=ell-a+1`, the supplied Eq3 boundary value is
`Htilde'_p+1`, not `Htilde'_p`.  Consequently it is outside the
same-coordinate interval and cannot be used as the supplied upper endpoint in
the Eq5 endpoint-coverage wrapper.

## Inputs

- A supplied `AoyagiLemma5Eq3PiecewiseSourceVector`.
- For the `p`-named wrapper, the coordinate identity `p = ell-a+1`.

## Proves

The value-level theorem proves:

```text
T(C.point (ell-a+1) - 1) != Htilde'_(ell-a+1).
```

The offset theorem proves:

```text
T(C.point (ell-a+1) - 1) notin Eq5Offsets_(ell-a+1).
```

The set-level theorem proves:

```text
insert (T(C.point (ell-a+1) - 1)) Eq5Offsets_(ell-a+1)
  != IntervalValueSet_(ell-a+1).
```

## Does Not Prove

- Eq3 source-label legality, introduced-label status, or own-source-label
  status.
- Upper endpoint coverage at `p=ell-a+1`.
- Construction of Eq3 or Eq5 displayed vectors.
- All-coordinate endpoint realisation, injection, back-to-label coverage,
  Lemma 5 order count, pole order, normal crossings, or RLCT extraction.

## Source

Aoyagi Lemma 5 equation `(3)`, PDF pp. 26-27, represented in Lean by the
supplied `AoyagiLemma5Eq3PiecewiseSourceVector.boundary` clause, combined with
the existing Eq5 finite offset-set containment theorem.
