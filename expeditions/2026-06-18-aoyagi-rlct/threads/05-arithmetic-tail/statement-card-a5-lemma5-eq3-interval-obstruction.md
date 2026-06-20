# Statement card - A5 Lemma 5 equation (3) interval obstruction

## Lean Artifact

File:

- `lean/DLNFibre/DLN/Aoyagi/Lemma5DisplayedVector.lean`

Names:

- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq3_boundaryValue_gt_upperNat`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq3_boundaryValue_not_mem_intervalValueSetNat`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq3_boundaryValue_not_mem_intervalValueSetNat_of_two_le`

## Statement

For a supplied Aoyagi Lemma 5 equation `(3)` branch certificate, the special
boundary value is one above the upper same-coordinate displayed-chain value:

```text
T(C.point (ell-a+1)-1) = Htilde'_(ell-a+1)+1.
```

Therefore it is not a member of the Nat-indexed same-coordinate interval value
set at coordinate `ell-a+1`.  In the strict boundary case `2<=a`, this applies
to the boundary point that lies inside the half-open selected span.

## Proved

- The supplied boundary value is strictly greater than
  `aoyagiHtildeUpperNat ell a M m (ell-a+1)`.
- The boundary value is not in
  `aoyagiHtildeIntervalValueSetNat ell a M m (ell-a+1)`.
- The strict selected-span version follows under `2<=a`.

## Assumed

- A supplied equation `(3)` piecewise branch certificate.
- For the strict selected-span wrapper, the explicit case hypothesis `2<=a`.

## Cited

- None in Lean. This is finite integer and interval-set arithmetic.

## Deferred

- Construction or existence of the displayed vector.
- Terminal `tilde t=0`.
- Case 1(2) chart sequence, introduced-label status, vector admissibility,
  Lemma 5 order count, normal crossings, and RLCT extraction.

## Verification

- `lake env lean DLNFibre/DLN/Aoyagi/Lemma5DisplayedVector.lean`
