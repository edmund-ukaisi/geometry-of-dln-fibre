# Statement card - A5 Lemma 5 equation (4) boundary membership forces p

## Lean Artifact

File:

- `lean/DLNFibre/DLN/Aoyagi/Lemma5DisplayedVector.lean`

Names:

- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq4_boundaryValue_mem_boundaryInterval_forces_two_le_p_of_sourceSelected`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq4_boundaryValue_not_mem_boundaryInterval_of_sourceSelected_of_p_lt_two`

## Statement

For a supplied Aoyagi Lemma 5 equation `(4)` branch certificate in the strict
boundary case `p+1<a`, Definition 3's selected-width hypotheses imply:

```text
B in the boundary-coordinate interval => 2 <= p.
```

Equivalently, if `p<2`, then the boundary value is not in the
boundary-coordinate interval.

## Proved

- Boundary-coordinate membership gives the lower width-window bound
  `M-p+1<=W_r`.
- Definition 3's strict selected-width inequality gives `W_r<=M-1`.
- These inequalities force `2<=p`.
- The contrapositive-style `p<2` nonmembership wrapper.

## Assumed

- A supplied equation `(4)` piecewise branch certificate.
- The strict boundary guard `p+1<a`.
- The selected-width sum and strict selected-width inequalities from
  Definition 3.

## Cited

- None in Lean. This is finite integer and interval arithmetic.

## Deferred

- Construction or existence of equation `(4)`'s displayed vector.
- Membership for `p>=2`.
- Terminal `tilde t=0`.
- Case 1(2) chart sequence, introduced-label status, vector admissibility,
  Lemma 5 order count, normal crossings, and RLCT extraction.

## Verification

- `lake env lean DLNFibre/DLN/Aoyagi/Lemma5DisplayedVector.lean`
- `lake build DLNFibre.DLN.Aoyagi.Lemma5DisplayedVector`
- `lake env lean DLNFibre.lean`
- `lake build DLNFibre`
- `./scripts/sorries`
- `git diff --check`
