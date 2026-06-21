# Statement card - A5 Lemma 5 equation (4) boundary-coordinate window

## Lean Artifact

Files:

- `lean/DLNFibre/DLN/Aoyagi/HtildeChainArithmetic.lean`
- `lean/DLNFibre/DLN/Aoyagi/Lemma5IntervalArithmetic.lean`
- `lean/DLNFibre/DLN/Aoyagi/Lemma5DisplayedVector.lean`

Names:

- `DLNFibre.DLN.Aoyagi.aoyagiHtildeUpperNat_succ_eq_add_selectedWidthNat_sub_increment`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq4_boundaryCoordinate_intervalExcess_eq_min`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq4_boundaryValue_sub_upperNat_boundaryCoordinate`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq4_boundaryValue_mem_boundaryCoordinateIntervalValueSetNat_iff_widthWindow`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq4_boundaryValue_mem_boundaryCoordinateIntervalValueSetNat_iff_widthWindow_min`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq4_boundaryValue_gt_boundaryUpper_of_p1_sourceSelected`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq4_boundaryValue_not_mem_boundaryInterval_of_p1_sourceSelected`

## Statement

For a supplied Aoyagi Lemma 5 equation `(4)` branch certificate in the strict
boundary case `p+1<a`, set

```text
r = p+(ell-a)+1.
```

Then the special boundary value belongs to the same-coordinate interval at
coordinate `r` if and only if the selected width at `r` lies in the window

```text
M - p + 1 <= W_r <= M - p + 1 + excess(ell,a,r).
```

The reduced-minimum theorem rewrites the excess at this coordinate as

```text
min(ell-a, a-p-1).
```

In the special case `p=1`, Definition 3's selected-width inequalities imply
`W_r<=M-1`, so the boundary value is strictly above the upper endpoint and is
not in the boundary-coordinate interval.

## Proved

- A reusable successor rule for the upper displayed `Htilde'` chain.
- The boundary-coordinate interval excess reduction.
- The Eq4 boundary value offset from the boundary-coordinate upper endpoint.
- The raw and reduced boundary-coordinate width-window iff.
- A source-shaped `p=1` above-upper and nonmembership corollary.

## Assumed

- A supplied equation `(4)` piecewise branch certificate.
- For the window theorems, the strict boundary guard `p+1<a`.
- For the `p=1` source corollaries, the selected-width sum and strict
  selected-width inequalities from Definition 3.

## Cited

- None in Lean. This is finite integer and interval-set arithmetic.

## Deferred

- Construction or existence of the displayed vector.
- Terminal `tilde t=0`.
- Case 1(2) chart sequence, introduced-label status, vector admissibility,
  Lemma 5 order count, normal crossings, and RLCT extraction.

## Verification

- From `lean/`:
  `lake build DLNFibre.DLN.Aoyagi.Lemma5DisplayedVector`
