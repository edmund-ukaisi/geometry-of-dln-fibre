# Statement card - A4 Case 2 constructed Cprime

## Lean Artifact

File:

- `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`

Names:

- `DLNFibre.DLN.Aoyagi.case2DisplayedPaperConstructedFollowingFactor`
- `DLNFibre.DLN.Aoyagi.case2DisplayedPaperCprime_of_constructedFollowingFactor`
- `DLNFibre.DLN.Aoyagi.case2DisplayedPaperDpp_mul_constructedCprime`

## Statement

Lean now proves the reverse coordinate direction for Aoyagi's displayed Case 2
following-factor operation in pivot-first coordinates.

Given a chart-coordinate following factor

```text
Cprime : Matrix (Unit ⊕ pivotComplement col) τ R,
```

define the old pivot-first following factor by

```text
Csrc = Q * Cprime.
```

Then `Q^-1 * Csrc = Cprime`, and

```text
D'' * Cprime = D_chart * Csrc.
```

## Proved

- The constructed old pivot-first following factor is `Q * Cprime`.
- Applying the displayed inverse `Q^-1` to that constructed factor recovers
  `Cprime`.
- The post-`Q` block identity holds with an arbitrary supplied `Cprime`.

## Assumed

- Displayed Case 2 stage and continuation hypotheses: `1<=S` and
  `J+1<=prefixMinNat n (S+1)`.
- A supplied source-normalised residual map in source coordinates.

## Cited

- None in Lean.  This is finite matrix algebra using the already-proved
  `Q^-1 * Q = 1`.

## Deferred

- Construction of a total source-coordinate following function from `Cprime`.
- Chart coverage, chart regularity, Jacobian arithmetic, recurrence post-data,
  exponent post-data, transition invariance, normal crossings, RLCT
  extraction, arbitrary-pivot coverage, terminal relabeling, and printed-vector
  repair.

## Verification

- `lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`
