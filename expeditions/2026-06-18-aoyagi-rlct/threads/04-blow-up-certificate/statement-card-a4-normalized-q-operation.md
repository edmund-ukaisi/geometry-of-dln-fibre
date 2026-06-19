# Statement card - A4 normalized Q operation

## Lean artifacts

File: `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean` @ `26f4171`.

Names:

- `DLNFibre.DLN.Aoyagi.pivotPreQBlock`
- `DLNFibre.DLN.Aoyagi.pivotQ`
- `DLNFibre.DLN.Aoyagi.pivotQinv`
- `DLNFibre.DLN.Aoyagi.pivotPostQBlock`
- `DLNFibre.DLN.Aoyagi.pivotPreQBlock_mul_pivotQ`
- `DLNFibre.DLN.Aoyagi.pivotQ_mul_pivotQinv`
- `DLNFibre.DLN.Aoyagi.pivotQinv_mul_pivotQ`
- `DLNFibre.DLN.Aoyagi.pivotPreQBlock_mul_eq_postQ_mul_Qinv_mul`

## Statement

In a normalized pivot block indexed as `Unit ⊕ lower` by rows and
`Unit ⊕ right` by columns, let

```text
D' = [ 1  y
      x  D ],
Q  = [ 1 -y
      0  I ],
Q^-1 = [ 1 y
        0 I ].
```

Lean proves:

```text
D' * Q = [ 1 0
           x D - x*y ],
Q * Q^-1 = 1,
Q^-1 * Q = 1,
D' * C = (D' * Q) * (Q^-1 * C).
```

The theorem is over a `CommRing`; no division, determinant, or analytic input
is used.

## Source role

This is the normalized displayed `Q` matrix identity behind Aoyagi PDF
pp. 17-21.  It applies to both Case 1(2) and Case 2 after the pivot entry has
been normalized to `1`.

Independent xhigh source-fidelity scout `Franklin the 2nd` checked the
pen-and-paper algebra and confirmed that it is independent of the Case 2
printed-vector mismatch.

## Proved

- `Q` clears the pivot row off the pivot.
- The lower-right block changes by the Schur-style update `D - x*y`.
- The displayed `Q^-1` is a two-sided inverse.
- Replacing the following factor by `Q^-1 C` preserves the local product.

## Not proved

- No construction of the pivot chart or proof that the pivot entry can be
  normalized to `1`.
- No proof of all pivot-chart coverage.
- No proof that `C ↦ Q^-1 C` is a regular polynomial coordinate change with
  unit Jacobian, or that it preserves analytic ideal germs.
- No connection yet to the monomial/exponent update.
- No full Case 1/2 transition invariant, termination proof, normal-crossing
  certificate, or RLCT extraction.

## Status

- Sorry-free and xhigh source-fidelity reviewed at `26f4171`.

## Verification

- `lake build DLNFibre.DLN.Aoyagi.BlowupArithmetic`
- `lake build DLNFibre`
- `./scripts/sorries`: `0 sorry, 0 #exit, 0 native_decide, 0 axiom`
- `git diff --check`
