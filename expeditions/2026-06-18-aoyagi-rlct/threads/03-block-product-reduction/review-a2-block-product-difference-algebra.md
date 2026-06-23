# Review - A2 block product-difference algebra

Date: 2026-06-23.

Reviewer: xhigh fidelity/scope reviewer `Fermat`.

## Verdict

Accepted.  No required fixes.

## Checks

- The Lean theorem
  `triangularBlockProductDifference_fromBlocks_indexed` assumes exactly the
  pointwise triangular endpoint form
  `[I 0; F3 I] * T * [I F2; 0 I] = [Ctop 0; 0 D]`.
- The conclusion matches the reproduced p. 13 block product-difference algebra:

```text
[I 0; F3 I] * (T - [I 0; 0 0]) * [I F2; 0 I]
  = [Ctop - I, -F2; -F3, D - F3 * F2].
```

- Dimensions are correct: `F2 : Matrix ι ν`, `F3 : Matrix μ ι`, hence
  `F3 * F2 : Matrix μ ν`; the opposite product is generally ill-typed.
- Signs are forced by subtracting
  `L * T0 * R = [I F2; F3 F3*F2]`.

## Fidelity Boundary

The theorem is a `fromBlocks` matrix equality over a commutative ring with the
triangular endpoint form supplied as a hypothesis.  It does not produce that
endpoint form, prove Aoyagi Theorem 3, state an ideal equality, transport an
analytic germ, construct regular-suspension charts, preserve pole order, or
prove any RLCT claim.

## Verification

Reviewer ran:

```text
cd lean && scripts/lb DLNFibre.DLN.Aoyagi.ProductReduction
```

The build passed.  Direct PDF text extraction was unavailable in the current
environment; the review did not use the quiver paper or quiver Lean as
evidence.
