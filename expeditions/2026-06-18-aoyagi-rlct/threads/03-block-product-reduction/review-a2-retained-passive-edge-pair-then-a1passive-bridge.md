# Review: A2 retained-passive edge-pair then `A1passive` bridge

Reviewer: xhigh `Pasteur the 2nd`.
Verdict: PASS.

## Checks

- `LinearEquiv.trans` order is correct: the composed equivalence is
  `E.trans S`, so the target edge-pair shear is applied first and the
  post-edge-pair `A1passive` shear second.
- The determinant theorem is scoped to the composed target-side linear
  equivalence.  It does not claim determinant equality for the actual
  raw-order Frechet derivative.
- The `(F2,C)` bridge uses the existing target edge-pair derivative bridge
  after the post-edge-pair `A1passive` shear fixes those fields.
- The `A3passive` bridge uses the existing raw lower-left derivative bridge;
  both component shears fix this field.
- The `A1passive` bridge uses the formal inverse of the edge-pair-normalised
  `(F2,C)` pair to recover the pre-edge-pair target-recovered successor
  family, then applies the existing target-staged `A1passive` theorem.
- The reproduction note and statement card explicitly avoid full tuple
  equality, `Ctop`/`F3` agreement, actual determinant equality, measure
  transport, normal crossings, pole order, and RLCT.

No Lean build was run by the reviewer under the read-only review constraint.
