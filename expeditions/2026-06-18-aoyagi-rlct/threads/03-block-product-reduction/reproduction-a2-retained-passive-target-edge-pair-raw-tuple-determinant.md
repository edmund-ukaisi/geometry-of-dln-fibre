# A2 retained-passive target edge-pair raw-tuple determinant: reproduction

## Scope

This note reproduces the determinant of the target-side raw-tuple
edge-pair shear

```text
retainedPassiveTargetEdgePairShearRawTupleLinearEquivAt
```

from the already-proved pointwise formulas.  It is a finite linear-algebra
calculation in the retained-passive raw tuple

```text
w = (A1passive, F2, A3passive, C, Ctop, F3).
```

It is independent of the formal raw `(F2,C)` determinant calculation.  The
formal edge-pair equivalence has nontrivial diagonal factors; the determinant
one statement here belongs to the full raw-tuple target shear after the side
fields are included.

## Edge Blocks

For each edge `q : Fin (M+1)`, define the raw edge readouts

```text
A1_q = rawEdgeTupleA1 w q,
A3_q = rawEdgeTupleA3 w q,
F_q  = w.F2 q,
C_q  = w.C q.
```

Thus `A1_0 = Ctop`, `A1_{p.succ} = A1passive p`,
`A3_{p.castSucc} = A3passive p`, and `A3_last = F3`.

Use the determinant-friendly edge block order

```text
q = M, M-1, ..., 0,
```

and within each edge use

```text
(A1_q, A3_q, F_q, C_q).
```

This is only a product-coordinate regrouping/permutation of the raw tuple.
Its determinant may be a sign, but conjugating by it does not change the
determinant of an endomorphism.

## Forward Map

Fix the retained-passive base `z` and write

```text
H_q = coord.F2 q.castSucc,
D_q = coord.C q,
X_q = retainedPassiveTargetRecoveredF2At z w q,
Xsucc_last = 0,
Xsucc_{p.castSucc} = cast (X_{p.succ}).
```

The forward raw-tuple map fixes the side readouts and sends

```text
A1'_q = A1_q,
A3'_q = A3_q,
F'_q  = F_q + A1_q * H_q - Xsucc_q * D_q,
C'_q  = C_q + A3_q * H_q.
```

The recurrence for `X_q` is backward.  Therefore `Xsucc_q` depends only on
edge data with index strictly larger than `q`; for the terminal edge it is
zero.  In descending edge order, those larger indices are earlier blocks.

Consequently the transported forward map is block lower triangular with
identity diagonal:

- `A1'_q` is the identity on `A1_q`;
- `A3'_q` is the identity on `A3_q`;
- `F'_q` is the identity on `F_q`, plus same-edge `A1_q` and earlier-edge
  terms;
- `C'_q` is the identity on `C_q`, plus same-edge `A3_q`.

Hence the determinant of the forward map is `1`.

## Inverse Map

For a target tuple `y`, let

```text
Y = ((retainedPassiveFormalRawF2CLinearEquivAt hz).symm (y.F2, y.C)).1,
Ysucc_last = 0,
Ysucc_{p.castSucc} = cast (Y_{p.succ}).
```

The proved inverse raw-tuple formula is

```text
A1^-_q = A1_q,
A3^-_q = A3_q,
F^-_q  = F_q - A1_q * H_q + Ysucc_q * D_q,
C^-_q  = C_q - A3_q * H_q.
```

The first component of the formal edge-pair inverse is explicit:

```text
Y_p = (coord.solvedA1 p)^(-1) * (coord.F2 p.succ * C_p - F_p).
```

Thus `Ysucc_q` depends only on the next edge's `(F,C)` block and hence, in
descending edge order, only on earlier blocks.  The inverse is also block
lower triangular with identity diagonal, so its determinant is `1`.

Since the forward and inverse maps are already proved to be inverse linear
maps, either determinant-one calculation implies the other.  The inverse
calculation is the cleaner Lean target because `Ysucc_q` has the displayed
one-edge formula, rather than the recursively defined `Xsucc_q`.

## Kill Conditions

- If the transported edge-block order omits either endpoint field
  (`Ctop` or `F3`), the determinant-one statement is false or ill-scoped:
  the full raw tuple is essential.
- If the proof uses the determinant of `retainedPassiveFormalRawF2CLinearEquivAt`
  itself as determinant one, it is wrong; that formal map has nontrivial
  `coord.solvedA1` factors.
- If a Lean theorem is stated for the analytic raw-order Frechet derivative
  rather than this target-side raw-tuple shear, it overclaims.  The actual
  raw-order derivative has the separate nontrivial product determinant.

## Lean Target

The intended theorem surface is:

```text
retainedPassiveTargetEdgePairShearRawTupleLinearEquivAt_symm_det_eq_one
retainedPassiveTargetEdgePairShearRawTupleLinearEquivAt_det_eq_one
retainedPassiveTargetEdgePairShearRawTupleLinearEquivAt_abs_det_eq_one
```

The forward linear-map version can be added when useful:

```text
retainedPassiveTargetEdgePairShearRawTupleLinearMapAt_det_eq_one
```

The proof should proceed through a unitriangular edge-block regrouping or an
equivalent finite triangular determinant lemma.
