# Statement Card - A2 Schur-core formal Jacobian unit

Date: 2026-06-26.

Lean file:

- `lean/DLNFibre/DLN/Aoyagi/ProductReductionStepJacobian.lean`

## Lean Names

```text
SchurCoreTangent
schurCoreFormalJacobian
schurCoreFormalJacobianInverse
schurCoreFormalJacobianEquiv
schurCoreFormalJacobian_det_isUnit
```

## Statement Shape

For a commutative ring `K`, finite decidable pivot index `ρ`, finite side
indices `μ` and `ν` for the determinant theorem, and a square pivot block

```text
B : Matrix ρ ρ K
```

with `IsUnit B.det`, the formal tangent map induced by

```text
F2 = -B^{-1} A2,
F3 = -A3 B^{-1},
C4 = A4 - A3 B^{-1} A2
```

the formal tangent map is a linear equivalence on

```text
Matrix ρ ν K × (Matrix μ ρ K × Matrix μ ν K).
```

Therefore, in the finite side-index case, its `LinearMap.det` is a unit:

```text
IsUnit (LinearMap.det (schurCoreFormalJacobian B A2 A3)).
```

## Scope

Finite formal Jacobian arithmetic for the fixed-pivot Schur-complement core of
Aoyagi Lemma 2 and Theorem 3.  The proof uses only determinant-unit
cancellation for `B`; it never inverts a passive residual block.

## Nonclaims

No full product-step Jacobian for `(C1,D,F3_old,A1,A2,A3,A4)`, no analytic
`HasFDerivAt`, no source-rank chart production, no chart coverage, no
source-measure pushforward, no density transport, no regular-suspension
certificate, no normal crossings, no pole-order theorem, and no RLCT
extraction.
