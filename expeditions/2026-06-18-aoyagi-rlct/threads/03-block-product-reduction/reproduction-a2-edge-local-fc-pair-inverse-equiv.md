# Reproduction - A2 edge-local `(F,C)` pair inverse equivalence

Date: 2026-06-27.

Status: controller pen-and-paper reproduction; Lean proved; xhigh review
PASS.

This is a generic finite-linear-algebra brick for the retained-passive
determinant frontier.  It is independent of the quiver-based paper.

## Setup

For finite index types, the reusable edge-local formal map is

```text
T_A,H,G(F,C) = (-(A + H G) F + H C, -G F + C).
```

Here

```text
A : rho x rho,
H : rho x mu,
G : mu x rho,
F : rho x kappa,
C : mu x kappa.
```

Assume `det A` is a unit, so `A^{-1}` is the nonsingular inverse used by Lean.

## Inverse Formula

For a target pair `(U,V)`, define

```text
F' = A^{-1} (H V - U),
C' = V + G F'.
```

This is linear in `(U,V)`.

## Check: inverse after forward map

Let

```text
U = -(A + H G) F + H C,
V = -G F + C.
```

Then

```text
H V - U
  = H(-G F + C) - (-(A + H G)F + H C)
  = -H G F + H C + A F + H G F - H C
  = A F.
```

Thus

```text
F' = A^{-1} A F = F,
C' = V + G F = (-G F + C) + G F = C.
```

## Check: forward after inverse

Let `Z = H V - U` and `F' = A^{-1} Z`, so `A F' = Z`.  Then

```text
T_A,H,G(F', V + G F')_2
  = -G F' + V + G F'
  = V,
```

and

```text
T_A,H,G(F', V + G F')_1
  = -(A + H G)F' + H(V + G F')
  = -A F' - H G F' + H V + H G F'
  = H V - A F'
  = H V - (H V - U)
  = U.
```

The only determinant-chart input is `IsUnit A.det`; the shears themselves are
unipotent and the diagonal invertibility is precisely left multiplication by
`A`.

## Lean Target

In `lean/DLNFibre/DLN/Aoyagi/MatrixLinearDeterminant.lean`:

```text
edgeLocalFCPairLinearMapInverse
edgeLocalFCPairLinearMapInverse_apply
edgeLocalFCPairLinearEquiv
edgeLocalFCPairLinearEquiv_apply
edgeLocalFCPairLinearEquiv_symm_apply
```

## Guardrails

- This is generic finite linear algebra only.
- It is not yet the retained-passive total raw-order target-side shear.
- It is not an actual Frechet derivative theorem.
- It does not prove the final retained-passive determinant comparison, measure
  transport, normal crossings, pole order, or RLCT.

## Independent Check

`Halley the 5th`, xhigh read-only reviewer, initially found a proof-performance
build failure.  After the controller replaced the broad `simp` proof with
explicit matrix identities, the reviewer returned PASS.  The focused
determinant-helper build now elaborates, the inverse formula and
noncommutative multiplication order match the reproduction, and the nonclaim
boundary remains finite-linear.
