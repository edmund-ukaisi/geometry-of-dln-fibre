# Reproduction - A2 retained-passive terminal `F2` target shear

Date: 2026-06-27.

Status: controller pen-and-paper reproduction before Lean formalisation.

This is the first actual-derivative edge-pair target-side slice after the
formal edge-pair product equivalence.  It handles only the terminal retained
edge.  The nonterminal edges still require staged/triangular bookkeeping
because their `F2` component involves the derivative of the successor `F2`
slot.

## Setup

Let

```text
p = Fin.last M : Fin (M+1).
```

The already-proved retained-passive `F2` shear component identity says, for
every edge `p`,

```text
dY12_p
  + dA1_p * F2_p
  - d(F2_{p+1}) * C_p
=
-(A_p + F2_{p+1} * G_p) * dF2_p + F2_{p+1} * dC_p.
```

Here

```text
A_p = coord.solvedA1 p,
G_p = coord.solvedA3 p,
F2_{p+1} = coord.F2 p.succ.
```

The right-hand side is the `F2` component of
`retainedPassiveFormalRawOrderJacobianAt z v`.

## Terminal Zero Convention

For the terminal edge `p = Fin.last M`, the successor index is

```text
p.succ = Fin.last (M+1) : Fin (M+2).
```

The nonredundant retained-passive coordinate data extends its stored `F2`
family by the terminal zero convention:

```text
coord.F2 (Fin.last (M+1)) = 0.
```

Therefore the map

```text
y |-> (ofTopologyTuple y).toCoordinateData.F2 (Fin.last (M+1))
```

is the constant zero map.  Its Frechet derivative is zero, so the terminal
`F2` identity reduces to

```text
dY12_last + dA1_last * F2_last
= formal.F2_last.
```

This is exactly the first edge-pair actual target shear with no successor
dependency.

## Boundary Cases

For `M = 0`, `Fin (M+1)` has one edge, so this theorem covers that unique
edge.  The stored `F2_p` is still the source-side `F2` block at `p.castSucc`,
while the successor `F2_{p+1}` is the terminal zero slot.  This theorem does
not identify the terminal top factor; that belongs to the separate `F3`
factor, where `LastTop = coord.Ctop` when `M = 0`.

## Guardrails

- This is terminal-edge only.
- It does not prove the nonterminal staged target-side shear.
- It does not include the terminal `C` recovery, `Ctop`, or `F3` endpoint
  factors.
- It is not an actual derivative determinant equality, measure theorem,
  normal-crossing theorem, pole-order theorem, or RLCT result.
