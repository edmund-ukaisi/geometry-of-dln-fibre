# Reproduction - A2 Retained-Passive Actual Derivative F2 Shear Bridge

Date: 2026-06-27.

Status: controller pen-and-paper reproduction; Lean target selected but not
yet implemented at the start of this note.

## Setup

Work in the retained-passive raw-order map

```text
raw = topologyTupleEdgeRawOrder.
```

At a tuple `z`, write

```text
data  = ofTopologyTuple z
coord = data.toCoordinateData
A_p   = coord.solvedA1 p
F_p   = coord.F2 p.castSucc
H_p   = coord.F2 p.succ
G_p   = coord.solvedA3 p
C_p   = coord.C p.
```

Here `coord.F2` is the full `F2full` family.  Thus `H_p` is the next
upper-right source coordinate when `p` is nonterminal, and is the terminal
zero matrix when `p = Fin.last M`.

For a tangent vector `v`, abbreviate Frechet differentials at `z` by

```text
dA_p = d(A_p)(v)
dF_p = d(F_p)(v) = v.F2_p
dH_p = d(H_p)(v)
dG_p = d(G_p)(v)
dC_p = d(C_p)(v) = v.C_p.
```

## Raw Formulas

The raw target blocks for edge `p : Fin (M+1)` are

```text
Y11_p = A_p + H_p * G_p,
Y12_p = - A_p * F_p + H_p * (C_p - G_p * F_p),
Y21_p = G_p,
Y22_p = C_p - G_p * F_p.
```

The lower-right bridge already proved that

```text
dY22_p + dY21_p * F_p = dC_p - G_p * dF_p.
```

The upper-right component needs the derivative of the next fixed-base
upper-unitriangular parameter `H_p` as well.

## Calculation

Differentiate the raw upper-right block:

```text
dY12_p
  = -dA_p * F_p - A_p * dF_p
    + dH_p * (C_p - G_p * F_p)
    + H_p * (dC_p - dG_p * F_p - G_p * dF_p).
```

Differentiate the raw top-left block:

```text
dY11_p = dA_p + dH_p * G_p + H_p * dG_p.
```

Now form

```text
dY12_p + dY11_p * F_p - dH_p * C_p.
```

Substituting the two derivatives gives

```text
  -dA_p * F_p - A_p * dF_p
  + dH_p * (C_p - G_p * F_p)
  + H_p * dC_p - H_p * dG_p * F_p - H_p * G_p * dF_p
  + dA_p * F_p + dH_p * G_p * F_p + H_p * dG_p * F_p
  - dH_p * C_p.
```

The `dA_p`, `dG_p`, and `dH_p` terms cancel, leaving

```text
-(A_p + H_p * G_p) * dF_p + H_p * dC_p.
```

This is exactly the `F2` component of
`retainedPassiveFormalRawOrderJacobianAt z v`.

## Uniform Endpoint Convention

No separate terminal theorem is mathematically needed.  The term

```text
dH_p = d(coord.F2 p.succ)(v)
```

uses the full `F2full` family.  If `p = Fin.last M`, then `p.succ` is the
terminal index of `Fin (M+2)`, `coord.F2 p.succ = 0`, and its derivative is
zero.  The same displayed identity specializes to

```text
dY12_p + dY11_p * F_p = -A_p * dF_p,
```

which is the formal terminal `F2` component because `H_p = 0`.

## Lean Target

The bounded component theorem should have shape

```text
fderiv(raw.F2_p)(v)
  + fderiv(rawA1_p)(v) * coord.F2 p.castSucc
  - fderiv(coord.F2 p.succ)(v) * coord.C p
= (retainedPassiveFormalRawOrderJacobianAt z v).F2_p.
```

Here `rawA1_p` means

```text
fun y => rawEdgeTupleA1 (raw y) p.
```

The target is still a component bridge, not the full determinant
factorization.  It is nevertheless a determinant-one shear ingredient: it is
triangular in the raw target `F2` coordinate after the top-left target readout
and the source-side next-`F2` triangular correction are accounted for.

## Guardrails

- This does not prove equality of the analytic raw-order derivative determinant
  with the formal determinant.
- This does not replace the separate endpoint top-left and terminal lower-left
  determinant-bearing solves.
- The only analytic facts used are ordinary Frechet differentiation of finite
  matrix products and the already-formalized retained-passive raw block
  formulas.
- The normal-crossing-to-RLCT extraction remains outside this elementary
  calculation and is the only intended citation boundary.
