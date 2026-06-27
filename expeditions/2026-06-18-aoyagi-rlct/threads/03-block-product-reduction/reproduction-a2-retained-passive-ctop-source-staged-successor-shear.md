# Reproduction - A2 Retained-Passive Ctop Source-Staged Successor Shear

Date: 2026-06-27.

Status: pen-and-paper reproduction for a narrow retained-passive Jacobian
factorisation slice.  This stages the successor `F2` and multiplied successor
lower-left terms in the first top-left branch.  It leaves the derivative of the
passive-tail inverse explicit.

## Setup

For a retained-passive raw tuple `z`, write

```text
data  = ofTopologyTuple z,
coord = data.toCoordinateData,
Dzv   = d(topologyTupleEdgeRawOrder)_z(v),
Tail  = retainedPassiveA1TailAfterFirst data.A1seed,
dInv  = d_y(Tail(y)^{-1})_z(v).
```

The previously proved first top-left component bridge says

```text
Dzv.Ctop
  - d(coord.F2_1)_z(v) * coord.solvedA3_0
  - coord.F2_1 * d(coord.solvedA3_0)_z(v)
  - dInv * coord.Ctop
= formal(z)(v).Ctop.
```

Here `1` is `(0 : Fin (M+1)).succ`, the successor extended `F2` slot after the
first retained edge.

## Successor F2 Term

The staged successor `F2` family already used in the edge-pair and passive
`A1` slices is

```text
X_F(q) =
  source F2 tangent at the successor retained edge, if q is nonterminal,
  0,                                              if q = Fin.last M.
```

The all-edge successor readout gives, in particular,

```text
d(coord.F2_1)_z(v) = X_F(0).
```

For `M = 0`, the index `0 : Fin (M+1)` is terminal and `coord.F2_1` is the
extended terminal zero slot, so both sides are zero.  For `M > 0`, this is the
ordinary projection to the next retained `F2` source tangent.

## Multiplied Lower-Left Term

Let `X_G` be the staged successor lower-left family from the passive `A1`
slice:

```text
X_G(q) =
  source A3passive tangent at q, if q is nonterminal,
  0,                         if q = Fin.last M.
```

We do not assert

```text
d(coord.solvedA3_q)_z(v) = X_G(q)
```

for all `q`.  That statement is false at the terminal lower-left coordinate.
The landed all-edge multiplier identity is the precise usable statement:

```text
coord.F2_{q.succ} * d(coord.solvedA3_q)_z(v)
  = coord.F2_{q.succ} * X_G(q).
```

At `q = 0`, this gives

```text
coord.F2_1 * d(coord.solvedA3_0)_z(v)
  = coord.F2_1 * X_G(0).
```

For `M = 0`, the same identity is still valid because `q = 0` is terminal and
`coord.F2_1` is the terminal extended zero slot.

## Resulting Ctop Formula

Substituting these two source-staged readouts into the old `Ctop` bridge gives

```text
Dzv.Ctop
  - X_F(0) * coord.solvedA3_0
  - coord.F2_1 * X_G(0)
  - dInv * coord.Ctop
= formal(z)(v).Ctop.
```

This is the intended Lean theorem
`Ctop_source_staged_shear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt`.

## Tail-Inverse Boundary

This slice does not replace `dInv` by an explicit product formula.  The next
elementary target is the separate identity

```text
d(Tail^{-1}) = - Tail^{-1} * dTail * Tail^{-1},
```

together with a recursive product formula for `dTail`.  That calculation needs
its own product-derivative reproduction and should not be hidden inside this
successor-staging theorem.

## Kill Conditions

- If the `- dInv * coord.Ctop` term is dropped, the formula is false whenever
  the passive top-left tail varies.
- If one claims `d(solvedA3_q) = X_G(q)` at the terminal index, the statement
  overclaims.  Only the left-multiplied identity is available.
- If `M = 0` is treated as a nonterminal case, the endpoint convention is lost:
  the relevant successor `F2` slot is the terminal zero slot.
- If this theorem is described as full `Ctop` source staging, it overclaims;
  the tail-inverse derivative remains explicit.

## Nonclaims

No explicit derivative formula for `Tail^{-1}`, no recursive product derivative
for the passive tail, no `F3` source staging, no fully source-staged tuple, no
target-side `LinearEquiv`, no determinant-one shear, no actual derivative
determinant equality, no measure theorem, no normal crossings, no pole order,
and no RLCT statement is proved by this slice.
