# Reproduction - A2 Retained-Passive A1 Passive Source-Staged Shear

Date: 2026-06-27.

Status: pen-and-paper reproduction for a narrow retained-passive Jacobian
factorisation slice.  This stages the passive `A1` branch only; it does not
stage `Ctop` or `F3`.

## Setup

For a retained-passive raw tuple `z`, write

```text
coord = (ofTopologyTuple z).toCoordinateData,
Dzv   = d(topologyTupleEdgeRawOrder)_z(v).
```

The previously proved passive `A1` component bridge says, for `p : Fin M`,

```text
Dzv.A1passive_p
  - d(coord.F2_{p.succ.succ})_z(v) * coord.solvedA3_{p.succ}
  - coord.F2_{p.succ.succ} * d(solvedA3_{p.succ})_z(v)
= formal(z)(v).A1passive_p.
```

The first derivative term is a successor `F2` derivative.  The all-edge
source-staged successor family is

```text
X_F(q) =
  source F2 tangent at the successor retained edge, if q is nonterminal,
  0,                                              if q = Fin.last M.
```

Equivalently, in Lean this is the `Fin.snoc` family already used for the
source-staged `(F2,C)` edge-pair package.

For the lower-left term we define the analogous displayed family

```text
X_G(q) =
  source A3passive tangent at q, if q is nonterminal,
  0,                         if q = Fin.last M.
```

This family is not the derivative of `solvedA3` at all edges.  It agrees with
that derivative only at nonterminal indices.

## Nonterminal Solved-A3 Projection

For `r : Fin M`, the nonterminal solved lower-left coordinate is just the stored
passive lower-left source coordinate:

```text
coord.solvedA3_{r.castSucc} = A3seed_{r.castSucc} = A3passive_r.
```

Therefore, for every raw tangent `v`,

```text
d(solvedA3_{r.castSucc})_z(v) = v.A3passive_r.
```

This is a projection derivative; it needs no determinant-chart hypothesis.

## Terminal Multiplier Case

The blanket statement

```text
d(solvedA3_q)_z(v) = X_G(q)
```

is false at `q = Fin.last M`, because the terminal solved lower-left block is

```text
solvedA3_last = -(F3 - EarlyTail) * LastTop.
```

Its derivative contains the `F3`, early-tail, and terminal top-factor
variations.  The passive `A1` expression uses this derivative only after
left-multiplication by

```text
coord.F2_{q.succ}.
```

When `q = Fin.last M`, this is the terminal extended `F2` slot
`coord.F2_{Fin.last (M+1)}`, hence zero by the retained-passive endpoint
convention.  Thus

```text
coord.F2_{q.succ} * d(solvedA3_q)_z(v)
  = coord.F2_{q.succ} * X_G(q)
```

for all `q : Fin (M+1)`: nonterminal by the projection calculation, terminal
because both sides have zero left factor.

## Source-Staged Passive A1 Formula

Substituting the all-edge successor `F2` derivative readout and the multiplier
identity into the old passive `A1` bridge gives

```text
Dzv.A1passive_p
  - X_F(p.succ) * coord.solvedA3_{p.succ}
  - coord.F2_{p.succ.succ} * X_G(p.succ)
= formal(z)(v).A1passive_p.
```

This is the intended Lean theorem.  It stages only the successor `F2` and
successor lower-left source tangents used by the passive `A1` correction.  It
does not claim that every `solvedA3` derivative is source-staged.

## Kill Conditions

- If the terminal `solvedA3` derivative is replaced by zero as a standalone
  derivative statement, the calculation is false.
- If the terminal multiplier `coord.F2_{Fin.last (M+1)} = 0` is removed,
  the all-edge lower-left multiplier identity is false.
- If the result is described as a fully source-staged tuple, it overclaims:
  `Ctop` still contains the tail-inverse derivative correction, and `F3` still
  contains early-tail and terminal top-factor derivative corrections.
- If `p.succ` is silently treated as nonterminal for the last passive edge,
  the proof loses the endpoint case.

## Nonclaims

No `Ctop` source staging, no `F3` source staging, no fully source-staged tuple,
no target-side `LinearEquiv`, no determinant-one shear, no actual derivative
determinant equality, no measure theorem, no normal crossings, no pole order,
and no RLCT statement is proved by this slice.
