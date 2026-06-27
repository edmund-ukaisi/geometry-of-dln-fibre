# Reproduction - A2 retained-passive passive A1 target-staged shear

Date: 2026-06-27.

Status: Lean proved; focused and full builds passed; sorry/whitespace/axiom
audits passed; xhigh review passed.

This note is independent of the quiver-based paper.  It target-stages the
passive `A1` correction using the target-recovered successor `F2` family and
the raw lower-left readout of the target derivative.  It is a passive
top-left branch theorem only, not a determinant theorem.

## Setup

Work at a retained-passive raw tuple `z` in the determinant chart, with tangent
`v`.  Write

```text
raw    = topologyTupleEdgeRawOrder,
coord  = (ofTopologyTuple z).toCoordinateData,
Dzv    = d(raw)_z(v),
formal = retainedPassiveFormalRawOrderJacobianAt(z)(v).
```

For a passive top-left source coordinate `p : Fin M`, put

```text
q = p.succ : Fin (M+1).
```

The already-proved source-staged passive `A1` identity is

```text
Dzv.A1passive_p
  - XsuccF2(q) * coord.solvedA3(q)
  - coord.F2(q.succ) * XsuccA3(q)
= formal.A1passive_p,
```

where `XsuccF2` is the source-staged successor `F2` tangent and `XsuccA3` is
the source-staged successor lower-left tangent.

## Target-Side Replacements

The previous slice proved the target-recovered successor `F2` theorem:

```text
targetXsuccF2(q) = XsuccF2(q)
```

on actual derivative targets `Dzv`.

For the lower-left factor, use the raw lower-left target readout

```text
rawEdgeTupleA3(Dzv,q).
```

This agrees with the source-staged lower-left tangent after multiplication by
the extended successor `F2` slot:

```text
coord.F2(q.succ) * rawEdgeTupleA3(Dzv,q)
  = coord.F2(q.succ) * XsuccA3(q).
```

The check splits on `q`.

If `q = r.castSucc` is nonterminal, then `rawEdgeTupleA3(Dzv,q)` is the
passive `A3` target component, and the existing derivative bridge identifies
it with the formal passive `A3` component, hence with `v.A3passive_r`.
This is exactly `XsuccA3(q)`.

If `q = Fin.last M`, then `XsuccA3(q)` is zero but
`rawEdgeTupleA3(Dzv,q)` is the terminal lower-left target derivative.  The
multiplier `coord.F2(q.succ)` is the retained-passive terminal extended `F2`
slot, hence zero, so both sides of the multiplied identity vanish.

## Target-Staged Passive A1 Formula

Substituting these two target-side replacements into the source-staged passive
`A1` identity gives

```text
Dzv.A1passive_p
  - targetXsuccF2(q) * coord.solvedA3(q)
  - coord.F2(q.succ) * rawEdgeTupleA3(Dzv,q)
= formal.A1passive_p.
```

Since the formal passive `A1` branch is projection-level, the same target-
staged expression recovers the source tangent:

```text
Dzv.A1passive_p
  - targetXsuccF2(q) * coord.solvedA3(q)
  - coord.F2(q.succ) * rawEdgeTupleA3(Dzv,q)
= v.A1passive_p.
```

## Boundary Cases

- If `M = 0`, there is no `p : Fin M`, so the passive `A1` theorem is
  vacuous but still correctly quantified.
- If `p.succ = Fin.last M`, the lower-left replacement is valid only because
  `coord.F2(p.succ.succ) = 0`; it is not claiming that the terminal raw
  lower-left derivative is zero.
- The target-recovered successor `F2` equality still requires the
  determinant-chart hypothesis through the edge-pair inverse.

## Kill Conditions

- If the terminal lower-left derivative is identified with source-staged zero
  before multiplying by `coord.F2(q.succ)`, the statement is false.
- If the successor `F2` correction is the source-staged family rather than the
  target-recovered family, the theorem is only the already-landed source-
  staged result.
- If the result is read as staging `Ctop`, staging `F3`, whole-tuple target
  normalization, determinant-one target-side `LinearEquiv`, determinant
  equality, measure transport, normal crossings, pole order, or RLCT, it
  overclaims.

## Nonclaims

No `Ctop` target staging, no `F3` target staging, no whole-tuple target-side
normalization, no determinant-one target-side `LinearEquiv`, no actual
derivative determinant formula, no measure transport, no normal crossings, no
pole order, and no RLCT follows from this passive `A1` target-staged shear.
