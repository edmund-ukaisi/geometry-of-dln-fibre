# A2 retained-passive full target normaliser determinant bridge: reproduction

## Scope

This note packages the already landed retained-passive target-side stages into a
single raw-tuple equality, separately for the zero-tail and positive-tail cases.
The raw tuple order is

```text
(A1passive, F2, A3passive, C, Ctop, F3).
```

Let

```text
raw = topologyTupleEdgeRawOrder,
Dzv = (fderiv raw z) v,
T12 = edge-pair stage followed by A1passive stage,
T123 = T12 followed by the Ctop stage,
T = T123 followed by the final F3 stage,
Fv = retainedPassiveFormalRawOrderJacobianAt z v.
```

The target is `T Dzv = Fv`.

## Component Assembly

The component equalities are:

```text
(T123 Dzv).A1passive = Fv.A1passive,
((T123 Dzv).F2, (T123 Dzv).C) = (Fv.F2, Fv.C),
(T123 Dzv).A3passive = Fv.A3passive,
(T123 Dzv).Ctop = Fv.Ctop,
(T Dzv).F3 = Fv.F3.
```

The first three are inherited from `T12` and the fact that the `Ctop` stage
preserves `A1passive`, `(F2,C)`, and `A3passive`.  The `A3passive` preservation
is the new small helper:

```text
retainedPassiveTargetEdgePairThenA1passiveThenCtopShearRawTupleLinearEquivAt_A3passive
```

The `Ctop` equality is the existing composed `Ctop` bridge.  The `F3` equality
is the existing final component bridge, using the zero-tail or positive-tail
post-`Ctop` `F3` shear as appropriate.

The final `F3` shear fixes all earlier components, so these five equalities
assemble by nested product extensionality into the full raw-tuple equality.

## Zero Tail

For `M = 0`, the composed map is

```text
retainedPassiveTargetEdgePairThenA1passiveThenCtopThenF3ZeroShearRawTupleLinearEquivAt hz.
```

The full tuple theorem is

```text
retainedPassiveTargetEdgePairThenA1passiveThenCtopThenF3ZeroShear_fderiv_eq_formalRawOrderJacobianAt
```

and its determinant-one input is

```text
retainedPassiveTargetEdgePairThenA1passiveThenCtopThenF3ZeroShearRawTupleLinearEquivAt_abs_det_eq_one.
```

## Positive Tail

For passive tail length `M + 1`, the composed map is

```text
retainedPassiveTargetEdgePairThenA1passiveThenCtopThenF3PosShearRawTupleLinearEquivAt hz.
```

The full tuple theorem is

```text
retainedPassiveTargetEdgePairThenA1passiveThenCtopThenF3PosShear_fderiv_eq_formalRawOrderJacobianAt
```

and its determinant-one input is

```text
retainedPassiveTargetEdgePairThenA1passiveThenCtopThenF3PosShearRawTupleLinearEquivAt_abs_det_eq_one.
```

## Determinant Bridge

The existing conditional determinant theorem says that if a target-side linear
equivalence `T` has absolute determinant one and

```text
T ((fderiv raw z) v) = retainedPassiveFormalRawOrderJacobianAt z v
```

for every `v`, then the actual raw-order Frechet derivative absolute
determinant equals the point-specialized formal raw-order absolute determinant.
The product-form version then rewrites the formal determinant to the solved
`A1` product formula.

Instantiating these conditional theorems with the zero-tail and positive-tail
composed maps gives:

```text
topologyTupleEdgeRawOrderFDerivAbsDet_eq_formalRawOrderAbsDetAt_zeroTail
topologyTupleEdgeRawOrderFDerivAbsDet_product_eq_zeroTail
topologyTupleEdgeRawOrderFDerivAbsDet_eq_formalRawOrderAbsDetAt_posTail
topologyTupleEdgeRawOrderFDerivAbsDet_product_eq_posTail
```

## Nonclaims

This checkpoint does not prove measure transport, normal crossings, pole order,
or RLCT.  It also keeps the zero-tail and positive-tail cases as separate Lean
theorems rather than exposing a single all-`M` wrapper.
