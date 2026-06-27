# A2 retained-passive inverse Jacobian density

## Scope

This note is the pen-and-paper calculation behind the retained-passive
chart-side inverse Jacobian density.  It is independent of the quiver paper and
uses only the already formalised retained-passive raw-order chart
homeomorphism.

It proves pointwise density algebra, and a conditional measure identity with
explicit measurability hypotheses.  It does not prove an explicit determinant
formula, determinant-density continuity, source-prior transport, normal
crossings, pole order, or RLCT.

## Setup

Let

- `S` be the retained-passive tuple determinant chart;
- `T` be the raw-order source-recursive determinant chart;
- `f : S -> T` be the retained-passive raw-order chart map, written in Lean as
  `topologyTupleEdgeRawOrder`;
- `g : T -> S` be the source-readback inverse, written in Lean as
  `topologyTupleEdgeRawOrderInverse`.

The topology layer proves:

```text
z in S        => g (f z) = z,
y in T        => f (g y) = y,
z in S        => f z in T,
y in T        => g y in S.
```

The derivative layer defines the forward source-side absolute determinant

```text
J(z) = |det Df_z|
```

and proves `J(z) > 0` for every `z in S`.

## Chart-side inverse density

Define the target-side inverse density on ambient raw-order tuples by

```text
K(y) = J(g y)^(-1).
```

This is deliberately a pointwise definition.  It is not a claim that `K` is
continuous or measurable.

For `z in S`,

```text
K(f z)
  = J(g(f z))^(-1)
  = J(z)^(-1),
```

using the left inverse law `g(f z)=z`.

Since `J(z)>0`, the extended nonnegative real densities cancel:

```text
ofReal(J z) * ofReal(K(f z))
  = ofReal(J z) * ofReal((J z)^(-1))
  = ofReal(J z) * (ofReal(J z))^(-1)
  = 1.
```

The last step uses that `ofReal(J z)` is neither `0` nor `top`: positivity gives
nonzero, and `ofReal` is finite.

For `y in T`, `g y in S`, hence

```text
K(y) = J(g y)^(-1) > 0.
```

Again, this is pointwise positivity on the target chart, not a local boundedness
or continuity statement.

## Conditional unweighted pushforward

Let `m` be an additive Haar measure on the ambient tuple space.  The previous
checkpoint proved the weighted change of variables identity

```text
f_* ((m|S).withDensity (ofReal o J)) = m|T.
```

Assume explicitly:

```text
F(z) = ofReal(J z)        is a.e.-measurable with respect to m|S,
G(y) = ofReal(K y)        is a.e.-measurable with respect to m|T,
G(f z)                   is a.e.-measurable with respect to m|S.
```

The map `f` is a.e.-measurable on `m|S` from continuity on the determinant-chart
subtype, and therefore also with respect to `(m|S).withDensity F` by absolute
continuity.

Using the standard transport identity for densities under a measurable map,

```text
f_* ((m|S).withDensity F).withDensity G
  = f_* (((m|S).withDensity F).withDensity (G o f)).
```

The density product rule gives

```text
((m|S).withDensity F).withDensity (G o f)
  = (m|S).withDensity (F * (G o f)).
```

The pointwise cancellation above holds on `S`, hence a.e. for `m|S`:

```text
F * (G o f) = 1.
```

Thus

```text
(m|T).withDensity G
  = f_* ((m|S).withDensity F).withDensity G
  = f_* (m|S).
```

Equivalently,

```text
f_* (m|S) = (m|T).withDensity G.
```

The measurability hypotheses are not cosmetic: they are exactly where a future
determinant-density continuity theorem would be consumed.
