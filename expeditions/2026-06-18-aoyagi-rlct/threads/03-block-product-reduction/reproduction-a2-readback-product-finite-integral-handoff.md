# Reproduction - A2 readback product finite-integral handoff

Status: pen-and-paper reproduction completed and formalized in Lean.

This is a generic measure-theoretic handoff.  It is meant to be used after an
edge-family prior has been read back to source coordinates, but it contains no
Aoyagi-specific determinant, density, or normal-crossing calculation.

## Question

Suppose a measure `mu` on an edge-family chart `E` is read back to source
coordinates `Theta` by a measurable map

```text
readback : E -> Theta
```

and suppose the source chart is a right inverse on the support of `mu`:

```text
sourceChart (readback x) = x
```

for `mu`-a.e. `x`.  If the pushforward source measure is dominated by a finite
scalar multiple of a reference source measure,

```text
map readback mu <= C * thetaMu,
C < infinity,
```

and a product integrand is finite after pulling it back along `sourceChart`,

```text
int^- (theta, beta),
  F (sourceChart theta, beta)
  d(thetaMu.prod eta)
< infinity,
```

does the original edge-family product integral

```text
int^- (x, beta), F (x, beta) d(mu.prod eta)
```

also have finite lower integral?

Answer: yes.  This is pure product-measure and pushforward bookkeeping.

## Calculation

Define

```text
Fsource(theta, beta) = F(sourceChart theta, beta),
readbackProd(x, beta) = (readback x, beta).
```

The product pushforward identity gives

```text
map readbackProd (mu.prod eta) = (map readback mu).prod eta.
```

The scalar domination on the left factor therefore transfers to product
measures:

```text
(map readback mu).prod eta <= C * (thetaMu.prod eta).
```

Since `C < infinity`, finite lower integral over `thetaMu.prod eta` implies
finite lower integral over `(map readback mu).prod eta`:

```text
int^- z, Fsource z d((map readback mu).prod eta) < infinity.
```

By the map formula for lower integrals, this is the same as

```text
int^- z, Fsource (readbackProd z) d(mu.prod eta) < infinity.
```

The right-inverse hypothesis pulls through the product projection:

```text
sourceChart (readback z.1) = z.1
```

for `mu.prod eta`-a.e. `z`.  Hence the last integrand agrees a.e. with
`F z`, and lower-integral congruence gives

```text
int^- z, F z d(mu.prod eta) < infinity.
```

## Lean target

The formalized theorem is in
`lean/DLNFibre/DLN/Aoyagi/LocalMeasureHandoff.lean`:

```text
lintegral_prod_lt_top_of_readback_map_le_smul
```

It depends on the earlier scalar-product handoff

```text
lintegral_prod_lt_top_of_left_measure_le_smul
```

and exposes the following hypotheses: measurable readback, the a.e.
right-inverse identity, finite scalar map domination, measurability of the
source-chart pullback integrand, and source-side finite integral.

## Boundary

This proves no localized with-following finite-integral wrapper by itself.  In
particular it does not prove measurable readback for the
`Case2PassiveThetaWithFollowingFactor` endpoint source chart, does not provide
a with-following source-side finite-integral theorem, and does not compare
with-following coordinate source measure to the older passive-theta finite
integral sockets.

It also proves no determinant-Haar transport, source-density positivity,
original source-prior origin, source/image coverage, normal crossings, pole
order, or RLCT extraction.
