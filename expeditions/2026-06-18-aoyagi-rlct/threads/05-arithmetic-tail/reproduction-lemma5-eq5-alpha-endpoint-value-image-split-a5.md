# Reproduction - Lemma 5 Eq5 alpha endpoint value-image split

Date: 2026-06-22.

Scope: one-coordinate finite value-image bookkeeping for equation `(5)` strict
offset branches plus supplied endpoint branches.  This does not construct
Aoyagi's branch family, prove source-label legality, prove branch injectivity
or cross-coordinate disjointness, construct a classifier, prove no-extra
terminal-minimum coverage, prove an order count, prove normal crossings, or
extract RLCT data.

## Source

Aoyagi PDF p. 27, equation `(5)`, uses strict offsets

```text
1 <= alpha < p
```

subject to the same-coordinate interval guard.  In Lean the strict alpha
domain is

```text
aoyagiLemma5Eq5AlphaDomain ell a p
  = { alpha | 1 <= alpha <= min(excess_p, p-1) },
```

and the corresponding own-coordinate values form

```text
E_p = { Htilde'_p - alpha | alpha in alpha-domain }.
```

The existing finite-set lemmas identify `E_p` as the Eq5 offset-value set.
They also split the endpoint deficit:

- outside the rising region, `E_p = I_p \ {Htilde'_p}`;
- in the rising region `p <= a` and `p <= ell-a`,
  `E_p = I_p \ {Htilde'_p,Htilde_p}`.

Here `I_p` is the same-coordinate interval value set.

## Reproduction

Let `branches : Finset beta` be a supplied finite family of strict Eq5 offset
records, with supplied maps

```text
alphaOf : beta -> Nat
value : beta -> Int.
```

Assume the alpha projection covers exactly the strict alpha domain:

```text
branches.image alphaOf = aoyagiLemma5Eq5AlphaDomain ell a p,
```

and that every branch has the Eq5 strict-offset value:

```text
value b = Htilde'_p - alphaOf b.
```

Then the existing value-image bridge gives

```text
branches.image value = E_p.
```

Now assume supplied endpoint branch records `upper` and `lower`, with

```text
value upper = Tupper(C.point p - 1),
Tupper(C.point p - 1) = Htilde'_p,
```

and, in the rising case,

```text
value lower = Tlower(C.point p - 1),
Tlower(C.point p - 1) = Htilde_p.
```

The existing endpoint-deficit split gives either:

```text
insert Htilde'_p E_p = I_p
```

or the rising case:

```text
insert Htilde'_p (insert Htilde_p E_p) = I_p.
```

Rewriting `E_p` as `branches.image value` and rewriting the supplied endpoint
values turns these into:

```text
(insert upper branches).image value = I_p
```

or

```text
(insert upper (insert lower branches)).image value = I_p.
```

This theorem is designed to feed the coordinate-wise `value_image` hypothesis
of `AoyagiLemma5SuppliedNonbaseFamily.ofCoordinateValueCoverage` after the
caller supplies the remaining global data: base-value membership, value
injectivity, and cross-coordinate disjointness.

## Lean Target

```text
aoyagiLemma5Eq5_alphaIndexedBranch_suppliedEndpointCoverage_value_image_split
```

## Nonclaims

- No construction of the Eq5 branch records.
- No proof that the supplied endpoint branches are legal source branches.
- No source-label legality; use the existing source-label wrappers separately.
- No branch injectivity, base-value membership, or cross-coordinate
  disjointness.
- No supplied nonbase family construction by itself.
- No counted-datum classifier, terminal-minimum no-extra theorem, order count,
  pole order, normal crossings, or RLCT extraction.
