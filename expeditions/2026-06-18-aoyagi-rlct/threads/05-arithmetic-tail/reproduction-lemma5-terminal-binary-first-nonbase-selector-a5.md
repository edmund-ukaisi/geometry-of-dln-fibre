# Reproduction - Lemma 5 terminal binary first-nonbase selector

Status: finite maps-to adapter; source-faithful only as conditional
bookkeeping under supplied terminal binary chain data.

## Source Position

The counted-datum codomain used for the Lemma 5 upper-bound boundary separates
the supplied base case from same-coordinate nonbase values in the intervals

```text
Htilde_j <= H_j <= Htilde'_j,     1 <= j <= ell-1.
```

The printed upper-bound paragraph supports the following conditional maps-to
step: once a terminal chain `H` is already known to have the binary
prefix-delta properties used by Lemma 4, each non-base interior value `H_j`
lands in the counted interval codomain.  It does not provide a canonical
classifier, an injection, or a back-to-label map.

## Finite Selector

Fix `ell`, a terminal chain `H : Fin (ell+1) -> Int`, and supplied base values
`baseValue : Nat -> Int`.

Define the finite set of nonbase interior coordinates by scanning the source
range:

```text
{ j in Icc 1 (ell-1) : H(aoyagiLemma5InteriorCoord ell j) != baseValue j }.
```

If this finite set is empty, the selector returns the base datum:

```text
none.
```

If it is nonempty, let `j0` be its least element and return the nonbase
counted datum

```text
some (j0, H_j0).
```

The use of the least element is only a deterministic Lean tie-breaker.  The
argument below never uses it for source uniqueness.

## Maps-To Argument

Assume the terminal binary-prefix-delta hypotheses:

```text
a <= ell,
H_0 = m_0,
H_ell = 0,
sum_i m_i = ell*(M-1)+a,
Delta_r in {0,1} for every r : Fin ell.
```

If the nonbase-coordinate set is empty, the selected datum is `none`, and
`none` belongs to the counted-datum set by the base insertion.

If the set is nonempty, the least coordinate `j0` is still an element of
`Icc 1 (ell-1)`, and its defining filter condition gives

```text
H_j0 != baseValue j0.
```

The already-proved terminal binary maps-to theorem then gives

```text
some (j0, H_j0) in aoyagiLemma5CountDatumSet ell a M m baseValue.
```

Thus the total first-nonbase-or-base selector always lands in the counted
datum set under the same supplied terminal binary hypotheses.

## Boundary Checks

- If `ell=0` or `ell=1`, the source range `Icc 1 (ell-1)` is empty, so the
  selector returns `none`.
- If every interior value agrees with `baseValue`, the filter is empty and the
  selector returns `none`.
- If at least one interior coordinate is nonbase, the selected coordinate is
  an actual member of `Icc 1 (ell-1)`, so the existing
  `aoyagiLemma5InteriorCoord` coercion is available.
- With a single nonbase coordinate, the selected datum is exactly that
  coordinate-value pair.

## Nonclaims

This does not construct Aoyagi's source vectors, classify all terminal
minimum labels, prove injectivity, prove no-extra coverage, prove
back-to-label coverage, construct Eq3/Eq4/Eq5 branches, identify pole order,
prove normal crossings, or extract RLCT data.
