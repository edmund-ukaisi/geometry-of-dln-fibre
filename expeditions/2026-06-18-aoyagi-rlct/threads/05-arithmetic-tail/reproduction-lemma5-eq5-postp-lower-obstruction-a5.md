# Reproduction - Lemma 5 Eq5 Post-p Lower Obstruction

Status: elementary obstruction calculation; formalisation-ready.

This slice generalizes the existing all-widths-four counterexample for
Aoyagi's equation `(5)` piecewise branch.  It proves a conditional lower-bound
failure criterion for the displayed post-`p` clause.  It is not a construction
of a corrected Eq5 family and it is not a disproof of Lemma 5.

## Setup

For a supplied equation `(5)` piecewise certificate, the post-`p` branch says
that for a selected block coordinate `b` in the post range

```text
p <= b <= p + (a - alpha),
```

and a source index `S` in that block,

```text
T(S) = Htilde'_b - alpha + p - b.
```

Equivalently, since `p <= b`,

```text
T(S) = Htilde'_b - (alpha + b - p).
```

The already-formalised Htilde gap identity gives

```text
Htilde'_b - Htilde_b = intervalExcess(ell,a,b).
```

## Criterion

If

```text
intervalExcess(ell,a,b) < alpha + b - p,
```

then

```text
Htilde'_b - Htilde_b < alpha + b - p.
```

Subtracting the larger quantity `alpha+b-p` from `Htilde'_b` puts the branch
strictly below `Htilde_b`:

```text
T(S) = Htilde'_b - (alpha+b-p) < Htilde_b.
```

Thus the printed post-`p` clause fails the lower Htilde bound at that block.

## Nonclaims

- This does not construct Aoyagi's displayed source vector.
- This does not show all equation `(5)` choices fail.
- This does not supply a corrected Eq5 branch family.
- This does not prove source-label legality, terminality, chart coverage,
  classifier injectivity, pole order, normal crossings, or RLCT extraction.
