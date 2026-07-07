# Reproduction - A2 dominated zero-locus nullity handoff

Date: 2026-07-07.

Status: generic Lean infrastructure proved locally.

## Claim

A recurring remaining hypothesis in the rank-cut original-prior local-loss
bridge is a zero-locus nullity statement for a restricted edge-family measure:

```text
mu {x | f x = 0} = 0.
```

The reusable measure-theory part is independent of Aoyagi coordinates:

```text
nu <= c • mu,
forall^ae x with respect to mu, 0 < f x
------------------------------------------------
nu {x | f x = 0} = 0.
```

This is the exact abstract handoff needed whenever an original-prior piece is
dominated by a source/reference measure for which the residual square-sum is
known positive almost everywhere.

## Proof

First, scalar domination transfers nullity of sets:

```text
nu <= c • mu,
mu s = 0
----------------
nu s = 0.
```

Indeed,

```text
nu s <= (c • mu) s = c * mu s = c * 0 = 0.
```

Second, if `0 < f x` holds `mu`-almost everywhere, then the zero locus of `f`
is contained in the exceptional set where `not (0 < f x)`.  Hence

```text
mu {x | f x = 0} = 0,
```

and scalar domination gives the same nullity for `nu`.

## Nonclaims

- No concrete original-prior domination theorem.
- No readback/source-chart residual equality.
- No residual positivity theorem for the original edge-family prior.
- No source-rank or analytic atlas coverage.
- No prior transport, determinant/raw Haar transport, normal crossings,
  pole order, or RLCT extraction.

This is a reusable measure socket only.  The Aoyagi-specific zero-locus theorem
still needs the correct dominated measure, the correct residual function, and
the existing source-side a.e. positivity theorem to be aligned.
