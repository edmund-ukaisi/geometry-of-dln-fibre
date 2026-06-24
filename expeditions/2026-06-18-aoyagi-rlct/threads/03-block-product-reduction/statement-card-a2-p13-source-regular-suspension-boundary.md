# Statement Card - A2 p.13 source regular-suspension boundary

## Claim

Aoyagi pp. 10-14 support the elementary source-side p. 13 block and finite
loss-comparison boundary, but they do not by themselves supply a Lean-ready
regular-suspension/RLCT construction.

## Source

Aoyagi 2023 preprint, printed pp. 10-14:

- p. 10: Lemma 2 one-block Schur reduction.
- pp. 11-13: Theorem 3 product block diagonalisation.
- p. 13: literal product-difference block and displayed learning-coefficient
  shift.
- p. 14: Theorem 4 invocation before reducing the residual analysis to
  `r(s)=r`.

## Formal Shape

The next safe Lean target is a source-side wrapper, not an RLCT theorem:

```text
real rank/source data
  -> exists fixed-base regular-coordinate source data
  -> eventually, in the source-rank stratum,
       literal p.13 square-sum <= 2 * cleaned p.13 square-sum
       and cleaned p.13 square-sum <= 2 * literal p.13 square-sum.
```

It should reuse the existing source-data constructor and factor-`2` theorem.

## Boundary

This is finite real square-sum/source-data packaging only.  It does not
construct `Cfull`, prove analytic regular coordinates, prove analytic ideal
transport, compute Jacobians, produce normal crossings, prove pole order, or
extract an RLCT.

## Reproduction

`reproduction-a2-p13-source-regular-suspension-boundary.md`

## Review

`review-a2-p13-source-regular-suspension-boundary.md`
