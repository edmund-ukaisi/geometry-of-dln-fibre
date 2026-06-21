# Statement Card - A5 Lemma 5 Prefix-Delta Chain Bounds

## Lean Names

- `DLNFibre.DLN.Aoyagi.aoyagiHtildeChainBounds_of_incrementPrefix_bounds`
- `DLNFibre.DLN.Aoyagi.aoyagiHtilde_interval_mem_of_incrementPrefix_bounds`

## Claim

For an intermediate `H` chain, supplied bounds on the prefix delta

```text
min(a, j-(ell-a)) <= D_j <= min(j,a)
```

imply the displayed chain bounds

```text
Htilde <= H <= Htilde'
```

and therefore interval membership for every coordinate.

The subtraction `j-(ell-a)` is natural-number truncated subtraction.

## Inputs

- For every `j : Fin (ell+1)`,
  `aoyagiHtildeUpperHighCount ell a j.val <= D_j`.
- For every `j : Fin (ell+1)`,
  `D_j <= aoyagiHtildeLowerHighCount a j.val`.
- For interval membership only: `ha : a <= ell`.

## Proves

```text
aoyagiHtildeLowerChain ell a M m <= H
H <= aoyagiHtildeUpperChain ell a M m
```

and

```text
H j in aoyagiHtildeIntervalValueSet ell a M m j
```

for every `j`.

## Does Not Prove

- The prefix-delta bounds from binary increments.
- Source vector classification.
- Case 1(2) uniqueness or back-to-label coverage.
- Terminal-label exactness, pole order, normal crossings, or RLCT extraction.

## Source

This is the elementary algebra behind the interval-membership part of
Aoyagi's Lemma 5 upper-bound discussion on PDF p. 26.  The source classifier
itself remains open.
