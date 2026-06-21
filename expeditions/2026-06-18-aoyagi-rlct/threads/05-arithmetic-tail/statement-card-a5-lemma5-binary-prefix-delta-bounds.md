# Statement Card - A5 Lemma 5 Binary Prefix-Delta Bounds

## Lean Names

- `DLNFibre.DLN.Aoyagi.aoyagiIntegerPrefix_binaryDelta_bounds`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma4IncrementPrefix_bounds_of_terminalH_binaryIncrementPrefixDelta`
- `DLNFibre.DLN.Aoyagi.aoyagiHtildeChainBounds_of_terminalH_binaryIncrementPrefixDelta`
- `DLNFibre.DLN.Aoyagi.aoyagiHtilde_interval_mem_of_terminalH_binaryIncrementPrefixDelta`

## Claim

If a prefix sequence has binary successive deltas, starts at `0`, and ends at
`a`, then its `j`th prefix lies between the low-first and high-first binary
count bounds:

```text
min(a, j-(ell-a)) <= D_j <= min(j,a).
```

The subtraction `j-(ell-a)` is natural-number truncated subtraction.

For Aoyagi's increment prefix

```text
D_j = P(j) - H_j - j*(M-1),
```

the terminal source hypotheses `H_0=m_0`, `H_ell=0`, and the selected-width
sum give `D_0=0` and `D_ell=a`.  A supplied binary-delta hypothesis therefore
implies the prefix-delta bounds required by
`aoyagiHtildeChainBounds_of_incrementPrefix_bounds`.

## Inputs

- `ha : a <= ell`.
- Source endpoint hypotheses:
  `H 0 = m 0`,
  `H (Fin.last ell) = 0`,
  and
  `sum m = ell*(M-1)+a`.
- Supplied binary deltas:
  `aoyagiLemma4IncrementPrefixDelta ell M m H j = 0 or = 1` for every
  `j : Fin ell`.

## Proves

The Aoyagi wrapper proves

```text
aoyagiHtildeUpperHighCount ell a j.val <= D_j
D_j <= aoyagiHtildeLowerHighCount a j.val
```

for every `j : Fin (ell+1)`, and consequently

```text
aoyagiHtildeLowerChain ell a M m <= H
H <= aoyagiHtildeUpperChain ell a M m
```

and interval membership for every coordinate.

## Does Not Prove

- That Aoyagi source exponent vectors have binary prefix deltas.
- The source `T -> (H_j),(S_j)` coordinate correspondence.
- The Lemma 5 upper-bound classifier from terminal lambda-vectors to counted
  interval data.
- Case 1(2) uniqueness, back-to-label coverage, pole order, normal crossings,
  or RLCT extraction.

## Source

This is elementary finite arithmetic supporting Aoyagi's Lemma 5 interval
count on PDF p. 26.  It is independent of the quiver-based paper and remains
below the source classifier frontier.
