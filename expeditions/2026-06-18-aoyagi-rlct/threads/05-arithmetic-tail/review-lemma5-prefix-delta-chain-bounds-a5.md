# Review - Lemma 5 Prefix-Delta Chain Bounds

Reviewer: Hooke, xhigh effort.

Status: passed after documentation correction.

## Scope

Reviewed:

- `reproduction-lemma5-prefix-delta-chain-bounds-a5.md`
- `statement-card-a5-lemma5-prefix-delta-chain-bounds.md`
- the prefix-delta additions in
  `lean/DLNFibre/DLN/Aoyagi/HtildeChainArithmetic.lean`

The review checked the algebra translating prefix-delta bounds into displayed
`Htilde` chain bounds, the use of `a <= ell`, and source-boundary clarity.

## Findings

The Lean algebra is correct:

```text
D_j <= min(j,a)
```

is exactly `Htilde_j <= H_j`, and

```text
min(a, j-(ell-a)) <= D_j
```

is exactly `H_j <= Htilde'_j` under the Lean definitions.

Two documentation precision issues were found and corrected:

1. interval-value-set membership needs the extra source range hypothesis
   `a <= ell`, although the chain-bound algebra itself does not;
2. `j-(ell-a)` is Lean's natural-number truncated subtraction, not integer
   subtraction.

## Verdict

No remaining overclaim found.  The slice does not prove binary-delta bounds,
source classification, branch construction, terminal-label exactness, pole
order, normal crossings, or RLCT extraction.
