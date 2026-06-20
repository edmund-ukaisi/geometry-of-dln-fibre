# Statement card - A5 Lemma 4 binary prefix delta

## Lean Artifact

Files:

- `lean/DLNFibre/DLN/Aoyagi/HtildeChainArithmetic.lean`

Names:

- `DLNFibre.DLN.Aoyagi.aoyagiLemma4IncrementPrefix`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma4F_eq_pred_add_incrementPrefixDelta`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma4F_twoValue_of_binaryIncrementPrefix`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma4_twoValueCount_of_terminalH_binaryIncrementPrefix`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma4_twoValueCount_of_HtildeChainBounds_binaryIncrementPrefix`

## Statement

Lean now proves a conditional bridge for Aoyagi Lemma 4's two-value increment
hypothesis.  For an arbitrary finite `H`-chain, define

```text
D_j = P(j) - H_j - j*(M-1).
```

Then

```text
F_j = (M-1) + (D_(j+1)-D_j).
```

Consequently, if every successive prefix delta `D_(j+1)-D_j` is `0` or `1`,
then every `F_j` is `M-1` or `M`.

## Proved

- The prefix-delta identity for arbitrary `m`, `H`, and `M`.
- Binary prefix deltas imply the finite two-value increment hypothesis.
- Terminal-`H` Lemma 4 count wrapper using binary prefix deltas.
- Same-coordinate `Htilde`-chain-bound count wrapper using binary prefix
  deltas.

## Assumed

- For the binary bridge, the binary prefix-delta hypothesis.
- For count wrappers, the same terminal/selected-width hypotheses required by
  existing Lemma 4 wrappers.
- For the `Htilde`-chain-bound wrapper, same-coordinate chain bounds.

## Cited

- None in Lean.  This is finite arithmetic.

## Deferred

- Source exponent vectors imply binary prefix deltas.
- Same-coordinate `Htilde <= H <= Htilde'` bounds imply binary prefix deltas.
- A source-faithful `T -> (H_j),(S_j)` correspondence.
- Vector admissibility and correspondence to `lambda`.
- Lemma 5 chart-family admissibility, coverage, exclusions, and pole-order
  interpretation.
- Normal crossings and RLCT extraction.

## Review

- Reproduction:
  `reproduction-lemma4-binary-prefix-delta-a5.md`.
- Review artifact:
  `review-lemma4-binary-prefix-delta-a5.md`.

## Verification

- From `lean/`: `lake env lean DLNFibre/DLN/Aoyagi/HtildeChainArithmetic.lean`
- From `lean/`: `lake env lean DLNFibre.lean`
- From `lean/`: `lake build DLNFibre`
- From `lean/`: `./scripts/sorries`
