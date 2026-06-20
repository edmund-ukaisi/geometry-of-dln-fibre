# Statement card - A5 Lemma 4 two-value count

## Lean Artifact

Files:

- `lean/DLNFibre/DLN/Aoyagi/Lemma4CountArithmetic.lean`
- `lean/DLNFibre.lean`

Names:

- `DLNFibre.DLN.Aoyagi.twoStepInt_count_eq`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma4_twoValueCount_int`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma4_twoValueCount_le_ell`

## Statement

Lean now proves the elementary finite count used in Aoyagi's Lemma 4: if an
`ell`-indexed integer family takes only the values `M-1` and `M`, and its sum
is `ell*(M-1)+a`, then exactly `a` entries are equal to `M` and exactly
`ell-a` entries are equal to `M-1`.

## Proved

- A reusable two-step theorem for values `lo` and `lo+1`.
- The Aoyagi-shaped theorem for values `M-1` and `M`.
- The same hypotheses force `a <= ell`.

## Assumed

- Every indexed entry is one of the two values.
- The sum identity `sum F_j = ell*(M-1)+a`.

## Cited

- None in Lean.  This is finite arithmetic.

## Deferred

- The source proof that the sum identity follows from `H_ell=0`.
- The `H_0` convention needed to write `F_1` uniformly.
- The vector inequalities `Ttilde <= T <= Ttilde'`.
- Lemma 4's conclusion that the vector corresponds to `lambda`.

## Review

- Reproduction:
  `reproduction-lemma4-two-value-count-a5.md`.
- Review artifact:
  `review-lemma4-two-value-count-a5.md`.

## Verification

- From `lean/`: `lake env lean DLNFibre/DLN/Aoyagi/Lemma4CountArithmetic.lean`
