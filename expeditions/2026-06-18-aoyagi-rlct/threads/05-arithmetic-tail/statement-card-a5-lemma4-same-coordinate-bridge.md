# Statement card - A5 Lemma 4 same-coordinate bridge

## Lean Artifact

Files:

- `lean/DLNFibre/DLN/Aoyagi/Lemma4CountArithmetic.lean`

Names:

- `DLNFibre.DLN.Aoyagi.aoyagiLemma4_terminalEndpointBounds_of_sameCoordinate`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma4_Hlast_eq_zero_of_sameCoordinate`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma4_twoValueCount_of_sameCoordinate`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma4_sameCoordinate_freeHighCount_lemma3A_eq_min`

## Statement

Lean now proves a conservative bridge from componentwise vector bounds to the
terminal endpoint sandwich, under an explicit same-coordinate correspondence:
if `Tlo <= T <= Thi` and the terminal endpoint values of all three vectors are
read from the same coordinate `p`, then the endpoint of `T` is squeezed
between the common terminal endpoint values of `Tlo` and `Thi`.

Together with the selected-width endpoint-zero calculation, this gives
`H_ell=0` and feeds the existing finite Lemma 4 count wrappers.

## Proved

- Same-coordinate componentwise bounds imply
  `endpoint <= H_ell <= endpoint`.
- With `a <= ell` and the selected-width sum, the same-coordinate bridge gives
  `H_ell=0`.
- A wrapper for the Lemma 4 two-value count using same-coordinate bounds.
- A wrapper for the Lemma 4 free-count-to-Lemma 3 bridge using
  same-coordinate bounds.

## Assumed

- The componentwise vector inequalities `Tlo <= T <= Thi`.
- The same endpoint coordinate `p` is used to read the lower endpoint, middle
  endpoint, and upper endpoint.
- The selected-width sum and `a <= ell`.
- For the count wrappers, the two-value increment hypothesis and
  `H_0=M(S_1)`.

## Cited

- None in Lean.  This is finite order arithmetic.

## Deferred

- A source-faithful unique correspondence `T -> (H_j),(S_j)`.
- Proof that Aoyagi's displayed `Ttilde <= T <= Ttilde'` supplies the
  same-coordinate hypotheses.
- Full definitions of `Htilde` and `Htilde'`.
- The two-value increment hypothesis.
- Vector admissibility and correspondence to `lambda`.
- Lemma 5 chart-family admissibility, coverage, and order count.
- Normal crossings and RLCT extraction.

## Review

- Reproduction:
  `reproduction-lemma4-same-coordinate-bridge-a5.md`.
- Review artifact:
  `review-lemma4-same-coordinate-bridge-a5.md`.

## Verification

- From `lean/`: `lake env lean DLNFibre/DLN/Aoyagi/Lemma4CountArithmetic.lean`
- From `lean/`: `lake env lean DLNFibre.lean`
- From `lean/`: `lake build DLNFibre`
- From `lean/`: `./scripts/sorries`
