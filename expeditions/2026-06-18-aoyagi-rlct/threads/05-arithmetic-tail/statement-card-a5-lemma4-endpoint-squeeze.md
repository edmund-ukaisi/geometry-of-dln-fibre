# Statement card - A5 Lemma 4 endpoint squeeze

## Lean Artifact

Files:

- `lean/DLNFibre/DLN/Aoyagi/Lemma4CountArithmetic.lean`

Names:

- `DLNFibre.DLN.Aoyagi.aoyagiLemma4TerminalEndpoint`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma4TerminalEndpoint_eq_zero_of_selectedSum`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma4_Hlast_eq_zero_of_terminalEndpoint_bounds`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma4_twoValueCount_of_terminalEndpointBounds`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma4_terminalEndpointBounds_freeHighCount_lemma3A_eq_min`

## Statement

Lean now proves the terminal endpoint arithmetic in Aoyagi's Lemma 4 proof.
The two displayed extremal endpoints `Htilde_ell` and `Htilde'_ell` share the
common endpoint expression

```text
sum_j M(S_j) - (a*M + (ell-a)*(M-1)),
```

and this expression is zero under Definition 3's selected-width sum.  Thus a
terminal `H_ell` squeezed between the two endpoint values is zero.

## Proved

- The common terminal endpoint expression.
- Endpoint zero under `a <= ell` and `sum M(S_j)=ell*(M-1)+a`.
- The endpoint squeeze theorem `endpoint <= H_ell <= endpoint -> H_ell=0`.
- A wrapper for the Lemma 4 two-value count using endpoint bounds instead of
  an explicit `H_ell=0` hypothesis.
- A wrapper for the Lemma 4 free-count-to-Lemma 3 bridge using endpoint bounds.

## Assumed

- The selected-width sum.
- `a <= ell`.
- The endpoint sandwich.
- For the count wrappers, the two-value increment hypothesis and `H_0=M(S_1)`.

## Cited

- None in Lean.  This is finite arithmetic.

## Deferred

- Full definitions of `Htilde` and `Htilde'`.
- The formal bridge from `Ttilde <= T <= Ttilde'` to the endpoint sandwich.
- The two-value increment hypothesis.
- Vector admissibility and correspondence to `lambda`.
- Lemma 5 chart-family admissibility, coverage, and order count.
- Normal crossings and RLCT extraction.

## Review

- Reproduction:
  `reproduction-lemma4-endpoint-squeeze-a5.md`.
- Review artifact:
  `review-lemma4-endpoint-squeeze-a5.md`.

## Verification

- From `lean/`: `lake env lean DLNFibre/DLN/Aoyagi/Lemma4CountArithmetic.lean`
- From `lean/`: `lake env lean DLNFibre.lean`
- From `lean/`: `lake build DLNFibre`
- From `lean/`: `./scripts/sorries`
