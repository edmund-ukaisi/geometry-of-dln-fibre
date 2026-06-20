# Review - A5 Lemma 4 same-coordinate binary-delta free count

Reviewer: xhigh `Raman`.

Scope:

- `aoyagiLemma4F_twoValue_of_binaryIncrementPrefixDelta`;
- `aoyagiLemma4_sameCoordinateChain_binaryIncrementPrefixDelta_freeHighCount_lemma3A_eq_min`;
- reproduction, statement card, and ledger updates.

## Findings

Low documentation issue: the reproduction and statement card initially omitted
the explicit source range bound `a <= ell` / `a <= n+1`, while the Lean theorem
has this hypothesis and the endpoint-zero step depends on it.

Resolution: the reproduction and statement card now list the `a <= ell`
assumption explicitly.

## Verdict

Pass after documentation fix.

No Lean/API overclaim was found.  The helper and wrapper are conditional finite
arithmetic: `coord`, componentwise bounds, selected sum, `H_0=m_0`, `a<=ell`,
and binary deltas remain supplied.  The wrapper does not assert source
vector-to-chain correspondence, vector admissibility, Lemma 5, pole order,
normal crossings, or RLCT extraction.

The ledger updates keep Lemma 5 equations `(3)` and `(4)` source-family
realisation open.

## Commands Run

- `lake env lean DLNFibre/DLN/Aoyagi/HtildeChainArithmetic.lean`
- forbidden-token scan for `sorry`, `axiom`, `native_decide`, `#exit` in
  `lean/DLNFibre/DLN/Aoyagi/HtildeChainArithmetic.lean`
- `git diff --check`
