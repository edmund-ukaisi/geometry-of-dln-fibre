# Statement card - A5 Lemma 4 same-coordinate binary-delta free count

## Lean Artifact

File:

- `lean/DLNFibre/DLN/Aoyagi/HtildeChainArithmetic.lean`

Names:

- `DLNFibre.DLN.Aoyagi.aoyagiLemma4F_twoValue_of_binaryIncrementPrefixDelta`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma4_sameCoordinateChain_binaryIncrementPrefixDelta_freeHighCount_lemma3A_eq_min`

## Statement

Lean now packages the existing same-coordinate `Htilde` chain-bound interface
and the named binary prefix-delta interface into the finite Lemma 4-to-Lemma 3
free-count conclusion.

Under a supplied coordinate map from vector entries to chain entries,
componentwise bounds

```text
Tlo <= T <= Thi
```

give

```text
Htilde_j <= H_j <= Htilde'_j.
```

If the named prefix deltas are binary, then the Lemma 4 increments are
two-valued, and the free high count among the first `ell-1` positions attains
the isolated Lemma 3 numerator minimum.

## Proved

- The named-delta bridge:
  `Delta_j in {0,1}` implies `F_j in {M-1,M}`.
- Same-coordinate vector bounds plus binary prefix deltas imply the existing
  free-count Lemma 3 equality conclusion.

## Assumed

- A supplied coordinate map `coord`.
- Componentwise vector bounds read in those same coordinates.
- Source convention `H_0=m_0`.
- Selected-width sum `sum m = ell*(M-1)+a`.
- Source range bound `a <= ell`.
- Binary prefix deltas.

## Cited

- None in Lean.  This is finite arithmetic and pointwise order.

## Deferred

- The source `T -> (H_j),(S_j)` correspondence.
- Binary prefix deltas from source exponent vectors.
- Vector admissibility and terminal exponent rewriting.
- Correspondence to `lambda`.
- Lemma 5 chart-family admissibility, coverage, exclusions, and pole-order
  interpretation.
- Normal crossings and RLCT extraction.

## Review

- Source/math target comparison by xhigh `Darwin`.
- Lean/API target by xhigh `Poincare`.
- Landed-patch review passed by xhigh `Raman` after adding the explicit
  `a <= ell` documentation assumption.

## Verification

- `lake env lean DLNFibre/DLN/Aoyagi/HtildeChainArithmetic.lean`
