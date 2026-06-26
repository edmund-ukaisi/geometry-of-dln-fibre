# Statement card - A5 Lemma 5 minimum numerator residue normalization

## Lean Name

File:

- `lean/DLNFibre/DLN/Aoyagi/Lemma5TerminalBridge.lean`

Name:

- `DLNFibre.DLN.Aoyagi.aoyagiLemma5MinNumerator_div_four_sq_eq_theorem2ResidueTerm`

## Claim

For `ell = n+1`, the isolated Lemma 5 minimum numerator contributes exactly
Aoyagi Theorem 2's residue term after division by the normal-crossing
denominator `4*ell^2`:

```text
((aoyagiLemma5MinNumerator n a : Q) / (4 * ((n+1 : Nat) : Q)^2))
  = ((a : Q) * (((n+1 : Nat) : Q) - (a : Q)))
      / (4 * ((n+1 : Nat) : Q)).
```

## Proved

Lean proves the rational cancellation.  The proof unfolds
`aoyagiLemma5MinNumerator`, normalizes the integer cast, proves `n+1 != 0` in
`Q`, and clears the denominator.

## Assumed

None beyond `n a : Nat`.

## Cited

None.  This is finite rational arithmetic over definitions already introduced
from Aoyagi's Lemma 3/Lemma 5 and Theorem 2 notation.

## Deferred

The source proof that a terminal exponent has numerator
`aoyagiLemma5MinNumerator`, active-ratio minimality, terminal-label exactness,
chart coverage, pole order, normal crossings, and RLCT extraction.

## Structure and Route

The pen-and-paper calculation is the one-line cancellation

```text
a ell (ell-a) / (4 ell^2) = a(ell-a)/(4 ell),
```

using `ell = n+1` and `ell != 0`.  Lean keeps the integer numerator definition,
so the formal proof first normalizes its cast to `Q`.

## Verification

Focused module build passed:

```text
cd lean
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.Lemma5TerminalBridge
```

Independent xhigh review passed in
`review-lemma5-min-numerator-residue-normalization-a5.md`.

Downstream build, sorry scan, and whitespace checks passed:

```text
cd lean
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.Theorem2TerminalOrderBridge
scripts/sorries
git diff --check
```

`scripts/sorries` reported `0 sorry`, `0 #exit`, `0 native_decide`, and
`0 axiom`.
