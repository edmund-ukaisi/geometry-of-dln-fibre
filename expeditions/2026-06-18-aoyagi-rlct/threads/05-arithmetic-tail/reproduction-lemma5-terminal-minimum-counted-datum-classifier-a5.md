# Reproduction - Lemma 5 terminal-minimum counted-datum classifier

Status: supplied classifier boundary; formalisation-ready.

This slice packages the source-facing upper-bound strategy separately from the
branch-label exactness API.  The candidate set is the finite set of terminal
minimum labels already defined in Lean:

```text
terminalMinimumLabels =
  introduced labels with leastValue = 0
  and terminalExponent = aoyagiLemma5MinNumerator.
```

## Supplied classifier

Assume a counted-datum classifier

```text
classify : terminalMinimumLabels -> AoyagiLemma5CountDatum
```

whose image lies in

```text
aoyagiLemma5CountDatumSet (n+1) a M m C.family.baseValue
```

and which is injective on `terminalMinimumLabels`.

This is exactly the finite injection that Aoyagi's p. 26 interval-count
paragraph suggests but does not prove in a formal classifier form.

## Count

The existing counted-datum classifier theorem gives

```text
terminalMinimumLabels.card <= a*((n+1)-a)+1
```

from:

1. `hell : 1 <= n+1`, which is `Nat.succ_pos n`;
2. `ha : a <= n+1`;
3. the supplied base-value membership already carried by the supplied Lemma 5
   branch family.

This count is an upper bound only.  It does not require or prove that
terminal-minimum labels are the same as the supplied branch-label image.

## Nonclaims

- No classifier is constructed from Aoyagi's printed equations.
- No source vector-to-chain correspondence is proved.
- No branch-label injectivity or no-extra exactness is proved.
- No back-to-label coverage is proved.
- No terminal-label equality, pole order, normal crossings, or RLCT extraction
  is proved.
