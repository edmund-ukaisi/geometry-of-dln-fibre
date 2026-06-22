# Reproduction - Lemma 5 terminal exactness cardinal-bound equivalence

Date: 2026-06-22.

Status: finite obstruction equivalence; formalisation-ready.

## Source Anchor

Aoyagi PDF pp. 25-27, especially the Lemma 5 counting paragraph.  The source
gives the intended terminal-order count, but the expedition audits record that
the printed paragraph does not by itself supply a Lean-level classifier,
branch-label injection, or back-to-label map for every terminal-minimum label.

This slice does not try to construct those source maps.  It isolates the exact
finite obstruction after supplied branches are already known to attain the
terminal minimum.

## Finite Calculation

Let

```text
B = C.fullBranches
I = C.branchLabelImage
T = C.terminalMinimumLabels
N = a * (n + 1 - a) + 1.
```

Existing Lean facts supply:

1. `I subset T`: every supplied branch label attains the terminal minimum.
2. If `branchLabel` is injective on `B`, then `|I| = |B|`.
3. The supplied family count gives `|B| = N`.

Therefore branch-label injectivity gives

```text
|I| = N.
```

If, in addition, a later source argument supplies only the numeric upper bound

```text
|T| <= N,
```

then `I subset T`, `|I| = N`, and `|T| <= N` imply `T = I`.  This is exactly
the no-extra field in `TerminalMinimumLabelExactness`.

Conversely, if `TerminalMinimumLabelExactness` holds, it supplies the branch
label injection, and the existing exact-count theorem gives

```text
|T| = N,
```

hence `|T| <= N`.

Thus:

```text
TerminalMinimumLabelExactness
  iff branchLabel injective on fullBranches
      and terminalMinimumLabels.card <= a*(n+1-a)+1.
```

## Lean Targets

Add the generic helper and equivalence in `Lemma5TerminalBridge.lean`:

```text
terminalMinimumLabels_eq_branchLabelImage_of_card_bound_and_branchLabel_injOn
terminalMinimumLabelExactness_iff_branchLabel_injOn_and_card_bound
```

## Nonclaims

This does not prove the upper cardinal bound from Aoyagi's source.  It does
not construct a classifier, branch-label injection, back-to-label map,
source-label legality, minimum-to-lambda bridge, chart coverage, pole order,
normal crossings, or RLCT extraction.
