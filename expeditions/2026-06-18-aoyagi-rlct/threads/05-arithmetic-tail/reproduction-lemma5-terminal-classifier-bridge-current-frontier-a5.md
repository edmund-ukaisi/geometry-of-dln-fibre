# Reproduction - Lemma 5 terminal-classifier bridge current frontier

Date: 2026-07-02.

Status: source reproduction and obstruction record; not a Lean implementation
target yet.

## Goal

Test whether Aoyagi Lemma 5 can currently be followed step by step to produce
one of the remaining Lean fields:

```text
TC.TerminalMinimumCountDatumClassifier
TC.UpperBoundClassifier
TC.TerminalMinimumCountDatumBackToBranchLabel
```

for the terminal-candidate family API in
`lean/DLNFibre/DLN/Aoyagi/Lemma5TerminalBridge.lean`.

## Source Reproduction

Definition 3 chooses selected positions `S_1,...,S_(ell+1)` and selected
widths `M(S_j)`.  It defines `M` and `a` by

```text
M - 1 < (sum_j M(S_j))/ell <= M,
a = sum_j M(S_j) - (M-1)*ell.
```

Theorem 2 states the order formula

```text
theta = a*(ell-a)+1.
```

Lemma 3 proves the isolated integer minimum

```text
A(a-1) = A(a) = a*ell*(ell-a).
```

Aoyagi then defines the two endpoint chains `Htilde_j` and `Htilde'_j`.
Their terminal endpoints agree:

```text
Htilde_ell = Htilde'_ell = 0.
```

Lemma 4 has the following logical form:

```text
if Ttilde <= T_{s,k} <= Ttilde'
and the associated increments are all M-1 or M,
then T_{s,k} corresponds to lambda.
```

This direction is sufficient for producing examples, but it is not a
classifier for all vectors corresponding to `lambda`.

In Lemma 5, Aoyagi then argues that if a vector has same-coordinate value

```text
t_{s,k}^{(S_{j+1}-1)} = H_j,
```

then the relevant values are counted by intervals

```text
Htilde_j <= H <= Htilde'_j.
```

The interval sizes have the three-region profile:

```text
j + 1                                      for j <= min(a, ell-a),
min(a, ell-a) + 1                          for min(a, ell-a)+1 <= j <= max(a, ell-a),
min(a, ell-a) + 1 + max(a, ell-a) - j      for max(a, ell-a)+1 <= j <= ell.
```

The already-formalized interval-excess arithmetic proves

```text
1 + sum_{j=1}^{ell-1} (|[Htilde_j,Htilde'_j]| - 1)
  = a*(ell-a)+1.
```

The source then says that because `J` is increased by one in Case 1(2), one
has

```text
theta <= a*(ell-a)+1.
```

For the lower count, the source displays families `(1)`--`(5)` and says that
families `(3)` and `(4)` construct the blow-up process in Case 1(2).

## Translation Attempt Into Lean

The Lean set

```text
TC.terminalMinimumLabels
```

is not defined as Aoyagi's set of vectors corresponding to `lambda`.  It is a
finite set of introduced labels with supplied terminal least value zero and
terminal exponent equal to `aoyagiLemma5MinNumerator`.

Thus the source upper count cannot be applied directly.  To use it one must
first prove:

```text
label in TC.terminalMinimumLabels
  -> source vector T_{s,k} corresponding to lambda.
```

The existing Lean finite-count API then offers two routes.

First, construct a counted-datum classifier:

```text
classify : TC.terminalMinimumLabels -> AoyagiLemma5CountDatum
mapsTo   : classify label in aoyagiLemma5CountDatumSet
injOn    : classify is injective on TC.terminalMinimumLabels.
```

Second, construct a no-extra branch classifier:

```text
forall label in TC.terminalMinimumLabels,
  exists x in TC.fullBranches, TC.branchLabel x = label.
```

The stronger back-to-label route combines both:

```text
exists x in TC.fullBranches,
  TC.branchLabel x = label
  and branchCountDatumOfCoord x = classify label.
```

## Current Failure Points

### Lemma 4 is one-way

Lemma 4 proves a sufficient condition for correspondence to `lambda`.  The
upper-bound use in Lemma 5 needs either a converse or an independent theorem
that every terminal-minimum label satisfies the Lemma 4 hypotheses.

The current Lean API has conditional Eq5 and first-nonbase routes, but they
assume the relevant terminal payloads and injectivity data rather than
deriving them from the PDF.

### The counted datum is not specified

Aoyagi's upper-bound paragraph counts possible interval values.  It does not
define a deterministic map from an arbitrary terminal-minimum label to one of
those values.

The Lean first-nonbase selector is a reasonable deterministic finite
tie-breaker.  However, it is a Lean construction, not a source theorem.  The
selector remains useful only under a supplied injectivity hypothesis.

### `J`-increase is not an injection theorem

The source sentence about `J` increasing in Case 1(2) is not yet a formal
nonduplication proof.  A Lean classifier would need an implication saying that
two labels with the same counted datum must have the same branch history and
hence the same `(s,k)`.

No such implication is stated in the source or present in the current Lean
development.

### Displayed families do not yet give back-to-label

The displayed families `(1)`--`(5)` are formulas for candidate vectors.  The
Lean back-to-label field needs produced terminal branch payloads with legal
source labels and compatible branch labels.

The existing blocked audit records two concrete obstructions:

- Equation `(3)` has label-legality failures from Definition 3 alone.
- Equation `(4)` needs extra own-coordinate and selected-index guards beyond
  the printed `j0 <= a`.

Both also require terminal-endpoint conventions if they are to prove
terminal least value zero.

## Consequence

The source currently supports the already-formalized finite arithmetic:

```text
aoyagiLemma5IntervalSize_excess_sum_Icc
terminalMinimumLabels_card_le_of_countDatumClassifier
terminalMinimumLabels_card_le_of_eq5EndpointChain_firstInteriorNonbase
```

and the conditional terminal-exactness/cardinal-squeeze wrappers.

It does not currently supply an unconditional proof of:

```text
TC.TerminalMinimumCountDatumClassifier
TC.UpperBoundClassifier
TC.TerminalMinimumCountDatumBackToBranchLabel
Set.InjOn TC.branchLabel TC.fullBranches
```

from Aoyagi pp. 24-27 alone.

## Next Work If A5 Is Reopened

The next A5 source-moving attempt should not be another wrapper.  It should
start with an independent finite certificate for terminal source vectors:

```text
sourceTerminalVector(label)
lambdaCorrespondence(label)
countDatum(label)
countDatum_mem(label)
countDatum_injOn
backToBranchLabel(label)
branchLabel_injOn
```

Only after these fields have a pen-and-paper proof should Lean implementation
begin.  The existing Lean APIs are already adequate consumers for such a
certificate.

## Nonclaims

No counted-datum classifier, source terminal-vector classifier,
back-to-label map, branch-label injectivity, no-extra theorem, exact order
count, pole order, normal crossings, or RLCT extraction is proved here.
