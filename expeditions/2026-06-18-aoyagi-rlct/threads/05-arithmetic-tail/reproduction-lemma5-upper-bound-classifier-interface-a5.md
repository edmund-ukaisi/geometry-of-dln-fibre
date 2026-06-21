# Reproduction - Lemma 5 Upper-Bound Classifier Interface

Status: supplied classifier interface; formalisation-ready as finite
bookkeeping, not source-backed exactness.

This note records the next honest boundary after the terminal-exactness source
audit.  Aoyagi's upper-bound paragraph in Lemma 5 counts source
lambda-vectors by interval data, but the current Lean terminal-minimum set is a
finite set of introduced labels with supplied least-value and terminal-exponent
certificates.  The bridge from these Lean labels to Aoyagi's counted vectors is
not yet reproduced from the PDF.

## Source Boundary

A source-backed proof of

```text
terminalMinimumLabels subset branchLabelImage
```

would need, at minimum, the following chain.

1. Every Lean terminal-minimum label has an Aoyagi terminal vector `T_{s,k}`.
2. The Lean conditions `leastValue=0` and minimum terminal exponent imply that
   the source vector corresponds to `lambda`.
3. Each such lambda-vector has a counted upper-bound datum: either the base
   vector or a pair `(j,H)` in Aoyagi's interval
   `Htilde_j <= H <= Htilde'_j`.
4. The Case 1(2) assertion that `J` increases by one gives the needed
   uniqueness/nonduplication for that classifier.
5. The counted datum identifies a supplied branch label, so the original Lean
   label is in `branchLabelImage`.

The first two fields already depend on the terminal certificate boundary from
A4: source labels, `\tilde t=0`, and the normalisation of Lean
`terminalExponent` against Aoyagi's `M_{s,k}`.

## Supplied Interface

The narrow interface is therefore:

```text
UpperBoundClassifier C:
  for every label in C.terminalMinimumLabels,
  there exists x in C.fullBranches with C.branchLabel x = label.
```

This is exactly the no-extra direction, phrased as a classifier that produces
a counted supplied branch.  It does not include branch-label injectivity.

## Consequences

From `UpperBoundClassifier C`, Lean can prove the finite containment

```text
C.terminalMinimumLabels subset C.branchLabelImage.
```

Combining this containment with the elementary bound
`branchLabelImage.card <= fullBranches.card` and the existing supplied branch
count gives the upper cardinal inequality

```text
C.terminalMinimumLabels.card <= a*(n+1-a)+1.
```

This upper count does not need branch-label injectivity.  If one also supplies
branch-label injectivity, the classifier packages into the existing
`TerminalMinimumLabelExactness` structure.  The exact equality of cardinalities
still uses the already proved easy inclusion
`branchLabelImage subset terminalMinimumLabels`, whose proof depends on the
selected-width sum and the supplied terminal-numerator bridge.

## Nonclaims

- The classifier is not proved from Aoyagi's printed paragraph.
- No label-to-vector bridge or minimum-to-lambda bridge is proved.
- No Case 1(2) uniqueness theorem is proved.
- No pole order, normal crossings, `theta`, or RLCT extraction is proved.
