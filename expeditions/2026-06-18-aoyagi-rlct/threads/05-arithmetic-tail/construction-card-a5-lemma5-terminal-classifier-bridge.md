# Construction Card - A5 Lemma 5 terminal-classifier bridge

Date: 2026-07-02.

Status: frontier specification; not formalisation-ready as a source-backed
Lean theorem.

## Source Scope

Allowed source: Aoyagi 2023 preprint only.

Relevant source pages:

- PDF pp. 8-9: Definition 3 and Theorem 2 notation, including
  `theta = a(ell-a)+1`.
- PDF pp. 24-25: Lemma 3 minimum
  `A(a-1)=A(a)=a*ell*(ell-a)` and the displayed `Htilde`, `Htilde'`
  endpoint chains.
- PDF p. 25: Lemma 4, a sufficient criterion for a vector `T_{s,k}` to
  correspond to `lambda`.
- PDF p. 26: Lemma 5 upper-count paragraph, interval sizes, and the sentence
  that `J` is increased by one in Case 1(2).
- PDF pp. 26-27: displayed families `(1)`--`(5)` for the lower-count
  construction, with `(3)` and `(4)` used in Case 1(2).

No quiver-paper fact is part of this card.  The normal-crossing-to-RLCT
extraction remains outside this finite A5 bridge.

## Lean Boundary

The current Lean boundary is in
`lean/DLNFibre/DLN/Aoyagi/Lemma5TerminalBridge.lean`.

For a supplied terminal-candidate family `TC`, Lean defines

```text
TC.terminalMinimumLabels
```

as introduced labels whose supplied terminal least value is zero and whose
terminal exponent is the Lemma 5 minimum numerator.

The remaining source-facing fields are:

```text
TC.TerminalMinimumCountDatumClassifier
TC.UpperBoundClassifier
TC.TerminalMinimumCountDatumBackToBranchLabel
Set.InjOn TC.branchLabel TC.fullBranches
```

Existing files such as `Lemma5Eq5TerminalClassifier.lean` and the endpoint
family cardinal-squeeze wrappers consume conditional Eq5 payloads,
counted-datum injectivity, branch-label injectivity, and endpoint-family
equalities.  They do not construct those data from Aoyagi's displayed
families.

## Target Bridge Fields

A source-backed Lemma 5 terminal-classifier bridge would have to provide the
following fields.

### 1. Label-to-source-vector

For every

```text
label in TC.terminalMinimumLabels
```

construct a source vector `T_{s,k}` in Aoyagi's notation, together with the
associated selected cutpoints and chain values `H_j`.

This is stronger than unpacking the Lean label `(s,k)`: it must prove that the
label is represented by the same kind of source object that Lemma 4 and Lemma
5 discuss.  In particular it must include source-label legality, the selected
coordinate convention, and the terminal `tilde t = 0`/least-value-zero
interpretation in the Aoyagi recurrence.

### 2. Minimum-to-lambda

Prove that the terminal-minimum hypotheses on the Lean label imply that the
constructed source vector is one of Aoyagi's vectors "corresponding to
lambda".

Lemma 4 is not enough by itself: it says that if a vector lies between
`Ttilde` and `Ttilde'` and its increments are all `M-1` or `M`, then it
corresponds to `lambda`.  A classifier needs the opposite direction or an
independent theorem showing that every Lean terminal-minimum label satisfies
the Lemma 4 hypotheses.

### 3. Counted datum

Define a deterministic map

```text
TC.terminalMinimumLabels -> AoyagiLemma5CountDatum
```

where the codomain is either the base datum or a pair `(j,H)` satisfying the
same-coordinate interval condition

```text
Htilde_j <= H <= Htilde'_j.
```

The interval-size arithmetic and codomain cardinality are already in Lean.
What is missing is the source-backed rule choosing a datum for an arbitrary
terminal-minimum label.

The existing first-nonbase selector is a valid finite Lean tie-breaker, but it
is not Aoyagi's source classifier unless one proves that the source count uses
that tie-breaker or that the tie-breaker is injective on the source terminal
labels.

### 4. Injection/nonduplication

Prove that the counted-datum map is injective on
`TC.terminalMinimumLabels`.

The sentence on PDF p. 26 that `J` is increased by one in Case 1(2) records a
step in the blow-up process.  To use it here one would need a finite theorem
of the following form:

```text
same counted datum for two terminal-minimum labels
  -> same Case 1(2) J-progress certificate
  -> same source branch
  -> same label.
```

No such theorem is currently present in the source reproduction or Lean API.

### 5. Back-to-label/no-extra

To discharge `TC.UpperBoundClassifier`, or the stronger
`TC.TerminalMinimumCountDatumBackToBranchLabel`, the counted datum must
identify a supplied branch label:

```text
exists x in TC.fullBranches,
  TC.branchLabel x = label
```

and, for the stronger bridge, the branch's counted datum must agree with the
classifier value.

This requires source-produced versions of the displayed lower-bound families,
not just formula-level vectors.  The branch must have a legal source label,
terminal payload data, a branch coordinate/value, and compatibility with the
terminal-candidate family.

## Source Obstructions

The current source reproduction leaves the bridge blocked for concrete
reasons.

1. Lemma 4 is a sufficient criterion.  It does not classify all terminal
   minimizers or all vectors corresponding to `lambda`.
2. The Lemma 5 upper-count paragraph asserts the interval count but does not
   define a Lean-level classifier from arbitrary terminal-minimum labels to
   interval data.
3. The Case 1(2) `J`-increase sentence is not an injectivity proof.
4. Equations `(3)` and `(4)` have guard and terminal-endpoint issues already
   recorded in `blocked-audit-lemma5-displayed-family-realisation-a5.md`.
   Equation `(3)` has source-label legality failures from Definition 3 alone;
   equation `(4)` needs additional own-coordinate and selected-index guards.
5. The displayed families `(1)`--`(5)` do not by themselves produce the Lean
   terminal-family equality, terminal Eq5 payloads, `(p,alpha)` injectivity,
   branch-label injectivity, or a counted-datum-preserving back-to-label map.

## Formalisation Recommendation

Do not add another conditional Lean wrapper unless it removes a concrete
remaining supplied field.

The next source-moving A5 theorem would require a new independent finite
construction, not merely a direct transcription of the PDF.  A suitable
future target would be a source certificate record with exactly the five
bridge fields above.  Once such a certificate is reproduced on paper, the
existing Lean APIs can consume it through one of the already-proved routes:

```text
terminalMinimumLabels_card_le_of_countDatumClassifier
terminalMinimumLabels_card_le_of_upperBoundClassifier
terminalMinimumLabels_card_le_of_countDatumBackToBranchLabel
terminalMinimumLabelExactness_of_countDatumBackToBranchLabel
terminalMinimumLabelExactness_iff_branchLabel_injOn_and_card_bound
```

Until then, A5 should remain a supplied finite boundary inside the Aoyagi-only
expedition, separate from the allowed analytic citation for
normal-crossing-to-RLCT extraction.

## Kill Conditions

- If Lemma 4 remains only one-way, it cannot by itself classify
  `TC.terminalMinimumLabels`.
- If `terminalMinimumLabels` cannot be identified with Aoyagi source vectors
  corresponding to `lambda`, the upper-count paragraph cannot discharge the
  Lean no-extra field.
- If the `J`-increase sentence cannot be made into an injection theorem, it
  cannot supply `TC.TerminalMinimumCountDatumClassifier.injOn`.
- If equations `(3)` and `(4)` need additional legality, terminal-zero, or
  index guards, they cannot provide an unconditional back-to-label map.
- If the displayed families remain formula-level rather than produced branch
  payloads, they cannot fill `TC.UpperBoundClassifier` or
  `TC.TerminalMinimumCountDatumBackToBranchLabel`.

## Nonclaims

No source-backed counted-datum classifier, branch-label injectivity,
back-to-label map, no-extra terminal-minimum theorem, terminal exactness,
order count, pole-order statement, normal-crossing theorem, or RLCT
extraction is proved here.
