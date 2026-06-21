# Reproduction - Lemma 5 Terminal Exactness Source Audit

Status: source-boundary audit; not formalisation-ready as a source-backed
no-extra theorem.

This note checks whether Aoyagi's Lemma 5 upper-bound paragraph can discharge
the supplied no-extra field

```text
terminalMinimumLabels subset branchLabelImage
```

from the Lean terminal-minimum package.

## Source

Aoyagi Lemma 5, PDF pp. 25-27, proves

```text
theta = a(ell-a)+1.
```

The first half is the upper-bound paragraph on PDF p. 26:

1. given a vector `T_{s,k}` corresponding to `lambda`, read the values
   `H_j` at the selected breakpoints;
2. Aoyagi invokes Lemma 4 to restrict the relevant values to the intervals
   `Htilde_j <= H <= Htilde'_j`, but the converse/classifier needed for a
   formal upper bound is not spelled out;
3. the interval sizes have the three-region profile already reproduced in
   Lean;
4. the sentence "Because J is increased by one for Case 1(2)" is used to pass
   from the interval count to `theta <= a(ell-a)+1`.

The lower-bound half then gives displayed formulas `(1)`--`(5)`, with
equations `(3)` and `(4)` said to construct the blow-up process in Case 1(2).
Separate reproduction has already found that the printed equations cannot be
used as complete all-branch Lemma 4 witnesses without extra guards or supplied
terminal conventions.

## What The Upper Bound Gives

Aoyagi asserts a finite upper-bound shape at the level of lambda-vectors:

```text
number of T-vectors corresponding to lambda <=
  1 + sum_{j=1}^{ell-1} |{H : Htilde_j <= H <= Htilde'_j}|
  = a(ell-a)+1.
```

The interval arithmetic and the aggregate count are elementary and already
represented in the A5 Lean development.  Reproducing the asserted upper bound
as a source-backed classifier is the strongest direction still worth probing:
it is independent of the obstructed printed lower-bound branch formulas.

## Gap Against Lean `terminalMinimumLabels`

The Lean set

```text
AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabels
```

contains introduced labels whose supplied terminal least value is zero and
whose terminal exponent equals the isolated Lemma 5 minimum numerator.

Aoyagi's upper-bound paragraph instead counts vectors `T_{s,k}` corresponding
to `lambda`.  To turn the source upper bound into Lean's no-extra containment,
one still needs a bridge with the following fields.

1. **Label-to-vector bridge.** Every introduced label in
   `terminalMinimumLabels` has a source terminal vector `T_{s,k}` in Aoyagi's
   sense.
2. **Minimum-to-lambda bridge.** The Lean conditions `leastValue=0` and
   terminal exponent equal to the isolated minimum imply that this vector is
   one of Aoyagi's vectors corresponding to `lambda`.
3. **Classifier.** Every such lambda-vector determines a counted interval
   datum, including the base vector or a pair `(j,H)` with
   `Htilde_j <= H <= Htilde'_j`.
4. **Case 1(2) uniqueness.** The source sentence that `J` increases by one
   must be made into an injectivity/nonduplication theorem for the classifier.
5. **Back-to-label bridge.** The counted datum must identify a supplied branch
   label, so the original terminal label lies in `branchLabelImage`.

None of these five bridges is currently proved from Aoyagi's PDF in the Lean
development.  The first two are also tied to the A4 terminal normal-crossing
certificate and terminal `tilde t = 0` data.

## Consequence

The no-extra field remains a supplied boundary:

```text
terminalMinimumLabels subset branchLabelImage
```

A source-backed theorem may still be possible, but its correct next target is
not the final equality.  The next target is a classifier/upper-bound theorem
with explicit hypotheses naming the five bridges above.  If these bridges are
supplied, the theorem would prove a cardinal inequality or containment below
the existing exactness package; if the bridges are reproduced from the PDF,
the no-extra field can be discharged.

## Kill Conditions

- Lemma 4 is only a sufficient criterion and does not classify all
  terminal-minimum labels.
- A terminal-minimum label cannot be canonically assigned to a counted
  interval datum.
- The Case 1(2) `J`-increase sentence is needed for uniqueness but cannot be
  converted into a finite injection.
- Lean's `terminalMinimumLabels` is not equivalent to Aoyagi's phrase
  "vectors corresponding to lambda" without extra A4 terminal-certificate
  data.

## Nonclaims

- No source-backed no-extra-minimizer theorem is proved here.
- No branch-label injectivity theorem is proved here.
- No terminal `tilde t=0`, chart coverage, transition invariant, pole order,
  normal crossings, or RLCT extraction is proved here.
