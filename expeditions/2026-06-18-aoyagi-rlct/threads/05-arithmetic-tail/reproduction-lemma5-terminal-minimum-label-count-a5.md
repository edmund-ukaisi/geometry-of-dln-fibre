# Reproduction - Lemma 5 Terminal Minimum Label Count

Status: supplied no-extra boundary; ready for a narrow Lean wrapper.

This note records the finite-set calculation after the supplied branch-label
image count.  It defines the current exact-minimum label set and separates the
proved candidate-inclusion direction from the supplied no-extra direction.

## Minimum Numerator

For total increment length `n+1`, the supplied Lemma 3 minimum numerator is

```text
N_min(n,a) = a*(n+1)*((n+1)-a).
```

Lean names this expression

```text
aoyagiLemma5MinNumerator n a.
```

## Finite Exact-Minimum Label Set

Work inside the finite introduced-label domain

```text
introducedLabelFinset L width S J.
```

Define `terminalMinimumLabels` to be the introduced labels `label=(s,k)` such
that

```text
leastValue(s,k) = 0
terminalExponent(t(s,k)) = N_min(n,a).
```

This is a finite set by construction.  It is not a pole-order set by itself:
it does not include chart coverage, normal-crossing unit data, or analytic
extraction.

## Proved Inclusion

The supplied branch-label image already has branchwise candidate data.  If

```text
label in branchLabelImage,
```

then there is `x in fullBranches` with

```text
label = branchLabel(x).
```

The previous terminal-candidate theorem gives

```text
introducedLabel(label),
leastValue(label)=0,
terminalExponent(label)=N_min(n,a).
```

Therefore

```text
branchLabelImage subset terminalMinimumLabels.
```

This is only the easy direction: every supplied candidate is a minimum label.

## Supplied No-Extra Boundary

To get an exact count, supply the reverse containment

```text
terminalMinimumLabels subset branchLabelImage.
```

This is the no-extra-minimizer boundary: every introduced label with least
value zero and terminal exponent equal to the supplied minimum numerator is
one of the supplied branch labels.

Together with the proved inclusion, this gives

```text
terminalMinimumLabels = branchLabelImage.
```

If the branch-label map is also injective on `fullBranches`, the previous
image-count theorem gives

```text
|branchLabelImage| = a*(n+1-a)+1.
```

Thus

```text
|terminalMinimumLabels| = a*(n+1-a)+1.
```

## Lean Targets

```text
aoyagiLemma5MinNumerator
AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabels
AoyagiLemma5SuppliedTerminalCandidateFamily.mem_terminalMinimumLabels
AoyagiLemma5SuppliedTerminalCandidateFamily.branchLabelImage_subset_terminalMinimumLabels
AoyagiLemma5SuppliedTerminalCandidateFamily.terminalMinimumLabels_card_of_noExtra
```

## Kill Conditions

- Do not prove the reverse containment from Aoyagi's printed equations unless
  the terminal label classification has been independently reproduced.
- Do not confuse `leastValue=0` with a source-backed proof of terminal
  `tilde t=0`; in this slice it remains supplied through the candidate family.
- Do not call `terminalMinimumLabels.card` a pole order without the cited
  normal-crossing extraction interface.
- Do not infer chart coverage, normal crossings, or RLCT data from this finite
  count.

## Nonclaims

- No source-backed no-extra-minimizer theorem is proved.
- No chart coverage or normal-crossing theorem is proved.
- No pole-order, `lambda`, `theta`, or RLCT theorem is proved.
